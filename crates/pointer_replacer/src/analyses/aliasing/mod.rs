//! Detects call sites where a mutable raw-pointer argument and one or more
//! immutable raw-pointer arguments to the same local callee are derived from the
//! same base.
//!
//! Base admissibility is recorded on each candidate as data for copy planning,
//! not used as a candidacy filter: every same-base call site feeds the callee's
//! alias cluster regardless of whether the caller's base will ever be promoted.
//!
//! Detected candidates then pass through per-site gates that plan the copies
//! (`gate_candidates`: the callee must never write through the read-only
//! parameters, and each read-only argument needs bounds evidence — an exact
//! read prefix or a whole caller-local array), and a per-callee selection
//! (`select_callees`) that keeps only callees whose every alias-inducing call
//! site is resolved, so the inserted copies actually dissolve the callee's
//! mutable alias cluster.
//!
//! `rewriter::rewrite_aliasing` drives the detect → gate → select stages and
//! emits the copies.
#![allow(dead_code)]

use points_to::andersen;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, def_id::LocalDefId};
use rustc_middle::{
    mir::{Body, CastKind, Const, Local, Location, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{self, Ty, TyCtxt, adjustment::PointerCoercion},
};

use crate::{
    analyses::{
        access_order::{
            AccessOrderAnalysis, AccessOrderVerdict, CallFrame, QueryError, WriteVerdict,
        },
        array_local_provenance::{ArrayLocalProvenance, BaseAdmissibility, BaseId},
        read_extent::{Extent, ReadExtentAnalysis, call_context},
    },
    utils::rustc::RustProgram,
};

#[cfg(test)]
mod tests;

/// A call site where a mutable and one or more immutable raw-pointer arguments
/// share the same base. Arguments are identified by their 0-based position in
/// the call's argument list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotCandidate {
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub location: Location,
    pub base: BaseId,
    /// The base's classification, so copy planning can tell promotable array
    /// bases from bases that only support a call-site copy.
    pub admissibility: BaseAdmissibility,
    pub mut_params: Vec<usize>,
    pub imm_params: Vec<usize>,
}

struct ArgInfo<'tcx> {
    index: usize,
    is_mut: bool,
    pointee: Ty<'tcx>,
    admissibility: BaseAdmissibility,
}

/// The calls that make an argument-index pair alias, keyed by the pair.
pub type PairSites = FxHashMap<(usize, usize), Vec<(LocalDefId, Location)>>;

/// For each local callee, the 0-based argument-index pairs whose points-to sets
/// intersect at some direct call, with the calls that create each pair. The pair
/// judgment matches `rewriter::find_param_aliases`, which reports the pairs
/// without their call sites; only the site attribution is new here.
#[derive(Debug, Default)]
pub struct AliasPairSites {
    pub pairs: FxHashMap<LocalDefId, PairSites>,
}

pub fn attribute_alias_pairs<'tcx>(
    tcx: TyCtxt<'tcx>,
    pre: &andersen::PreAnalysisData<'tcx>,
    solutions: &andersen::Solutions,
) -> AliasPairSites {
    let mut result = AliasPairSites::default();
    // Pairs are over the callee's parameters; extra (variadic) call arguments
    // beyond the parameter count are not part of the judgment.
    let mut arg_counts: FxHashMap<LocalDefId, usize> = FxHashMap::default();

    // The caller set must match the bodies the points-to pre-analysis recorded
    // calls from: free functions except `main`, plus statics.
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        match item.kind {
            ItemKind::Fn { ident, .. } if ident.name.as_str() != "main" => {}
            ItemKind::Static(..) => {}
            _ => continue,
        }
        let caller = item.owner_id.def_id;
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();

        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call { func, args, .. } = &block_data.terminator().kind else {
                continue;
            };
            let Some(func_const) = func.constant() else {
                continue;
            };
            let Const::Val(_, func_ty) = func_const.const_ else {
                continue;
            };
            let ty::TyKind::FnDef(callee_def_id, _) = func_ty.kind() else {
                continue;
            };
            let Some(callee) = callee_def_id.as_local() else {
                continue;
            };
            // Only callees whose calls the pre-analysis recorded have argument
            // points-to sets to compare.
            if !pre.call_args.contains_key(&callee) {
                continue;
            }
            let arg_count = *arg_counts.entry(callee).or_insert_with(|| {
                tcx.mir_drops_elaborated_and_const_checked(callee)
                    .borrow()
                    .arg_count
            });

            // Constant operands have no points-to set; the pre-analysis also
            // records only place operands. Projections are irrelevant: the
            // points-to variable is the place's base local.
            let arg_locs: Vec<Option<andersen::Loc>> = args
                .iter()
                .take(arg_count)
                .map(|a| {
                    a.node.place().and_then(|p| {
                        pre.vars
                            .get(&andersen::Var::Local(caller, p.local))
                            .copied()
                    })
                })
                .collect();

            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            for i in 0..arg_locs.len() {
                for j in 0..i {
                    let (Some(loc_i), Some(loc_j)) = (arg_locs[i], arg_locs[j]) else {
                        continue;
                    };
                    let mut sol = solutions[loc_i].clone();
                    sol.intersect(&solutions[loc_j]);
                    if !sol.is_empty() {
                        result
                            .pairs
                            .entry(callee)
                            .or_default()
                            .entry((j, i))
                            .or_default()
                            .push((caller, location));
                    }
                }
            }
        }
    }
    result
}

pub fn detect_snapshot_candidates<'tcx>(
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    access_order: &AccessOrderAnalysis<'_, 'tcx>,
    trace: bool,
) -> Vec<SnapshotCandidate> {
    let tcx = input.tcx;
    let mut candidates = vec![];

    for &caller in &input.functions {
        let Some(provenance) = provenances.get(&caller) else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();

        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            // Only direct calls to a local function are eligible. Indirect calls
            // have a non-constant func operand; extern callees are not local.
            let TerminatorKind::Call { func, args, .. } = &block_data.terminator().kind else {
                continue;
            };
            let Some(func_const) = func.constant() else {
                continue;
            };
            let ty::TyKind::FnDef(callee_def_id, _) = func_const.ty().kind() else {
                continue;
            };
            let Some(callee) = callee_def_id.as_local() else {
                continue;
            };

            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            let call_access = match access_order.at_call(caller, location) {
                Ok(call_access) => call_access,
                Err(error) => {
                    if trace {
                        snapshot_skip(
                            tcx,
                            "DETECT",
                            caller,
                            callee,
                            location,
                            &query_error_evidence(tcx, &error),
                        );
                    }
                    continue;
                }
            };

            // Group raw-pointer arguments by their unique non-null base.
            let mut by_base: FxHashMap<BaseId, Vec<ArgInfo<'tcx>>> = FxHashMap::default();
            for (index, arg) in args.iter().enumerate() {
                let operand = &arg.node;
                let arg_ty = operand.ty(&body.local_decls, tcx);
                let ty::TyKind::RawPtr(pointee, mutbl) = arg_ty.kind() else {
                    continue;
                };
                let Some(ob) = provenance.unique_non_null_base_of_operand(operand, &body, tcx)
                else {
                    continue;
                };
                by_base.entry(ob.base).or_default().push(ArgInfo {
                    index,
                    is_mut: mutbl.is_mut(),
                    pointee: *pointee,
                    admissibility: ob.admissibility,
                });
            }

            for (base, group) in by_base {
                // Need at least one mutable and one immutable raw-pointer argument.
                let mut_params: Vec<usize> =
                    group.iter().filter(|a| a.is_mut).map(|a| a.index).collect();
                let imm_params: Vec<usize> = group
                    .iter()
                    .filter(|a| !a.is_mut)
                    .map(|a| a.index)
                    .collect();
                if mut_params.is_empty() || imm_params.is_empty() {
                    continue;
                }

                // The snapshot copies between these arguments, so their pointee
                // element types must be identical after region erasure.
                let mut pointees = group.iter().map(|a| tcx.erase_regions(a.pointee));
                let first = pointees.next().expect("group is non-empty");
                if !pointees.all(|p| p == first) {
                    continue;
                }

                // Keep the call site only when the call-site-sensitive analysis
                // proves that all reads precede potentially aliasing writes.
                let verdict = call_access.reads_precede_writes(&mut_params, &imm_params);
                if !matches!(verdict, AccessOrderVerdict::Proven) {
                    if trace {
                        let evidence = access_order_rejection_evidence(tcx, &verdict)
                            .expect("non-proven verdict has rejection evidence");
                        snapshot_skip(
                            tcx,
                            "DETECT",
                            caller,
                            callee,
                            location,
                            &format!(
                                "base={base:?} mut={mut_params:?} imm={imm_params:?} {evidence}"
                            ),
                        );
                    }
                    continue;
                }

                // All group members share the base, so they share its
                // classification.
                let admissibility = group
                    .first()
                    .expect("group is non-empty")
                    .admissibility
                    .clone();

                candidates.push(SnapshotCandidate {
                    caller,
                    callee,
                    location,
                    base,
                    admissibility,
                    mut_params,
                    imm_params,
                });
            }
        }
    }

    candidates
}

/// A candidate that passed every per-site gate, with the copy each immutable
/// argument needs.
#[derive(Clone, Debug)]
pub struct GatedCandidate {
    pub candidate: SnapshotCandidate,
    /// One plan per entry of the candidate's `imm_params`, in order.
    pub copies: Vec<CopyPlan>,
}

/// How one immutable argument's bytes reach the snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CopyPlan {
    /// Copy `elems` elements of the argument's pointee type from the
    /// argument pointer into a fresh local array.
    ExactPrefix { arg_index: usize, elems: u64 },
    /// Copy the whole caller-local array base and re-derive the argument
    /// from the copy.
    WholeArray {
        arg_index: usize,
        base_local: Local,
        len: u64,
    },
}

/// Applies the per-site gates and plans the copies. Detection already
/// required reads through the immutable arguments to precede writes; a
/// candidate additionally needs its callee to never write through those
/// parameters (the write would land in the dropped copy and be lost), and
/// every immutable argument needs bounds evidence: the exact prefix the
/// callee reads under this call's constant scalar arguments, or — when no
/// extent is known — a caller-local array base whose whole contents can be
/// copied because the callee never observes the pointer's address.
pub fn gate_candidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    candidates: Vec<SnapshotCandidate>,
    access_order: &AccessOrderAnalysis<'_, 'tcx>,
    extents: &mut ReadExtentAnalysis<'tcx>,
    trace: bool,
) -> Vec<GatedCandidate> {
    let gate_skip = |candidate: &SnapshotCandidate, reason: &str| {
        if trace {
            eprintln!(
                "SNAPSHOT_GATE_SKIP caller={} callee={} call_location={} reason={reason}",
                tcx.def_path_str(candidate.caller.to_def_id()),
                tcx.def_path_str(candidate.callee.to_def_id()),
                location_evidence(candidate.location),
            );
        }
    };
    let mut gated = vec![];
    'candidates: for candidate in candidates {
        let call_access = match access_order.at_call(candidate.caller, candidate.location) {
            Ok(call_access) => call_access,
            Err(error) => {
                gate_skip(&candidate, &query_error_evidence(tcx, &error));
                continue;
            }
        };
        let verdict = call_access.never_written(&candidate.imm_params);
        if !matches!(verdict, WriteVerdict::NeverWritten) {
            gate_skip(
                &candidate,
                &write_rejection_evidence(tcx, &verdict)
                    .expect("non-never-written verdict has rejection evidence"),
            );
            continue;
        }
        let body = tcx
            .mir_drops_elaborated_and_const_checked(candidate.caller)
            .borrow();
        let TerminatorKind::Call { args, .. } = &body.basic_blocks[candidate.location.block]
            .terminator()
            .kind
        else {
            continue;
        };
        let ctx = call_context(tcx, candidate.caller, candidate.location);
        let typing_env = ty::TypingEnv::post_analysis(tcx, candidate.caller);

        let mut copies = vec![];
        for &imm in &candidate.imm_params {
            let Some(arg) = args.get(imm) else {
                continue 'candidates;
            };
            let arg_ty = arg.node.ty(&body.local_decls, tcx);
            let ty::TyKind::RawPtr(pointee, _) = arg_ty.kind() else {
                continue 'candidates;
            };
            // Exact prefix first: it copies the fewest bytes and needs no
            // knowledge of the base.
            let extent = extents.extent(candidate.callee, imm, &ctx);
            if let Extent::Const(bytes) = extent {
                let elem_size = tcx
                    .layout_of(typing_env.as_query_input(*pointee))
                    .ok()
                    .map(|l| l.size.bytes());
                if let Some(size) = elem_size
                    && size > 0
                    && bytes % size == 0
                {
                    copies.push(CopyPlan::ExactPrefix {
                        arg_index: imm,
                        elems: bytes / size,
                    });
                    continue;
                }
            }
            // Whole-array fallback: the base must be a caller-local array of
            // known length, and the callee must never observe the pointer's
            // address, which the copy would change.
            if let BaseId::LocalArray { local } = &candidate.base
                && let ty::TyKind::Array(_, len) = body.local_decls[*local].ty.kind()
                && let Some(len) = len.try_to_target_usize(tcx)
                && !extents
                    .classify_param_uses(candidate.callee, imm)
                    .identity_observed
            {
                copies.push(CopyPlan::WholeArray {
                    arg_index: imm,
                    base_local: *local,
                    len,
                });
                continue;
            }
            gate_skip(
                &candidate,
                &format!(
                    "no copy plan for argument {imm}: extent={extent:?} ctx={ctx:?} base={:?}",
                    candidate.base
                ),
            );
            continue 'candidates;
        }
        gated.push(GatedCandidate { candidate, copies });
    }
    gated
}

fn snapshot_skip(
    tcx: TyCtxt<'_>,
    stage: &str,
    caller: LocalDefId,
    callee: LocalDefId,
    location: Location,
    evidence: &str,
) {
    eprintln!(
        "SNAPSHOT_{stage}_SKIP caller={} callee={} call_location={} reason={evidence}",
        tcx.def_path_str(caller.to_def_id()),
        tcx.def_path_str(callee.to_def_id()),
        location_evidence(location),
    );
}

fn location_evidence(location: Location) -> String {
    format!("{:?}[{}]", location.block, location.statement_index)
}

fn call_chain_evidence(tcx: TyCtxt<'_>, call_chain: &[CallFrame]) -> String {
    let frames: Vec<_> = call_chain
        .iter()
        .map(|frame| {
            format!(
                "{}->{}@{}",
                tcx.def_path_str(frame.caller.to_def_id()),
                tcx.def_path_str(frame.callee.to_def_id()),
                location_evidence(frame.location),
            )
        })
        .collect();
    format!("[{frames}]", frames = frames.join(","))
}

fn query_error_evidence(tcx: TyCtxt<'_>, error: &QueryError) -> String {
    match error {
        QueryError::MissingCallerFlow { caller } => format!(
            "query_error=missing_caller_flow caller={}",
            tcx.def_path_str(caller.to_def_id())
        ),
        QueryError::InvalidLocation { caller, location } => format!(
            "query_error=invalid_location caller={} location={}",
            tcx.def_path_str(caller.to_def_id()),
            location_evidence(*location)
        ),
        QueryError::NotCall { caller, location } => format!(
            "query_error=not_call caller={} location={}",
            tcx.def_path_str(caller.to_def_id()),
            location_evidence(*location)
        ),
        QueryError::IndirectCall { caller, location } => format!(
            "query_error=indirect_call caller={} location={}",
            tcx.def_path_str(caller.to_def_id()),
            location_evidence(*location)
        ),
        QueryError::NonLocalCallee {
            caller,
            location,
            callee,
        } => format!(
            "query_error=non_local_callee caller={} callee={} location={}",
            tcx.def_path_str(caller.to_def_id()),
            tcx.def_path_str(*callee),
            location_evidence(*location)
        ),
        QueryError::MissingCalleeSummary { callee } => format!(
            "query_error=missing_callee_summary callee={}",
            tcx.def_path_str(callee.to_def_id())
        ),
    }
}

fn access_order_rejection_evidence(
    tcx: TyCtxt<'_>,
    verdict: &AccessOrderVerdict,
) -> Option<String> {
    match verdict {
        AccessOrderVerdict::Proven => None,
        AccessOrderVerdict::MayReadAfterWrite { witness } => Some(format!(
            "hazard order={:?} write_location={} read_location={} write_base={:?} \
             write_offset={:?} read_base={:?} read_offset={:?} write_call_chain={} \
             read_call_chain={}",
            witness.order,
            location_evidence(witness.write_location),
            location_evidence(witness.read_location),
            witness.write_address.base,
            witness.write_address.offset,
            witness.read_address.base,
            witness.read_address.offset,
            call_chain_evidence(tcx, &witness.write_call_chain),
            call_chain_evidence(tcx, &witness.read_call_chain),
        )),
        AccessOrderVerdict::Unknown { reasons } => Some(format!("unknown reasons={reasons:?}")),
    }
}

fn write_rejection_evidence(tcx: TyCtxt<'_>, verdict: &WriteVerdict) -> Option<String> {
    match verdict {
        WriteVerdict::NeverWritten => None,
        WriteVerdict::MayBeWritten { witness } => Some(format!(
            "modeled_write location={} base={:?} offset={:?} call_chain={}",
            location_evidence(witness.location),
            witness.address.base,
            witness.address.offset,
            call_chain_evidence(tcx, &witness.call_chain),
        )),
        WriteVerdict::Unknown { reasons } => Some(format!("unknown reasons={reasons:?}")),
    }
}

/// The resolution status of one call site contributing an alias pair.
enum SiteStatus {
    /// A gated candidate at this site isolates the pair.
    Covered,
    /// The site passes the caller's own parameters straight through; the
    /// pair is resolved when the caller's pair is.
    Forwarded(LocalDefId, (usize, usize)),
    Blocked,
}

/// Selects the callees whose every attributed alias pair is resolved by the
/// gated candidates, iterating because a forwarding site's discharge depends
/// on the caller's own pair being resolved first. C-exposed callees are
/// selected like any other: the pointer pass rewrites their signatures too,
/// and the interface pass restores their C ABI behind a wrapper afterwards.
/// Emission applies to the covering candidates of selected callees only.
pub fn select_callees(
    tcx: TyCtxt<'_>,
    gated: &[GatedCandidate],
    pair_sites: &AliasPairSites,
    trace: bool,
) -> FxHashSet<LocalDefId> {
    // The gated candidates at each call site. A candidate isolates a pair
    // when both indices share its base and at least one is immutable:
    // immutable arguments get fresh copies, while two mutable arguments
    // keep aliasing even at a gated site.
    let mut covering: FxHashMap<(LocalDefId, Location, LocalDefId), Vec<&SnapshotCandidate>> =
        FxHashMap::default();
    for g in gated {
        let c = &g.candidate;
        covering
            .entry((c.caller, c.location, c.callee))
            .or_default()
            .push(c);
    }
    let covers =
        |caller: LocalDefId, location: Location, callee: LocalDefId, i: usize, j: usize| {
            covering
                .get(&(caller, location, callee))
                .is_some_and(|cands| {
                    cands.iter().any(|c| {
                        let in_group =
                            |x: &usize| c.mut_params.contains(x) || c.imm_params.contains(x);
                        in_group(&i)
                            && in_group(&j)
                            && !(c.mut_params.contains(&i) && c.mut_params.contains(&j))
                    })
                })
        };

    let mut statuses: FxHashMap<(LocalDefId, (usize, usize)), Vec<SiteStatus>> =
        FxHashMap::default();
    for (&callee, pairs) in &pair_sites.pairs {
        for (&(i, j), sites) in pairs {
            let entry = statuses.entry((callee, (i, j))).or_default();
            for &(caller, location) in sites {
                if covers(caller, location, callee, i, j) {
                    entry.push(SiteStatus::Covered);
                } else {
                    entry.push(forwarding_status(tcx, caller, location, i, j));
                }
            }
        }
    }

    let mut resolved: FxHashSet<(LocalDefId, (usize, usize))> = FxHashSet::default();
    loop {
        let mut changed = false;
        for (key, sites) in &statuses {
            if resolved.contains(key) {
                continue;
            }
            let done = sites.iter().all(|s| match s {
                SiteStatus::Covered => true,
                SiteStatus::Forwarded(caller, pair) => {
                    // A pair no call site ever creates cannot hold at
                    // runtime (parameters bind at a single call), so an
                    // absent dependency is vacuously resolved.
                    resolved.contains(&(*caller, *pair))
                        || !statuses.contains_key(&(*caller, *pair))
                }
                SiteStatus::Blocked => false,
            });
            if done {
                resolved.insert(*key);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let candidate_callees = gated.iter().map(|g| g.candidate.callee);
    let mut selected = FxHashSet::default();
    for callee in candidate_callees.chain(pair_sites.pairs.keys().copied()) {
        let all_resolved = pair_sites
            .pairs
            .get(&callee)
            .is_none_or(|pairs| pairs.keys().all(|&p| resolved.contains(&(callee, p))));
        if all_resolved {
            selected.insert(callee);
        } else if trace {
            for (&pair, sites) in &pair_sites.pairs[&callee] {
                if resolved.contains(&(callee, pair)) {
                    continue;
                }
                for (status, &(caller, _)) in statuses[&(callee, pair)].iter().zip(sites) {
                    let status = match status {
                        SiteStatus::Covered => continue,
                        SiteStatus::Forwarded(dep_caller, dep_pair) => format!(
                            "forwarded-to-unresolved {} {dep_pair:?}",
                            tcx.def_path_str(dep_caller.to_def_id())
                        ),
                        SiteStatus::Blocked => "blocked".to_string(),
                    };
                    eprintln!(
                        "SNAPSHOT_UNRESOLVED callee={} pair={pair:?} site={} status={status}",
                        tcx.def_path_str(callee.to_def_id()),
                        tcx.def_path_str(caller.to_def_id()),
                    );
                }
            }
        }
    }
    selected
}

/// Classifies a non-covered site: forwarding when both pair operands are the
/// caller's own distinct parameters passed unmodified, blocked otherwise.
fn forwarding_status(
    tcx: TyCtxt<'_>,
    caller: LocalDefId,
    location: Location,
    i: usize,
    j: usize,
) -> SiteStatus {
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let TerminatorKind::Call { args, .. } = &body.basic_blocks[location.block].terminator().kind
    else {
        return SiteStatus::Blocked;
    };
    let roots = (
        args.get(i)
            .and_then(|arg| param_root_of_operand(&body, &arg.node)),
        args.get(j)
            .and_then(|arg| param_root_of_operand(&body, &arg.node)),
    );
    let (Some(a), Some(b)) = roots else {
        return SiteStatus::Blocked;
    };
    // The same parameter passed twice aliases on its own; nothing upstream
    // can discharge that.
    if a == b {
        return SiteStatus::Blocked;
    }
    SiteStatus::Forwarded(caller, (a.min(b), a.max(b)))
}

/// The 0-based caller parameter an argument operand copies, when the operand
/// is the parameter's incoming value passed unmodified: an unprojected place
/// reached through single-definition plain copies and pointer casts, from a
/// parameter local that is never reassigned.
fn param_root_of_operand<'a, 'tcx>(
    body: &'a Body<'tcx>,
    operand: &'a Operand<'tcx>,
) -> Option<usize> {
    // Locals with exactly one plain-statement definition, mapped to its
    // rvalue; `None` for reassigned locals and call results.
    let mut defs: FxHashMap<Local, Option<&'a Rvalue<'tcx>>> = FxHashMap::default();
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind
                && place.projection.is_empty()
            {
                defs.entry(place.local)
                    .and_modify(|e| *e = None)
                    .or_insert(Some(rvalue));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && destination.projection.is_empty()
        {
            defs.insert(destination.local, None);
        }
    }
    let mut op = operand;
    for _ in 0..32 {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let index = place.local.as_usize();
        if index >= 1 && index <= body.arg_count {
            // A reassigned parameter local no longer names the incoming
            // value.
            return (!defs.contains_key(&place.local)).then_some(index - 1);
        }
        match defs.get(&place.local) {
            Some(Some(Rvalue::Use(inner))) => op = inner,
            Some(Some(Rvalue::Cast(
                CastKind::PtrToPtr
                | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _),
                inner,
                _,
            ))) => op = inner,
            _ => return None,
        }
    }
    None
}
