//! Detects call sites where a mutable raw-pointer argument and one or more
//! immutable raw-pointer arguments to the same local callee are derived from the
//! same base.
//!
//! Base admissibility is recorded on each candidate as data for copy planning,
//! not used as a candidacy filter: every same-base call site feeds the callee's
//! alias cluster regardless of whether the caller's base will ever be promoted.
//!
//! This is detection only. A detected candidate still requires a read-before-write
//! proof and bounds evidence before its read-only arguments can be safely isolated
//! into an immutable snapshot.
//!
//! The detection is not yet wired into the rewrite pipeline, so the public items
//! below are exercised only by tests for now.
#![allow(dead_code)]

use points_to::andersen;
use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, def_id::LocalDefId};
use rustc_middle::{
    mir::{Const, Location, TerminatorKind},
    ty::{self, Ty, TyCtxt},
};

use crate::{
    analyses::array_local_provenance::{ArrayLocalProvenance, BaseAdmissibility, BaseId},
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
    access_order: &FxHashMap<LocalDefId, outparam_replacer::ai::access_order::AccessOrderSummary>,
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

                // Keep the call site only when the callee never reads an
                // immutable-argument parameter after writing the mutable one.
                let ordered = access_order
                    .get(&callee)
                    .is_some_and(|s| s.reads_precede_writes(&mut_params, &imm_params));
                if !ordered {
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
