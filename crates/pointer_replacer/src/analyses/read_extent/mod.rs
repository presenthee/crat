//! Read-extent analysis: for a raw-pointer parameter of a local function,
//! computes the exact byte prefix `[0, K)` the function reads through that
//! parameter, specialized to call-site-constant scalar arguments (the
//! "context"). This is the bounds evidence a snapshot rewrite needs to copy
//! `[T; K]` out of an immutable argument: the copy may neither over-read (the
//! pointee is only known to hold what the callee itself reads) nor under-read
//! (the callee would run off the snapshot's end), so the may- and must-read
//! footprints have to coincide.
//!
//! The analysis is a demand-driven walk over drops-elaborated MIR. There is no
//! symbolic summary domain: the rewriter must emit a literal array length
//! anyway, so every useful query bottoms out in constants once the caller's
//! constant scalar arguments are substituted. Branches whose condition
//! const-evaluates under the context are pruned, which is what resolves
//! callees that dispatch on a block-count parameter; branches that remain must
//! read the same footprint on every arm. Calls that cannot return
//! abnormally-but-observably (core wrapping arithmetic and pointer methods,
//! the memcpy family, and abort-only allocation such as `vec::from_elem`) are
//! exempt from the every-path requirement; any other reachable call counts as
//! a possible exit that all reads must precede.
//!
//! Classified reads are direct loads at constant offsets (through `offset`
//! call chains), memcpy/memmove/copy sources (with lengths const-evaluated
//! through the wrapping-arithmetic calls C2Rust emits), whole-pointer
//! forwarding to another local function (recursively), loops reading one
//! element per iteration through an index counting up to a constant bound,
//! and count-down loops walking a cursor over the pointer in constant steps
//! with a per-iteration read of one step's worth (a direct load or a call
//! to a local function that reads that prefix and always returns).
//!
//! Call sites that fall back to copying a whole caller-side array rather
//! than an exact prefix skip the extent question, but still need to know
//! that the callee never observes the pointer *as an address* — the copy
//! has a different one. `classify_param_uses` answers that with a
//! flow-insensitive taint check over the same MIR.
//!
//! Both queries serve the copy planning in `analyses::aliasing`, driven by
//! `rewriter::rewrite_aliasing`.
#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Location, Operand, Place, ProjectionElem,
        RETURN_PLACE, Rvalue, START_BLOCK, StatementKind, TerminatorKind, UnOp,
        visit::{PlaceContext, Visitor},
    },
    ty::{self, Ty, TyCtxt, adjustment::PointerCoercion},
};

pub use super::const_eval::Ctx;
use super::const_eval::{DefSite, EvalCx, MAX_EVAL_DEPTH, collect_defs};

#[cfg(test)]
mod tests;

/// The byte footprint a function reads through one raw-pointer parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Extent {
    /// Exactly this many bytes are read through the parameter, as a contiguous
    /// prefix from offset 0, on every execution that does not abort the
    /// process.
    Const(u64),
    /// Exactly `count(v)` values of the queried raw pointer's pointee type
    /// are read as a contiguous prefix on every complete execution, where
    /// `v` is the entry value of integer parameter `param` (0-based), and
    /// `count(v)` is `max(v, 0)` for signed parameters and `v` for unsigned
    /// parameters.
    RuntimeParam {
        param: usize,
    },
    Unknown,
}

/// How a function uses one raw-pointer parameter's value.
#[derive(Debug, Default, Clone, Copy)]
pub struct ParamUseReport {
    /// The pointer's identity may be observed: compared, subtracted, cast
    /// to an integer, stored, returned, or passed to a callee this analysis
    /// cannot see into. A snapshot copy substitutes a different address, so
    /// any such use disqualifies the rewrite.
    pub identity_observed: bool,
}

/// Distinct walks per function before further queries give up.
const MAX_CONTEXTS_PER_FN: usize = 16;
/// Levels of direct local callees the parameter-use classifier follows a
/// forwarded pointer into. Three levels cover the deepest corpus chain
/// (`sha256` → `sha256_inc_finalize` → `crypto_hashblocks_sha256` →
/// `load_bigendian_32`).
const IDENTITY_FORWARD_DEPTH: usize = 3;

pub struct ReadExtentAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Cached query results, with a flag telling whether the function can
    /// only leave through a `Return` (as opposed to panicking, diverging in
    /// an unknown callee, or otherwise not coming back). Reads consumed
    /// inside a matched loop need that guarantee from their callee.
    memo: FxHashMap<(LocalDefId, usize, Ctx), (Extent, bool)>,
    contexts_per_fn: FxHashMap<LocalDefId, usize>,
    in_progress: FxHashSet<(LocalDefId, usize)>,
    /// Cached identity-observation answers, keyed by function, parameter,
    /// and remaining forwarding depth: a deeper budget can clear a function
    /// that a shallower one could not.
    identity_memo: FxHashMap<(LocalDefId, usize, usize), bool>,
}

impl<'tcx> ReadExtentAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            memo: FxHashMap::default(),
            contexts_per_fn: FxHashMap::default(),
            in_progress: FxHashSet::default(),
            identity_memo: FxHashMap::default(),
        }
    }

    /// The exact byte prefix read through `param` (0-based) of `def_id` on
    /// every complete execution under `ctx`.
    pub fn extent(&mut self, def_id: LocalDefId, param: usize, ctx: &Ctx) -> Extent {
        self.query(def_id, param, ctx).0
    }

    /// Whether the function can observe the identity of `param`'s pointer
    /// (0-based, raw). Unlike `extent`, nothing is asked about how much is
    /// read — a whole-base snapshot keeps any read inside the copied object
    /// — so reads need no constant offsets, lengths, or loop structure;
    /// only the address itself leaking matters.
    pub fn classify_param_uses(&mut self, def_id: LocalDefId, param: usize) -> ParamUseReport {
        ParamUseReport {
            identity_observed: self.identity_observed(def_id, param, IDENTITY_FORWARD_DEPTH),
        }
    }

    /// The extent plus whether the function always comes back: every way it
    /// ends is a plain return (or a process abort in a curated call).
    fn query(&mut self, def_id: LocalDefId, param: usize, ctx: &Ctx) -> (Extent, bool) {
        let key = (def_id, param, ctx.clone());
        if let Some(&cached) = self.memo.get(&key) {
            return cached;
        }
        // Cycles get no answer and no memo entry: an answer under a cycle is
        // provisional, and the code this targets has no recursion.
        if !self.in_progress.insert((def_id, param)) {
            return (Extent::Unknown, false);
        }
        let count = self.contexts_per_fn.entry(def_id).or_insert(0);
        let result = if *count >= MAX_CONTEXTS_PER_FN {
            tracing::debug!("read-extent context cap hit for {def_id:?} (param {param})");
            None
        } else {
            *count += 1;
            self.walk(def_id, param, ctx)
        };
        let result = match result {
            Some((extent, total)) => (extent, total),
            None => (Extent::Unknown, false),
        };
        self.in_progress.remove(&(def_id, param));
        self.memo.insert(key, result);
        result
    }

    fn walk(&mut self, def_id: LocalDefId, param: usize, ctx: &Ctx) -> Option<(Extent, bool)> {
        let tcx = self.tcx;
        if tcx.generics_of(def_id.to_def_id()).count() > 0 {
            return None;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let body = &*body;
        if param >= body.arg_count {
            return None;
        }
        let param_local = Local::from_usize(param + 1);
        let ty::TyKind::RawPtr(queried_pointee, _) = body.local_decls[param_local].ty.kind() else {
            return None;
        };
        let queried_pointee = *queried_pointee;
        let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
        let defs = collect_defs(body);

        // Context values and the queried pointer stand for the argument at
        // entry, so the parameter locals must not be reassigned. Two
        // exceptions, both checked after loop matching: a count parameter
        // whose only reassignment is the decrement of a matched count-down
        // loop, and the queried pointer itself when it is such a loop's
        // walking cursor (C2Rust steps the parameter in place for
        // `while (num-- > 0) { .. src += w; }`).
        let param_reassigned = defs.contains_key(&param_local);
        let mut unstable_ctx_params: Vec<Local> = vec![];
        for &i in ctx.keys() {
            if i >= body.arg_count {
                return None;
            }
            let local = Local::from_usize(i + 1);
            if defs.contains_key(&local) {
                unstable_ctx_params.push(local);
            }
        }

        let eval = EvalCx {
            tcx,
            body,
            defs: &defs,
            ctx,
            typing_env,
        };
        // A stepped-in-place parameter has no fixed offset, so nothing may
        // be derived from it: every use must be consumed by the matched
        // loop, which the closed-use check enforces through `loop_locals`.
        let derived = if param_reassigned {
            Derived {
                offsets: FxHashMap::default(),
                stmt_sites: FxHashSet::default(),
            }
        } else {
            collect_derived(body, &defs, &eval, param_local)
        };

        // Traverse the context-pruned CFG. Unknown terminator kinds fail the
        // walk rather than being skipped: not following their successors
        // would silently drop reads. Calls are only collected here; they are
        // classified after loop matching, which decides which call blocks a
        // loop consumes.
        let mut contributions: Vec<(BasicBlock, Contribution)> = vec![];
        let mut exits: FxHashSet<BasicBlock> = FxHashSet::default();
        let mut allowed_call_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
        let mut call_blocks: Vec<BasicBlock> = vec![];
        let mut successors: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        let mut reachable: FxHashSet<BasicBlock> = FxHashSet::default();
        let mut worklist = vec![START_BLOCK];
        while let Some(bb) = worklist.pop() {
            if body.basic_blocks[bb].is_cleanup || !reachable.insert(bb) {
                continue;
            }
            let mut succs = vec![];
            match &body.basic_blocks[bb].terminator().kind {
                TerminatorKind::Goto { target } => succs.push(*target),
                TerminatorKind::Drop { target, .. } => succs.push(*target),
                TerminatorKind::Assert {
                    cond,
                    expected,
                    target,
                    ..
                } => {
                    match eval.operand(cond, MAX_EVAL_DEPTH) {
                        // Statically known to pass under this context: a
                        // plain goto.
                        Some(v) if (v.bits != 0) == *expected => {}
                        // Statically failing: every execution reaching here
                        // panics, so no footprint claim is possible.
                        Some(_) => return None,
                        // May panic at runtime; reads must already have
                        // happened.
                        None => {
                            exits.insert(bb);
                        }
                    }
                    succs.push(*target);
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    match eval.operand(discr, MAX_EVAL_DEPTH) {
                        Some(v) => succs.push(targets.target_for_value(v.bits)),
                        None => succs.extend(targets.all_targets().iter().copied()),
                    }
                }
                TerminatorKind::Return => {
                    exits.insert(bb);
                }
                TerminatorKind::Unreachable => {}
                TerminatorKind::Call { target, .. } => {
                    succs.extend(*target);
                    call_blocks.push(bb);
                }
                _ => return None,
            }
            successors.insert(bb, succs.clone());
            worklist.extend(succs);
        }

        let idom = pruned_dominators(&successors, &reachable);

        // Matched loops explain pointer uses the per-call and per-statement
        // classification below cannot: an indexed read's per-iteration
        // `offset` call has a non-constant index, and a walking cursor is a
        // reassigned local with no fixed offset.
        let loops = self.match_read_loops(
            &eval,
            &derived,
            param_local,
            queried_pointee,
            param_reassigned,
            &reachable,
            &successors,
            &exits,
            &idom,
        );
        contributions.extend(loops.contributions.iter().copied());

        // A reassigned context parameter is acceptable only as the count of
        // a matched count-down loop, where the decrement is the sole
        // reassignment and the initial value is what the context names; the
        // reassigned queried pointer only as such a loop's cursor.
        if !unstable_ctx_params
            .iter()
            .all(|l| loops.exempt_count_params.contains(l))
        {
            return None;
        }
        if param_reassigned && !loops.exempt_cursor_params.contains(&param_local) {
            return None;
        }

        for bb in call_blocks {
            if loops.consumed_calls.contains(&bb) {
                allowed_call_blocks.insert(bb);
                continue;
            }
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &body.basic_blocks[bb].terminator().kind
            else {
                unreachable!("collected as a call block above");
            };
            let call = self.classify_call(&eval, &derived, func, args, destination)?;
            for read in call.reads {
                contributions.push((bb, read.into()));
            }
            if call.mentions_allowed {
                allowed_call_blocks.insert(bb);
            }
            if call.is_exit {
                exits.insert(bb);
            }
        }

        // Classify statements in reachable blocks: recognized pointer
        // derivations and direct loads through the pointer are allowed;
        // contributing loads are recorded.
        let mut allowed_statements: FxHashSet<(BasicBlock, usize)> = FxHashSet::default();
        for &bb in &reachable {
            for (i, stmt) in body.basic_blocks[bb].statements.iter().enumerate() {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if derived.stmt_sites.contains(&(bb, i)) {
                    allowed_statements.insert((bb, i));
                    continue;
                }
                // A destination involving the pointer is a write through it;
                // leave it unclassified so the mention check rejects it.
                if derived.offsets.contains_key(&place.local) {
                    continue;
                }
                let Some(loads) = classify_loads(&eval, &derived, rvalue) else {
                    continue;
                };
                if !loads.is_empty() {
                    allowed_statements.insert((bb, i));
                    for load in loads {
                        contributions.push((bb, load.into()));
                    }
                }
            }
        }

        // Every mention of the pointer (and of the per-iteration pointers of
        // matched loops) must be a recognized derivation, a classified load,
        // or sit in a classified call; anything else (stores, comparisons,
        // integer casts, escapes) defeats the exact-footprint claim.
        let mut tracked = derived.offsets.clone();
        tracked.extend(loops.loop_locals.iter().map(|&l| (l, 0)));
        let mut mentions = MentionCollector {
            derived: &tracked,
            mentions: vec![],
        };
        mentions.visit_body(body);
        for (location, context) in mentions.mentions {
            if matches!(context, PlaceContext::NonUse(_)) || !reachable.contains(&location.block) {
                continue;
            }
            let is_terminator =
                location.statement_index == body.basic_blocks[location.block].statements.len();
            let allowed = if is_terminator {
                allowed_call_blocks.contains(&location.block)
            } else {
                let site = (location.block, location.statement_index);
                allowed_statements.contains(&site) || loops.allowed_statements.contains(&site)
            };
            if !allowed {
                return None;
            }
        }

        let must = certify_contributions(body, &successors, &exits, &idom, contributions)?;

        // The union of certified reads must be a contiguous prefix starting at
        // offset 0; overlaps are fine, gaps are not. An empty footprint is not
        // useful evidence, so it gets no answer. Runtime-parameter
        // contributions may coexist only when they all name the same
        // parameter, and never alongside a constant contribution: the union
        // of a fixed byte count and a symbolic count is not expressible in
        // this domain.
        let mut intervals = vec![];
        let mut runtime_param = None;
        for contribution in must {
            match contribution {
                Contribution::Const(interval) => intervals.push(interval),
                Contribution::RuntimeParam { param } => match runtime_param {
                    Some(existing) if existing != param => return None,
                    _ => runtime_param = Some(param),
                },
            }
        }
        let extent = if let Some(param) = runtime_param {
            if !intervals.is_empty() {
                return None;
            }
            Extent::RuntimeParam { param }
        } else {
            intervals.sort_unstable();
            let mut end = 0u64;
            for iv in &intervals {
                if iv.start > end {
                    return None;
                }
                end = end.max(iv.end);
            }
            if end == 0 {
                return None;
            }
            Extent::Const(end)
        };
        // The function always comes back when its only remaining ways out
        // are plain returns; consumed in-loop calls were required to be
        // total themselves, and curated calls return or abort the process.
        let total = exits.iter().all(|&e| {
            matches!(
                body.basic_blocks[e].terminator().kind,
                TerminatorKind::Return
            )
        });
        Some((extent, total))
    }

    /// Classifies one reachable call terminator. Returns `None` (failing the
    /// whole walk) when the queried pointer is used in a way the analysis
    /// cannot account for.
    fn classify_call(
        &mut self,
        eval: &EvalCx<'_, 'tcx>,
        derived: &Derived,
        func: &Operand<'tcx>,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) -> Option<CallReads> {
        let tcx = self.tcx;

        // Loads through the pointer in argument position happen when the
        // operands are evaluated, before the call itself runs, so they are
        // fine for any callee. The pointer's own value appearing anywhere
        // else must be accounted for below.
        let mut reads: Vec<Interval> = vec![];
        let mut value_positions: Vec<usize> = vec![];
        for (i, arg) in args.iter().enumerate() {
            let Some(place) = arg.node.place() else {
                continue;
            };
            let Some(&offset) = derived.offsets.get(&place.local) else {
                continue;
            };
            if place.projection.is_empty() {
                value_positions.push(i);
            } else if place.projection[..] == [ProjectionElem::Deref] {
                let ptr_ty = eval.body.local_decls[place.local].ty;
                reads.push(load_interval(eval, offset, ptr_ty)?);
            } else {
                return None;
            }
        }
        if func
            .place()
            .is_some_and(|p| derived.offsets.contains_key(&p.local))
        {
            return None;
        }
        // A tracked destination needs no rejection here: tracked locals are
        // single-def, so it can only be the `offset` derivation accepted in
        // the curated branch below.
        let has_loads = !reads.is_empty();

        let callee = func.constant().and_then(|c| match c.ty().kind() {
            ty::TyKind::FnDef(def_id, args) => Some((*def_id, *args)),
            _ => None,
        });
        let Some((callee, generic_args)) = callee else {
            // Indirect call: fine as long as the pointer's value is not
            // passed to it.
            return value_positions.is_empty().then_some(CallReads {
                reads,
                mentions_allowed: has_loads,
                is_exit: true,
            });
        };
        let name = tcx.def_path_str(callee);

        // memcpy-family reads: the pointer may appear only as the source,
        // unprojected, with a length that const-evaluates under the context.
        if let Some((src_index, len, elem_size)) =
            memcpy_src_and_len(tcx, callee, &name, args, generic_args)
        {
            match value_positions[..] {
                [] => {
                    return Some(CallReads {
                        reads,
                        mentions_allowed: has_loads,
                        is_exit: false,
                    });
                }
                [pos] if pos == src_index => {
                    let offset = exact_local_offset(&args[pos].node, &derived.offsets)?;
                    let len = eval.operand(&len, MAX_EVAL_DEPTH)?;
                    let bytes = u64::try_from(len.bits).ok()?.checked_mul(elem_size)?;
                    let end = offset.checked_add(bytes)?;
                    reads.push(Interval { start: offset, end });
                    return Some(CallReads {
                        reads,
                        mentions_allowed: true,
                        is_exit: false,
                    });
                }
                _ => return None,
            }
        }

        // `offset` on the tracked pointer is a recognized derivation
        // (collected up front); on any other pointer it is curated pure
        // arithmetic. A tracked receiver whose derivation was not recorded
        // (non-constant amount, reassigned destination) stays unclassified.
        if is_curated_nondiverging(tcx, callee, &name) {
            if value_positions.is_empty() {
                return Some(CallReads {
                    reads,
                    mentions_allowed: has_loads,
                    is_exit: false,
                });
            }
            if value_positions == [0] && derived.offsets.contains_key(&destination.local) {
                return Some(CallReads {
                    reads,
                    mentions_allowed: true,
                    is_exit: false,
                });
            }
            return None;
        }

        // Forwarding: the pointer, at offset 0, passed whole to one parameter
        // of a direct local callee. Foreign items have no MIR to walk, and a
        // generic instantiation would need its arguments substituted.
        let forwardable = callee.as_local().filter(|&local| {
            !tcx.is_foreign_item(callee) && tcx.generics_of(local.to_def_id()).count() == 0
        });
        if let Some(local_callee) = forwardable {
            if let [pos] = value_positions[..] {
                if exact_local_offset(&args[pos].node, &derived.offsets)? != 0 {
                    return None;
                }
                let mut ctx_g = Ctx::new();
                for (j, arg) in args.iter().enumerate() {
                    let arg_ty = arg.node.ty(&eval.body.local_decls, tcx);
                    if matches!(arg_ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_))
                        && let Some(v) = eval.operand(&arg.node, MAX_EVAL_DEPTH)
                    {
                        ctx_g.insert(j, v.bits);
                    }
                }
                let Extent::Const(len) = self.extent(local_callee, pos, &ctx_g) else {
                    return None;
                };
                // The callee performs its reads before any divergence of its
                // own (its walk enforces it), so the call both contributes
                // and exits.
                reads.push(Interval { start: 0, end: len });
                return Some(CallReads {
                    reads,
                    mentions_allowed: true,
                    is_exit: true,
                });
            }
            if value_positions.is_empty() {
                return Some(CallReads {
                    reads,
                    mentions_allowed: has_loads,
                    is_exit: true,
                });
            }
            return None;
        }

        value_positions.is_empty().then_some(CallReads {
            reads,
            mentions_allowed: has_loads,
            is_exit: true,
        })
    }
}

/// The context a direct call passes to its callee: each integer argument
/// that const-evaluates in the caller's body without assuming anything
/// about the caller's own parameter values, keyed by 0-based argument
/// position. `location` must be a call terminator of `caller`.
pub fn call_context(tcx: TyCtxt<'_>, caller: LocalDefId, location: Location) -> Ctx {
    let mut ctx = Ctx::new();
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let Some(block) = body.basic_blocks.get(location.block) else {
        return ctx;
    };
    let TerminatorKind::Call { args, .. } = &block.terminator().kind else {
        return ctx;
    };
    let defs = collect_defs(&body);
    let empty = Ctx::new();
    let eval = EvalCx {
        tcx,
        body: &body,
        defs: &defs,
        ctx: &empty,
        typing_env: ty::TypingEnv::post_analysis(tcx, caller),
    };
    for (i, arg) in args.iter().enumerate() {
        let arg_ty = arg.node.ty(&body.local_decls, tcx);
        if matches!(arg_ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_))
            && let Some(v) = eval.operand(&arg.node, MAX_EVAL_DEPTH)
        {
            ctx.insert(i, v.bits);
        }
    }
    ctx
}

/// A byte range `[start, end)` read through the queried pointer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Interval {
    start: u64,
    end: u64,
}

/// One certified contribution to a function's read footprint: either a
/// constant byte interval, as today, or a claim that the queried pointer's
/// pointee is read `count(v)` times for runtime parameter `v`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Contribution {
    Const(Interval),
    RuntimeParam { param: usize },
}

impl From<Interval> for Contribution {
    fn from(interval: Interval) -> Self {
        Self::Const(interval)
    }
}

/// The bound of a matched indexed loop: either a constant, as today, or a
/// direct stable integer parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IndexedBound {
    Const(u64),
    RuntimeParam { param: usize },
}

/// What one call terminator does with the queried pointer.
struct CallReads {
    reads: Vec<Interval>,
    /// The terminator's mentions of the pointer are all accounted for (read
    /// sources, argument loads, or a derivation), so they pass the
    /// closed-use check.
    mentions_allowed: bool,
    /// The call may diverge or unwind observably, so every certified read
    /// must precede it.
    is_exit: bool,
}

/// Certifies that the collected reads happen on every complete execution.
///
/// A read must dominate every exit — its own block included: statement reads
/// precede their block's terminator, and a forwarding call's reads happen
/// inside the callee before any divergence of the callee's own. Reads that do
/// not are grouped under the deepest unresolved-branch arm dominating them
/// (grouping under a shallower arm would let a nested branch bypass the read
/// unnoticed); when every arm of that branch carries the same read multiset
/// and no exit is reachable from the arm while bypassing the read's block,
/// the reads are re-attributed to the branch block and re-certified.
/// Dominators are computed over the pruned CFG: under pruning, a live arm
/// legitimately dominates the join.
fn certify_contributions(
    body: &Body<'_>,
    successors: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
    exits: &FxHashSet<BasicBlock>,
    idom: &FxHashMap<BasicBlock, BasicBlock>,
    contributions: Vec<(BasicBlock, Contribution)>,
) -> Option<Vec<Contribution>> {
    // Arm blocks of branches the context did not resolve, mapped to their
    // branch block. An arm shared by two branches cannot anchor a grouping,
    // which the `None` sentinel encodes.
    let mut branch_of: FxHashMap<BasicBlock, Option<BasicBlock>> = FxHashMap::default();
    for (&bb, succs) in successors {
        if !matches!(
            body.basic_blocks[bb].terminator().kind,
            TerminatorKind::SwitchInt { .. }
        ) {
            continue;
        }
        let mut arms = succs.clone();
        arms.sort_unstable();
        arms.dedup();
        if arms.len() < 2 {
            continue;
        }
        for arm in arms {
            branch_of
                .entry(arm)
                .and_modify(|e| *e = None)
                .or_insert(Some(bb));
        }
    }
    let branch_arms = |branch: BasicBlock| -> Vec<BasicBlock> {
        let mut arms = successors[&branch].clone();
        arms.sort_unstable();
        arms.dedup();
        arms
    };

    let mut pending = contributions;
    let mut must: Vec<Contribution> = vec![];
    loop {
        let mut regroup = vec![];
        for (bb, iv) in pending {
            if exits.iter().all(|&e| e == bb || dominates(idom, bb, e)) {
                must.push(iv);
            } else {
                regroup.push((bb, iv));
            }
        }
        if regroup.is_empty() {
            return Some(must);
        }

        let mut groups: FxHashMap<BasicBlock, ArmGroups> = FxHashMap::default();
        for (bb, iv) in regroup {
            let mut cursor = bb;
            let arm = loop {
                match branch_of.get(&cursor) {
                    Some(Some(branch)) => break (*branch, cursor),
                    // No dominating arm to promote through, or an ambiguous
                    // one: the read is conditional with no matching
                    // counterpart, so no exact footprint exists.
                    Some(None) => return None,
                    None => {
                        let up = idom[&cursor];
                        if up == cursor {
                            return None;
                        }
                        cursor = up;
                    }
                }
            };
            let (branch, arm) = arm;
            // An execution that leaves through the arm but skips the read's
            // block would read less than the promoted claim.
            if exit_bypasses(successors, exits, arm, bb) {
                return None;
            }
            groups
                .entry(branch)
                .or_default()
                .entry(arm)
                .or_default()
                .push((bb, iv));
        }

        // A branch promotes only when every arm reads the same multiset; a
        // mismatched branch stays pending, since a later promotion out of a
        // nested branch can still fill in the missing arm.
        let mut progressed = false;
        pending = vec![];
        for (branch, by_arm) in groups {
            let multiset = |arm: BasicBlock| -> Vec<Contribution> {
                let mut ivs: Vec<Contribution> = by_arm
                    .get(&arm)
                    .map(|g| g.iter().map(|&(_, iv)| iv).collect())
                    .unwrap_or_default();
                ivs.sort_unstable();
                ivs
            };
            let arms = branch_arms(branch);
            let first = multiset(arms[0]);
            if arms[1..].iter().all(|&arm| multiset(arm) == first) {
                let mut intervals = first;
                intervals.dedup();
                pending.extend(intervals.into_iter().map(|iv| (branch, iv)));
                progressed = true;
            } else {
                pending.extend(by_arm.into_values().flatten());
            }
        }
        if !progressed {
            return None;
        }
    }
}

type ArmGroups = FxHashMap<BasicBlock, Vec<(BasicBlock, Contribution)>>;

/// True when `a` dominates `b` in the pruned CFG (`a == b` included).
fn dominates(idom: &FxHashMap<BasicBlock, BasicBlock>, a: BasicBlock, mut b: BasicBlock) -> bool {
    loop {
        if a == b {
            return true;
        }
        let up = idom[&b];
        if up == b {
            return false;
        }
        b = up;
    }
}

/// True when some exit is reachable from `from` without passing through
/// `through`, i.e. the read at `through` can be skipped by an execution that
/// still completes.
fn exit_bypasses(
    successors: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
    exits: &FxHashSet<BasicBlock>,
    from: BasicBlock,
    through: BasicBlock,
) -> bool {
    if from == through {
        return false;
    }
    let mut seen = FxHashSet::default();
    let mut worklist = vec![from];
    while let Some(bb) = worklist.pop() {
        if bb == through || !seen.insert(bb) {
            continue;
        }
        if exits.contains(&bb) {
            return true;
        }
        if let Some(succs) = successors.get(&bb) {
            worklist.extend(succs.iter().copied());
        }
    }
    false
}

/// Facts from matched read loops. Two shapes are recognized: an indexed
/// read (an induction variable counting 0..B one by one, the loop's only
/// exit at the header's `i < B` test, and a per-iteration load of
/// `*p.offset(i)`) and a walking count-down read (a cursor starting at the
/// pointer and stepping by a constant while a count runs down to zero, with
/// a per-iteration read of one step's worth). Either shape reads exactly
/// `[0, count * step)` bytes through the pointer, certified at the loop
/// header: any execution reaching the header completes every read before
/// leaving through the single counted exit.
#[derive(Default)]
struct LoopReads {
    /// Call blocks a schema accounts for (per-iteration `offset` calls,
    /// cursor steps, per-iteration read calls); excluded from generic call
    /// classification and accepted by the closed-use check.
    consumed_calls: FxHashSet<BasicBlock>,
    /// Statements a schema accounts for: loads through the per-iteration
    /// pointers, cursor initializations, and cursor copies.
    allowed_statements: FxHashSet<(BasicBlock, usize)>,
    /// The per-iteration pointer locals (offset results, cursors, and their
    /// copies); their only accepted uses are the sites above.
    loop_locals: FxHashSet<Local>,
    /// Reassigned context parameters whose sole reassignment is a consumed
    /// count decrement, exempted from the parameter-stability rule.
    exempt_count_params: FxHashSet<Local>,
    /// A reassigned queried pointer whose sole reassignment is a consumed
    /// cursor step, likewise exempted.
    exempt_cursor_params: FxHashSet<Local>,
    contributions: Vec<(BasicBlock, Contribution)>,
}

impl LoopReads {
    fn merge(&mut self, other: LoopReads) {
        self.consumed_calls.extend(other.consumed_calls);
        self.allowed_statements.extend(other.allowed_statements);
        self.loop_locals.extend(other.loop_locals);
        self.exempt_count_params.extend(other.exempt_count_params);
        self.exempt_cursor_params.extend(other.exempt_cursor_params);
        self.contributions.extend(other.contributions);
    }
}

impl<'tcx> ReadExtentAnalysis<'tcx> {
    #[expect(clippy::too_many_arguments)]
    fn match_read_loops(
        &mut self,
        eval: &EvalCx<'_, 'tcx>,
        derived: &Derived,
        param_local: Local,
        queried_pointee: Ty<'tcx>,
        param_reassigned: bool,
        reachable: &FxHashSet<BasicBlock>,
        successors: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
        early_exits: &FxHashSet<BasicBlock>,
        idom: &FxHashMap<BasicBlock, BasicBlock>,
    ) -> LoopReads {
        let mut preds: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        for (&bb, succs) in successors {
            for &s in succs {
                preds.entry(s).or_default().push(bb);
            }
        }
        // Back edges: an edge to a block that dominates its source.
        let mut latches: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        for (&bb, succs) in successors {
            let mut targets = succs.clone();
            targets.sort_unstable();
            targets.dedup();
            for header in targets {
                if dominates(idom, header, bb) {
                    latches.entry(header).or_default().push(bb);
                }
            }
        }

        let mut facts = LoopReads::default();
        for (&header, latch_list) in &latches {
            let &[latch] = &latch_list[..] else {
                continue;
            };
            // Natural loop membership: blocks that reach the latch without
            // passing through the header.
            let mut loop_blocks = FxHashSet::default();
            loop_blocks.insert(header);
            let mut worklist = vec![latch];
            while let Some(bb) = worklist.pop() {
                if !loop_blocks.insert(bb) {
                    continue;
                }
                if let Some(ps) = preds.get(&bb) {
                    worklist.extend(ps.iter().copied());
                }
            }
            let one = match_one_indexed_loop(
                eval,
                derived,
                queried_pointee,
                reachable,
                successors,
                early_exits,
                idom,
                header,
                latch,
                &loop_blocks,
            )
            .or_else(|| {
                self.match_one_walking_loop(
                    eval,
                    derived,
                    param_local,
                    param_reassigned,
                    reachable,
                    successors,
                    early_exits,
                    idom,
                    header,
                    latch,
                    &loop_blocks,
                )
            });
            if let Some(one) = one {
                facts.merge(one);
            }
        }
        facts
    }
}

#[expect(clippy::too_many_arguments)]
fn match_one_indexed_loop<'tcx>(
    eval: &EvalCx<'_, 'tcx>,
    derived: &Derived,
    queried_pointee: Ty<'tcx>,
    reachable: &FxHashSet<BasicBlock>,
    successors: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
    early_exits: &FxHashSet<BasicBlock>,
    idom: &FxHashMap<BasicBlock, BasicBlock>,
    header: BasicBlock,
    latch: BasicBlock,
    loop_blocks: &FxHashSet<BasicBlock>,
) -> Option<LoopReads> {
    let tcx = eval.tcx;
    let body = eval.body;

    // The header tests `i < B` and is the loop's only way out: the
    // false edge leaves the loop, everything else stays inside.
    let TerminatorKind::SwitchInt { discr, targets } = &body.basic_blocks[header].terminator().kind
    else {
        return None;
    };
    let value_targets: Vec<(u128, BasicBlock)> = targets.iter().collect();
    let [(0, exit_target)] = value_targets[..] else {
        return None;
    };
    let body_target = targets.otherwise();
    if loop_blocks.contains(&exit_target) || !loop_blocks.contains(&body_target) {
        return None;
    }
    let (cond_local, _) = resolve_copy_chain(eval, discr, false)?;
    let Some(Some(DefSite::Stmt(cb, ci))) = eval.defs.get(&cond_local) else {
        return None;
    };
    let StatementKind::Assign(box (_, Rvalue::BinaryOp(BinOp::Lt, box (lhs, rhs)))) =
        &body.basic_blocks[*cb].statements[*ci].kind
    else {
        return None;
    };
    let (induction, _) = resolve_copy_chain(eval, lhs, false)?;
    let induction_ty = body.local_decls[induction].ty;
    let size = eval.int_size(induction_ty)?;
    // Const-first: only when the bound does not const-evaluate under the
    // context is a direct runtime parameter bound considered.
    let bound = if let Some(value) = eval.operand(rhs, MAX_EVAL_DEPTH) {
        // The comparison follows the operands' signedness; a negative bound
        // means the loop never runs, which this schema does not claim.
        let value = if induction_ty.is_signed() {
            u64::try_from(size.sign_extend(value.bits)).ok()?
        } else {
            u64::try_from(value.bits).ok()?
        };
        IndexedBound::Const(value)
    } else {
        IndexedBound::RuntimeParam {
            param: resolve_runtime_bound_param(eval, rhs)?,
        }
    };

    // The induction variable has one in-loop increment by one; every other
    // definition sits outside the loop and assigns zero (C2Rust regularly
    // emits two such zeros for a C `for` loop: the declaration's default
    // initializer and the loop's own init statement).
    let sites = def_sites_of(body, induction);
    let (in_loop, outside): (Vec<DefSite>, Vec<DefSite>) = sites
        .into_iter()
        .partition(|s| loop_blocks.contains(&def_site_block(*s)));
    let [incr] = in_loop[..] else {
        return None;
    };
    if outside.is_empty() {
        return None;
    }
    let mut zero_dominates_header = false;
    for init in outside {
        let DefSite::Stmt(ib, ii) = init else {
            return None;
        };
        let StatementKind::Assign(box (_, init_rvalue)) =
            &body.basic_blocks[ib].statements[ii].kind
        else {
            return None;
        };
        if eval.rvalue(init_rvalue, induction_ty, MAX_EVAL_DEPTH)?.bits != 0 {
            return None;
        }
        if dominates(idom, ib, header) {
            zero_dominates_header = true;
        }
    }
    // A zero must be in effect on the first pass through the header — since
    // every outside definition is a zero and one of them dominates, the
    // variable cannot reach the loop with another value. (Re-entering an
    // inner loop with the counter already at its bound is fine — the reads
    // certified here happened on the first pass.)
    if !zero_dominates_header {
        return None;
    }
    if !is_step_by_one(eval, incr, induction, BinOp::Add) {
        return None;
    }

    // Scan the loop body: nothing may leave or abort mid-iteration, and
    // every call is either curated non-diverging or the per-iteration
    // `offset` on the tracked pointer.
    let mut per_iteration: Vec<(BasicBlock, Local, u64)> = vec![];
    for &bb in loop_blocks {
        if bb == header {
            continue;
        }
        if early_exits.contains(&bb) {
            return None;
        }
        if successors[&bb].iter().any(|s| !loop_blocks.contains(s)) {
            return None;
        }
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &body.basic_blocks[bb].terminator().kind
        else {
            continue;
        };
        let func_const = func.constant()?;
        let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
            return None;
        };
        let name = tcx.def_path_str(*callee);
        let is_offset_on_pointer = tcx.item_name(*callee).as_str() == "offset"
            && matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
            && args.len() == 2
            && exact_local_offset(&args[0].node, &derived.offsets).is_some()
            // Constant-index offsets were already recorded as ordinary
            // derivations; the generic classification handles them.
            && !derived.offsets.contains_key(&destination.local);
        if !is_offset_on_pointer {
            if is_curated_nondiverging(tcx, *callee, &name) {
                continue;
            }
            return None;
        }
        // The per-iteration pointer: `p.offset(i)` with no displacement,
        // the index being the induction variable through value-preserving
        // casts.
        if exact_local_offset(&args[0].node, &derived.offsets)? != 0 {
            return None;
        }
        let (index_root, casts) = resolve_copy_chain(eval, &args[1].node, true)?;
        if index_root != induction {
            return None;
        }
        // For a constant bound, every type the index passes through must
        // represent B - 1, as before. For a runtime bound, every cast target
        // must represent the induction type's full nonnegative range: this
        // keeps a widening cast such as `i32/u32 as isize` valid while
        // rejecting a narrowing one, without knowing the runtime value.
        match bound {
            IndexedBound::Const(bound) if bound > 0 => {
                for cast_ty in &casts {
                    if u128::from(bound - 1) > max_nonnegative_int(eval, *cast_ty)? {
                        return None;
                    }
                }
            }
            IndexedBound::RuntimeParam { .. } => {
                let source_max = max_nonnegative_int(eval, induction_ty)?;
                for cast_ty in &casts {
                    if source_max > max_nonnegative_int(eval, *cast_ty)? {
                        return None;
                    }
                }
            }
            IndexedBound::Const(_) => {}
        }
        let q = destination.local;
        if !destination.projection.is_empty()
            || !matches!(eval.defs.get(&q), Some(Some(DefSite::Call(_))))
        {
            return None;
        }
        let recv_ty = args[0].node.ty(&body.local_decls, tcx);
        let ty::TyKind::RawPtr(pointee, _) = recv_ty.kind() else {
            return None;
        };
        let width = tcx
            .layout_of(eval.typing_env.as_query_input(*pointee))
            .ok()?
            .size
            .bytes();
        if width == 0 {
            return None;
        }
        per_iteration.push((bb, q, width));
    }
    if per_iteration.is_empty() {
        return None;
    }

    // Each per-iteration pointer may only be loaded through, and at least
    // one load must run on every iteration (dominate the latch).
    let mut one = LoopReads::default();
    for (call_bb, q, width) in per_iteration {
        let tracked: FxHashMap<Local, u64> = [(q, 0u64)].into_iter().collect();
        let q_derived = Derived {
            offsets: tracked.clone(),
            stmt_sites: FxHashSet::default(),
        };
        let mut collector = MentionCollector {
            derived: &tracked,
            mentions: vec![],
        };
        collector.visit_body(body);
        let mut load_dominates_latch = false;
        for (location, context) in collector.mentions {
            if matches!(context, PlaceContext::NonUse(_)) || !reachable.contains(&location.block) {
                continue;
            }
            let block_data = &body.basic_blocks[location.block];
            if location.statement_index == block_data.statements.len() {
                if location.block != call_bb {
                    return None;
                }
                continue;
            }
            let StatementKind::Assign(box (place, rvalue)) =
                &block_data.statements[location.statement_index].kind
            else {
                return None;
            };
            if place.local == q {
                return None;
            }
            let loads = classify_loads(eval, &q_derived, rvalue)?;
            if loads.is_empty() {
                return None;
            }
            one.allowed_statements
                .insert((location.block, location.statement_index));
            if loop_blocks.contains(&location.block) && dominates(idom, location.block, latch) {
                load_dominates_latch = true;
            }
        }
        if !load_dominates_latch {
            return None;
        }
        one.consumed_calls.insert(call_bb);
        one.loop_locals.insert(q);
        match bound {
            IndexedBound::Const(bound) => {
                if let Some(bytes) = bound.checked_mul(width).filter(|&bytes| bytes > 0) {
                    one.contributions.push((
                        header,
                        Interval {
                            start: 0,
                            end: bytes,
                        }
                        .into(),
                    ));
                } else if bound > 0 {
                    return None;
                }
            }
            IndexedBound::RuntimeParam { param } => {
                let queried_width = tcx
                    .layout_of(eval.typing_env.as_query_input(queried_pointee))
                    .ok()?
                    .size
                    .bytes();
                if queried_width == 0 || width != queried_width {
                    return None;
                }
                one.contributions
                    .push((header, Contribution::RuntimeParam { param }));
            }
        }
    }
    Some(one)
}

/// The largest nonnegative value `ty` (a MIR integer type) can represent:
/// `2^(bits-1) - 1` for a signed type, or the full unsigned max otherwise.
fn max_nonnegative_int<'tcx>(eval: &EvalCx<'_, 'tcx>, ty: Ty<'tcx>) -> Option<u128> {
    let size = eval.int_size(ty)?;
    Some(if ty.is_signed() {
        (1u128 << (size.bits() - 1)) - 1
    } else {
        size.unsigned_int_max()
    })
}

impl<'tcx> ReadExtentAnalysis<'tcx> {
    /// Matches a walking count-down read loop: a cursor starting at the
    /// tracked pointer and advancing by a constant step each iteration, a
    /// count running down by one to a `> 0` test that is the loop's only
    /// exit, and a per-iteration read of exactly one step's worth through
    /// the cursor — a direct load or a call to a local function that reads
    /// that prefix and always returns. Iteration `k` reads
    /// `[k * step, (k + 1) * step)`, so the loop reads `[0, count * step)`.
    #[expect(clippy::too_many_arguments)]
    fn match_one_walking_loop(
        &mut self,
        eval: &EvalCx<'_, 'tcx>,
        derived: &Derived,
        param_local: Local,
        param_reassigned: bool,
        reachable: &FxHashSet<BasicBlock>,
        successors: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
        early_exits: &FxHashSet<BasicBlock>,
        idom: &FxHashMap<BasicBlock, BasicBlock>,
        header: BasicBlock,
        latch: BasicBlock,
        loop_blocks: &FxHashSet<BasicBlock>,
    ) -> Option<LoopReads> {
        let tcx = eval.tcx;
        let body = eval.body;

        // The loop's single way out: one block with an edge leaving the
        // loop, switching on the count test.
        let mut leaving = loop_blocks.iter().filter_map(|&bb| {
            let outside: Vec<BasicBlock> = successors[&bb]
                .iter()
                .copied()
                .filter(|s| !loop_blocks.contains(s))
                .collect();
            (!outside.is_empty()).then_some((bb, outside))
        });
        let (test_block, mut exit_targets) = leaving.next()?;
        if leaving.next().is_some() {
            return None;
        }
        exit_targets.sort_unstable();
        exit_targets.dedup();
        let [exit_target] = exit_targets[..] else {
            return None;
        };
        let TerminatorKind::SwitchInt { discr, targets } =
            &body.basic_blocks[test_block].terminator().kind
        else {
            return None;
        };
        let mut test_succs: Vec<BasicBlock> = successors[&test_block].clone();
        test_succs.sort_unstable();
        test_succs.dedup();
        if test_succs.len() != 2 {
            return None;
        }
        let value_targets: Vec<(u128, BasicBlock)> = targets.iter().collect();
        let [(0, zero_target)] = value_targets[..] else {
            return None;
        };
        let otherwise_target = targets.otherwise();
        if !dominates(idom, test_block, latch) {
            return None;
        }
        let test_position: Position = (test_block, TERMINATOR);

        // Resolve the test to `x > 0`, seen through an optional negation
        // (`if !(x > 0) { break }` leaves the loop on the nonzero arm).
        let (cond_local, _) = resolve_copy_chain(eval, discr, false)?;
        let Some(Some(DefSite::Stmt(cb, ci))) = eval.defs.get(&cond_local) else {
            return None;
        };
        let (compare_rvalue, negated) = match &body.basic_blocks[*cb].statements[*ci].kind {
            StatementKind::Assign(box (_, Rvalue::UnaryOp(UnOp::Not, inner))) => {
                let (inner_local, _) = resolve_copy_chain(eval, inner, false)?;
                let Some(Some(DefSite::Stmt(ib, ii))) = eval.defs.get(&inner_local) else {
                    return None;
                };
                let StatementKind::Assign(box (_, rv)) =
                    &body.basic_blocks[*ib].statements[*ii].kind
                else {
                    return None;
                };
                (rv, true)
            }
            StatementKind::Assign(box (_, rv)) => (rv, false),
            _ => return None,
        };
        let Rvalue::BinaryOp(BinOp::Gt, box (tested, zero)) = compare_rvalue else {
            return None;
        };
        if eval.operand(zero, MAX_EVAL_DEPTH)?.bits != 0 {
            return None;
        }
        let (continue_target, real_exit) = if negated {
            (zero_target, otherwise_target)
        } else {
            (otherwise_target, zero_target)
        };
        if real_exit != exit_target || !loop_blocks.contains(&continue_target) {
            return None;
        }

        // The tested value must be the count as of loop-pass entry: either
        // the count itself, tested before its decrement, or a copy of it
        // taken before the decrement and before the test.
        let chain = copy_chain_sites(eval, tested)?;
        let (count, _) = *chain.last()?;
        let count_ty = body.local_decls[count].ty;
        let count_size = eval.int_size(count_ty)?;
        let count_index = count.as_usize();
        let is_param = count_index >= 1 && count_index <= body.arg_count;
        let sites = def_sites_of(body, count);
        let (initial_bits, decrement) = if is_param {
            let [decrement] = sites[..] else {
                return None;
            };
            (*eval.ctx.get(&(count_index - 1))?, decrement)
        } else {
            let [first, second] = sites[..] else {
                return None;
            };
            let (init, decrement) = if loop_blocks.contains(&def_site_block(second)) {
                (first, second)
            } else {
                (second, first)
            };
            let DefSite::Stmt(ib, ii) = init else {
                return None;
            };
            if loop_blocks.contains(&ib) || !dominates(idom, ib, header) {
                return None;
            }
            let StatementKind::Assign(box (_, init_rvalue)) =
                &body.basic_blocks[ib].statements[ii].kind
            else {
                return None;
            };
            (
                eval.rvalue(init_rvalue, count_ty, MAX_EVAL_DEPTH)?.bits,
                decrement,
            )
        };
        let count0 = if count_ty.is_signed() {
            u64::try_from(count_size.sign_extend(count_size.truncate(initial_bits))).ok()?
        } else {
            u64::try_from(count_size.truncate(initial_bits)).ok()?
        };
        let decrement_block = def_site_block(decrement);
        let decrement_position: Position = match decrement {
            DefSite::Stmt(bb, i) => (bb, i),
            DefSite::Call(bb) => (bb, TERMINATOR),
        };
        if !loop_blocks.contains(&decrement_block)
            || !dominates(idom, decrement_block, latch)
            || !is_step_by_one(eval, decrement, count, BinOp::Sub)
        {
            return None;
        }
        match chain[..] {
            // The count is tested live, so the decrement must come strictly
            // after the test in each pass.
            [(_, None)] => {
                if !executes_before(idom, test_position, decrement_position) {
                    return None;
                }
            }
            // A pre-decrement copy: taken before the decrement, on every
            // pass before the test reads it.
            [.., (_, Some(_)), (_, None)] => {
                let sample = chain[chain.len() - 2].1?;
                if !executes_before(idom, sample, decrement_position)
                    || !executes_before(idom, sample, test_position)
                    || !loop_blocks.contains(&sample.0)
                {
                    return None;
                }
            }
            _ => return None,
        }

        // The cursor: initialized to the tracked pointer at offset zero
        // outside the loop — or the queried parameter itself, stepped in
        // place — advanced by one in-loop `offset` call whose receiver is
        // the cursor itself. The call assigns the cursor directly or
        // through a write-back of a single-use temporary
        // (`t = q.offset(w); q = move t`), which is how surface assignments
        // lower.
        struct CursorStep {
            q: Local,
            call_block: BasicBlock,
            /// Where the cursor actually changes value: the write-back
            /// statement, or the call itself.
            advance: Position,
            step_bytes: u64,
            /// `None` when the cursor is the queried parameter, whose
            /// initial value is implicit.
            init_site: Option<(BasicBlock, usize)>,
            writeback: Option<((BasicBlock, usize), Local)>,
        }
        let mut cursor: Option<CursorStep> = None;
        for &bb in loop_blocks {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &body.basic_blocks[bb].terminator().kind
            else {
                continue;
            };
            let Some(func_const) = func.constant() else {
                continue;
            };
            let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
                continue;
            };
            if tcx.item_name(*callee).as_str() != "offset"
                || !matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
                || args.len() != 2
                || !destination.projection.is_empty()
            {
                continue;
            }
            let Some((q, casts)) = resolve_copy_chain(eval, &args[0].node, false) else {
                continue;
            };
            if !casts.is_empty() {
                continue;
            }
            let q_sites = def_sites_of(body, q);
            // Either a separate cursor local — initialized outside the loop
            // from the tracked pointer at offset zero — or the queried
            // parameter itself, whose entry value is the tracked pointer
            // and whose only explicit definition is the in-loop step.
            let (init_site, step_def) = match q_sites[..] {
                [only] if q == param_local && param_reassigned => (None, only),
                [first, second] => {
                    let (init, step_def) = if loop_blocks.contains(&def_site_block(second)) {
                        (first, second)
                    } else {
                        (second, first)
                    };
                    let DefSite::Stmt(init_bb, init_i) = init else {
                        continue;
                    };
                    if loop_blocks.contains(&init_bb) || !dominates(idom, init_bb, header) {
                        continue;
                    }
                    let StatementKind::Assign(box (_, init_rvalue)) =
                        &body.basic_blocks[init_bb].statements[init_i].kind
                    else {
                        continue;
                    };
                    let init_source = match init_rvalue {
                        Rvalue::Use(op)
                        | Rvalue::Cast(
                            CastKind::PtrToPtr
                            | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _),
                            op,
                            _,
                        ) => op,
                        _ => continue,
                    };
                    if exact_local_offset(init_source, &derived.offsets) != Some(0) {
                        continue;
                    }
                    (Some((init_bb, init_i)), step_def)
                }
                _ => continue,
            };
            // The in-loop definition must be this very call's result.
            let writeback = match step_def {
                DefSite::Call(cbb) if cbb == bb && destination.local == q => None,
                DefSite::Stmt(sbb, si) => {
                    let StatementKind::Assign(box (_, Rvalue::Use(op))) =
                        &body.basic_blocks[sbb].statements[si].kind
                    else {
                        continue;
                    };
                    let temp_matches = match op {
                        Operand::Copy(p) | Operand::Move(p) => {
                            p.projection.is_empty()
                                && p.local == destination.local
                                && matches!(
                                    eval.defs.get(&p.local),
                                    Some(Some(DefSite::Call(cbb))) if *cbb == bb
                                )
                        }
                        _ => false,
                    };
                    if !temp_matches || !loop_blocks.contains(&sbb) {
                        continue;
                    }
                    Some(((sbb, si), destination.local))
                }
                _ => continue,
            };
            // A second tracked cursor in one loop is not recognized.
            if cursor.is_some() {
                return None;
            }
            let amount = eval.operand(&args[1].node, MAX_EVAL_DEPTH)?;
            let amount_size = eval.int_size(amount.ty)?;
            let elems = amount_size.sign_extend(amount.bits);
            let recv_ty = args[0].node.ty(&body.local_decls, tcx);
            let ty::TyKind::RawPtr(pointee, _) = recv_ty.kind() else {
                return None;
            };
            let pointee_size = tcx
                .layout_of(eval.typing_env.as_query_input(*pointee))
                .ok()?
                .size
                .bytes();
            let step_bytes = u64::try_from(elems)
                .ok()
                .and_then(|e| e.checked_mul(pointee_size))
                .filter(|&w| w > 0)?;
            let advance = match writeback {
                Some(((sbb, si), _)) => (sbb, si),
                None => (bb, TERMINATOR),
            };
            if !dominates(idom, advance.0, latch) {
                return None;
            }
            cursor = Some(CursorStep {
                q,
                call_block: bb,
                advance,
                step_bytes,
                init_site,
                writeback,
            });
        }
        let CursorStep {
            q,
            call_block: step_block,
            advance: step_position,
            step_bytes,
            init_site,
            writeback,
        } = cursor?;

        // Cursor copies and pointer casts taken inside the loop stand for
        // the cursor's current value.
        let mut aliases: FxHashMap<Local, u64> = FxHashMap::default();
        aliases.insert(q, 0);
        let mut alias_defs: FxHashSet<(BasicBlock, usize)> = FxHashSet::default();
        loop {
            let mut changed = false;
            for &bb in loop_blocks {
                for (i, stmt) in body.basic_blocks[bb].statements.iter().enumerate() {
                    let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                        continue;
                    };
                    if !place.projection.is_empty() || aliases.contains_key(&place.local) {
                        continue;
                    }
                    let source = match rvalue {
                        Rvalue::Use(op)
                        | Rvalue::Cast(
                            CastKind::PtrToPtr
                            | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _),
                            op,
                            _,
                        ) => op,
                        _ => continue,
                    };
                    if exact_local_offset(source, &aliases) != Some(0) {
                        continue;
                    }
                    let is_single_def_ptr = matches!(eval.defs.get(&place.local), Some(Some(_)))
                        && matches!(
                            body.local_decls[place.local].ty.kind(),
                            ty::TyKind::RawPtr(..)
                        );
                    if is_single_def_ptr {
                        aliases.insert(place.local, 0);
                        alias_defs.insert((bb, i));
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Every mention of the cursor and its aliases must be its
        // initialization, an alias definition, the step, or a per-iteration
        // read of exactly one step's worth, positioned after the test and
        // before the step.
        let mut one = LoopReads::default();
        if let Some(site) = init_site {
            one.allowed_statements.insert(site);
        } else {
            // The queried parameter is the cursor; its step is the sole
            // reassignment the stability rule exempts.
            one.exempt_cursor_params.insert(q);
        }
        one.allowed_statements.extend(alias_defs.iter().copied());
        one.loop_locals.extend(aliases.keys().copied());
        one.consumed_calls.insert(step_block);
        // The write-back temporary holds the advanced pointer; its only
        // accepted uses are the step call and the write-back itself.
        if let Some((site, temp)) = writeback {
            one.allowed_statements.insert(site);
            one.loop_locals.insert(temp);
        }
        let alias_derived = Derived {
            offsets: aliases.clone(),
            stmt_sites: FxHashSet::default(),
        };
        let mut collector = MentionCollector {
            derived: &aliases,
            mentions: vec![],
        };
        collector.visit_body(body);
        let mut read_dominates_latch = false;
        let mut classified_read_calls: FxHashSet<BasicBlock> = FxHashSet::default();
        for (location, context) in collector.mentions {
            if matches!(context, PlaceContext::NonUse(_)) || !reachable.contains(&location.block) {
                continue;
            }
            let block_data = &body.basic_blocks[location.block];
            let read_position: Position = if location.statement_index == block_data.statements.len()
            {
                if location.block == step_block {
                    continue;
                }
                if !classified_read_calls.insert(location.block) {
                    continue;
                }
                self.classify_walking_read_call(
                    eval,
                    derived,
                    &aliases,
                    location.block,
                    step_bytes,
                )?;
                one.consumed_calls.insert(location.block);
                (location.block, TERMINATOR)
            } else {
                let site = (location.block, location.statement_index);
                if Some(site) == init_site
                    || alias_defs.contains(&site)
                    || writeback.is_some_and(|(wb, _)| wb == site)
                {
                    continue;
                }
                let StatementKind::Assign(box (place, rvalue)) =
                    &block_data.statements[location.statement_index].kind
                else {
                    return None;
                };
                if aliases.contains_key(&place.local) {
                    return None;
                }
                let loads = classify_loads(eval, &alias_derived, rvalue)?;
                if loads.is_empty() || loads.iter().any(|iv| iv.end - iv.start != step_bytes) {
                    return None;
                }
                one.allowed_statements.insert(site);
                site
            };
            // Reads run only on continue passes (strictly after the test)
            // and see the pre-step cursor.
            if !loop_blocks.contains(&location.block)
                || !executes_before(idom, test_position, read_position)
                || !executes_before(idom, read_position, step_position)
            {
                return None;
            }
            if dominates(idom, location.block, latch) {
                read_dominates_latch = true;
            }
        }
        if !read_dominates_latch {
            return None;
        }

        // Every other structural requirement on the loop body: no aborting
        // or escaping operations, and only accounted-for calls.
        for &bb in loop_blocks {
            if early_exits.contains(&bb) {
                return None;
            }
            if bb != test_block && successors[&bb].iter().any(|s| !loop_blocks.contains(s)) {
                return None;
            }
            let TerminatorKind::Call {
                func, destination, ..
            } = &body.basic_blocks[bb].terminator().kind
            else {
                continue;
            };
            if one.consumed_calls.contains(&bb) {
                continue;
            }
            let func_const = func.constant()?;
            let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
                return None;
            };
            let name = tcx.def_path_str(*callee);
            // Constant-offset derivations of the tracked pointer are
            // handled by the generic classification.
            if derived.offsets.contains_key(&destination.local)
                || is_curated_nondiverging(tcx, *callee, &name)
            {
                continue;
            }
            return None;
        }

        if is_param {
            one.exempt_count_params.insert(count);
        }
        if let Some(bytes) = count0.checked_mul(step_bytes).filter(|&b| b > 0) {
            one.contributions.push((
                header,
                Interval {
                    start: 0,
                    end: bytes,
                }
                .into(),
            ));
        } else if count0 > 0 {
            return None;
        }
        Some(one)
    }

    /// A per-iteration read call: exactly one cursor alias passed whole at
    /// one argument position to a direct local callee that reads exactly
    /// `step_bytes` through it and always comes back. Nothing else about
    /// the call may involve the cursor or the tracked pointer.
    fn classify_walking_read_call(
        &mut self,
        eval: &EvalCx<'_, 'tcx>,
        derived: &Derived,
        aliases: &FxHashMap<Local, u64>,
        bb: BasicBlock,
        step_bytes: u64,
    ) -> Option<()> {
        let tcx = eval.tcx;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &eval.body.basic_blocks[bb].terminator().kind
        else {
            return None;
        };
        let mut alias_positions = vec![];
        for (i, arg) in args.iter().enumerate() {
            let Some(place) = arg.node.place() else {
                continue;
            };
            if derived.offsets.contains_key(&place.local) {
                return None;
            }
            if aliases.contains_key(&place.local) {
                if !place.projection.is_empty() {
                    return None;
                }
                alias_positions.push(i);
            }
        }
        let [pos] = alias_positions[..] else {
            return None;
        };
        if func.place().is_some_and(|p| {
            aliases.contains_key(&p.local) || derived.offsets.contains_key(&p.local)
        }) || aliases.contains_key(&destination.local)
            || derived.offsets.contains_key(&destination.local)
        {
            return None;
        }
        let func_const = func.constant()?;
        let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
            return None;
        };
        let local_callee = callee.as_local()?;
        if tcx.is_foreign_item(*callee) || tcx.generics_of(local_callee.to_def_id()).count() > 0 {
            return None;
        }
        let mut ctx_g = Ctx::new();
        for (j, arg) in args.iter().enumerate() {
            let arg_ty = arg.node.ty(&eval.body.local_decls, tcx);
            if matches!(arg_ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_))
                && let Some(v) = eval.operand(&arg.node, MAX_EVAL_DEPTH)
            {
                ctx_g.insert(j, v.bits);
            }
        }
        // The callee must always return: a divergence mid-loop would leave
        // later iterations' reads unperformed while the loop's claim covers
        // them.
        match self.query(local_callee, pos, &ctx_g) {
            (Extent::Const(k), true) if k == step_bytes => Some(()),
            _ => None,
        }
    }
}

impl<'tcx> ReadExtentAnalysis<'tcx> {
    /// Memoized entry for the identity check. `forward_depth` is how many
    /// levels of direct local callees a forwarded pointer may still be
    /// followed into.
    fn identity_observed(
        &mut self,
        def_id: LocalDefId,
        param: usize,
        forward_depth: usize,
    ) -> bool {
        let key = (def_id, param, forward_depth);
        if let Some(&cached) = self.identity_memo.get(&key) {
            return cached;
        }
        let observed = self.identity_walk(def_id, param, forward_depth).is_none();
        self.identity_memo.insert(key, observed);
        observed
    }

    /// `Some(())` when every use of the parameter's pointer value is
    /// accounted for without the address becoming observable. This is a
    /// flow-insensitive taint check, deliberately weaker than the extent
    /// walk: non-constant offsets and lengths, walking cursors, and reads
    /// on some paths only are all fine, since none of them expose an
    /// address. Over-tainting is sound for a may-observe question, so
    /// multi-definition locals and reassigned parameters need no special
    /// handling, and no blocks are pruned (cleanup included).
    fn identity_walk(
        &mut self,
        def_id: LocalDefId,
        param: usize,
        forward_depth: usize,
    ) -> Option<()> {
        let tcx = self.tcx;
        if tcx.generics_of(def_id.to_def_id()).count() > 0 {
            return None;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let body = &*body;
        if param >= body.arg_count {
            return None;
        }
        let param_local = Local::from_usize(param + 1);
        if !matches!(
            body.local_decls[param_local].ty.kind(),
            ty::TyKind::RawPtr(..)
        ) {
            return None;
        }

        // Locals that may hold an address derived from the parameter. The
        // map's values are unused (always 0); the map form is what
        // `MentionCollector` and `exact_local_offset` take.
        let mut tainted: FxHashMap<Local, u64> = FxHashMap::default();
        tainted.insert(param_local, 0);
        loop {
            let mut changed = false;
            for data in body.basic_blocks.iter() {
                for stmt in &data.statements {
                    let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                        continue;
                    };
                    if !place.projection.is_empty() || tainted.contains_key(&place.local) {
                        continue;
                    }
                    let carried = match rvalue {
                        Rvalue::Use(op)
                        | Rvalue::Cast(
                            CastKind::PtrToPtr
                            | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _),
                            op,
                            _,
                        ) => exact_local_offset(op, &tainted).is_some(),
                        // A reborrow re-derives the address rather than
                        // loading a value.
                        Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source) => {
                            tainted.contains_key(&source.local)
                                && source.projection.first() == Some(&ProjectionElem::Deref)
                        }
                        Rvalue::BinaryOp(BinOp::Offset, box (a, _)) => {
                            exact_local_offset(a, &tainted).is_some()
                        }
                        _ => false,
                    };
                    if carried {
                        tainted.insert(place.local, 0);
                        changed = true;
                    }
                }
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &data.terminator().kind
                else {
                    continue;
                };
                if !destination.projection.is_empty() || tainted.contains_key(&destination.local) {
                    continue;
                }
                let Some(func_const) = func.constant() else {
                    continue;
                };
                let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
                    continue;
                };
                let name = tcx.def_path_str(*callee);
                // `offset` yields the advanced pointer; the memcpy family
                // returns its destination argument.
                let carried = (is_ptr_offset_call(tcx, *callee, args.len())
                    && exact_local_offset(&args[0].node, &tainted).is_some())
                    || (is_memcpy_family(tcx, *callee, &name, args.len())
                        && args
                            .iter()
                            .any(|a| exact_local_offset(&a.node, &tainted).is_some()));
                if carried {
                    tainted.insert(destination.local, 0);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        if tainted.contains_key(&RETURN_PLACE) {
            return None;
        }
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (i, stmt) in data.statements.iter().enumerate() {
                let location = Location {
                    block: bb,
                    statement_index: i,
                };
                match &stmt.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        if !assign_mentions_ok(&tainted, place, rvalue, location) {
                            return None;
                        }
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => {}
                    _ => {
                        if mentions_tainted(&tainted, |c| c.visit_statement(stmt, location)) {
                            return None;
                        }
                    }
                }
            }
            let terminator = data.terminator();
            let location = Location {
                block: bb,
                statement_index: data.statements.len(),
            };
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    self.identity_call_ok(&tainted, func, args, destination, forward_depth)?;
                }
                // Any other terminator kind has no accepted use of the
                // pointer's value (switch discriminants and assert
                // conditions are integers built in earlier statements).
                _ => {
                    if mentions_tainted(&tainted, |c| c.visit_terminator(terminator, location)) {
                        return None;
                    }
                }
            }
        }
        Some(())
    }

    /// Checks one call's uses of tainted locals. Loads in argument position
    /// happen at operand evaluation and yield pointee data. The pointer
    /// value itself may go to the memcpy family (which only reads or writes
    /// through it), to `offset` (whose result the fixpoint taints), or
    /// whole to a direct local callee that itself never observes the
    /// address; anything else observes it.
    fn identity_call_ok(
        &mut self,
        tainted: &FxHashMap<Local, u64>,
        func: &Operand<'tcx>,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        forward_depth: usize,
    ) -> Option<()> {
        let tcx = self.tcx;
        if func.place().is_some_and(|p| {
            tainted.contains_key(&p.local) && p.projection.first() != Some(&ProjectionElem::Deref)
        }) {
            return None;
        }
        if tainted.contains_key(&destination.local)
            && !destination.projection.is_empty()
            && destination.projection.first() != Some(&ProjectionElem::Deref)
        {
            return None;
        }
        let mut value_positions: Vec<usize> = vec![];
        for (i, arg) in args.iter().enumerate() {
            let Some(place) = arg.node.place() else {
                continue;
            };
            if !tainted.contains_key(&place.local) {
                continue;
            }
            if place.projection.is_empty() {
                value_positions.push(i);
            } else if place.projection.first() != Some(&ProjectionElem::Deref) {
                return None;
            }
        }
        if value_positions.is_empty() {
            return Some(());
        }
        let func_const = func.constant()?;
        let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
            return None;
        };
        let name = tcx.def_path_str(*callee);
        if is_memcpy_family(tcx, *callee, &name, args.len())
            || (is_ptr_offset_call(tcx, *callee, args.len()) && value_positions[..] == [0])
        {
            // The returned pointer must land in a plain local for the
            // fixpoint's taint to cover it.
            return destination.projection.is_empty().then_some(());
        }
        let local_callee = callee.as_local().filter(|l| {
            !tcx.is_foreign_item(*callee) && tcx.generics_of(l.to_def_id()).count() == 0
        })?;
        if forward_depth == 0 {
            return None;
        }
        for pos in value_positions {
            if self.identity_observed(local_callee, pos, forward_depth - 1) {
                return None;
            }
        }
        Some(())
    }
}

/// Whether one assignment's uses of tainted locals are all accounted for.
/// The destination may be a tainted local itself (a definition) or a write
/// through one; source mentions may load through the pointer or carry its
/// value into another plain local, which the taint fixpoint covers.
/// Anything else — storing the value into memory, comparing it, casting it
/// to an integer, packing it into an aggregate — observes the address.
fn assign_mentions_ok<'tcx>(
    tainted: &FxHashMap<Local, u64>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
    location: Location,
) -> bool {
    if tainted.contains_key(&place.local)
        && !place.projection.is_empty()
        && place.projection.first() != Some(&ProjectionElem::Deref)
    {
        return false;
    }
    let carries_to_local = place.projection.is_empty();
    // A reborrow re-derives the address rather than loading a value, so the
    // deref-projection rule below does not apply to it.
    if let Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source) = rvalue {
        return !tainted.contains_key(&source.local)
            || (source.projection.first() == Some(&ProjectionElem::Deref) && carries_to_local);
    }
    // (source place, whether the destination receives the pointer value
    // itself rather than a loaded or derived non-address value)
    let mut sources: Vec<(Place<'tcx>, bool)> = vec![];
    match rvalue {
        Rvalue::Use(op) => sources.extend(op.place().map(|p| (p, true))),
        Rvalue::Cast(kind, op, _) => {
            let carries = matches!(
                kind,
                CastKind::PtrToPtr
                    | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _)
            );
            sources.extend(op.place().map(|p| (p, carries)));
        }
        Rvalue::BinaryOp(op, box (a, b)) => {
            sources.extend(a.place().map(|p| (p, *op == BinOp::Offset)));
            sources.extend(b.place().map(|p| (p, false)));
        }
        Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, _) | Rvalue::ShallowInitBox(op, _) => {
            sources.extend(op.place().map(|p| (p, false)));
        }
        Rvalue::Aggregate(_, ops) => {
            sources.extend(ops.iter().filter_map(|op| op.place()).map(|p| (p, false)));
        }
        Rvalue::Discriminant(p) | Rvalue::CopyForDeref(p) => sources.push((*p, false)),
        Rvalue::NullaryOp(..) | Rvalue::ThreadLocalRef(..) => {}
        // `Ref`/`RawPtr` are handled above; anything else is conservatively
        // rejected as soon as it mentions a tainted local at all.
        _ => return !mentions_tainted(tainted, |c| c.visit_rvalue(rvalue, location)),
    }
    for (source, carries) in sources {
        if !tainted.contains_key(&source.local) {
            continue;
        }
        if source.projection.first() == Some(&ProjectionElem::Deref) {
            continue;
        }
        if source.projection.is_empty() && carries && carries_to_local {
            continue;
        }
        return false;
    }
    true
}

/// True when the visited node uses a tainted local at all; the conservative
/// fallback for statement, terminator, and rvalue kinds the identity check
/// does not recognize.
fn mentions_tainted<'s>(
    tainted: &'s FxHashMap<Local, u64>,
    visit: impl FnOnce(&mut MentionCollector<'s>),
) -> bool {
    let mut collector = MentionCollector {
        derived: tainted,
        mentions: vec![],
    };
    visit(&mut collector);
    collector
        .mentions
        .iter()
        .any(|(_, context)| !matches!(context, PlaceContext::NonUse(_)))
}

/// The memcpy family for identity purposes: these read or write through
/// their pointer arguments and return the destination pointer, but never
/// retain or expose an address. Unlike `memcpy_src_and_len`, no length is
/// needed.
fn is_memcpy_family(tcx: TyCtxt<'_>, callee: DefId, name: &str, arg_count: usize) -> bool {
    if arg_count != 3 {
        return false;
    }
    match name.rsplit("::").next() {
        Some("memcpy" | "memmove" | "memset") => true,
        Some("copy" | "copy_nonoverlapping") => {
            matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
        }
        _ => false,
    }
}

/// A core/std `offset` call: the one pointer-arithmetic call C2Rust emits.
fn is_ptr_offset_call(tcx: TyCtxt<'_>, callee: DefId, arg_count: usize) -> bool {
    arg_count == 2
        && tcx.item_name(callee).as_str() == "offset"
        && matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
}

fn def_site_block(site: DefSite) -> BasicBlock {
    match site {
        DefSite::Stmt(bb, _) => bb,
        DefSite::Call(bb) => bb,
    }
}

/// The projectionless definition sites of one local.
fn def_sites_of(body: &Body<'_>, local: Local) -> Vec<DefSite> {
    let mut sites = vec![];
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (i, stmt) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, _)) = &stmt.kind
                && place.projection.is_empty()
                && place.local == local
            {
                sites.push(DefSite::Stmt(bb, i));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && destination.projection.is_empty()
            && destination.local == local
        {
            sites.push(DefSite::Call(bb));
        }
    }
    sites
}

/// True when the definition assigns `var + 1` or `var - 1` (per `op`): a
/// `wrapping_add`/`wrapping_sub` call (directly or through a copied
/// temporary) or a plain checked-free `Add`/`Sub` by one.
fn is_step_by_one(eval: &EvalCx<'_, '_>, site: DefSite, var: Local, op: BinOp) -> bool {
    let body = eval.body;
    let wrapping_name = if op == BinOp::Add {
        "wrapping_add"
    } else {
        "wrapping_sub"
    };
    let wrapping_call_of = |bb: BasicBlock| -> bool {
        let TerminatorKind::Call { func, args, .. } = &body.basic_blocks[bb].terminator().kind
        else {
            return false;
        };
        let Some(func_const) = func.constant() else {
            return false;
        };
        let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
            return false;
        };
        eval.tcx.item_name(*callee).as_str() == wrapping_name
            && args.len() == 2
            && resolve_copy_chain(eval, &args[0].node, false).is_some_and(|(l, _)| l == var)
            && eval
                .operand(&args[1].node, MAX_EVAL_DEPTH)
                .is_some_and(|v| v.bits == 1)
    };
    match site {
        DefSite::Call(bb) => wrapping_call_of(bb),
        DefSite::Stmt(bb, i) => {
            let StatementKind::Assign(box (_, rvalue)) = &body.basic_blocks[bb].statements[i].kind
            else {
                return false;
            };
            match rvalue {
                Rvalue::BinaryOp(stmt_op, box (a, b)) if *stmt_op == op => {
                    resolve_copy_chain(eval, a, false).is_some_and(|(l, _)| l == var)
                        && eval.operand(b, MAX_EVAL_DEPTH).is_some_and(|v| v.bits == 1)
                }
                Rvalue::Use(inner) => {
                    let Some((root, _)) = resolve_copy_chain(eval, inner, false) else {
                        return false;
                    };
                    matches!(eval.defs.get(&root), Some(Some(DefSite::Call(bb))) if wrapping_call_of(*bb))
                }
                _ => false,
            }
        }
    }
}

/// Follows an operand backward through zero or more single-def, unprojected,
/// same-typed `Rvalue::Use` copies to a stable integer parameter: one never
/// assigned (so its value is the entry value throughout). Any cast, any
/// arithmetic, any local whose type differs from the operand's own, or any
/// local that does not eventually resolve to an unassigned parameter fails
/// the match. Unlike `resolve_copy_chain`, this helper has no cast or
/// arithmetic arm by design: a parameter reached through either would not be
/// the runtime count itself.
fn resolve_runtime_bound_param<'tcx>(
    eval: &EvalCx<'_, 'tcx>,
    operand: &Operand<'tcx>,
) -> Option<usize> {
    let mut operand = operand;
    let expected_ty = operand.ty(&eval.body.local_decls, eval.tcx);
    if !matches!(expected_ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_)) {
        return None;
    }
    for _ in 0..MAX_EVAL_DEPTH {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        if !place.projection.is_empty() || eval.body.local_decls[place.local].ty != expected_ty {
            return None;
        }
        let local = place.local;
        if local_address_taken(eval.body, local) {
            return None;
        }
        let index = local.as_usize();
        if index >= 1 && index <= eval.body.arg_count {
            return (!eval.defs.contains_key(&local)).then_some(index - 1);
        }
        let Some(Some(DefSite::Stmt(bb, statement))) = eval.defs.get(&local) else {
            return None;
        };
        let StatementKind::Assign(box (_, Rvalue::Use(inner))) =
            &eval.body.basic_blocks[*bb].statements[*statement].kind
        else {
            return None;
        };
        if inner.ty(&eval.body.local_decls, eval.tcx) != expected_ty {
            return None;
        }
        operand = inner;
    }
    None
}

/// Whether any statement in `body` takes a reference or raw address of
/// `target` (`&target`, `&mut target`, `&raw const target`, or
/// `&raw mut target`). A runtime bound resolved through such a local would
/// no longer be provably stable: code reached through the taken address
/// could rewrite it before the loop reads it.
fn local_address_taken(body: &Body<'_>, target: Local) -> bool {
    body.basic_blocks.iter().any(|block| {
        block.statements.iter().any(|statement| {
            matches!(
                &statement.kind,
                StatementKind::Assign(box (_, Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)))
                    if place.local == target
            )
        })
    })
}

/// Follows an operand backward through single-def unprojected copies (and,
/// when `through_casts`, integer-to-integer casts, collecting each cast's
/// target type) to the local it names. Parameters are never followed
/// through an explicit definition: their implicit entry value makes such a
/// definition location-dependent.
fn resolve_copy_chain<'tcx>(
    eval: &EvalCx<'_, 'tcx>,
    op: &Operand<'tcx>,
    through_casts: bool,
) -> Option<(Local, Vec<Ty<'tcx>>)> {
    let mut op = op;
    let mut casts = vec![];
    for _ in 0..MAX_EVAL_DEPTH {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let local = place.local;
        if local.as_usize() >= 1 && local.as_usize() <= eval.body.arg_count {
            return Some((local, casts));
        }
        let Some(Some(DefSite::Stmt(bb, i))) = eval.defs.get(&local) else {
            return Some((local, casts));
        };
        let StatementKind::Assign(box (_, rvalue)) =
            &eval.body.basic_blocks[*bb].statements[*i].kind
        else {
            return Some((local, casts));
        };
        match rvalue {
            Rvalue::Use(inner) => op = inner,
            Rvalue::Cast(CastKind::IntToInt, inner, to_ty) if through_casts => {
                casts.push(*to_ty);
                op = inner;
            }
            _ => return Some((local, casts)),
        }
    }
    None
}

/// A local in a copy chain, with the statement site of the copy that
/// defines it (`None` for the chain's final entry, whose definition — if
/// any — is not a plain copy).
type ChainLink = (Local, Option<(BasicBlock, usize)>);

/// The single-def unprojected copy chain from an operand: every local it
/// passes through. Parameters are never followed through, as in
/// `resolve_copy_chain`.
fn copy_chain_sites<'tcx>(eval: &EvalCx<'_, 'tcx>, op: &Operand<'tcx>) -> Option<Vec<ChainLink>> {
    let mut op = op;
    let mut chain = vec![];
    for _ in 0..MAX_EVAL_DEPTH {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let local = place.local;
        let is_param = local.as_usize() >= 1 && local.as_usize() <= eval.body.arg_count;
        let followable = if is_param {
            None
        } else if let Some(Some(DefSite::Stmt(bb, i))) = eval.defs.get(&local)
            && let StatementKind::Assign(box (_, Rvalue::Use(inner))) =
                &eval.body.basic_blocks[*bb].statements[*i].kind
        {
            Some(((*bb, *i), inner))
        } else {
            None
        };
        match followable {
            Some((site, inner)) => {
                chain.push((local, Some(site)));
                op = inner;
            }
            None => {
                chain.push((local, None));
                return Some(chain);
            }
        }
    }
    None
}

/// A position inside a body: a statement index, or the block's terminator
/// (ordered after every statement of the block).
type Position = (BasicBlock, usize);

const TERMINATOR: usize = usize::MAX;

/// True when the operation at `a` executes strictly before the one at `b`
/// on every path: same block with a smaller index, or a strictly
/// dominating block.
fn executes_before(idom: &FxHashMap<BasicBlock, BasicBlock>, a: Position, b: Position) -> bool {
    if a.0 == b.0 {
        a.1 < b.1
    } else {
        dominates(idom, a.0, b.0)
    }
}

/// Immediate dominators of the pruned CFG, computed iteratively over a
/// reverse postorder. The start block maps to itself.
fn pruned_dominators(
    successors: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
    reachable: &FxHashSet<BasicBlock>,
) -> FxHashMap<BasicBlock, BasicBlock> {
    let mut postorder = vec![];
    let mut seen = FxHashSet::default();
    let mut stack = vec![(START_BLOCK, 0usize)];
    seen.insert(START_BLOCK);
    while let Some(&mut (bb, ref mut next)) = stack.last_mut() {
        if let Some(&s) = successors[&bb].get(*next) {
            *next += 1;
            if reachable.contains(&s) && seen.insert(s) {
                stack.push((s, 0));
            }
        } else {
            postorder.push(bb);
            stack.pop();
        }
    }
    let rpo_index: FxHashMap<BasicBlock, usize> = postorder
        .iter()
        .rev()
        .enumerate()
        .map(|(i, &bb)| (bb, i))
        .collect();
    let mut preds: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
    for (&bb, succs) in successors {
        for &s in succs {
            preds.entry(s).or_default().push(bb);
        }
    }

    let mut idom: FxHashMap<BasicBlock, BasicBlock> = FxHashMap::default();
    idom.insert(START_BLOCK, START_BLOCK);
    let intersect =
        |mut a: BasicBlock, mut b: BasicBlock, idom: &FxHashMap<BasicBlock, BasicBlock>| {
            while a != b {
                while rpo_index[&a] > rpo_index[&b] {
                    a = idom[&a];
                }
                while rpo_index[&b] > rpo_index[&a] {
                    b = idom[&b];
                }
            }
            a
        };
    let mut changed = true;
    while changed {
        changed = false;
        for &bb in postorder.iter().rev() {
            if bb == START_BLOCK {
                continue;
            }
            let new_idom = preds[&bb]
                .iter()
                .copied()
                .filter(|p| idom.contains_key(p))
                .reduce(|a, b| intersect(a, b, &idom));
            let Some(new_idom) = new_idom else { continue };
            if idom.get(&bb) != Some(&new_idom) {
                idom.insert(bb, new_idom);
                changed = true;
            }
        }
    }
    idom
}

/// Byte range of a load `(*q)` where `q` holds the pointer at `offset`.
fn load_interval<'tcx>(eval: &EvalCx<'_, 'tcx>, offset: u64, ptr_ty: Ty<'tcx>) -> Option<Interval> {
    let ty::TyKind::RawPtr(pointee, _) = ptr_ty.kind() else {
        return None;
    };
    let size = eval
        .tcx
        .layout_of(eval.typing_env.as_query_input(*pointee))
        .ok()?
        .size
        .bytes();
    let end = offset.checked_add(size)?;
    (size > 0).then_some(Interval { start: offset, end })
}

/// The recognized loads of an rvalue: every mention of the tracked pointer
/// must be a plain `(*q)` in a value-consuming position. Returns the loads'
/// byte ranges, or `None` when the rvalue uses the pointer some other way
/// (by value, behind a reference, or under a deeper projection).
fn classify_loads<'tcx>(
    eval: &EvalCx<'_, 'tcx>,
    derived: &Derived,
    rvalue: &Rvalue<'tcx>,
) -> Option<Vec<Interval>> {
    let operands: Vec<&Operand<'tcx>> = match rvalue {
        Rvalue::Use(op) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) => vec![op],
        Rvalue::BinaryOp(_, box (a, b)) => vec![a, b],
        // Other rvalue kinds (references, aggregates, discriminants) never
        // read through the pointer in a way this analysis accepts; leaving
        // their loads empty defers any pointer mention in them to the
        // closed-use check.
        _ => return Some(vec![]),
    };
    let mut loads = vec![];
    for op in operands {
        let Some(place) = op.place() else { continue };
        let Some(&offset) = derived.offsets.get(&place.local) else {
            continue;
        };
        if place.projection[..] == [ProjectionElem::Deref] {
            let ptr_ty = eval.body.local_decls[place.local].ty;
            loads.push(load_interval(eval, offset, ptr_ty)?);
        } else {
            return None;
        }
    }
    Some(loads)
}

/// The source position, length operand, and per-element byte size of a
/// memcpy-family call, when `callee` is one. The extern "C" functions take a
/// byte count; the core copy intrinsics count elements of their type
/// argument.
fn memcpy_src_and_len<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    name: &str,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    generic_args: ty::GenericArgsRef<'tcx>,
) -> Option<(usize, Operand<'tcx>, u64)> {
    if args.len() != 3 {
        return None;
    }
    match name.rsplit("::").next()? {
        "memcpy" | "memmove" => Some((1, args[2].node.clone(), 1)),
        "copy" | "copy_nonoverlapping"
            if matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std") =>
        {
            let elem = generic_args.type_at(0);
            let size = tcx
                .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(elem))
                .ok()?
                .size
                .bytes();
            Some((0, args[2].node.clone(), size))
        }
        _ => None,
    }
}

/// Calls that either return normally or abort the whole process, so a read
/// placed after them still happens on every observable execution. Abort-only
/// allocation (`from_elem`) is included deliberately: an environment-dependent
/// OOM abort cannot correlate with the size of the pointee object, so eagerly
/// reading the footprint stays valid on every run the original program itself
/// completes. Recognition is by trailing path segment, restricted to the
/// standard crates; the memcpy family is extern "C", declared locally, and
/// recognized by name alone.
fn is_curated_nondiverging(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let Some(last) = name.rsplit("::").next() else {
        return false;
    };
    if matches!(last, "memcpy" | "memmove" | "memset") {
        return true;
    }
    match tcx.crate_name(def_id.krate).as_str() {
        "core" | "std" => matches!(
            last,
            "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "offset"
                | "size_of"
                | "as_ptr"
                | "as_mut_ptr"
                | "from"
                | "into"
                | "copy"
                | "copy_nonoverlapping"
        ),
        "alloc" => {
            (last == "from_elem" && name.contains("::vec::"))
                || matches!(last, "as_ptr" | "as_mut_ptr")
        }
        _ => false,
    }
}

/// The byte offset of an unprojected tracked-local operand.
fn exact_local_offset(op: &Operand<'_>, offsets: &FxHashMap<Local, u64>) -> Option<u64> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            offsets.get(&p.local).copied()
        }
        _ => None,
    }
}

/// Locals holding the queried pointer with their constant byte offset from
/// it: the parameter itself, plus single-def unprojected copies, pointer
/// casts, and `offset`-by-constant call results, to a fixpoint. `stmt_sites`
/// are the copy/cast definitions the mention check accepts; the `offset`-call
/// definitions are accepted through the call classifier.
struct Derived {
    offsets: FxHashMap<Local, u64>,
    stmt_sites: FxHashSet<(BasicBlock, usize)>,
}

fn collect_derived<'tcx>(
    body: &Body<'tcx>,
    defs: &FxHashMap<Local, Option<DefSite>>,
    eval: &EvalCx<'_, 'tcx>,
    param_local: Local,
) -> Derived {
    let tcx = eval.tcx;
    let mut offsets = FxHashMap::default();
    offsets.insert(param_local, 0u64);
    let mut stmt_sites = FxHashSet::default();
    let single_def_ptr = |local: Local| {
        matches!(defs.get(&local), Some(Some(_)))
            && matches!(body.local_decls[local].ty.kind(), ty::TyKind::RawPtr(..))
    };
    loop {
        let mut changed = false;
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (i, stmt) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() || offsets.contains_key(&place.local) {
                    continue;
                }
                let source = match rvalue {
                    Rvalue::Use(op) => op,
                    Rvalue::Cast(
                        CastKind::PtrToPtr
                        | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _),
                        op,
                        _,
                    ) => op,
                    _ => continue,
                };
                let Some(offset) = exact_local_offset(source, &offsets) else {
                    continue;
                };
                if single_def_ptr(place.local) {
                    offsets.insert(place.local, offset);
                    stmt_sites.insert((bb, i));
                    changed = true;
                }
            }

            // `q = p.offset(c)` advances the tracked offset by `c` elements
            // of `p`'s pointee type.
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
            else {
                continue;
            };
            if !destination.projection.is_empty()
                || offsets.contains_key(&destination.local)
                || args.len() != 2
            {
                continue;
            }
            let Some(func_const) = func.constant() else {
                continue;
            };
            let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
                continue;
            };
            if tcx.item_name(*callee).as_str() != "offset"
                || !matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
            {
                continue;
            }
            let Some(receiver_offset) = exact_local_offset(&args[0].node, &offsets) else {
                continue;
            };
            let recv_ty = args[0].node.ty(&body.local_decls, tcx);
            let ty::TyKind::RawPtr(pointee, _) = recv_ty.kind() else {
                continue;
            };
            let Ok(layout) = tcx.layout_of(eval.typing_env.as_query_input(*pointee)) else {
                continue;
            };
            let Some(amount) = eval.operand(&args[1].node, MAX_EVAL_DEPTH) else {
                continue;
            };
            let Some(amount_size) = eval.int_size(amount.ty) else {
                continue;
            };
            let elems = amount_size.sign_extend(amount.bits);
            let new_offset = elems
                .checked_mul(layout.size.bytes() as i128)
                .and_then(|d| (receiver_offset as i128).checked_add(d))
                .and_then(|o| u64::try_from(o).ok());
            let Some(new_offset) = new_offset else {
                continue;
            };
            if single_def_ptr(destination.local) {
                offsets.insert(destination.local, new_offset);
                changed = true;
            }
        }
        if !changed {
            return Derived {
                offsets,
                stmt_sites,
            };
        }
    }
}

/// Collects every use of a tracked local, to be checked against the
/// classified derivations, loads, and calls.
struct MentionCollector<'s> {
    derived: &'s FxHashMap<Local, u64>,
    mentions: Vec<(Location, PlaceContext)>,
}

impl<'tcx> Visitor<'tcx> for MentionCollector<'_> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if self.derived.contains_key(&local) {
            self.mentions.push((location, context));
        }
    }
}
