//! Read-extent analysis: for a raw-pointer parameter of a local function,
//! computes the exact byte prefix `[0, K)` that the function reads through that
//! parameter on every complete execution, specialized to call-site-constant
//! scalar arguments (the "context"). This is the bounds evidence a snapshot
//! rewrite needs to copy `[T; K]` out of an immutable argument: the copy may
//! neither over-read (the pointee is only known to hold what the callee itself
//! reads) nor under-read (the callee would run off the snapshot's end), so the
//! may- and must-read footprints have to coincide.
//!
//! The analysis is a demand-driven walk over drops-elaborated MIR. There is no
//! symbolic summary domain: the rewriter must emit a literal array length
//! anyway, so every useful query bottoms out in constants once the caller's
//! constant scalar arguments are substituted. Branches whose condition
//! const-evaluates under the context are pruned, which is what resolves
//! callees that dispatch on a block-count parameter. Calls that cannot return
//! abnormally-but-observably (core wrapping arithmetic, memcpy-family, and
//! abort-only allocation such as `vec::from_elem`) are exempt from the
//! every-path requirement; any other reachable call counts as a possible exit
//! that all reads must precede.
//!
//! Currently classified reads are memcpy/memmove sources (with the length
//! const-evaluated through the wrapping-arithmetic calls C2Rust emits) and
//! whole-pointer forwarding to another local function, recursively. Direct
//! loads and the two loop shapes (indexed reads with a constant bound and
//! walking-pointer count-down loops) are not classified yet; queries needing
//! them return `None`.
//!
//! Not wired into the rewrite pipeline yet; exercised only by tests.
#![allow(dead_code)]

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Location, Operand, Place, Rvalue, StatementKind,
        TerminatorKind,
        visit::{PlaceContext, Visitor},
    },
    ty::{self, Ty, TyCtxt, adjustment::PointerCoercion},
};

#[cfg(test)]
mod tests;

/// Constant scalar arguments known at the querying call site, keyed by 0-based
/// parameter index. Values are raw bits, truncated to the parameter's width.
pub type ScalarCtx = BTreeMap<usize, u128>;

/// Distinct contexts analyzed per function before further queries give up.
const MAX_CONTEXTS_PER_FN: usize = 16;
/// Depth bound for backward const-evaluation of operand def chains.
const MAX_EVAL_DEPTH: usize = 32;

/// Calls that either return normally or abort the whole process, so a read
/// placed after them still happens on every observable execution. Abort-only
/// allocation (`from_elem`) is included deliberately: an environment-dependent
/// OOM abort cannot correlate with the size of the pointee object, so eagerly
/// reading the footprint stays valid on every run that the original program
/// itself completes.
const NON_DIVERGING_CALLEES: &[&str] = &[
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "size_of",
    "offset",
    "as_ptr",
    "as_mut_ptr",
    "from_elem",
    "memcpy",
    "memmove",
    "memset",
];

/// A query identity: function, parameter index, and sorted context entries.
type QueryKey = (LocalDefId, usize, Vec<(usize, u128)>);

pub struct ReadExtents<'tcx> {
    tcx: TyCtxt<'tcx>,
    memo: FxHashMap<QueryKey, Option<u64>>,
    in_progress: FxHashSet<(LocalDefId, usize)>,
    contexts_seen: FxHashMap<LocalDefId, FxHashSet<Vec<(usize, u128)>>>,
}

impl<'tcx> ReadExtents<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            memo: FxHashMap::default(),
            in_progress: FxHashSet::default(),
            contexts_seen: FxHashMap::default(),
        }
    }

    /// The exact byte prefix read through `param` (0-based) of `def_id` on
    /// every complete execution under `ctx`, or `None` when no exact constant
    /// footprint can be established.
    pub fn extent_bytes(
        &mut self,
        def_id: LocalDefId,
        param: usize,
        ctx: &ScalarCtx,
    ) -> Option<u64> {
        let ctx_key: Vec<(usize, u128)> = ctx.iter().map(|(&k, &v)| (k, v)).collect();
        let key = (def_id, param, ctx_key.clone());
        if let Some(&cached) = self.memo.get(&key) {
            return cached;
        }
        // Cycles get no answer and no memo entry: an answer under a cycle is
        // provisional, and the code this targets has no recursion.
        if !self.in_progress.insert((def_id, param)) {
            return None;
        }
        let over_cap = {
            let seen = self.contexts_seen.entry(def_id).or_default();
            let over = seen.len() >= MAX_CONTEXTS_PER_FN && !seen.contains(&ctx_key);
            if !over {
                seen.insert(ctx_key);
            }
            over
        };
        let result = if over_cap {
            None
        } else {
            self.walk(def_id, param, ctx)
        };
        self.in_progress.remove(&(def_id, param));
        self.memo.insert(key, result);
        result
    }

    fn walk(&mut self, def_id: LocalDefId, param: usize, ctx: &ScalarCtx) -> Option<u64> {
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
        let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
        let defs = collect_defs(body);

        // Context values and the queried pointer stand for the argument at
        // entry, so the parameter locals must never be reassigned.
        if defs.contains_key(&param_local) {
            return None;
        }
        for &i in ctx.keys() {
            if i >= body.arg_count || defs.contains_key(&Local::from_usize(i + 1)) {
                return None;
            }
        }

        let eval = EvalCx {
            tcx,
            body,
            defs: &defs,
            ctx,
            typing_env,
        };
        let (derived, derivation_sites) = collect_derived(body, &defs, param_local);

        // Traverse the context-pruned CFG, classifying every reachable
        // terminator. Unknown terminator kinds fail the walk rather than being
        // skipped: not following their successors would silently drop reads.
        let mut contributions: FxHashMap<BasicBlock, u64> = FxHashMap::default();
        let mut exits: Vec<(BasicBlock, ExitKind)> = vec![];
        let mut allowed_call_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
        let mut successors: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        let mut reachable: FxHashSet<BasicBlock> = FxHashSet::default();
        let mut worklist = vec![rustc_middle::mir::START_BLOCK];
        while let Some(bb) = worklist.pop() {
            if body.basic_blocks[bb].is_cleanup || !reachable.insert(bb) {
                continue;
            }
            let mut succs = vec![];
            match &body.basic_blocks[bb].terminator().kind {
                TerminatorKind::Goto { target } => succs.push(*target),
                TerminatorKind::Drop { target, .. } => succs.push(*target),
                TerminatorKind::Assert { target, .. } => {
                    // The check may panic, so reads must already have happened.
                    exits.push((bb, ExitKind::Plain));
                    succs.push(*target);
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    match eval.operand(discr, MAX_EVAL_DEPTH) {
                        Some(v) => succs.push(targets.target_for_value(v.bits)),
                        None => succs.extend(targets.all_targets().iter().copied()),
                    }
                }
                TerminatorKind::Return | TerminatorKind::Unreachable => {}
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    succs.extend(*target);
                    match self.classify_call(&eval, &derived, func, args, destination)? {
                        CallKind::MemcpySrc(len) => {
                            contributions.insert(bb, len);
                            allowed_call_blocks.insert(bb);
                        }
                        CallKind::Forward(callee, arg_index, ctx_g) => {
                            let len = self.extent_bytes(callee, arg_index, &ctx_g)?;
                            contributions.insert(bb, len);
                            allowed_call_blocks.insert(bb);
                            exits.push((bb, ExitKind::Forward(len)));
                        }
                        CallKind::NonDiverging => {}
                        CallKind::Opaque => exits.push((bb, ExitKind::Plain)),
                    }
                }
                _ => return None,
            }
            successors.insert(bb, succs.clone());
            worklist.extend(succs);
        }

        // Every mention of the pointer must be a recognized derivation or sit
        // in a classified call; anything else (loads, stores, comparisons,
        // escapes) defeats the exact-footprint claim.
        let mut mentions = MentionCollector {
            derived: &derived,
            mentions: vec![],
        };
        mentions.visit_body(body);
        for (location, context) in mentions.mentions {
            if matches!(context, PlaceContext::NonUse(_)) {
                continue;
            }
            let is_terminator =
                location.statement_index == body.basic_blocks[location.block].statements.len();
            let allowed = if is_terminator {
                allowed_call_blocks.contains(&location.block)
            } else {
                derivation_sites.contains(&(location.block, location.statement_index))
            };
            // Mentions in pruned-away blocks are dead under this context.
            if !allowed && reachable.contains(&location.block) {
                return None;
            }
        }

        let may_k = contributions.values().copied().max().filter(|&k| k > 0)?;

        // Must-availability dataflow over the pruned CFG: `avail_in[bb]` is
        // the byte prefix guaranteed to have been read on every path reaching
        // `bb`. Contributions take effect at their block's terminator.
        let mut preds: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        for (&bb, succs) in &successors {
            for &s in succs {
                preds.entry(s).or_default().push(bb);
            }
        }
        let start = rustc_middle::mir::START_BLOCK;
        let mut avail_in: FxHashMap<BasicBlock, u64> =
            reachable.iter().map(|&bb| (bb, u64::MAX)).collect();
        avail_in.insert(start, 0);
        let out = |b: BasicBlock, avail_in: &FxHashMap<BasicBlock, u64>| {
            let base = avail_in[&b];
            contributions.get(&b).map_or(base, |&len| base.max(len))
        };
        let mut worklist: Vec<BasicBlock> = reachable.iter().copied().collect();
        while let Some(bb) = worklist.pop() {
            if bb == start || !avail_in.contains_key(&bb) {
                continue;
            }
            let Some(ps) = preds.get(&bb) else { continue };
            let new_in = ps
                .iter()
                .filter(|p| avail_in.contains_key(p))
                .map(|&p| out(p, &avail_in))
                .min()
                .unwrap_or(u64::MAX);
            if new_in < avail_in[&bb] {
                avail_in.insert(bb, new_in);
                if let Some(succs) = successors.get(&bb) {
                    worklist.extend(succs.iter().copied());
                }
            }
        }

        // Exactness: every way out of the function must have seen the whole
        // prefix. Forwarding callees perform their own reads before any
        // divergence of theirs (their walk enforces it), so as exits they are
        // exempt from covering their own contribution.
        for &bb in &reachable {
            if matches!(
                body.basic_blocks[bb].terminator().kind,
                TerminatorKind::Return
            ) && avail_in[&bb] < may_k
            {
                return None;
            }
        }
        for (bb, kind) in exits {
            let covered = match kind {
                ExitKind::Plain => avail_in[&bb] >= may_k,
                ExitKind::Forward(own) => own >= may_k || avail_in[&bb] >= may_k,
            };
            if !covered {
                return None;
            }
        }

        Some(may_k)
    }

    /// Classifies one reachable call terminator. Returns `None` (failing the
    /// whole walk) when the queried pointer is used in a way the analysis
    /// cannot account for.
    fn classify_call(
        &self,
        eval: &EvalCx<'_, 'tcx>,
        derived: &FxHashSet<Local>,
        func: &Operand<'tcx>,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) -> Option<CallKind> {
        let tcx = self.tcx;
        let derived_mentions = args
            .iter()
            .map(|a| operand_mentions(&a.node, derived))
            .sum::<usize>()
            + place_mentions(destination, derived)
            + func.place().map_or(0, |p| place_mentions(&p, derived));

        let callee = func.constant().and_then(|c| match c.ty().kind() {
            ty::TyKind::FnDef(def_id, _) => Some(*def_id),
            _ => None,
        });
        let Some(callee) = callee else {
            // Indirect call: fine as long as the pointer is not involved.
            return (derived_mentions == 0).then_some(CallKind::Opaque);
        };
        let name = tcx.item_name(callee);
        let name = name.as_str();

        if matches!(name, "memcpy" | "memmove") {
            if derived_mentions == 0 {
                return Some(CallKind::NonDiverging);
            }
            // The pointer may appear only as the source, unprojected.
            if derived_mentions == 1
                && args.len() == 3
                && operand_is_exact_local(&args[1].node, derived)
            {
                let len = eval.operand(&args[2].node, MAX_EVAL_DEPTH)?;
                return Some(CallKind::MemcpySrc(u64::try_from(len.bits).ok()?));
            }
            return None;
        }
        if NON_DIVERGING_CALLEES.contains(&name) {
            return (derived_mentions == 0).then_some(CallKind::NonDiverging);
        }

        let forwardable = callee.as_local().filter(|&local| {
            !tcx.is_foreign_item(callee) && tcx.generics_of(local.to_def_id()).count() == 0
        });
        if let Some(local_callee) = forwardable {
            let exact_positions: Vec<usize> = args
                .iter()
                .enumerate()
                .filter(|(_, a)| operand_is_exact_local(&a.node, derived))
                .map(|(i, _)| i)
                .collect();
            if let [arg_index] = exact_positions[..]
                && derived_mentions == 1
            {
                let mut ctx_g = ScalarCtx::new();
                for (j, arg) in args.iter().enumerate() {
                    let arg_ty = arg.node.ty(&eval.body.local_decls, tcx);
                    if matches!(arg_ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_))
                        && let Some(v) = eval.operand(&arg.node, MAX_EVAL_DEPTH)
                    {
                        ctx_g.insert(j, v.bits);
                    }
                }
                return Some(CallKind::Forward(local_callee, arg_index, ctx_g));
            }
            if derived_mentions == 0 {
                return Some(CallKind::Opaque);
            }
            return None;
        }

        (derived_mentions == 0).then_some(CallKind::Opaque)
    }
}

enum ExitKind {
    /// Reads must be complete when this terminator runs.
    Plain,
    /// A forwarding call: exempt from covering its own contribution.
    Forward(u64),
}

enum CallKind {
    /// memcpy/memmove reading `len` bytes from the queried pointer.
    MemcpySrc(u64),
    /// The pointer is forwarded whole to a local callee's parameter.
    Forward(LocalDefId, usize, ScalarCtx),
    /// Curated total call; not an exit.
    NonDiverging,
    /// Unrelated call that may diverge; an exit.
    Opaque,
}

#[derive(Clone, Copy)]
enum DefSite {
    Stmt(BasicBlock, usize),
    Call(BasicBlock),
}

/// Single direct definitions per local; multiply-defined locals map to `None`.
fn collect_defs(body: &Body<'_>) -> FxHashMap<Local, Option<DefSite>> {
    let mut defs: FxHashMap<Local, Option<DefSite>> = FxHashMap::default();
    let record = |local: Local, site: DefSite, defs: &mut FxHashMap<Local, Option<DefSite>>| {
        defs.entry(local)
            .and_modify(|e| *e = None)
            .or_insert(Some(site));
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (i, stmt) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, _)) = &stmt.kind
                && place.projection.is_empty()
            {
                record(place.local, DefSite::Stmt(bb, i), &mut defs);
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && destination.projection.is_empty()
        {
            record(destination.local, DefSite::Call(bb), &mut defs);
        }
    }
    defs
}

/// Locals holding the queried pointer: the parameter plus single-def,
/// unprojected copies and pointer-to-pointer casts, to a fixpoint.
fn collect_derived(
    body: &Body<'_>,
    defs: &FxHashMap<Local, Option<DefSite>>,
    param_local: Local,
) -> (FxHashSet<Local>, FxHashSet<(BasicBlock, usize)>) {
    let mut derived = FxHashSet::default();
    derived.insert(param_local);
    let mut sites = FxHashSet::default();
    loop {
        let mut changed = false;
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (i, stmt) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() || derived.contains(&place.local) {
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
                if operand_is_exact_local(source, &derived)
                    && matches!(defs.get(&place.local), Some(Some(_)))
                    && matches!(
                        body.local_decls[place.local].ty.kind(),
                        ty::TyKind::RawPtr(..)
                    )
                {
                    derived.insert(place.local);
                    sites.insert((bb, i));
                    changed = true;
                }
            }
        }
        if !changed {
            return (derived, sites);
        }
    }
}

fn operand_is_exact_local(op: &Operand<'_>, derived: &FxHashSet<Local>) -> bool {
    matches!(
        op,
        Operand::Copy(p) | Operand::Move(p)
            if p.projection.is_empty() && derived.contains(&p.local)
    )
}

fn operand_mentions(op: &Operand<'_>, derived: &FxHashSet<Local>) -> usize {
    match op {
        Operand::Copy(p) | Operand::Move(p) => place_mentions(p, derived),
        Operand::Constant(_) => 0,
    }
}

fn place_mentions(place: &Place<'_>, derived: &FxHashSet<Local>) -> usize {
    let base = usize::from(derived.contains(&place.local));
    let idx = place
        .projection
        .iter()
        .filter(|elem| match elem {
            rustc_middle::mir::ProjectionElem::Index(l) => derived.contains(l),
            _ => false,
        })
        .count();
    base + idx
}

/// Collects every use of a derived local, to be checked against the
/// classified derivations and calls.
struct MentionCollector<'s> {
    derived: &'s FxHashSet<Local>,
    mentions: Vec<(Location, PlaceContext)>,
}

impl<'tcx> Visitor<'tcx> for MentionCollector<'_> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if self.derived.contains(&local) {
            self.mentions.push((location, context));
        }
    }
}

/// A constant scalar with its MIR type; `bits` are truncated to the type's
/// width.
#[derive(Clone, Copy)]
struct ScalarVal<'tcx> {
    bits: u128,
    ty: Ty<'tcx>,
}

struct EvalCx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    defs: &'a FxHashMap<Local, Option<DefSite>>,
    ctx: &'a ScalarCtx,
    typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> EvalCx<'_, 'tcx> {
    fn int_size(&self, ty: Ty<'tcx>) -> Option<rustc_abi::Size> {
        if !matches!(
            ty.kind(),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Bool | ty::TyKind::Char
        ) {
            return None;
        }
        Some(
            self.tcx
                .layout_of(self.typing_env.as_query_input(ty))
                .ok()?
                .size,
        )
    }

    fn operand(&self, op: &Operand<'tcx>, depth: usize) -> Option<ScalarVal<'tcx>> {
        if depth == 0 {
            return None;
        }
        match op {
            Operand::Constant(c) => {
                let (int, ty) = if let Some(scalar) = c.const_.try_to_scalar()
                    && let Ok(int) = scalar.try_to_scalar_int()
                {
                    (int, c.const_.ty())
                } else if let rustc_middle::mir::Const::Unevaluated(uv, ty) = c.const_
                    && uv.promoted.is_none()
                    && let Ok(v) = self.tcx.const_eval_poly(uv.def)
                    && let rustc_middle::mir::ConstValue::Scalar(scalar) = v
                    && let Ok(int) = scalar.try_to_scalar_int()
                {
                    (int, ty)
                } else {
                    return None;
                };
                Some(ScalarVal {
                    bits: int.to_bits(int.size()),
                    ty,
                })
            }
            Operand::Copy(place) | Operand::Move(place) => {
                if !place.projection.is_empty() {
                    return None;
                }
                self.local(place.local, depth - 1)
            }
        }
    }

    fn local(&self, local: Local, depth: usize) -> Option<ScalarVal<'tcx>> {
        let index = local.as_usize();
        let ty = self.body.local_decls[local].ty;
        if index >= 1 && index <= self.body.arg_count && !self.defs.contains_key(&local) {
            let bits = *self.ctx.get(&(index - 1))?;
            let size = self.int_size(ty)?;
            return Some(ScalarVal {
                bits: size.truncate(bits),
                ty,
            });
        }
        match self.defs.get(&local).copied()?? {
            DefSite::Stmt(bb, i) => {
                let StatementKind::Assign(box (place, rvalue)) =
                    &self.body.basic_blocks[bb].statements[i].kind
                else {
                    return None;
                };
                if place.local != local {
                    return None;
                }
                self.rvalue(rvalue, ty, depth)
            }
            DefSite::Call(bb) => self.call_result(bb, ty, depth),
        }
    }

    fn rvalue(&self, rvalue: &Rvalue<'tcx>, ty: Ty<'tcx>, depth: usize) -> Option<ScalarVal<'tcx>> {
        match rvalue {
            Rvalue::Use(op) => self.operand(op, depth),
            Rvalue::Cast(CastKind::IntToInt, op, to_ty) => {
                let v = self.operand(op, depth)?;
                let from_size = self.int_size(v.ty)?;
                let to_size = self.int_size(*to_ty)?;
                let extended = if v.ty.is_signed() {
                    from_size.sign_extend(v.bits) as u128
                } else {
                    v.bits
                };
                Some(ScalarVal {
                    bits: to_size.truncate(extended),
                    ty: *to_ty,
                })
            }
            Rvalue::BinaryOp(op, box (a, b)) => {
                let l = self.operand(a, depth)?;
                let r = self.operand(b, depth)?;
                self.binary(*op, l, r, ty)
            }
            _ => None,
        }
    }

    fn binary(
        &self,
        op: BinOp,
        l: ScalarVal<'tcx>,
        r: ScalarVal<'tcx>,
        result_ty: Ty<'tcx>,
    ) -> Option<ScalarVal<'tcx>> {
        let size = self.int_size(l.ty)?;
        let signed = l.ty.is_signed();
        let (ls, rs) = (size.sign_extend(l.bits), size.sign_extend(r.bits));
        let arith = |v: u128| ScalarVal {
            bits: size.truncate(v),
            ty: result_ty,
        };
        let cmp = |c: bool| ScalarVal {
            bits: c as u128,
            ty: self.tcx.types.bool,
        };
        Some(match op {
            BinOp::Add => arith(l.bits.wrapping_add(r.bits)),
            BinOp::Sub => arith(l.bits.wrapping_sub(r.bits)),
            BinOp::Mul => arith(l.bits.wrapping_mul(r.bits)),
            BinOp::BitAnd => arith(l.bits & r.bits),
            BinOp::BitOr => arith(l.bits | r.bits),
            BinOp::BitXor => arith(l.bits ^ r.bits),
            BinOp::Eq => cmp(l.bits == r.bits),
            BinOp::Ne => cmp(l.bits != r.bits),
            BinOp::Lt if signed => cmp(ls < rs),
            BinOp::Le if signed => cmp(ls <= rs),
            BinOp::Gt if signed => cmp(ls > rs),
            BinOp::Ge if signed => cmp(ls >= rs),
            BinOp::Lt => cmp(l.bits < r.bits),
            BinOp::Le => cmp(l.bits <= r.bits),
            BinOp::Gt => cmp(l.bits > r.bits),
            BinOp::Ge => cmp(l.bits >= r.bits),
            _ => return None,
        })
    }

    /// Results of the curated pure calls: wrapping arithmetic and `size_of`.
    fn call_result(&self, bb: BasicBlock, ty: Ty<'tcx>, depth: usize) -> Option<ScalarVal<'tcx>> {
        let TerminatorKind::Call { func, args, .. } = &self.body.basic_blocks[bb].terminator().kind
        else {
            return None;
        };
        let ty::TyKind::FnDef(callee, generic_args) = func.constant()?.ty().kind() else {
            return None;
        };
        let name = self.tcx.item_name(*callee);
        match name.as_str() {
            "wrapping_add" | "wrapping_sub" | "wrapping_mul" if args.len() == 2 => {
                let l = self.operand(&args[0].node, depth)?;
                let r = self.operand(&args[1].node, depth)?;
                let op = match name.as_str() {
                    "wrapping_add" => BinOp::Add,
                    "wrapping_sub" => BinOp::Sub,
                    _ => BinOp::Mul,
                };
                self.binary(op, l, r, ty)
            }
            "size_of" if args.is_empty() => {
                let size = self
                    .tcx
                    .layout_of(self.typing_env.as_query_input(generic_args.type_at(0)))
                    .ok()?
                    .size;
                Some(ScalarVal {
                    bits: size.bytes() as u128,
                    ty,
                })
            }
            _ => None,
        }
    }
}
