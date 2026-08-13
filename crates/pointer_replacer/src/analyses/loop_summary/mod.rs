//! Loop-structure recognizer for access-order summaries: pattern-matches
//! counted C2Rust-shaped loops (`while iv < bound`, stepped by exactly `+1`,
//! branch-free body) in MIR and produces a [`LoopSummary`] when every
//! indirect access in the loop is the blessed `param.offset(iv)` pattern —
//! classifying each into `reads`/`writes` and deriving `internal_pairs` from
//! statement order. A loop this recognizer cannot certify (branchy, non-Goto
//! terminators other than `ptr::offset`, non-unit stride, or any indirect
//! access it can't trace to a parameter) is simply omitted from the result,
//! which is always safe since the interpreter falls back to normal
//! interpretation for unsummarized loops.

use outparam_replacer::ai::access_order::LoopSummary;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{self, TyCtxt},
};

pub fn summarize_loops(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Vec<LoopSummary> {
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
    let body = &*body;
    let dominators = body.basic_blocks.dominators();
    let mut summaries = vec![];
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        for header in bbd.terminator().successors() {
            // A back edge bb -> header: header dominates bb.
            if !dominators.dominates(header, bb) {
                continue;
            }
            if let Some(shape) = match_counted_loop(tcx, body, header, bb)
                && let Some(summary) = classify_accesses(body, &shape)
            {
                summaries.push(summary);
            }
        }
    }
    summaries
}

/// If `local` is defined within `data` by a plain `Use` of another local
/// (`local = copy/move other`), returns that other local. Handles the
/// single-block copy C2Rust emits ahead of the header's comparison
/// (`_7 = copy _3; _c = Lt(move _7, ...)`).
fn resolve_local_copy_in_block(
    data: &rustc_middle::mir::BasicBlockData<'_>,
    local: Local,
) -> Option<Local> {
    data.statements.iter().find_map(|stmt| {
        let StatementKind::Assign(box (place, Rvalue::Use(op))) = &stmt.kind else {
            return None;
        };
        if place.as_local() != Some(local) {
            return None;
        }
        match op {
            Operand::Copy(p) | Operand::Move(p) => p.as_local(),
            Operand::Constant(_) => None,
        }
    })
}

/// Structural facts about one recognized loop, before access classification.
struct LoopShape {
    header: BasicBlock,
    /// Body chain from the header's non-exit successor to the latch,
    /// inclusive of the latch, in order.
    chain: Vec<BasicBlock>,
    /// The induction variable, stepped by exactly `+1` somewhere in `chain`.
    iv: Local,
}

/// Matches the counted-loop lowering of `while iv < bound`: header ends in
/// `_c = Lt(iv, bound)` then `SwitchInt` on `_c` with a two-way exit/body
/// split; the body is a single branch-free chain of `Goto`/`ptr::offset`
/// terminators ending in the back edge to `header` at `latch`; and `iv` is
/// stepped by exactly `+1` exactly once, somewhere in the chain.
fn match_counted_loop<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    header: BasicBlock,
    latch: BasicBlock,
) -> Option<LoopShape> {
    // Header: last statement `_c = Lt(iv, bound)`, terminator `SwitchInt`
    // on `_c` with two targets (0 -> exit, otherwise -> body-entry).
    let header_data = &body.basic_blocks[header];
    let TerminatorKind::SwitchInt { discr, targets } = &header_data.terminator().kind else {
        return None;
    };
    let discr_local = discr.place()?.as_local()?;
    let last_stmt = header_data.statements.last()?;
    let StatementKind::Assign(box (place, Rvalue::BinaryOp(BinOp::Lt, box (lhs, _rhs)))) =
        &last_stmt.kind
    else {
        return None;
    };
    if place.as_local() != Some(discr_local) {
        return None;
    }
    // `lhs` is typically a same-block copy of the real induction variable
    // (`_7 = copy _3; _c = Lt(move _7, ...)`); resolve one level of that
    // copy chain within the header's own statements.
    let lhs_local = lhs.place()?.as_local()?;
    let iv = resolve_local_copy_in_block(header_data, lhs_local).unwrap_or(lhs_local);

    let value_targets: Vec<(u128, BasicBlock)> = targets.iter().collect();
    let [(0, exit_target)] = value_targets[..] else {
        return None;
    };
    let body_entry = targets.otherwise();
    if body_entry == exit_target {
        return None;
    }

    // Walk the chain from body-entry to the latch. Each block's terminator
    // must be `Goto` or a call to `ptr::offset`, with a single successor;
    // stop at latch (which must itself goto back to header) or bail on
    // anything else, a revisit, or a side exit.
    let mut chain = vec![];
    let mut seen: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut cur = body_entry;
    let mut step_count = 0usize;
    loop {
        if !seen.insert(cur) {
            return None;
        }
        chain.push(cur);
        let data = &body.basic_blocks[cur];
        step_count += count_steps_by_one(data, iv);
        let next = match &data.terminator().kind {
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::Call {
                func,
                args,
                target: Some(target),
                ..
            } => {
                if !is_ptr_offset_call(tcx, func) || args.len() != 2 {
                    return None;
                }
                *target
            }
            _ => return None,
        };
        if cur == latch {
            if next != header {
                return None;
            }
            break;
        }
        cur = next;
    }
    if step_count != 1 {
        return None;
    }

    Some(LoopShape { header, chain, iv })
}

/// Counts `data`'s statements that are exactly `iv = Add(iv, const 1)`. The
/// caller sums this across the whole chain and requires exactly one such
/// statement total — counting per statement (not per block) is what catches
/// a block with two increments (net stride +2). This only recognizes the
/// plain-`Add` lowering; C2Rust's `i += 1` on a signed/unsigned induction
/// variable bounded by the header's `<` test lowers this way in the shapes
/// this task targets, with no `AddWithOverflow`/`Assert` overflow check
/// observed.
fn count_steps_by_one(data: &rustc_middle::mir::BasicBlockData<'_>, iv: Local) -> usize {
    data.statements
        .iter()
        .filter(|stmt| {
            let StatementKind::Assign(box (place, Rvalue::BinaryOp(BinOp::Add, box (a, b)))) =
                &stmt.kind
            else {
                return false;
            };
            place.as_local() == Some(iv)
                && a.place().and_then(|p| p.as_local()) == Some(iv)
                && is_const_one(b)
        })
        .count()
}

/// True when `op` is an integer constant `1`, checked via its raw bit
/// pattern (the same value for `1` regardless of signedness or width).
fn is_const_one(op: &Operand<'_>) -> bool {
    let Operand::Constant(c) = op else {
        return false;
    };
    c.const_
        .try_to_scalar()
        .and_then(|s| s.try_to_scalar_int().ok())
        .is_some_and(|int| int.to_bits_unchecked() == 1)
}

/// A core/std `ptr::offset` call: the only call this task allows in a loop
/// body chain (Task 3 relies on it being recognized).
fn is_ptr_offset_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some(func_const) = func.constant() else {
        return false;
    };
    let ty::TyKind::FnDef(callee, _) = func_const.ty().kind() else {
        return false;
    };
    tcx.item_name(*callee).as_str() == "offset"
        && matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
}

/// One classified access: which parameter it touches, and its statement
/// order within the loop (for the internal-pair verdict below).
struct Access {
    param: usize,
    order: (usize, usize),
}

/// Classifies every indirect access in the loop as a read or write through a
/// traced parameter (the blessed `param.offset(iv)` pattern), or refuses the
/// whole loop if any indirect access can't be attributed this way. Direct
/// places are ignored. On success, also computes `internal_pairs`: a strict
/// write-before-read on different params, in statement order.
fn classify_accesses(body: &Body<'_>, shape: &LoopShape) -> Option<LoopSummary> {
    let mut blocks = FxHashSet::default();
    blocks.insert(shape.header);
    blocks.extend(shape.chain.iter().copied());

    // Chain order: header first, then the body chain in order, matching the
    // task's `{header} ∪ chain` walk.
    let ordered_blocks: Vec<BasicBlock> = std::iter::once(shape.header)
        .chain(shape.chain.iter().copied())
        .collect();

    let mut reads = vec![];
    let mut writes = vec![];

    for (pos, &bb) in ordered_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in body.basic_blocks[bb].statements.iter().enumerate() {
            let order = (pos, stmt_idx);
            match &stmt.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    if is_indirect(place) {
                        let param = trace_offset_to_param(body, shape, place.local)?;
                        writes.push(Access { param, order });
                    }
                    for op_local in rvalue_indirect_operand_locals(rvalue)? {
                        let param = trace_offset_to_param(body, shape, op_local)?;
                        reads.push(Access { param, order });
                    }
                }
                // These kinds are provably memory-inert: `StorageLive`/
                // `StorageDead` only mark a local's allocation lifetime,
                // `Nop` does nothing, and `ConstEvalCounter`/`Coverage`
                // exist solely for const-eval step counting and coverage
                // instrumentation. Anything else (`Intrinsic` — e.g.
                // `copy_nonoverlapping`, which reads/writes memory without
                // an `Assign` — `SetDiscriminant`, `Deinit`, `Retag`,
                // `FakeRead`, `PlaceMention`, ...) may touch memory in ways
                // this classifier doesn't track, so it refuses the whole
                // loop: refusal is always safe, an unaccounted access is
                // not.
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::ConstEvalCounter
                | StatementKind::Coverage(_) => {}
                _ => return None,
            }
        }
    }

    let mut internal_pairs = FxHashSet::default();
    for w in &writes {
        for r in &reads {
            if w.order < r.order && w.param != r.param {
                internal_pairs.insert((r.param, w.param));
            }
        }
    }

    Some(LoopSummary {
        blocks,
        reads: reads.into_iter().map(|a| a.param).collect(),
        writes: writes.into_iter().map(|a| a.param).collect(),
        internal_pairs,
    })
}

/// Traces a pointer local used in an indirect access back to a 0-based
/// parameter index, requiring exactly the blessed pattern: `local` is the
/// destination of a `ptr::offset` call terminator in the loop's chain, whose
/// arg 0 traces (through simple same-block copies) to a raw-pointer
/// parameter local, and whose arg 1 traces through an `IntToInt` cast
/// (possibly via one intermediate copy) to `copy shape.iv`. Bounded,
/// non-fixpoint tracing: anything beyond a couple of direct hops refuses.
fn trace_offset_to_param(body: &Body<'_>, shape: &LoopShape, local: Local) -> Option<usize> {
    for &bb in &shape.chain {
        let data = &body.basic_blocks[bb];
        let TerminatorKind::Call {
            args, destination, ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if destination.as_local() != Some(local) {
            continue;
        }
        // `match_counted_loop` already verified every `Call` terminator in
        // the chain is a `ptr::offset` call with exactly 2 args.
        let arg0 = args[0].node.place()?;
        let arg1 = args[1].node.place()?;

        let param_local = trace_copies_in_block(data, arg0.as_local()?)?;
        if !(1..=body.arg_count).contains(&param_local.index()) {
            return None;
        }
        if !is_raw_ptr_local(body, param_local) {
            return None;
        }

        if !trace_cast_to_iv(data, arg1.as_local()?, shape.iv) {
            return None;
        }

        return Some(param_local.index() - 1);
    }
    None
}

/// Follows plain same-block `local = copy/move other` assignments starting
/// from `local`, up to a couple of hops, and returns the final local. This
/// only looks at `data`'s own statements, so it can't escape the loop's
/// blocks.
fn trace_copies_in_block(
    data: &rustc_middle::mir::BasicBlockData<'_>,
    local: Local,
) -> Option<Local> {
    let mut cur = local;
    for _ in 0..3 {
        match resolve_local_copy_in_block(data, cur) {
            Some(next) => cur = next,
            None => return Some(cur),
        }
    }
    None
}

/// True when `local` in `data` is defined by `local = move/copy other as isize
/// (IntToInt)` where `other` is (possibly through one intermediate same-block
/// copy) exactly `copy iv`.
fn trace_cast_to_iv(data: &rustc_middle::mir::BasicBlockData<'_>, local: Local, iv: Local) -> bool {
    let Some(cast_src) = data.statements.iter().find_map(|stmt| {
        let StatementKind::Assign(box (place, Rvalue::Cast(CastKind::IntToInt, op, _))) =
            &stmt.kind
        else {
            return None;
        };
        if place.as_local() != Some(local) {
            return None;
        }
        match op {
            Operand::Copy(p) | Operand::Move(p) => p.as_local(),
            Operand::Constant(_) => None,
        }
    }) else {
        return false;
    };
    if cast_src == iv {
        return true;
    }
    // Allow exactly one intermediate same-block copy: `_x = copy iv; _y =
    // move _x as isize`.
    data.statements.iter().any(|stmt| {
        let StatementKind::Assign(box (place, Rvalue::Use(Operand::Copy(p)))) = &stmt.kind else {
            return false;
        };
        place.as_local() == Some(cast_src) && p.as_local() == Some(iv)
    })
}

fn is_raw_ptr_local(body: &Body<'_>, local: Local) -> bool {
    matches!(body.local_decls[local].ty.kind(), ty::TyKind::RawPtr(..))
}

/// Locals of the indirect places read by `rvalue`'s `Copy`/`Move` operands —
/// each one to be traced back to a parameter by the caller. `Ref`, `RawPtr`,
/// `CopyForDeref`, `Len`, and `Discriminant` read a place directly rather
/// than through an operand; this task's traceable pattern is a plain `Use`
/// read (`_x = copy (*_y)`; see the fma/write-before-read tests), so an
/// indirect place in one of those forms is untraceable and refuses the loop,
/// same as any other rvalue kind not listed here.
fn rvalue_indirect_operand_locals(rvalue: &Rvalue<'_>) -> Option<Vec<Local>> {
    fn locals(ops: &[&Operand<'_>]) -> Option<Vec<Local>> {
        ops.iter()
            .filter(|op| operand_is_indirect(op))
            .map(|op| match op {
                Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                Operand::Constant(_) => None,
            })
            .collect()
    }
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::Repeat(op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::Cast(_, op, _) => locals(&[op]),
        Rvalue::BinaryOp(_, box (a, b)) => locals(&[a, b]),
        Rvalue::Aggregate(_, operands) => locals(&operands.iter().collect::<Vec<_>>()),
        Rvalue::ShallowInitBox(op, _) => locals(&[op]),
        _ => {
            if rvalue_has_indirect_operand(rvalue) {
                None
            } else {
                Some(vec![])
            }
        }
    }
}

fn is_indirect(place: &Place<'_>) -> bool {
    place.projection.first() == Some(&ProjectionElem::Deref)
}

fn operand_is_indirect(op: &Operand<'_>) -> bool {
    match op {
        Operand::Copy(p) | Operand::Move(p) => is_indirect(p),
        Operand::Constant(_) => false,
    }
}

fn rvalue_has_indirect_operand(rvalue: &Rvalue<'_>) -> bool {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::Repeat(op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::Cast(_, op, _) => operand_is_indirect(op),
        Rvalue::BinaryOp(_, box (a, b)) => operand_is_indirect(a) || operand_is_indirect(b),
        Rvalue::Aggregate(_, operands) => operands.iter().any(operand_is_indirect),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::CopyForDeref(place) => {
            is_indirect(place)
        }
        Rvalue::Len(place) | Rvalue::Discriminant(place) => is_indirect(place),
        Rvalue::ShallowInitBox(op, _) => operand_is_indirect(op),
        _ => false,
    }
}

#[cfg(test)]
mod tests;
