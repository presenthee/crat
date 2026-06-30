//! Detects call sites where a mutable raw-pointer argument and one or more
//! immutable raw-pointer arguments to the same local callee are derived from the
//! same directly-rewriteable base.
//!
//! This is detection only. A detected candidate still requires a read-before-write
//! proof and bounds evidence before its read-only arguments can be safely isolated
//! into an immutable snapshot.

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Location, TerminatorKind},
    ty::{self, Ty},
};

use crate::{
    analyses::array_local_provenance::{ArrayLocalProvenance, BaseAdmissibility, BaseId},
    utils::rustc::RustProgram,
};

#[cfg(test)]
mod tests;

/// A call site where a mutable and one or more immutable raw-pointer arguments
/// share the same directly-rewriteable base. Arguments are identified by their
/// 0-based position in the call's argument list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern2Candidate {
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub location: Location,
    pub base: BaseId,
    pub mut_params: Vec<usize>,
    pub imm_params: Vec<usize>,
}

struct ArgInfo<'tcx> {
    index: usize,
    is_mut: bool,
    pointee: Ty<'tcx>,
    admissibility: BaseAdmissibility,
}

pub fn detect_pattern2_candidates<'tcx>(
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
) -> Vec<Pattern2Candidate> {
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
                // Every argument on this base must be directly rewriteable; a base
                // that will not be promoted has no aliasing hazard to isolate.
                if group
                    .iter()
                    .any(|a| a.admissibility != BaseAdmissibility::DirectlyRewriteable)
                {
                    continue;
                }

                // Need at least one mutable and one immutable raw-pointer argument.
                let mut_params: Vec<usize> =
                    group.iter().filter(|a| a.is_mut).map(|a| a.index).collect();
                let imm_params: Vec<usize> =
                    group.iter().filter(|a| !a.is_mut).map(|a| a.index).collect();
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

                candidates.push(Pattern2Candidate {
                    caller,
                    callee,
                    location,
                    base,
                    mut_params,
                    imm_params,
                });
            }
        }
    }

    candidates
}
