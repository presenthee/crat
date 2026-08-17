use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        BinOp, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};

use super::{
    ACCESS_SUMMARY_BUDGET, AccessEffect, AccessFootprint, AccessKind, CallFrame,
    FunctionAccessSummary, HazardOrder, OffsetExpr, PotentialHazard, SymbolicAddress, WidthExpr,
    extractor::{
        ResolvedPointerOrigins, constant_usize, raw_pointer_pointee, resolve_pointer_operand,
    },
    summary::complete_builtin_accesses,
};
use crate::analyses::{
    loop_recognizer::{RecognizedLoop, recognize_loops},
    pointer_flow::{PointerFlowResult, builtin::is_pointer_arithmetic},
};

#[derive(Clone, Debug)]
pub(crate) struct AtomicLoopEffect {
    pub recognized: RecognizedLoop,
    pub effect: AccessEffect,
}

pub(crate) fn build_loop_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    recognized: &RecognizedLoop,
    flow: &PointerFlowResult,
    callee_summaries: &FxHashMap<LocalDefId, FunctionAccessSummary>,
    recursive_callees: &FxHashSet<LocalDefId>,
) -> Option<AtomicLoopEffect> {
    if recognized.region.blocks.iter().any(|&block| {
        body.basic_blocks[block]
            .terminator()
            .successors()
            .any(|successor| body.basic_blocks[successor].is_cleanup)
    }) {
        return None;
    }
    let induction_constant = induction_initial_constant(tcx, def_id, body, recognized)?;
    let tracer = LoopTracer {
        tcx,
        def_id,
        body,
        recognized,
        flow,
        induction_constant,
    };
    let mut accesses = vec![];
    let mut same_iteration_hazards = vec![];
    let mut phase = 0_u64;

    for &block in &recognized.ordered_blocks {
        let block_data = &body.basic_blocks[block];
        for (statement_index, statement) in block_data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if let StatementKind::Intrinsic(
                box rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy),
            ) = &statement.kind
            {
                let count = constant_usize(&copy.count, tcx)?;
                let element_ty = raw_pointer_pointee(copy.src.ty(body, tcx))?;
                let width = tracer.layout(element_ty)?.size.bytes().checked_mul(count)?;
                let mut intrinsic_phase_accesses = tracer.resolve_operand_access(
                    &copy.src,
                    width,
                    AccessKind::Read,
                    location,
                    phase,
                )?;
                intrinsic_phase_accesses.extend(tracer.resolve_operand_access(
                    &copy.dst,
                    width,
                    AccessKind::Write,
                    location,
                    phase,
                )?);
                accesses.extend(intrinsic_phase_accesses);
                phase = phase.checked_add(1)?;
                continue;
            }
            let raw_accesses = tracer.statement_accesses(&statement.kind)?;
            for raw in raw_accesses {
                let footprints = tracer.resolve_access(raw, location)?;
                accesses.extend(footprints.into_iter().map(|(kind, footprint)| LoopAccess {
                    kind,
                    footprint,
                    phase,
                }));
                phase = phase.checked_add(1)?;
            }
        }

        let location = Location {
            block,
            statement_index: block_data.statements.len(),
        };
        match &block_data.terminator().kind {
            TerminatorKind::Call { func, args, .. } => {
                let callee = direct_callee(func)?;
                let path = tcx.def_path_str(callee);
                if is_pointer_arithmetic(tcx, callee, &path) {
                    continue;
                }
                if let Some(builtin_accesses) =
                    complete_builtin_accesses(tcx, def_id, body, callee, &path, args)
                {
                    let mut builtin_phase_accesses = vec![];
                    for access in builtin_accesses {
                        let operand = &args.get(access.arg_index)?.node;
                        builtin_phase_accesses.extend(tracer.resolve_operand_access(
                            operand,
                            access.width,
                            access.kind,
                            location,
                            phase,
                        )?);
                    }
                    for (index, write) in builtin_phase_accesses.iter().enumerate() {
                        if write.kind != AccessKind::Write {
                            continue;
                        }
                        for read in &builtin_phase_accesses[index + 1..] {
                            if read.kind == AccessKind::Read {
                                same_iteration_hazards.push(PotentialHazard {
                                    write: write.footprint.clone(),
                                    read: read.footprint.clone(),
                                    order: HazardOrder::SameIteration(recognized.id),
                                });
                            }
                        }
                    }
                    accesses.extend(builtin_phase_accesses);
                    phase = phase.checked_add(1)?;
                    continue;
                }
                let local_callee = callee.as_local()?;
                if recursive_callees.contains(&local_callee) {
                    return None;
                }
                let summary = callee_summaries.get(&local_callee)?;
                if summary.effect.contains_repetition || !summary.effect.invalidations.is_empty() {
                    return None;
                }
                let frame = CallFrame {
                    caller: def_id,
                    callee: local_callee,
                    location,
                };
                for read in &summary.effect.reads {
                    accesses.extend(
                        tracer
                            .substitute_footprint(read, args, frame)?
                            .into_iter()
                            .map(|footprint| LoopAccess {
                                kind: AccessKind::Read,
                                footprint,
                                phase,
                            }),
                    );
                }
                for write in &summary.effect.writes {
                    accesses.extend(
                        tracer
                            .substitute_footprint(write, args, frame)?
                            .into_iter()
                            .map(|footprint| LoopAccess {
                                kind: AccessKind::Write,
                                footprint,
                                phase,
                            }),
                    );
                }
                for hazard in &summary.effect.hazards {
                    if hazard.order != HazardOrder::Sequential {
                        return None;
                    }
                    let writes = tracer.substitute_footprint(&hazard.write, args, frame)?;
                    let reads = tracer.substitute_footprint(&hazard.read, args, frame)?;
                    same_iteration_hazards.extend(writes.iter().flat_map(|write| {
                        reads.iter().map(|read| PotentialHazard {
                            write: write.clone(),
                            read: read.clone(),
                            order: HazardOrder::SameIteration(recognized.id),
                        })
                    }));
                }
                phase = phase.checked_add(1)?;
            }
            TerminatorKind::SwitchInt { discr, .. }
            | TerminatorKind::Assert { cond: discr, .. } => {
                for raw in tracer.operand_accesses(discr, Some(AccessKind::Read))? {
                    let footprints = tracer.resolve_access(raw, location)?;
                    accesses.extend(footprints.into_iter().map(|(kind, footprint)| LoopAccess {
                        kind,
                        footprint,
                        phase,
                    }));
                    phase = phase.checked_add(1)?;
                }
            }
            TerminatorKind::Goto { .. } => {}
            TerminatorKind::Drop { .. }
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::Return
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(..)
            | TerminatorKind::Unreachable
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => return None,
        }
    }

    let reads: Vec<_> = accesses
        .iter()
        .filter(|access| access.kind == AccessKind::Read)
        .collect();
    let writes: Vec<_> = accesses
        .iter()
        .filter(|access| access.kind == AccessKind::Write)
        .collect();
    let mut hazards = same_iteration_hazards;
    for write in &writes {
        for read in &reads {
            if write.phase < read.phase {
                hazards.push(PotentialHazard {
                    write: write.footprint.clone(),
                    read: read.footprint.clone(),
                    order: HazardOrder::SameIteration(recognized.id),
                });
            }
            hazards.push(PotentialHazard {
                write: write.footprint.clone(),
                read: read.footprint.clone(),
                order: HazardOrder::LaterIteration(recognized.id),
            });
        }
    }

    let mut effect = AccessEffect {
        reads: reads
            .into_iter()
            .map(|access| access.footprint.clone())
            .collect(),
        writes: writes
            .into_iter()
            .map(|access| access.footprint.clone())
            .collect(),
        hazards,
        invalidations: vec![],
        contains_repetition: true,
    };
    effect.normalize();
    if effect.element_count() > ACCESS_SUMMARY_BUDGET {
        return None;
    }
    Some(AtomicLoopEffect {
        recognized: recognized.clone(),
        effect,
    })
}

pub(crate) fn build_body_loop_effects<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    flow: &PointerFlowResult,
    callee_summaries: &FxHashMap<LocalDefId, FunctionAccessSummary>,
    recursive_callees: &FxHashSet<LocalDefId>,
) -> Vec<AtomicLoopEffect> {
    recognize_loops(tcx, def_id)
        .iter()
        .filter_map(|recognized| {
            build_loop_effect(
                tcx,
                def_id,
                body,
                recognized,
                flow,
                callee_summaries,
                recursive_callees,
            )
        })
        .collect()
}

struct LoopAccess {
    kind: AccessKind,
    footprint: AccessFootprint,
    phase: u64,
}

#[derive(Clone, Copy)]
struct RawAccess<'tcx> {
    kind: AccessKind,
    pointer: Place<'tcx>,
    accessed_ty: Ty<'tcx>,
    projected_offset: i64,
}

#[derive(Clone, Copy)]
struct AffinePointer {
    origin: usize,
    stride_bytes: i64,
    constant_bytes: i64,
}

enum ResolvedAffinePointer {
    Parameter(AffinePointer),
    ProvenDisjoint,
}

#[derive(Clone, Copy)]
struct IntegerExpr {
    iteration_coefficient: i64,
    constant: i64,
}

struct LoopTracer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'a Body<'tcx>,
    recognized: &'a RecognizedLoop,
    flow: &'a PointerFlowResult,
    induction_constant: i64,
}

impl<'tcx> LoopTracer<'_, 'tcx> {
    fn statement_accesses(&self, kind: &StatementKind<'tcx>) -> Option<Vec<RawAccess<'tcx>>> {
        match kind {
            StatementKind::Assign(box (destination, rvalue)) => {
                let mut accesses = self.rvalue_accesses(rvalue)?;
                accesses.extend(self.place_accesses(*destination, Some(AccessKind::Write))?);
                Some(accesses)
            }
            StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
                self.place_accesses(**place, Some(AccessKind::Write))
            }
            StatementKind::Intrinsic(box intrinsic) => match intrinsic {
                rustc_middle::mir::NonDivergingIntrinsic::Assume(operand) => {
                    self.operand_accesses(operand, Some(AccessKind::Read))
                }
                rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => None,
            },
            StatementKind::FakeRead(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Retag(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::Nop => Some(vec![]),
        }
    }

    fn rvalue_accesses(&self, rvalue: &Rvalue<'tcx>) -> Option<Vec<RawAccess<'tcx>>> {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::ShallowInitBox(operand, _)
            | Rvalue::WrapUnsafeBinder(operand, _) => {
                self.operand_accesses(operand, Some(AccessKind::Read))
            }
            Rvalue::BinaryOp(_, box (left, right)) => {
                let mut accesses = self.operand_accesses(left, Some(AccessKind::Read))?;
                accesses.extend(self.operand_accesses(right, Some(AccessKind::Read))?);
                Some(accesses)
            }
            Rvalue::Aggregate(_, operands) => {
                let mut accesses = vec![];
                for operand in operands {
                    accesses.extend(self.operand_accesses(operand, Some(AccessKind::Read))?);
                }
                Some(accesses)
            }
            Rvalue::CopyForDeref(place) | Rvalue::Len(place) | Rvalue::Discriminant(place) => {
                self.place_accesses(*place, Some(AccessKind::Read))
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                self.place_accesses(*place, None)
            }
            Rvalue::NullaryOp(..) | Rvalue::ThreadLocalRef(..) => Some(vec![]),
        }
    }

    fn operand_accesses(
        &self,
        operand: &Operand<'tcx>,
        kind: Option<AccessKind>,
    ) -> Option<Vec<RawAccess<'tcx>>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_accesses(*place, kind),
            Operand::Constant(_) => Some(vec![]),
        }
    }

    fn place_accesses(
        &self,
        place: Place<'tcx>,
        final_kind: Option<AccessKind>,
    ) -> Option<Vec<RawAccess<'tcx>>> {
        let derefs: Vec<_> = place
            .projection
            .iter()
            .enumerate()
            .filter_map(|(index, elem)| matches!(elem, ProjectionElem::Deref).then_some(index))
            .collect();
        let Some(&last_deref) = derefs.last() else {
            return Some(vec![]);
        };

        let mut accesses = vec![];
        for (position, &deref_index) in derefs.iter().enumerate() {
            let kind = if deref_index == last_deref {
                final_kind
            } else {
                Some(AccessKind::Read)
            };
            let Some(kind) = kind else {
                continue;
            };
            let projection_end = derefs
                .get(position + 1)
                .copied()
                .unwrap_or(place.projection.len());
            let accessed_place = Place::from(place.local)
                .project_deeper(&place.projection[..projection_end], self.tcx);
            let pointer =
                Place::from(place.local).project_deeper(&place.projection[..deref_index], self.tcx);
            accesses.push(RawAccess {
                kind,
                pointer,
                accessed_ty: accessed_place.ty(self.body, self.tcx).ty,
                projected_offset: self.post_deref_offset(place, deref_index + 1, projection_end)?,
            });
        }
        Some(accesses)
    }

    fn resolve_access(
        &self,
        raw: RawAccess<'tcx>,
        location: Location,
    ) -> Option<Vec<(AccessKind, AccessFootprint)>> {
        let width = self.layout(raw.accessed_ty)?.size.bytes();
        if width == 0 {
            return None;
        }
        let operand = Operand::Copy(raw.pointer);
        let resolved = self.resolve_affine_pointer(&operand)?;
        let ResolvedAffinePointer::Parameter(mut pointer) = resolved else {
            return Some(vec![]);
        };
        pointer.constant_bytes = pointer.constant_bytes.checked_add(raw.projected_offset)?;
        self.validate_stride(raw.pointer.ty(self.body, self.tcx).ty, pointer.stride_bytes)?;
        let address = self.symbolic_address(pointer);
        Some(vec![(
            raw.kind,
            AccessFootprint {
                address,
                width: WidthExpr::Const(width),
                location,
                call_chain: vec![],
            },
        )])
    }

    fn substitute_footprint(
        &self,
        footprint: &AccessFootprint,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        frame: CallFrame,
    ) -> Option<Vec<AccessFootprint>> {
        let actual = args.get(footprint.address.origin)?;
        let resolved = self.resolve_affine_pointer(&actual.node)?;
        let ResolvedAffinePointer::Parameter(mut pointer) = resolved else {
            return Some(vec![]);
        };
        let OffsetExpr::Const(callee_offset) = footprint.address.offset else {
            return None;
        };
        pointer.constant_bytes = pointer.constant_bytes.checked_add(callee_offset)?;
        self.validate_stride(actual.node.ty(self.body, self.tcx), pointer.stride_bytes)?;
        let mut call_chain = footprint.call_chain.clone();
        call_chain.insert(0, frame);
        Some(vec![AccessFootprint {
            address: self.symbolic_address(pointer),
            width: footprint.width,
            location: footprint.location,
            call_chain,
        }])
    }

    fn resolve_operand_access(
        &self,
        operand: &Operand<'tcx>,
        width: u64,
        kind: AccessKind,
        location: Location,
        phase: u64,
    ) -> Option<Vec<LoopAccess>> {
        if width == 0 {
            return Some(vec![]);
        }
        let resolved = self.resolve_affine_pointer(operand)?;
        let ResolvedAffinePointer::Parameter(pointer) = resolved else {
            return Some(vec![]);
        };
        self.validate_stride(operand.ty(self.body, self.tcx), pointer.stride_bytes)?;
        Some(vec![LoopAccess {
            kind,
            footprint: AccessFootprint {
                address: self.symbolic_address(pointer),
                width: WidthExpr::Const(width),
                location,
                call_chain: vec![],
            },
            phase,
        }])
    }

    fn symbolic_address(&self, pointer: AffinePointer) -> SymbolicAddress {
        let offset = if pointer.stride_bytes == 0 {
            OffsetExpr::Const(pointer.constant_bytes)
        } else {
            OffsetExpr::LoopAffine {
                loop_id: self.recognized.id,
                stride_bytes: pointer.stride_bytes,
                constant_bytes: pointer.constant_bytes,
            }
        };
        SymbolicAddress {
            origin: pointer.origin,
            offset,
        }
    }

    fn resolve_affine_pointer(&self, operand: &Operand<'tcx>) -> Option<ResolvedAffinePointer> {
        let origins = resolve_pointer_operand(self.tcx, self.def_id, self.body, self.flow, operand);
        if origins.unresolved {
            return None;
        }
        if origins.addresses.is_empty() {
            return Some(ResolvedAffinePointer::ProvenDisjoint);
        }
        let origin = unique_parameter_origin(&origins)?;
        let place = operand.place()?;
        let pointer = self.trace_pointer_place(place, &mut FxHashSet::default())?;
        if pointer.origin != origin
            || origins.addresses.iter().any(|address| {
                !matches!(
                    address.offset,
                    OffsetExpr::Unknown if pointer.stride_bytes != 0
                ) && !matches!(
                    address.offset,
                    OffsetExpr::Const(offset)
                        if pointer.stride_bytes == 0 && offset == pointer.constant_bytes
                )
            })
        {
            return None;
        }
        Some(ResolvedAffinePointer::Parameter(pointer))
    }

    fn trace_pointer_place(
        &self,
        place: Place<'tcx>,
        seen: &mut FxHashSet<Local>,
    ) -> Option<AffinePointer> {
        if !place.projection.is_empty() {
            return None;
        }
        self.trace_pointer_local(place.local, seen)
    }

    fn trace_pointer_local(
        &self,
        local: Local,
        seen: &mut FxHashSet<Local>,
    ) -> Option<AffinePointer> {
        if !seen.insert(local) {
            return None;
        }
        let result = (|| {
            if self.body.args_iter().any(|argument| argument == local) {
                if !local_definitions(self.body, local).is_empty() {
                    return None;
                }
                return Some(AffinePointer {
                    origin: local.index().checked_sub(1)?,
                    stride_bytes: 0,
                    constant_bytes: 0,
                });
            }

            let definitions = local_definitions(self.body, local);
            let [definition] = definitions.as_slice() else {
                return None;
            };
            match definition {
                LocalDefinition::Statement(rvalue) => match rvalue {
                    Rvalue::Use(operand) => self.trace_pointer_place(operand.place()?, seen),
                    Rvalue::CopyForDeref(place) => self.trace_pointer_place(*place, seen),
                    Rvalue::Cast(_, operand, target_ty)
                        if operand.ty(self.body, self.tcx).is_raw_ptr()
                            && target_ty.is_raw_ptr() =>
                    {
                        self.trace_pointer_place(operand.place()?, seen)
                    }
                    _ => None,
                },
                LocalDefinition::Call { func, args } => {
                    let callee = direct_callee(func)?;
                    let path = self.tcx.def_path_str(callee);
                    if !is_pointer_arithmetic(self.tcx, callee, &path) {
                        return None;
                    }
                    let receiver = args.first()?;
                    let count = args.get(1)?;
                    let mut pointer = self.trace_pointer_place(receiver.node.place()?, seen)?;
                    let integer =
                        self.trace_integer_operand(&count.node, &mut FxHashSet::default())?;
                    let scale = self
                        .pointer_arithmetic_scale(&path, receiver.node.ty(self.body, self.tcx))?;
                    let stride = integer.iteration_coefficient.checked_mul(scale)?;
                    let constant = integer.constant.checked_mul(scale)?;
                    pointer.stride_bytes = pointer.stride_bytes.checked_add(stride)?;
                    pointer.constant_bytes = pointer.constant_bytes.checked_add(constant)?;
                    Some(pointer)
                }
            }
        })();
        seen.remove(&local);
        result
    }

    fn trace_integer_operand(
        &self,
        operand: &Operand<'tcx>,
        seen: &mut FxHashSet<Local>,
    ) -> Option<IntegerExpr> {
        match operand {
            Operand::Constant(_) => Some(IntegerExpr {
                iteration_coefficient: 0,
                constant: self.literal_integer(operand)?,
            }),
            Operand::Copy(place) | Operand::Move(place) => {
                if !place.projection.is_empty() {
                    return None;
                }
                let local = place.local;
                if local == self.recognized.induction.local {
                    return Some(IntegerExpr {
                        iteration_coefficient: 1,
                        constant: self.induction_constant,
                    });
                }
                if !seen.insert(local) {
                    return None;
                }
                let result = (|| {
                    let definitions = local_definitions(self.body, local);
                    let [LocalDefinition::Statement(rvalue)] = definitions.as_slice() else {
                        return None;
                    };
                    match rvalue {
                        Rvalue::Use(operand) => self.trace_integer_operand(operand, seen),
                        Rvalue::Cast(_, operand, target_ty) => {
                            let source_ty = operand.ty(self.body, self.tcx);
                            if let Some(value) =
                                cast_literal_integer(self.tcx, self.def_id, operand, *target_ty)
                            {
                                return Some(IntegerExpr {
                                    iteration_coefficient: 0,
                                    constant: value,
                                });
                            }
                            let mut integer = self.trace_integer_operand(operand, seen)?;
                            if integer.iteration_coefficient == 0 {
                                integer.constant = cast_integer_constant(
                                    self.tcx,
                                    self.def_id,
                                    integer.constant,
                                    source_ty,
                                    *target_ty,
                                )?;
                                return Some(integer);
                            }
                            value_preserving_integer_cast(
                                self.tcx,
                                self.def_id,
                                source_ty,
                                *target_ty,
                            )
                            .then_some(integer)
                        }
                        Rvalue::BinaryOp(BinOp::Add, box (left, right)) => {
                            let left = self.trace_integer_operand(left, seen)?;
                            let right = self.trace_integer_operand(right, seen)?;
                            let coefficient = left
                                .iteration_coefficient
                                .checked_add(right.iteration_coefficient)?;
                            if coefficient > 1 {
                                return None;
                            }
                            Some(IntegerExpr {
                                iteration_coefficient: coefficient,
                                constant: left.constant.checked_add(right.constant)?,
                            })
                        }
                        Rvalue::BinaryOp(BinOp::Sub, box (left, right)) => {
                            let left = self.trace_integer_operand(left, seen)?;
                            let right = self.trace_integer_operand(right, seen)?;
                            if right.iteration_coefficient != 0 {
                                return None;
                            }
                            Some(IntegerExpr {
                                iteration_coefficient: left.iteration_coefficient,
                                constant: left.constant.checked_sub(right.constant)?,
                            })
                        }
                        _ => None,
                    }
                })();
                seen.remove(&local);
                result
            }
        }
    }

    fn pointer_arithmetic_scale(&self, path: &str, receiver_ty: Ty<'tcx>) -> Option<i64> {
        let last = path.rsplit("::").next()?;
        let mut scale = if matches!(last, "byte_offset" | "wrapping_byte_offset") {
            1
        } else {
            let ty::TyKind::RawPtr(pointee, _) = receiver_ty.kind() else {
                return None;
            };
            i64::try_from(self.layout(*pointee)?.size.bytes()).ok()?
        };
        if matches!(last, "sub" | "wrapping_sub") {
            scale = scale.checked_neg()?;
        }
        Some(scale)
    }

    fn validate_stride(&self, pointer_ty: Ty<'tcx>, stride: i64) -> Option<()> {
        if stride == 0 {
            return Some(());
        }
        let ty::TyKind::RawPtr(pointee, _) = pointer_ty.kind() else {
            return None;
        };
        let pointee_size = i64::try_from(self.layout(*pointee)?.size.bytes()).ok()?;
        (stride == pointee_size).then_some(())
    }

    fn post_deref_offset(&self, place: Place<'tcx>, start: usize, end: usize) -> Option<i64> {
        let mut displacement = 0_i64;
        for projection_index in start..end {
            let projection = place.projection[projection_index];
            let prefix = Place::from(place.local)
                .project_deeper(&place.projection[..projection_index], self.tcx);
            let prefix_ty = prefix.ty(self.body, self.tcx);
            let bytes = match projection {
                ProjectionElem::Field(field, _) => {
                    let mut layout = self.layout(prefix_ty.ty)?;
                    if let Some(variant) = prefix_ty.variant_index {
                        let layout_cx = rustc_middle::ty::layout::LayoutCx::new(
                            self.tcx,
                            ty::TypingEnv::post_analysis(self.tcx, self.def_id),
                        );
                        layout = layout.for_variant(&layout_cx, variant);
                    }
                    layout.fields.offset(field.index()).bytes()
                }
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let element_ty = prefix_ty.ty.builtin_index()?;
                    let element_size = self.layout(element_ty)?.size.bytes();
                    let element_index = if from_end {
                        let ty::TyKind::Array(_, length) = prefix_ty.ty.kind() else {
                            return None;
                        };
                        length.try_to_target_usize(self.tcx)?.checked_sub(offset)?
                    } else {
                        offset
                    };
                    element_size.checked_mul(element_index)?
                }
                ProjectionElem::Subslice { from, .. } => {
                    let element_ty = prefix_ty.ty.builtin_index()?;
                    self.layout(element_ty)?.size.bytes().checked_mul(from)?
                }
                ProjectionElem::Downcast(..)
                | ProjectionElem::OpaqueCast(..)
                | ProjectionElem::Subtype(..)
                | ProjectionElem::UnwrapUnsafeBinder(..) => 0,
                ProjectionElem::Index(_) | ProjectionElem::Deref => return None,
            };
            displacement = displacement.checked_add(i64::try_from(bytes).ok()?)?;
        }
        Some(displacement)
    }

    fn literal_integer(&self, operand: &Operand<'tcx>) -> Option<i64> {
        literal_integer(operand)
    }

    fn layout(&self, ty: Ty<'tcx>) -> Option<rustc_middle::ty::layout::TyAndLayout<'tcx>> {
        self.tcx
            .layout_of(ty::TypingEnv::post_analysis(self.tcx, self.def_id).as_query_input(ty))
            .ok()
    }
}

fn induction_initial_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    recognized: &RecognizedLoop,
) -> Option<i64> {
    let rvalue = body.basic_blocks[recognized.induction.init_block]
        .statements
        .iter()
        .rev()
        .find_map(|statement| {
            let StatementKind::Assign(box (place, rvalue)) = &statement.kind else {
                return None;
            };
            (place.as_local() == Some(recognized.induction.local)).then_some(rvalue)
        })?;
    match rvalue {
        Rvalue::Use(operand) => literal_integer(operand),
        Rvalue::Cast(_, operand, target) => cast_literal_integer(tcx, def_id, operand, *target)
            .or_else(|| {
                cast_integer_constant(
                    tcx,
                    def_id,
                    literal_integer(operand)?,
                    operand.ty(body, tcx),
                    *target,
                )
            }),
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct IntegerType {
    signed: bool,
    bits: u32,
}

fn integer_type<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId, ty: Ty<'tcx>) -> Option<IntegerType> {
    let signed = match ty.kind() {
        ty::TyKind::Int(_) => true,
        ty::TyKind::Uint(_) => false,
        _ => return None,
    };
    let bits = tcx
        .layout_of(ty::TypingEnv::post_analysis(tcx, def_id).as_query_input(ty))
        .ok()?
        .size
        .bits()
        .try_into()
        .ok()?;
    Some(IntegerType { signed, bits })
}

pub(crate) fn value_preserving_integer_cast<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
) -> bool {
    let Some(source) = integer_type(tcx, def_id, source) else {
        return false;
    };
    let Some(target) = integer_type(tcx, def_id, target) else {
        return false;
    };
    source.signed == target.signed && source.bits <= target.bits
        || !source.signed && target.signed && source.bits < target.bits
}

pub(crate) fn cast_literal_integer<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    operand: &Operand<'tcx>,
    target: Ty<'tcx>,
) -> Option<i64> {
    let constant = operand.constant()?;
    let scalar = constant.const_.try_to_scalar()?;
    let integer = scalar.try_to_scalar_int().ok()?;
    cast_integer_bits(
        tcx,
        def_id,
        integer.to_bits(integer.size()),
        constant.const_.ty(),
        target,
    )
}

fn cast_integer_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    value: i64,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
) -> Option<i64> {
    let source = integer_type(tcx, def_id, source)?;
    let target = integer_type(tcx, def_id, target)?;
    let bits = (i128::from(value) as u128) & low_bits_mask(source.bits);
    cast_integer_bits_with_types(bits, source, target)
}

fn cast_integer_bits<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    bits: u128,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
) -> Option<i64> {
    let source = integer_type(tcx, def_id, source)?;
    let target = integer_type(tcx, def_id, target)?;
    cast_integer_bits_with_types(bits, source, target)
}

fn cast_integer_bits_with_types(
    bits: u128,
    source: IntegerType,
    target: IntegerType,
) -> Option<i64> {
    let mut bits = bits & low_bits_mask(source.bits);
    if source.signed && target.bits > source.bits && bits & (1_u128 << (source.bits - 1)) != 0 {
        bits |= low_bits_mask(target.bits) ^ low_bits_mask(source.bits);
    }
    bits &= low_bits_mask(target.bits);
    if target.signed && bits & (1_u128 << (target.bits - 1)) != 0 {
        let value = if target.bits == 128 {
            bits as i128
        } else {
            (bits | !low_bits_mask(target.bits)) as i128
        };
        i64::try_from(value).ok()
    } else {
        i64::try_from(bits).ok()
    }
}

fn low_bits_mask(bits: u32) -> u128 {
    if bits == 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    }
}

fn literal_integer(operand: &Operand<'_>) -> Option<i64> {
    let constant = operand.constant()?;
    let scalar = constant.const_.try_to_scalar()?;
    let integer = scalar.try_to_scalar_int().ok()?;
    let bits = integer.to_bits(integer.size());
    let value = match constant.const_.ty().kind() {
        ty::TyKind::Int(_) => integer.size().sign_extend(bits),
        ty::TyKind::Uint(_) => i128::try_from(bits).ok()?,
        _ => return None,
    };
    i64::try_from(value).ok()
}

pub(crate) enum LocalDefinition<'a, 'tcx> {
    Statement(&'a Rvalue<'tcx>),
    Call {
        func: &'a Operand<'tcx>,
        args: &'a [rustc_span::source_map::Spanned<Operand<'tcx>>],
    },
}

pub(crate) fn local_definitions<'a, 'tcx>(
    body: &'a Body<'tcx>,
    local: Local,
) -> Vec<LocalDefinition<'a, 'tcx>> {
    let mut definitions = vec![];
    for block_data in body.basic_blocks.iter() {
        for statement in &block_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &statement.kind
                && place.as_local() == Some(local)
            {
                definitions.push(LocalDefinition::Statement(rvalue));
            }
        }
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &block_data.terminator().kind
            && destination.as_local() == Some(local)
        {
            definitions.push(LocalDefinition::Call { func, args });
        }
    }
    definitions
}

fn unique_parameter_origin(origins: &ResolvedPointerOrigins) -> Option<usize> {
    let mut origins = origins.addresses.iter().map(|address| address.origin);
    let origin = origins.next()?;
    origins.all(|other| other == origin).then_some(origin)
}

fn direct_callee(func: &Operand<'_>) -> Option<DefId> {
    let constant = func.constant()?;
    let ty::TyKind::FnDef(def_id, _) = constant.ty().kind() else {
        return None;
    };
    Some(*def_id)
}
