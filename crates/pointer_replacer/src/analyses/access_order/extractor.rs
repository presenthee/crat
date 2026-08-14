use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        Body, Location, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_span::source_map::Spanned;

use super::{
    AccessEffect, AccessFootprint, AccessKind, AccessUnknownReason, Invalidation, OffsetExpr,
    ParamScope, SymbolicAddress,
};
use crate::analyses::pointer_flow::{
    PointerFlowResult,
    graph::{BaseId, Offset, PfgNode},
};

#[derive(Clone, Debug)]
pub(crate) struct CallSite<'tcx> {
    pub(crate) func: Operand<'tcx>,
    pub(crate) args: Vec<Spanned<Operand<'tcx>>>,
}

#[derive(Clone, Debug)]
pub(crate) enum LocationEffect<'tcx> {
    Effect(AccessEffect),
    Call(CallSite<'tcx>),
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ResolvedPointerOrigins {
    pub(crate) addresses: Vec<SymbolicAddress>,
    pub(crate) unresolved: bool,
    pub(crate) unknown_offset: bool,
}

pub(crate) fn extract_body_effects<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    flow: &PointerFlowResult,
) -> FxHashMap<Location, LocationEffect<'tcx>> {
    let mut effects = FxHashMap::default();
    let extractor = Extractor {
        tcx,
        def_id,
        body,
        flow,
    };

    for (block, block_data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in block_data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if let Some(effect) = extractor.statement_effect(&statement.kind, location) {
                effects.insert(location, LocationEffect::Effect(effect));
            }
        }

        let location = Location {
            block,
            statement_index: block_data.statements.len(),
        };
        if let Some(effect) = extractor.terminator_effect(&block_data.terminator().kind, location) {
            effects.insert(location, effect);
        }
    }

    effects
}

struct Extractor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'a Body<'tcx>,
    flow: &'a PointerFlowResult,
}

impl<'tcx> Extractor<'_, 'tcx> {
    fn statement_effect(
        &self,
        kind: &StatementKind<'tcx>,
        location: Location,
    ) -> Option<AccessEffect> {
        match kind {
            StatementKind::Assign(box (destination, rvalue)) => {
                let effect = self.rvalue_effect(rvalue, location).then(self.place_effect(
                    *destination,
                    Some(AccessKind::Write),
                    location,
                ));
                nonempty(effect)
            }
            StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
                nonempty(self.place_effect(**place, Some(AccessKind::Write), location))
            }
            StatementKind::Intrinsic(box intrinsic) => {
                nonempty(self.intrinsic_effect(intrinsic, location))
            }
            StatementKind::FakeRead(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Retag(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::Nop => None,
        }
    }

    fn terminator_effect(
        &self,
        kind: &TerminatorKind<'tcx>,
        location: Location,
    ) -> Option<LocationEffect<'tcx>> {
        match kind {
            TerminatorKind::SwitchInt { discr, .. }
            | TerminatorKind::Assert { cond: discr, .. } => {
                nonempty(self.operand_effect(discr, location)).map(LocationEffect::Effect)
            }
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => Some(LocationEffect::Call(CallSite {
                func: func.clone(),
                args: args.to_vec(),
            })),
            TerminatorKind::Drop { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => Some(LocationEffect::Effect(invalidation_effect(
                AccessUnknownReason::UnsupportedTerminator,
                location,
            ))),
            TerminatorKind::InlineAsm { .. } => Some(LocationEffect::Effect(invalidation_effect(
                AccessUnknownReason::InlineAssembly,
                location,
            ))),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(..)
            | TerminatorKind::Unreachable
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => None,
        }
    }

    fn rvalue_effect(&self, rvalue: &Rvalue<'tcx>, location: Location) -> AccessEffect {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::ShallowInitBox(operand, _)
            | Rvalue::WrapUnsafeBinder(operand, _) => self.operand_effect(operand, location),
            Rvalue::BinaryOp(_, box (left, right)) => self
                .operand_effect(left, location)
                .then(self.operand_effect(right, location)),
            Rvalue::Aggregate(_, operands) => operands
                .iter()
                .fold(AccessEffect::empty(), |effect, operand| {
                    effect.then(self.operand_effect(operand, location))
                }),
            Rvalue::CopyForDeref(place) => {
                self.place_effect(*place, Some(AccessKind::Read), location)
            }
            Rvalue::Len(place) | Rvalue::Discriminant(place) => {
                self.place_effect(*place, Some(AccessKind::Read), location)
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                self.place_effect(*place, None, location)
            }
            Rvalue::NullaryOp(..) | Rvalue::ThreadLocalRef(..) => AccessEffect::empty(),
        }
    }

    fn intrinsic_effect(
        &self,
        intrinsic: &NonDivergingIntrinsic<'tcx>,
        location: Location,
    ) -> AccessEffect {
        match intrinsic {
            NonDivergingIntrinsic::Assume(operand) => self.operand_effect(operand, location),
            NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                let Some(count) = constant_usize(&copy.count, self.tcx) else {
                    return self.relevant_invalidation(
                        [&copy.src, &copy.dst],
                        AccessUnknownReason::UnknownWidth,
                        location,
                    );
                };
                let Some(element_ty) = raw_pointer_pointee(copy.src.ty(self.body, self.tcx)) else {
                    return self.relevant_invalidation(
                        [&copy.src, &copy.dst],
                        AccessUnknownReason::UnsupportedStatement,
                        location,
                    );
                };
                let Some(element_size) = self.layout(element_ty).map(|layout| layout.size.bytes())
                else {
                    return self.relevant_invalidation(
                        [&copy.src, &copy.dst],
                        AccessUnknownReason::UnknownWidth,
                        location,
                    );
                };
                let Some(width) = element_size.checked_mul(count) else {
                    return self.relevant_invalidation(
                        [&copy.src, &copy.dst],
                        AccessUnknownReason::UnknownWidth,
                        location,
                    );
                };
                if width == 0 {
                    return AccessEffect::empty();
                }

                self.pointer_operand_effect(&copy.src, width, AccessKind::Read, location)
                    .then(self.pointer_operand_effect(
                        &copy.dst,
                        width,
                        AccessKind::Write,
                        location,
                    ))
            }
        }
    }

    fn operand_effect(&self, operand: &Operand<'tcx>, location: Location) -> AccessEffect {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.place_effect(*place, Some(AccessKind::Read), location)
            }
            Operand::Constant(_) => AccessEffect::empty(),
        }
    }

    fn place_effect(
        &self,
        place: Place<'tcx>,
        final_kind: Option<AccessKind>,
        location: Location,
    ) -> AccessEffect {
        let derefs: Vec<_> = place
            .projection
            .iter()
            .enumerate()
            .filter_map(|(index, elem)| matches!(elem, ProjectionElem::Deref).then_some(index))
            .collect();
        let Some(&last_deref) = derefs.last() else {
            return AccessEffect::empty();
        };

        let mut effect = AccessEffect::empty();
        for (position, &deref_index) in derefs.iter().enumerate() {
            let is_last = deref_index == last_deref;
            let Some(kind) = (if is_last {
                final_kind
            } else {
                Some(AccessKind::Read)
            }) else {
                continue;
            };
            let projection_end = derefs
                .get(position + 1)
                .copied()
                .unwrap_or(place.projection.len());
            let accessed_place = Place::from(place.local)
                .project_deeper(&place.projection[..projection_end], self.tcx);
            let pointer_place =
                Place::from(place.local).project_deeper(&place.projection[..deref_index], self.tcx);
            let projected_offset = self.post_deref_offset(place, deref_index + 1, projection_end);
            effect = effect.then(self.deref_effect(
                pointer_place,
                accessed_place.ty(self.body, self.tcx).ty,
                projected_offset,
                kind,
                location,
            ));
        }
        effect
    }

    fn deref_effect(
        &self,
        pointer_place: Place<'tcx>,
        accessed_ty: Ty<'tcx>,
        projected_offset: ProjectedOffset,
        kind: AccessKind,
        location: Location,
    ) -> AccessEffect {
        let origins = self.resolve_pointer_place(pointer_place, projected_offset);
        if origins.addresses.is_empty() && !origins.unresolved {
            return AccessEffect::empty();
        }
        let Some(width) = self.access_width(accessed_ty) else {
            return effect_for_unknown_width(origins, location);
        };

        effect_for_resolved_origins(origins, width, kind, location)
    }

    fn pointer_operand_effect(
        &self,
        operand: &Operand<'tcx>,
        width: u64,
        kind: AccessKind,
        location: Location,
    ) -> AccessEffect {
        let origins = self.resolve_pointer_operand(operand);
        effect_for_resolved_origins(origins, width, kind, location)
    }

    fn relevant_invalidation<'op>(
        &self,
        operands: impl IntoIterator<Item = &'op Operand<'tcx>>,
        reason: AccessUnknownReason,
        location: Location,
    ) -> AccessEffect
    where
        'tcx: 'op,
    {
        let mut scope = FxHashSet::default();
        let mut unresolved = false;
        for operand in operands {
            let origins = self.resolve_pointer_operand(operand);
            scope.extend(origins.addresses.into_iter().map(|address| address.origin));
            unresolved |= origins.unresolved;
        }
        if scope.is_empty() && !unresolved {
            return AccessEffect::empty();
        }
        AccessEffect {
            invalidations: vec![Invalidation {
                scope: if unresolved {
                    ParamScope::All
                } else {
                    ParamScope::Known(scope)
                },
                reason,
                location,
                call_chain: vec![],
            }],
            ..AccessEffect::empty()
        }
    }

    fn resolve_pointer_operand(&self, operand: &Operand<'tcx>) -> ResolvedPointerOrigins {
        let Some(place) = operand.place() else {
            return ResolvedPointerOrigins {
                unresolved: true,
                ..ResolvedPointerOrigins::default()
            };
        };
        self.resolve_pointer_place(place, ProjectedOffset::Const(0))
    }

    fn resolve_call_operand(&self, operand: &Operand<'tcx>) -> ResolvedPointerOrigins {
        let ty = operand.ty(self.body, self.tcx);
        let pointer_shape = classify_data_pointers(
            ty,
            self.tcx,
            &mut FxHashSet::default(),
            DATA_POINTER_RECURSION_LIMIT,
        );
        let Some(place) = operand.place() else {
            return ResolvedPointerOrigins {
                unresolved: pointer_shape.may_contain(),
                ..ResolvedPointerOrigins::default()
            };
        };
        let Some(slots) = self.flow.slot_table.place_slots(place, self.body, self.tcx) else {
            return ResolvedPointerOrigins {
                unresolved: pointer_shape.may_contain(),
                ..ResolvedPointerOrigins::default()
            };
        };
        let has_slots = !slots.is_empty();
        let mut origins = self.resolve_pointer_slots(slots, ProjectedOffset::Const(0));
        origins.unresolved |=
            pointer_shape.unrepresented || pointer_shape.represented && !has_slots;
        origins
    }

    fn resolve_pointer_place(
        &self,
        pointer_place: Place<'tcx>,
        projected_offset: ProjectedOffset,
    ) -> ResolvedPointerOrigins {
        let Some(slot) = self
            .flow
            .slot_table
            .place_slots(pointer_place, self.body, self.tcx)
            .and_then(|mut slots| slots.next())
        else {
            return ResolvedPointerOrigins {
                unresolved: true,
                ..ResolvedPointerOrigins::default()
            };
        };
        self.resolve_pointer_slots(std::iter::once(slot), projected_offset)
    }

    fn resolve_pointer_slots(
        &self,
        slots: impl IntoIterator<Item = usize>,
        projected_offset: ProjectedOffset,
    ) -> ResolvedPointerOrigins {
        let mut result = ResolvedPointerOrigins::default();
        for slot in slots {
            let node = PfgNode::Slot(slot);
            let Some(bases) = self.flow.provenance.reachable_bases.get(&node) else {
                result.unresolved = true;
                continue;
            };
            for base in bases {
                match base {
                    BaseId::Param { local, .. } => {
                        let Some(origin) = local.index().checked_sub(1) else {
                            result.unresolved = true;
                            continue;
                        };
                        let base_offset = self
                            .flow
                            .provenance
                            .offset_from_base(&node, base)
                            .unwrap_or(Offset::Unknown);
                        let offset = match projected_offset {
                            ProjectedOffset::Const(displacement) => {
                                let composed = base_offset.compose(Offset::Const(displacement));
                                if matches!(composed, Offset::Unknown) {
                                    result.unknown_offset = true;
                                }
                                match composed {
                                    Offset::Const(offset) => OffsetExpr::Const(offset),
                                    Offset::Unknown => OffsetExpr::Unknown,
                                }
                            }
                            ProjectedOffset::Unknown => {
                                result.unknown_offset = true;
                                OffsetExpr::Unknown
                            }
                        };
                        result.addresses.push(SymbolicAddress { origin, offset });
                    }
                    BaseId::LocalArray { local } if self.is_direct_local_array(*local) => {}
                    BaseId::RawBorrow {
                        target: Some(_),
                        location,
                    } if self.is_direct_local_raw_borrow(*location) => {}
                    BaseId::LocalVec { .. }
                    | BaseId::LocalScalar { .. }
                    | BaseId::HeapAlloc { .. } => {}
                    BaseId::LocalArray { .. }
                    | BaseId::RawBorrow {
                        target: Some(_), ..
                    }
                    | BaseId::OpaqueReturn { .. }
                    | BaseId::IntToPtr { .. }
                    | BaseId::RawBorrow { target: None, .. }
                    | BaseId::Unknown { .. } => result.unresolved = true,
                }
            }
        }

        result.addresses.sort_by_key(|address| address.origin);
        result.addresses.dedup();
        result
    }

    fn post_deref_offset(&self, place: Place<'tcx>, start: usize, end: usize) -> ProjectedOffset {
        let mut displacement = 0_i64;
        for projection_index in start..end {
            let projection = place.projection[projection_index];
            let prefix = Place::from(place.local)
                .project_deeper(&place.projection[..projection_index], self.tcx);
            let prefix_ty = prefix.ty(self.body, self.tcx);
            let bytes = match projection {
                ProjectionElem::Field(field, _) => {
                    let Some(mut layout) = self.layout(prefix_ty.ty) else {
                        return ProjectedOffset::Unknown;
                    };
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
                    let Some(element_ty) = prefix_ty.ty.builtin_index() else {
                        return ProjectedOffset::Unknown;
                    };
                    let Some(element_size) =
                        self.layout(element_ty).map(|layout| layout.size.bytes())
                    else {
                        return ProjectedOffset::Unknown;
                    };
                    let element_index = if from_end {
                        let ty::TyKind::Array(_, length) = prefix_ty.ty.kind() else {
                            return ProjectedOffset::Unknown;
                        };
                        let Some(length) = length.try_to_target_usize(self.tcx) else {
                            return ProjectedOffset::Unknown;
                        };
                        let Some(index) = length.checked_sub(offset) else {
                            return ProjectedOffset::Unknown;
                        };
                        index
                    } else {
                        offset
                    };
                    let Some(bytes) = element_size.checked_mul(element_index) else {
                        return ProjectedOffset::Unknown;
                    };
                    bytes
                }
                ProjectionElem::Subslice { from, .. } => {
                    let Some(element_ty) = prefix_ty.ty.builtin_index() else {
                        return ProjectedOffset::Unknown;
                    };
                    let Some(element_size) =
                        self.layout(element_ty).map(|layout| layout.size.bytes())
                    else {
                        return ProjectedOffset::Unknown;
                    };
                    let Some(bytes) = element_size.checked_mul(from) else {
                        return ProjectedOffset::Unknown;
                    };
                    bytes
                }
                ProjectionElem::Downcast(..)
                | ProjectionElem::OpaqueCast(..)
                | ProjectionElem::Subtype(..)
                | ProjectionElem::UnwrapUnsafeBinder(..) => 0,
                ProjectionElem::Index(_) | ProjectionElem::Deref => {
                    return ProjectedOffset::Unknown;
                }
            };
            let Some(bytes) = i64::try_from(bytes).ok() else {
                return ProjectedOffset::Unknown;
            };
            let Some(next) = displacement.checked_add(bytes) else {
                return ProjectedOffset::Unknown;
            };
            displacement = next;
        }
        ProjectedOffset::Const(displacement)
    }

    fn is_direct_local_array(&self, local: rustc_middle::mir::Local) -> bool {
        matches!(
            self.body.local_decls[local].ty.kind(),
            ty::TyKind::Array(..)
        )
    }

    fn is_direct_local_raw_borrow(&self, location: Location) -> bool {
        let Some(statement) = self.body.basic_blocks[location.block]
            .statements
            .get(location.statement_index)
        else {
            return false;
        };
        let StatementKind::Assign(box (
            _,
            Rvalue::RawPtr(_, borrowed) | Rvalue::Ref(_, _, borrowed),
        )) = &statement.kind
        else {
            return false;
        };
        !borrowed
            .projection
            .iter()
            .any(|projection| matches!(projection, ProjectionElem::Deref))
    }

    fn layout(&self, ty: Ty<'tcx>) -> Option<rustc_middle::ty::layout::TyAndLayout<'tcx>> {
        let typing_env = ty::TypingEnv::post_analysis(self.tcx, self.def_id);
        self.tcx.layout_of(typing_env.as_query_input(ty)).ok()
    }

    fn access_width(&self, ty: Ty<'tcx>) -> Option<u64> {
        let width = self.layout(ty)?.size.bytes();
        (width > 0).then_some(width)
    }
}

pub(crate) fn resolve_pointer_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    flow: &PointerFlowResult,
    operand: &Operand<'tcx>,
) -> ResolvedPointerOrigins {
    Extractor {
        tcx,
        def_id,
        body,
        flow,
    }
    .resolve_pointer_operand(operand)
}

pub(crate) fn resolve_call_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
    flow: &PointerFlowResult,
    operand: &Operand<'tcx>,
) -> ResolvedPointerOrigins {
    Extractor {
        tcx,
        def_id,
        body,
        flow,
    }
    .resolve_call_operand(operand)
}

pub(crate) fn effect_for_resolved_origins(
    origins: ResolvedPointerOrigins,
    width: u64,
    kind: AccessKind,
    location: Location,
) -> AccessEffect {
    if width == 0 || origins.addresses.is_empty() && !origins.unresolved {
        return AccessEffect::empty();
    }
    let parameter_scope = known_scope(&origins.addresses);
    let mut effect = AccessEffect::empty();
    let footprints = origins
        .addresses
        .into_iter()
        .map(|address| AccessFootprint {
            address,
            width,
            location,
            call_chain: vec![],
        })
        .collect();
    match kind {
        AccessKind::Read => effect.reads = footprints,
        AccessKind::Write => effect.writes = footprints,
    }
    if origins.unknown_offset
        && let Some(scope) = parameter_scope
    {
        effect.invalidations.push(Invalidation {
            scope,
            reason: AccessUnknownReason::UnknownOffset,
            location,
            call_chain: vec![],
        });
    }
    if origins.unresolved {
        effect.invalidations.push(Invalidation {
            scope: ParamScope::All,
            reason: AccessUnknownReason::UnresolvedOrigin,
            location,
            call_chain: vec![],
        });
    }
    effect.normalize();
    effect
}

fn effect_for_unknown_width(origins: ResolvedPointerOrigins, location: Location) -> AccessEffect {
    let mut invalidations = vec![];
    if origins.unknown_offset
        && let Some(scope) = known_scope(&origins.addresses)
    {
        invalidations.push(Invalidation {
            scope,
            reason: AccessUnknownReason::UnknownOffset,
            location,
            call_chain: vec![],
        });
    }
    if let Some(scope) = known_scope(&origins.addresses) {
        invalidations.push(Invalidation {
            scope,
            reason: AccessUnknownReason::UnknownWidth,
            location,
            call_chain: vec![],
        });
    }
    if origins.unresolved {
        invalidations.push(Invalidation {
            scope: ParamScope::All,
            reason: AccessUnknownReason::UnresolvedOrigin,
            location,
            call_chain: vec![],
        });
    }
    AccessEffect {
        invalidations,
        ..AccessEffect::empty()
    }
}

pub(crate) fn constant_usize<'tcx>(operand: &Operand<'tcx>, tcx: TyCtxt<'tcx>) -> Option<u64> {
    let constant = operand.constant()?;
    if constant.const_.ty() != tcx.types.usize {
        return None;
    }
    let scalar = if let Some(scalar) = constant.const_.try_to_scalar() {
        scalar
    } else if let rustc_middle::mir::Const::Unevaluated(unevaluated, _) = constant.const_
        && unevaluated.promoted.is_none()
        && let Ok(rustc_middle::mir::ConstValue::Scalar(scalar)) =
            tcx.const_eval_poly(unevaluated.def)
    {
        scalar
    } else {
        return None;
    };
    let integer = scalar.try_to_scalar_int().ok()?;
    u64::try_from(integer.to_bits(integer.size())).ok()
}

pub(crate) fn raw_pointer_pointee<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::TyKind::RawPtr(pointee, _) = ty.kind() else {
        return None;
    };
    Some(*pointee)
}

const DATA_POINTER_RECURSION_LIMIT: usize = 64;

#[derive(Clone, Copy, Default)]
struct DataPointerShape {
    represented: bool,
    unrepresented: bool,
}

impl DataPointerShape {
    fn may_contain(self) -> bool {
        self.represented || self.unrepresented
    }

    fn then(self, other: Self) -> Self {
        Self {
            represented: self.represented || other.represented,
            unrepresented: self.unrepresented || other.unrepresented,
        }
    }
}

fn classify_data_pointers<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    seen_adts: &mut FxHashSet<DefId>,
    remaining_depth: usize,
) -> DataPointerShape {
    if remaining_depth == 0 {
        return DataPointerShape {
            unrepresented: true,
            ..DataPointerShape::default()
        };
    }
    let next_depth = remaining_depth - 1;

    if let Some(pointee) = ty.builtin_deref(true) {
        let nested = classify_data_pointers(pointee, tcx, seen_adts, next_depth);
        return DataPointerShape {
            represented: true,
            unrepresented: nested.unrepresented,
        };
    }
    if let Some(element) = ty.builtin_index() {
        return classify_data_pointers(element, tcx, seen_adts, next_depth);
    }

    match ty.kind() {
        ty::TyKind::Adt(adt_def, args) => {
            let def_id = adt_def.did();
            if !seen_adts.insert(def_id) {
                return DataPointerShape {
                    unrepresented: true,
                    ..DataPointerShape::default()
                };
            }
            let fields = adt_def
                .all_fields()
                .map(|field| {
                    classify_data_pointers(field.ty(tcx, args), tcx, seen_adts, next_depth)
                })
                .fold(DataPointerShape::default(), DataPointerShape::then);
            seen_adts.remove(&def_id);

            if (adt_def.is_struct() && !adt_def.is_union()) || !fields.may_contain() {
                fields
            } else {
                DataPointerShape {
                    unrepresented: true,
                    ..DataPointerShape::default()
                }
            }
        }
        ty::TyKind::Tuple(fields) => fields
            .iter()
            .map(|field| classify_data_pointers(field, tcx, seen_adts, next_depth))
            .fold(DataPointerShape::default(), DataPointerShape::then),
        ty::TyKind::Pat(inner, _) => classify_data_pointers(*inner, tcx, seen_adts, next_depth),
        ty::TyKind::Bool
        | ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_)
        | ty::TyKind::Float(_)
        | ty::TyKind::Str
        | ty::TyKind::FnDef(..)
        | ty::TyKind::FnPtr(..)
        | ty::TyKind::Never => DataPointerShape::default(),
        _ => DataPointerShape {
            unrepresented: true,
            ..DataPointerShape::default()
        },
    }
}

#[derive(Clone, Copy)]
enum ProjectedOffset {
    Const(i64),
    Unknown,
}

fn known_scope(addresses: &[SymbolicAddress]) -> Option<ParamScope> {
    let scope: FxHashSet<_> = addresses.iter().map(|address| address.origin).collect();
    (!scope.is_empty()).then_some(ParamScope::Known(scope))
}

fn invalidation_effect(reason: AccessUnknownReason, location: Location) -> AccessEffect {
    AccessEffect {
        invalidations: vec![Invalidation {
            scope: ParamScope::All,
            reason,
            location,
            call_chain: vec![],
        }],
        ..AccessEffect::empty()
    }
}

fn nonempty(effect: AccessEffect) -> Option<AccessEffect> {
    (!effect.reads.is_empty()
        || !effect.writes.is_empty()
        || !effect.hazards.is_empty()
        || !effect.invalidations.is_empty()
        || effect.contains_repetition)
        .then_some(effect)
}
