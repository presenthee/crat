use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{Body, Location, Operand},
    ty::{self, Ty, TyCtxt, TypeVisitableExt},
};

use super::{
    AccessEffect, AccessFootprint, AccessKind, AccessUnknownReason, CallFrame, Invalidation,
    OffsetExpr, ParamIdx, ParamScope, PotentialHazard,
    extractor::{
        CallSite, LocationEffect, ResolvedPointerOrigins, constant_usize,
        effect_for_resolved_origins, extract_body_effects, raw_pointer_pointee,
        resolve_call_operand, resolve_pointer_operand,
    },
    loop_effect::build_body_loop_effects,
    solver::solve_body,
};
use crate::{
    analyses::{
        mir::CallGraphPostOrder,
        pointer_flow::{PointerFlowResult, builtin::is_pointer_arithmetic},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, Default)]
pub struct FunctionAccessSummary {
    pub effect: AccessEffect,
}

pub struct AccessOrderAnalysis<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    flows: &'a FxHashMap<LocalDefId, PointerFlowResult>,
    summaries: FxHashMap<LocalDefId, FunctionAccessSummary>,
}

impl<'a, 'tcx> AccessOrderAnalysis<'a, 'tcx> {
    pub fn analyze(
        input: &RustProgram<'tcx>,
        flows: &'a FxHashMap<LocalDefId, PointerFlowResult>,
    ) -> Self {
        let mut analysis = Self {
            tcx: input.tcx,
            flows,
            summaries: FxHashMap::default(),
        };
        analysis.build_summaries(input);
        analysis
    }

    pub fn summary(&self, def_id: LocalDefId) -> Option<&FunctionAccessSummary> {
        self.summaries.get(&def_id)
    }

    pub(crate) fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub(crate) fn flow(&self, def_id: LocalDefId) -> Option<&PointerFlowResult> {
        self.flows.get(&def_id)
    }

    fn build_summaries(&mut self, input: &RustProgram<'tcx>) {
        let functions: FxHashSet<_> = input.functions.iter().copied().collect();
        for scc in CallGraphPostOrder::new(input).sccs() {
            let local_scc: Vec<_> = scc
                .iter()
                .filter_map(|def_id| def_id.as_local())
                .filter(|def_id| functions.contains(def_id))
                .collect();
            if local_scc.is_empty() {
                continue;
            }

            let recursive = local_scc.len() > 1
                || local_scc.first().is_some_and(|def_id| {
                    let body = self
                        .tcx
                        .mir_drops_elaborated_and_const_checked(*def_id)
                        .borrow();
                    body_calls(&body, def_id.to_def_id())
                });
            let recursive_callees: FxHashSet<_> = if recursive {
                local_scc.iter().copied().collect()
            } else {
                FxHashSet::default()
            };

            for def_id in local_scc {
                let body = self
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let Some(flow) = self.flows.get(&def_id) else {
                    self.summaries.insert(
                        def_id,
                        FunctionAccessSummary {
                            effect: invalidation_effect(
                                ParamScope::All,
                                AccessUnknownReason::IncompleteCallee,
                                Location {
                                    block: rustc_middle::mir::START_BLOCK,
                                    statement_index: 0,
                                },
                                vec![],
                            ),
                        },
                    );
                    continue;
                };
                let mut effects = extract_body_effects(self.tcx, def_id, &body, flow);
                for (location, location_effect) in &mut effects {
                    let LocationEffect::Call(call) = location_effect else {
                        continue;
                    };
                    let effect =
                        self.call_effect(def_id, &body, flow, *location, call, &recursive_callees);
                    *location_effect = LocationEffect::Effect(effect);
                }
                let atomic_loops = build_body_loop_effects(
                    self.tcx,
                    def_id,
                    &body,
                    flow,
                    &self.summaries,
                    &recursive_callees,
                );
                let summary = solve_body(&body, &effects, &atomic_loops);
                self.summaries.insert(def_id, summary);
            }
        }
    }

    fn call_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        location: Location,
        call: &CallSite<'tcx>,
        recursive_callees: &FxHashSet<LocalDefId>,
    ) -> AccessEffect {
        let Some(callee) = direct_callee(&call.func) else {
            return self.unknown_call_effect(
                caller,
                body,
                flow,
                &call.args,
                AccessUnknownReason::IndirectCall,
                location,
            );
        };
        let path = self.tcx.def_path_str(callee);

        if is_pointer_arithmetic(self.tcx, callee, &path) {
            return AccessEffect::empty();
        }
        if let Some(effect) =
            self.core_ptr_builtin_effect(caller, body, flow, callee, &path, &call.args, location)
        {
            return effect;
        }
        if self.tcx.is_foreign_item(callee) {
            if let Some(effect) =
                self.foreign_builtin_effect(caller, body, flow, callee, &call.args, location)
            {
                return effect;
            }
            return self.unknown_call_effect(
                caller,
                body,
                flow,
                &call.args,
                AccessUnknownReason::ForeignCall,
                location,
            );
        }

        if let Some(local_callee) = callee.as_local() {
            let frame = CallFrame {
                caller,
                callee: local_callee,
                location,
            };
            if recursive_callees.contains(&local_callee) {
                return match self.reachable_scope(
                    caller,
                    body,
                    flow,
                    call.args.iter().map(|arg| &arg.node),
                ) {
                    ReachableScope::Known(scope) => invalidation_effect(
                        ParamScope::Known(scope),
                        AccessUnknownReason::RecursiveCall,
                        location,
                        vec![frame],
                    ),
                    ReachableScope::Unbounded => invalidation_effect(
                        ParamScope::All,
                        AccessUnknownReason::RecursiveCall,
                        location,
                        vec![frame],
                    ),
                    ReachableScope::Disjoint => AccessEffect::empty(),
                };
            }
            if let Some(summary) = self.summaries.get(&local_callee) {
                return self.substitute_effect(
                    caller,
                    local_callee,
                    body,
                    flow,
                    &call.args,
                    location,
                    &summary.effect,
                );
            }
            return self.unknown_call_effect(
                caller,
                body,
                flow,
                &call.args,
                AccessUnknownReason::IncompleteCallee,
                location,
            );
        }

        self.unknown_call_effect(
            caller,
            body,
            flow,
            &call.args,
            AccessUnknownReason::UnsupportedCall,
            location,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn core_ptr_builtin_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        callee: DefId,
        path: &str,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        location: Location,
    ) -> Option<AccessEffect> {
        let crate_name = self.tcx.crate_name(callee.krate);
        if !matches!(crate_name.as_str(), "core" | "std") {
            return None;
        }
        let name = path
            .strip_prefix("core::ptr::")
            .or_else(|| path.strip_prefix("std::ptr::"))?;
        if name.contains("::") {
            return None;
        }

        let effect = match name {
            "read" | "read_unaligned" | "read_volatile" => {
                let Some([pointer]) = exact_args::<1>(args) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                let Some(pointee) = raw_pointer_pointee(pointer.ty(body, self.tcx)) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                self.typed_access_effect(
                    caller,
                    body,
                    flow,
                    pointer,
                    pointee,
                    AccessKind::Read,
                    location,
                )
            }
            "write" | "write_unaligned" | "write_volatile" => {
                let Some([pointer, _value]) = exact_args::<2>(args) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                let Some(pointee) = mutable_raw_pointer_pointee(pointer.ty(body, self.tcx)) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                self.typed_access_effect(
                    caller,
                    body,
                    flow,
                    pointer,
                    pointee,
                    AccessKind::Write,
                    location,
                )
            }
            "copy" | "copy_nonoverlapping" => {
                let Some([source, destination, count]) = exact_args::<3>(args) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                let Some(source_ty) = raw_pointer_pointee(source.ty(body, self.tcx)) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                let Some(destination_ty) =
                    mutable_raw_pointer_pointee(destination.ty(body, self.tcx))
                else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                if source_ty != destination_ty {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                }
                self.copy_effect(
                    caller,
                    body,
                    flow,
                    source,
                    destination,
                    count,
                    source_ty,
                    location,
                )
            }
            "write_bytes" => {
                let Some([destination, _value, count]) = exact_args::<3>(args) else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                let Some(pointee) = mutable_raw_pointer_pointee(destination.ty(body, self.tcx))
                else {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                };
                self.repeated_access_effect(
                    caller,
                    body,
                    flow,
                    destination,
                    count,
                    pointee,
                    AccessKind::Write,
                    location,
                )
            }
            _ => return None,
        };
        Some(effect)
    }

    fn foreign_builtin_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        callee: DefId,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        location: Location,
    ) -> Option<AccessEffect> {
        let name = self
            .tcx
            .codegen_fn_attrs(callee)
            .link_name
            .unwrap_or_else(|| self.tcx.item_name(callee));
        let signature = self.tcx.fn_sig(callee).instantiate_identity().skip_binder();
        if !matches!(signature.abi, rustc_abi::ExternAbi::C { .. })
            || signature.c_variadic
            || signature.inputs().len() != 3
        {
            return None;
        }
        let inputs = signature.inputs();
        let signature_is_supported = match name.as_str() {
            "memcpy" | "memmove" => {
                mutable_thin_raw_pointer_pointee(self.tcx, inputs[0]).is_some()
                    && thin_raw_pointer_pointee(self.tcx, inputs[1]).is_some()
                    && inputs[2] == self.tcx.types.usize
                    && mutable_thin_raw_pointer_pointee(self.tcx, signature.output()).is_some()
            }
            "memset" => {
                mutable_thin_raw_pointer_pointee(self.tcx, inputs[0]).is_some()
                    && inputs[1] == self.tcx.types.i32
                    && inputs[2] == self.tcx.types.usize
                    && mutable_thin_raw_pointer_pointee(self.tcx, signature.output()).is_some()
            }
            "memcmp" => {
                thin_raw_pointer_pointee(self.tcx, inputs[0]).is_some()
                    && thin_raw_pointer_pointee(self.tcx, inputs[1]).is_some()
                    && inputs[2] == self.tcx.types.usize
                    && signature.output() == self.tcx.types.i32
            }
            _ => return None,
        };
        if !signature_is_supported {
            return None;
        }

        let effect = match name.as_str() {
            "memcpy" | "memmove" => {
                let [destination, source, count] = exact_args::<3>(args)?;
                self.byte_copy_effect(caller, body, flow, source, destination, count, location)
            }
            "memset" => {
                let [destination, _value, count] = exact_args::<3>(args)?;
                self.byte_access_effect(
                    caller,
                    body,
                    flow,
                    destination,
                    count,
                    AccessKind::Write,
                    location,
                )
            }
            "memcmp" => {
                let [left, right, count] = exact_args::<3>(args)?;
                let Some(width) = constant_usize(count, self.tcx) else {
                    return Some(self.unknown_width_effect(
                        caller,
                        body,
                        flow,
                        [left, right],
                        location,
                    ));
                };
                if raw_pointer_pointee(left.ty(body, self.tcx)).is_none()
                    || raw_pointer_pointee(right.ty(body, self.tcx)).is_none()
                {
                    return Some(
                        self.invalid_builtin_signature(caller, body, flow, args, location),
                    );
                }
                self.pointer_access_effect(
                    caller,
                    body,
                    flow,
                    left,
                    width,
                    AccessKind::Read,
                    location,
                )
                .then(self.pointer_access_effect(
                    caller,
                    body,
                    flow,
                    right,
                    width,
                    AccessKind::Read,
                    location,
                ))
            }
            _ => unreachable!(),
        };
        Some(effect)
    }

    #[allow(clippy::too_many_arguments)]
    fn copy_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        source: &Operand<'tcx>,
        destination: &Operand<'tcx>,
        count: &Operand<'tcx>,
        element_ty: Ty<'tcx>,
        location: Location,
    ) -> AccessEffect {
        let Some(element_size) = self.type_size(caller, element_ty) else {
            return self.unknown_width_effect(caller, body, flow, [source, destination], location);
        };
        let Some(count) = constant_usize(count, self.tcx) else {
            return self.unknown_width_effect(caller, body, flow, [source, destination], location);
        };
        let Some(width) = element_size.checked_mul(count) else {
            return self.unknown_width_effect(caller, body, flow, [source, destination], location);
        };

        self.pointer_access_effect(
            caller,
            body,
            flow,
            source,
            width,
            AccessKind::Read,
            location,
        )
        .then(self.pointer_access_effect(
            caller,
            body,
            flow,
            destination,
            width,
            AccessKind::Write,
            location,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn byte_copy_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        source: &Operand<'tcx>,
        destination: &Operand<'tcx>,
        count: &Operand<'tcx>,
        location: Location,
    ) -> AccessEffect {
        let Some(width) = constant_usize(count, self.tcx) else {
            return self.unknown_width_effect(caller, body, flow, [source, destination], location);
        };
        if raw_pointer_pointee(source.ty(body, self.tcx)).is_none()
            || mutable_raw_pointer_pointee(destination.ty(body, self.tcx)).is_none()
        {
            return self.invalid_builtin_signature(caller, body, flow, &[], location);
        }

        self.pointer_access_effect(
            caller,
            body,
            flow,
            source,
            width,
            AccessKind::Read,
            location,
        )
        .then(self.pointer_access_effect(
            caller,
            body,
            flow,
            destination,
            width,
            AccessKind::Write,
            location,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn repeated_access_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        pointer: &Operand<'tcx>,
        count: &Operand<'tcx>,
        element_ty: Ty<'tcx>,
        kind: AccessKind,
        location: Location,
    ) -> AccessEffect {
        let Some(element_size) = self.type_size(caller, element_ty) else {
            return self.unknown_width_effect(caller, body, flow, [pointer], location);
        };
        let Some(count) = constant_usize(count, self.tcx) else {
            return self.unknown_width_effect(caller, body, flow, [pointer], location);
        };
        let Some(width) = element_size.checked_mul(count) else {
            return self.unknown_width_effect(caller, body, flow, [pointer], location);
        };
        self.pointer_access_effect(caller, body, flow, pointer, width, kind, location)
    }

    #[allow(clippy::too_many_arguments)]
    fn byte_access_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        pointer: &Operand<'tcx>,
        count: &Operand<'tcx>,
        kind: AccessKind,
        location: Location,
    ) -> AccessEffect {
        let Some(width) = constant_usize(count, self.tcx) else {
            return self.unknown_width_effect(caller, body, flow, [pointer], location);
        };
        if raw_pointer_pointee(pointer.ty(body, self.tcx)).is_none() {
            return self.invalid_builtin_signature(caller, body, flow, &[], location);
        }
        self.pointer_access_effect(caller, body, flow, pointer, width, kind, location)
    }

    #[allow(clippy::too_many_arguments)]
    fn typed_access_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        pointer: &Operand<'tcx>,
        pointee: Ty<'tcx>,
        kind: AccessKind,
        location: Location,
    ) -> AccessEffect {
        let Some(width) = self.type_size(caller, pointee) else {
            return self.unknown_width_effect(caller, body, flow, [pointer], location);
        };
        self.pointer_access_effect(caller, body, flow, pointer, width, kind, location)
    }

    #[allow(clippy::too_many_arguments)]
    fn pointer_access_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        pointer: &Operand<'tcx>,
        width: u64,
        kind: AccessKind,
        location: Location,
    ) -> AccessEffect {
        let origins = resolve_pointer_operand(self.tcx, caller, body, flow, pointer);
        effect_for_resolved_origins(origins, width, kind, location)
    }

    fn unknown_width_effect<'op>(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        pointers: impl IntoIterator<Item = &'op Operand<'tcx>>,
        location: Location,
    ) -> AccessEffect
    where
        'tcx: 'op,
    {
        match self.head_pointer_scope(caller, body, flow, pointers) {
            ReachableScope::Known(scope) => invalidation_effect(
                ParamScope::Known(scope),
                AccessUnknownReason::UnknownWidth,
                location,
                vec![],
            ),
            ReachableScope::Unbounded => invalidation_effect(
                ParamScope::All,
                AccessUnknownReason::UnknownWidth,
                location,
                vec![],
            ),
            ReachableScope::Disjoint => AccessEffect::empty(),
        }
    }

    fn invalid_builtin_signature(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        location: Location,
    ) -> AccessEffect {
        match self.reachable_scope(caller, body, flow, args.iter().map(|arg| &arg.node)) {
            ReachableScope::Known(scope) => invalidation_effect(
                ParamScope::Known(scope),
                AccessUnknownReason::UnsupportedCall,
                location,
                vec![],
            ),
            ReachableScope::Unbounded | ReachableScope::Disjoint => invalidation_effect(
                ParamScope::All,
                AccessUnknownReason::UnsupportedCall,
                location,
                vec![],
            ),
        }
    }

    fn unknown_call_effect(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        reason: AccessUnknownReason,
        location: Location,
    ) -> AccessEffect {
        match self.reachable_scope(caller, body, flow, args.iter().map(|arg| &arg.node)) {
            ReachableScope::Known(scope) => {
                invalidation_effect(ParamScope::Known(scope), reason, location, vec![])
            }
            ReachableScope::Unbounded | ReachableScope::Disjoint => {
                invalidation_effect(ParamScope::All, reason, location, vec![])
            }
        }
    }

    fn reachable_scope<'op>(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        operands: impl IntoIterator<Item = &'op Operand<'tcx>>,
    ) -> ReachableScope
    where
        'tcx: 'op,
    {
        let mut scope = FxHashSet::default();
        let mut unresolved = false;
        for operand in operands {
            let origins = resolve_call_operand(self.tcx, caller, body, flow, operand);
            scope.extend(origins.addresses.into_iter().map(|address| address.origin));
            unresolved |= origins.unresolved;
        }
        if unresolved {
            ReachableScope::Unbounded
        } else if scope.is_empty() {
            ReachableScope::Disjoint
        } else {
            ReachableScope::Known(scope)
        }
    }

    fn head_pointer_scope<'op>(
        &self,
        caller: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        operands: impl IntoIterator<Item = &'op Operand<'tcx>>,
    ) -> ReachableScope
    where
        'tcx: 'op,
    {
        let mut scope = FxHashSet::default();
        let mut unresolved = false;
        for operand in operands {
            let origins = resolve_pointer_operand(self.tcx, caller, body, flow, operand);
            scope.extend(origins.addresses.into_iter().map(|address| address.origin));
            unresolved |= origins.unresolved;
        }
        if unresolved {
            ReachableScope::Unbounded
        } else if scope.is_empty() {
            ReachableScope::Disjoint
        } else {
            ReachableScope::Known(scope)
        }
    }

    fn type_size(&self, owner: LocalDefId, ty: Ty<'tcx>) -> Option<u64> {
        self.tcx
            .layout_of(ty::TypingEnv::post_analysis(self.tcx, owner).as_query_input(ty))
            .ok()
            .map(|layout| layout.size.bytes())
    }

    #[allow(clippy::too_many_arguments)]
    fn substitute_effect(
        &self,
        caller: LocalDefId,
        callee: LocalDefId,
        body: &Body<'tcx>,
        flow: &PointerFlowResult,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        location: Location,
        callee_effect: &AccessEffect,
    ) -> AccessEffect {
        let frame = CallFrame {
            caller,
            callee,
            location,
        };
        let mut substitutions: FxHashMap<ParamIdx, ResolvedPointerOrigins> = FxHashMap::default();
        let mut resolve = |formal: ParamIdx| {
            substitutions
                .entry(formal)
                .or_insert_with(|| {
                    args.get(formal).map_or_else(
                        || ResolvedPointerOrigins {
                            unresolved: true,
                            ..ResolvedPointerOrigins::default()
                        },
                        |arg| resolve_call_operand(self.tcx, caller, body, flow, &arg.node),
                    )
                })
                .clone()
        };

        let mut result = AccessEffect {
            contains_repetition: callee_effect.contains_repetition,
            ..AccessEffect::empty()
        };
        for read in &callee_effect.reads {
            let (reads, invalidations) =
                substitute_footprint(read, resolve(read.address.origin), frame, location);
            result.reads.extend(reads);
            result.invalidations.extend(invalidations);
        }
        for write in &callee_effect.writes {
            let (writes, invalidations) =
                substitute_footprint(write, resolve(write.address.origin), frame, location);
            result.writes.extend(writes);
            result.invalidations.extend(invalidations);
        }
        for hazard in &callee_effect.hazards {
            let (writes, write_invalidations) = substitute_footprint(
                &hazard.write,
                resolve(hazard.write.address.origin),
                frame,
                location,
            );
            let (reads, read_invalidations) = substitute_footprint(
                &hazard.read,
                resolve(hazard.read.address.origin),
                frame,
                location,
            );
            result.invalidations.extend(write_invalidations);
            result.invalidations.extend(read_invalidations);
            result.hazards.extend(writes.iter().flat_map(|write| {
                reads.iter().map(|read| PotentialHazard {
                    write: write.clone(),
                    read: read.clone(),
                    order: hazard.order,
                })
            }));
        }
        for invalidation in &callee_effect.invalidations {
            let scope = match &invalidation.scope {
                ParamScope::All => Some(ParamScope::All),
                ParamScope::Known(formals) => {
                    let mut caller_scope = FxHashSet::default();
                    let mut unresolved = false;
                    for formal in formals {
                        let origins = resolve(*formal);
                        caller_scope
                            .extend(origins.addresses.into_iter().map(|address| address.origin));
                        unresolved |= origins.unresolved;
                    }
                    if unresolved {
                        Some(ParamScope::All)
                    } else if caller_scope.is_empty() {
                        None
                    } else {
                        Some(ParamScope::Known(caller_scope))
                    }
                }
            };
            if let Some(scope) = scope {
                let mut call_chain = invalidation.call_chain.clone();
                call_chain.insert(0, frame);
                result.invalidations.push(Invalidation {
                    scope,
                    reason: invalidation.reason,
                    location: invalidation.location,
                    call_chain,
                });
            }
        }
        result.normalize();
        result
    }
}

enum ReachableScope {
    Known(FxHashSet<ParamIdx>),
    Disjoint,
    Unbounded,
}

fn body_calls(body: &Body<'_>, target: DefId) -> bool {
    body.basic_blocks.iter().any(|block| {
        let func = match &block.terminator().kind {
            rustc_middle::mir::TerminatorKind::Call { func, .. }
            | rustc_middle::mir::TerminatorKind::TailCall { func, .. } => func,
            _ => return false,
        };
        direct_callee(func) == Some(target)
    })
}

fn direct_callee(func: &Operand<'_>) -> Option<DefId> {
    let constant = func.constant()?;
    let ty::TyKind::FnDef(def_id, _) = constant.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CompleteBuiltinAccess {
    pub(crate) arg_index: usize,
    pub(crate) kind: AccessKind,
    pub(crate) width: u64,
}

pub(crate) fn complete_builtin_accesses<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &Body<'tcx>,
    callee: DefId,
    path: &str,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
) -> Option<Vec<CompleteBuiltinAccess>> {
    let type_size = |ty| {
        tcx.layout_of(ty::TypingEnv::post_analysis(tcx, owner).as_query_input(ty))
            .ok()
            .map(|layout| layout.size.bytes())
    };
    let repeated_width = |pointer: &Operand<'tcx>, count: &Operand<'tcx>| {
        let pointee = raw_pointer_pointee(pointer.ty(body, tcx))?;
        type_size(pointee)?.checked_mul(constant_usize(count, tcx)?)
    };

    let crate_name = tcx.crate_name(callee.krate);
    if matches!(crate_name.as_str(), "core" | "std")
        && let Some(name) = path
            .strip_prefix("core::ptr::")
            .or_else(|| path.strip_prefix("std::ptr::"))
        && !name.contains("::")
    {
        return match name {
            "read" | "read_unaligned" | "read_volatile" => {
                let [pointer] = exact_args::<1>(args)?;
                let pointee = raw_pointer_pointee(pointer.ty(body, tcx))?;
                Some(vec![CompleteBuiltinAccess {
                    arg_index: 0,
                    kind: AccessKind::Read,
                    width: type_size(pointee)?,
                }])
            }
            "write" | "write_unaligned" | "write_volatile" => {
                let [pointer, _value] = exact_args::<2>(args)?;
                let pointee = mutable_raw_pointer_pointee(pointer.ty(body, tcx))?;
                Some(vec![CompleteBuiltinAccess {
                    arg_index: 0,
                    kind: AccessKind::Write,
                    width: type_size(pointee)?,
                }])
            }
            "copy" | "copy_nonoverlapping" => {
                let [source, destination, count] = exact_args::<3>(args)?;
                let source_ty = raw_pointer_pointee(source.ty(body, tcx))?;
                let destination_ty = mutable_raw_pointer_pointee(destination.ty(body, tcx))?;
                if source_ty != destination_ty {
                    return None;
                }
                let width = repeated_width(source, count)?;
                Some(vec![
                    CompleteBuiltinAccess {
                        arg_index: 0,
                        kind: AccessKind::Read,
                        width,
                    },
                    CompleteBuiltinAccess {
                        arg_index: 1,
                        kind: AccessKind::Write,
                        width,
                    },
                ])
            }
            "write_bytes" => {
                let [destination, _value, count] = exact_args::<3>(args)?;
                mutable_raw_pointer_pointee(destination.ty(body, tcx))?;
                Some(vec![CompleteBuiltinAccess {
                    arg_index: 0,
                    kind: AccessKind::Write,
                    width: repeated_width(destination, count)?,
                }])
            }
            _ => None,
        };
    }

    if !tcx.is_foreign_item(callee) {
        return None;
    }
    let name = tcx
        .codegen_fn_attrs(callee)
        .link_name
        .unwrap_or_else(|| tcx.item_name(callee));
    let signature = tcx.fn_sig(callee).instantiate_identity().skip_binder();
    if !matches!(signature.abi, rustc_abi::ExternAbi::C { .. })
        || signature.c_variadic
        || signature.inputs().len() != 3
    {
        return None;
    }
    let inputs = signature.inputs();
    let [_, _, count] = exact_args::<3>(args)?;
    let width = constant_usize(count, tcx)?;
    match name.as_str() {
        "memcpy" | "memmove"
            if mutable_thin_raw_pointer_pointee(tcx, inputs[0]).is_some()
                && thin_raw_pointer_pointee(tcx, inputs[1]).is_some()
                && inputs[2] == tcx.types.usize
                && mutable_thin_raw_pointer_pointee(tcx, signature.output()).is_some() =>
        {
            Some(vec![
                CompleteBuiltinAccess {
                    arg_index: 1,
                    kind: AccessKind::Read,
                    width,
                },
                CompleteBuiltinAccess {
                    arg_index: 0,
                    kind: AccessKind::Write,
                    width,
                },
            ])
        }
        "memset"
            if mutable_thin_raw_pointer_pointee(tcx, inputs[0]).is_some()
                && inputs[1] == tcx.types.i32
                && inputs[2] == tcx.types.usize
                && mutable_thin_raw_pointer_pointee(tcx, signature.output()).is_some() =>
        {
            Some(vec![CompleteBuiltinAccess {
                arg_index: 0,
                kind: AccessKind::Write,
                width,
            }])
        }
        "memcmp"
            if thin_raw_pointer_pointee(tcx, inputs[0]).is_some()
                && thin_raw_pointer_pointee(tcx, inputs[1]).is_some()
                && inputs[2] == tcx.types.usize
                && signature.output() == tcx.types.i32 =>
        {
            Some(vec![
                CompleteBuiltinAccess {
                    arg_index: 0,
                    kind: AccessKind::Read,
                    width,
                },
                CompleteBuiltinAccess {
                    arg_index: 1,
                    kind: AccessKind::Read,
                    width,
                },
            ])
        }
        _ => None,
    }
}

fn exact_args<'a, 'tcx, const N: usize>(
    args: &'a [rustc_span::source_map::Spanned<Operand<'tcx>>],
) -> Option<[&'a Operand<'tcx>; N]> {
    let args: [&Operand<'tcx>; N] = args
        .iter()
        .map(|arg| &arg.node)
        .collect::<Vec<_>>()
        .try_into()
        .ok()?;
    Some(args)
}

fn mutable_raw_pointer_pointee<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::TyKind::RawPtr(pointee, mutability) = ty.kind() else {
        return None;
    };
    mutability.is_mut().then_some(*pointee)
}

fn thin_raw_pointer_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let pointee = raw_pointer_pointee(ty)?;
    if incomplete_foreign_pointer_type(pointee) {
        return None;
    }
    // This rustc can report unsafe-binder DST pointers as thin, so reject them before layout.
    let mut remaining_work = FOREIGN_POINTER_TYPE_WORK_LIMIT;
    if contains_unsafe_binder(
        tcx,
        pointee,
        &mut FxHashSet::default(),
        FOREIGN_POINTER_TYPE_RECURSION_LIMIT,
        &mut remaining_work,
    ) != Some(false)
    {
        return None;
    }
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    (layout.size == tcx.data_layout.pointer_size
        && matches!(
            layout.backend_repr,
            rustc_abi::BackendRepr::Scalar(scalar)
                if matches!(
                    scalar.primitive(),
                    rustc_abi::Primitive::Pointer(address_space)
                        if address_space == rustc_abi::AddressSpace::DATA
                )
        ))
    .then_some(pointee)
}

fn incomplete_foreign_pointer_type(ty: Ty<'_>) -> bool {
    let incomplete = ty::TypeFlags::HAS_PARAM
        | ty::TypeFlags::HAS_INFER
        | ty::TypeFlags::HAS_PLACEHOLDER
        | ty::TypeFlags::HAS_ALIAS
        | ty::TypeFlags::HAS_ERROR
        | ty::TypeFlags::HAS_BOUND_VARS;
    ty.has_type_flags(incomplete)
        || matches!(ty.kind(), ty::TyKind::UnsafeBinder(_) | ty::TyKind::Pat(..))
}

const FOREIGN_POINTER_TYPE_RECURSION_LIMIT: usize = 64;
// Bound the total reachable types and fields inspected for one foreign pointer signature.
const FOREIGN_POINTER_TYPE_WORK_LIMIT: usize = 64;

fn contains_unsafe_binder<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    seen_adts: &mut FxHashSet<DefId>,
    remaining_depth: usize,
    remaining_work: &mut usize,
) -> Option<bool> {
    if remaining_depth == 0 {
        return None;
    }
    let next_depth = remaining_depth - 1;

    for nested in ty.walk().filter_map(|arg| arg.as_type()) {
        consume_foreign_pointer_work(remaining_work)?;
        if matches!(nested.kind(), ty::TyKind::UnsafeBinder(_)) {
            return Some(true);
        }
        if incomplete_foreign_pointer_type(nested) {
            return None;
        }
        let ty::TyKind::Adt(adt_def, args) = nested.kind() else {
            continue;
        };
        let def_id = adt_def.did();
        if !seen_adts.insert(def_id) {
            return None;
        }
        let result = (|| {
            for field in adt_def.all_fields() {
                consume_foreign_pointer_work(remaining_work)?;
                if contains_unsafe_binder(
                    tcx,
                    field.ty(tcx, args),
                    seen_adts,
                    next_depth,
                    remaining_work,
                )? {
                    return Some(true);
                }
            }
            Some(false)
        })();
        seen_adts.remove(&def_id);
        if result? {
            return Some(true);
        }
    }
    Some(false)
}

fn consume_foreign_pointer_work(remaining_work: &mut usize) -> Option<()> {
    *remaining_work = (*remaining_work).checked_sub(1)?;
    Some(())
}

fn mutable_thin_raw_pointer_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::TyKind::RawPtr(_, mutability) = ty.kind() else {
        return None;
    };
    if !mutability.is_mut() {
        return None;
    }
    thin_raw_pointer_pointee(tcx, ty)
}

fn substitute_footprint(
    footprint: &AccessFootprint,
    origins: ResolvedPointerOrigins,
    frame: CallFrame,
    call_location: Location,
) -> (Vec<AccessFootprint>, Vec<Invalidation>) {
    let mut footprints = vec![];
    let mut invalidations = vec![];
    let mut unknown_offset = origins.unknown_offset;
    let caller_scope: FxHashSet<_> = origins
        .addresses
        .iter()
        .map(|address| address.origin)
        .collect();
    let mut invalidation_call_chain = footprint.call_chain.clone();
    invalidation_call_chain.insert(0, frame);
    for address in origins.addresses {
        let offset = compose_offsets(address.offset, footprint.address.offset.clone());
        unknown_offset |= matches!(offset, OffsetExpr::Unknown);
        let mut call_chain = footprint.call_chain.clone();
        call_chain.insert(0, frame);
        footprints.push(AccessFootprint {
            address: super::SymbolicAddress {
                origin: address.origin,
                offset,
            },
            width: footprint.width,
            location: footprint.location,
            call_chain,
        });
    }
    if unknown_offset && !caller_scope.is_empty() {
        invalidations.push(Invalidation {
            scope: ParamScope::Known(caller_scope),
            reason: AccessUnknownReason::UnknownOffset,
            location: call_location,
            call_chain: invalidation_call_chain.clone(),
        });
    }
    if origins.unresolved {
        invalidations.push(Invalidation {
            scope: ParamScope::All,
            reason: AccessUnknownReason::UnresolvedOrigin,
            location: call_location,
            call_chain: invalidation_call_chain,
        });
    }
    (footprints, invalidations)
}

fn compose_offsets(caller: OffsetExpr, callee: OffsetExpr) -> OffsetExpr {
    match (caller, callee) {
        (OffsetExpr::Const(caller), OffsetExpr::Const(callee)) => caller
            .checked_add(callee)
            .map_or(OffsetExpr::Unknown, OffsetExpr::Const),
        (
            OffsetExpr::Const(caller),
            OffsetExpr::LoopAffine {
                loop_id,
                stride_bytes,
                constant_bytes,
            },
        ) => caller
            .checked_add(constant_bytes)
            .map_or(OffsetExpr::Unknown, |constant_bytes| {
                OffsetExpr::LoopAffine {
                    loop_id,
                    stride_bytes,
                    constant_bytes,
                }
            }),
        _ => OffsetExpr::Unknown,
    }
}

fn invalidation_effect(
    scope: ParamScope,
    reason: AccessUnknownReason,
    location: Location,
    call_chain: Vec<CallFrame>,
) -> AccessEffect {
    AccessEffect {
        invalidations: vec![Invalidation {
            scope,
            reason,
            location,
            call_chain,
        }],
        ..AccessEffect::empty()
    }
}
