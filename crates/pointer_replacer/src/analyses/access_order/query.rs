use std::cmp::Ordering;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{Body, Location, Operand, TerminatorKind},
    ty,
};
use z3::{SatResult, Solver, ast::Int};

use super::{
    AccessEffect, AccessFootprint, AccessOrderAnalysis, AccessOrderVerdict, AccessUnknownReason,
    CallFrame, HazardOrder, HazardWitness, Invalidation, OffsetExpr, ParamIdx, ParamScope,
    SubstitutedAddress, WidthExpr, WriteVerdict, WriteWitness, extractor::resolve_call_operand,
};
use crate::analyses::pointer_flow::graph::{BaseId, Offset, PfgNode, UnknownReason};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ActualAddress {
    pub base: BaseId,
    pub offset: Offset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum QueryError {
    MissingCallerFlow {
        caller: LocalDefId,
    },
    InvalidLocation {
        caller: LocalDefId,
        location: Location,
    },
    NotCall {
        caller: LocalDefId,
        location: Location,
    },
    IndirectCall {
        caller: LocalDefId,
        location: Location,
    },
    NonLocalCallee {
        caller: LocalDefId,
        location: Location,
        callee: DefId,
    },
    MissingCalleeSummary {
        callee: LocalDefId,
    },
}

pub struct CallSiteAccess<'a> {
    #[allow(dead_code)]
    pub caller: LocalDefId,
    #[allow(dead_code)]
    pub callee: LocalDefId,
    pub location: Location,
    effect: &'a AccessEffect,
    actual_args: FxHashMap<ParamIdx, Vec<ActualAddress>>,
    unresolved_actual_bases: FxHashMap<ParamIdx, BaseId>,
    substitution_invalidations: Vec<Invalidation>,
}

impl AccessOrderAnalysis<'_, '_> {
    pub fn at_call(
        &self,
        caller: LocalDefId,
        location: Location,
    ) -> Result<CallSiteAccess<'_>, QueryError> {
        let Some(flow) = self.flow(caller) else {
            return Err(QueryError::MissingCallerFlow { caller });
        };
        let tcx = self.tcx();
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let Some(block) = body.basic_blocks.get(location.block) else {
            return Err(QueryError::InvalidLocation { caller, location });
        };
        if location.statement_index > block.statements.len() {
            return Err(QueryError::InvalidLocation { caller, location });
        }
        if location.statement_index != block.statements.len() {
            return Err(QueryError::NotCall { caller, location });
        }
        let (func, args) = match &block.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => return Err(QueryError::NotCall { caller, location }),
        };
        let Some(callee) = direct_callee(func) else {
            return Err(QueryError::IndirectCall { caller, location });
        };
        let Some(callee) = callee.as_local() else {
            return Err(QueryError::NonLocalCallee {
                caller,
                location,
                callee,
            });
        };
        let Some(summary) = self.summary(callee) else {
            return Err(QueryError::MissingCalleeSummary { callee });
        };
        let frame = CallFrame {
            caller,
            callee,
            location,
        };
        let mut actual_args = FxHashMap::default();
        let mut unresolved_actual_bases = FxHashMap::default();
        let mut substitution_invalidations = vec![];

        for (formal, arg) in args.iter().enumerate() {
            let resolved = resolve_call_operand(tcx, caller, &body, flow, &arg.node);
            let mut addresses = actual_addresses(&body, tcx, flow, &arg.node);
            addresses.sort_by(compare_actual_address);
            addresses.dedup();

            if addresses.is_empty() {
                let reason = if arg.node.place().is_none() {
                    UnknownReason::ConstantPointer
                } else {
                    UnknownReason::UnsupportedProjection
                };
                unresolved_actual_bases.insert(formal, BaseId::Unknown { location, reason });
            }

            if resolved.unresolved {
                push_substitution_invalidation(
                    &mut substitution_invalidations,
                    formal,
                    AccessUnknownReason::UnresolvedOrigin,
                    location,
                    frame,
                );
            }
            actual_args.insert(formal, addresses);
        }

        Ok(CallSiteAccess {
            caller,
            callee,
            location,
            effect: &summary.effect,
            actual_args,
            unresolved_actual_bases,
            substitution_invalidations,
        })
    }
}

impl CallSiteAccess<'_> {
    pub fn reads_precede_writes(
        &self,
        writers: &[ParamIdx],
        readers: &[ParamIdx],
    ) -> AccessOrderVerdict {
        let mut reasons =
            self.relevant_reasons(&writers.iter().chain(readers).copied().collect::<Vec<_>>());
        let mut witness = None;

        for hazard in &self.effect.hazards {
            if !writers.contains(&hazard.write.address.origin)
                || !readers.contains(&hazard.read.address.origin)
            {
                continue;
            }
            let Some(write_actuals) = self.actual_args.get(&hazard.write.address.origin) else {
                push_reason(&mut reasons, AccessUnknownReason::UnresolvedOrigin);
                continue;
            };
            let Some(read_actuals) = self.actual_args.get(&hazard.read.address.origin) else {
                push_reason(&mut reasons, AccessUnknownReason::UnresolvedOrigin);
                continue;
            };
            if write_actuals.is_empty() || read_actuals.is_empty() {
                push_reason(&mut reasons, AccessUnknownReason::UnresolvedOrigin);
                continue;
            }
            for write_actual in write_actuals {
                for read_actual in read_actuals {
                    if write_actual.base != read_actual.base {
                        continue;
                    }
                    let (WidthExpr::Const(write_width), WidthExpr::Const(read_width)) =
                        (hazard.write.width, hazard.read.width)
                    else {
                        let reason = if hazard.write.width == WidthExpr::Unknown
                            || hazard.read.width == WidthExpr::Unknown
                        {
                            AccessUnknownReason::UnknownWidth
                        } else {
                            AccessUnknownReason::UnresolvedSymbolicWidth
                        };
                        push_reason(&mut reasons, reason);
                        continue;
                    };
                    let write_offset =
                        match compose_offset(write_actual.offset, &hazard.write.address.offset) {
                            Ok(offset) => offset,
                            Err(reason) => {
                                push_reason(&mut reasons, reason);
                                continue;
                            }
                        };
                    let read_offset =
                        match compose_offset(read_actual.offset, &hazard.read.address.offset) {
                            Ok(offset) => offset,
                            Err(reason) => {
                                push_reason(&mut reasons, reason);
                                continue;
                            }
                        };

                    match overlap_feasibility(
                        &write_offset,
                        write_width,
                        &read_offset,
                        read_width,
                        hazard.order,
                    ) {
                        Feasibility::Feasible if witness.is_none() => {
                            witness = Some(HazardWitness {
                                write_location: hazard.write.location,
                                read_location: hazard.read.location,
                                write_address: SubstitutedAddress {
                                    base: write_actual.base.clone(),
                                    offset: write_offset,
                                },
                                read_address: SubstitutedAddress {
                                    base: read_actual.base.clone(),
                                    offset: read_offset,
                                },
                                write_call_chain: hazard.write.call_chain.clone(),
                                read_call_chain: hazard.read.call_chain.clone(),
                                order: hazard.order,
                            });
                        }
                        Feasibility::Unknown(reason) => push_reason(&mut reasons, reason),
                        Feasibility::Feasible | Feasibility::Infeasible => {}
                    }
                }
            }
        }

        if let Some(witness) = witness {
            AccessOrderVerdict::MayReadAfterWrite { witness }
        } else if reasons.is_empty() {
            AccessOrderVerdict::Proven
        } else {
            AccessOrderVerdict::Unknown { reasons }
        }
    }

    pub fn never_written(&self, params: &[ParamIdx]) -> WriteVerdict {
        for write in &self.effect.writes {
            if !params.contains(&write.address.origin) {
                continue;
            }

            let address = self
                .actual_args
                .get(&write.address.origin)
                .and_then(|actuals| actuals.first())
                .map(|actual| SubstitutedAddress {
                    base: actual.base.clone(),
                    offset: compose_offset(actual.offset, &write.address.offset)
                        .unwrap_or(OffsetExpr::Unknown),
                })
                .unwrap_or_else(|| SubstitutedAddress {
                    base: self
                        .unresolved_actual_bases
                        .get(&write.address.origin)
                        .cloned()
                        .unwrap_or(BaseId::Unknown {
                            location: self.location,
                            reason: UnknownReason::UnsupportedProjection,
                        }),
                    offset: OffsetExpr::Unknown,
                });
            return WriteVerdict::MayBeWritten {
                witness: write_witness(write, address),
            };
        }

        let reasons = self.relevant_reasons(params);
        if reasons.is_empty() {
            WriteVerdict::NeverWritten
        } else {
            WriteVerdict::Unknown { reasons }
        }
    }

    fn relevant_reasons(&self, params: &[ParamIdx]) -> Vec<AccessUnknownReason> {
        let mut reasons = vec![];
        for invalidation in self
            .effect
            .invalidations
            .iter()
            .chain(&self.substitution_invalidations)
        {
            if invalidation.scope.intersects(params) {
                push_reason(&mut reasons, invalidation.reason);
            }
        }
        reasons
    }
}

fn actual_addresses<'tcx>(
    body: &Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    flow: &crate::analyses::pointer_flow::PointerFlowResult,
    operand: &Operand<'tcx>,
) -> Vec<ActualAddress> {
    let Some(place) = operand.place() else {
        return vec![];
    };
    let Some(slots) = flow.slot_table.place_slots(place, body, tcx) else {
        return vec![];
    };
    let mut addresses = vec![];
    for slot in slots {
        let node = PfgNode::Slot(slot);
        let Some(bases) = flow.provenance.reachable_bases.get(&node) else {
            continue;
        };
        addresses.extend(bases.iter().cloned().map(|base| {
            ActualAddress {
                offset: flow
                    .provenance
                    .offset_from_base(&node, &base)
                    .unwrap_or(Offset::Unknown),
                base,
            }
        }));
    }
    addresses
}

fn push_substitution_invalidation(
    invalidations: &mut Vec<Invalidation>,
    formal: ParamIdx,
    reason: AccessUnknownReason,
    location: Location,
    frame: CallFrame,
) {
    let invalidation = Invalidation {
        scope: ParamScope::Known(FxHashSet::from_iter([formal])),
        reason,
        location,
        call_chain: vec![frame],
    };
    if !invalidations.contains(&invalidation) {
        invalidations.push(invalidation);
    }
}

fn direct_callee(func: &Operand<'_>) -> Option<DefId> {
    let constant = func.constant()?;
    let ty::TyKind::FnDef(def_id, _) = constant.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

fn compose_offset(actual: Offset, formal: &OffsetExpr) -> Result<OffsetExpr, AccessUnknownReason> {
    let Offset::Const(actual) = actual else {
        return Err(AccessUnknownReason::UnknownOffset);
    };
    match formal {
        OffsetExpr::Const(formal) => actual
            .checked_add(*formal)
            .map(OffsetExpr::Const)
            .ok_or(AccessUnknownReason::UnknownOffset),
        OffsetExpr::LoopAffine {
            loop_id,
            stride_bytes,
            constant_bytes,
        } => actual
            .checked_add(*constant_bytes)
            .map(|constant_bytes| OffsetExpr::LoopAffine {
                loop_id: *loop_id,
                stride_bytes: *stride_bytes,
                constant_bytes,
            })
            .ok_or(AccessUnknownReason::UnknownOffset),
        OffsetExpr::Unknown => Err(AccessUnknownReason::UnknownOffset),
    }
}

enum Feasibility {
    Feasible,
    Infeasible,
    Unknown(AccessUnknownReason),
}

fn overlap_feasibility(
    write_offset: &OffsetExpr,
    write_width: u64,
    read_offset: &OffsetExpr,
    read_width: u64,
    order: HazardOrder,
) -> Feasibility {
    let solver = Solver::new();
    let write_iteration = Int::new_const("access_order_write_iteration");
    let read_iteration = Int::new_const("access_order_read_iteration");
    let zero = Int::from_i64(0);

    match order {
        HazardOrder::Sequential => {
            if matches!(write_offset, OffsetExpr::LoopAffine { .. }) {
                solver.assert(write_iteration.ge(&zero));
            }
            if matches!(read_offset, OffsetExpr::LoopAffine { .. }) {
                solver.assert(read_iteration.ge(&zero));
            }
        }
        HazardOrder::SameIteration(loop_id) | HazardOrder::LaterIteration(loop_id) => {
            if !matches_order(write_offset, loop_id) || !matches_order(read_offset, loop_id) {
                return Feasibility::Unknown(AccessUnknownReason::IncompatibleHazardOrder);
            }
            solver.assert(write_iteration.ge(&zero));
            solver.assert(read_iteration.ge(&zero));
            match order {
                HazardOrder::SameIteration(_) => solver.assert(write_iteration.eq(&read_iteration)),
                HazardOrder::LaterIteration(_) => {
                    solver.assert(write_iteration.lt(&read_iteration))
                }
                HazardOrder::Sequential => unreachable!(),
            }
        }
    }

    let Some(write_start) = symbolic_start(write_offset, &write_iteration) else {
        return Feasibility::Unknown(AccessUnknownReason::UnknownOffset);
    };
    let Some(read_start) = symbolic_start(read_offset, &read_iteration) else {
        return Feasibility::Unknown(AccessUnknownReason::UnknownOffset);
    };
    let read_end = Int::add(&[&read_start, &Int::from_u64(read_width)]);
    let write_end = Int::add(&[&write_start, &Int::from_u64(write_width)]);
    solver.assert(write_start.lt(&read_end));
    solver.assert(read_start.lt(&write_end));

    match solver.check() {
        SatResult::Unsat => Feasibility::Infeasible,
        SatResult::Unknown => Feasibility::Unknown(AccessUnknownReason::SolverUnknown),
        SatResult::Sat => {
            let Some(model) = solver.get_model() else {
                return Feasibility::Unknown(AccessUnknownReason::SolverUnknown);
            };
            if model.eval(&write_start, true).is_none() || model.eval(&read_start, true).is_none() {
                Feasibility::Unknown(AccessUnknownReason::SolverUnknown)
            } else {
                Feasibility::Feasible
            }
        }
    }
}

fn matches_order(
    offset: &OffsetExpr,
    order_loop: crate::analyses::loop_recognizer::LoopId,
) -> bool {
    match offset {
        OffsetExpr::Const(_) => true,
        OffsetExpr::LoopAffine { loop_id, .. } => *loop_id == order_loop,
        OffsetExpr::Unknown => false,
    }
}

fn symbolic_start(offset: &OffsetExpr, iteration: &Int) -> Option<Int> {
    match offset {
        OffsetExpr::Const(constant) => Some(Int::from_i64(*constant)),
        OffsetExpr::LoopAffine {
            stride_bytes,
            constant_bytes,
            ..
        } => {
            let scaled = Int::mul(&[&Int::from_i64(*stride_bytes), iteration]);
            Some(Int::add(&[&scaled, &Int::from_i64(*constant_bytes)]))
        }
        OffsetExpr::Unknown => None,
    }
}

fn write_witness(write: &AccessFootprint, address: SubstitutedAddress) -> WriteWitness {
    WriteWitness {
        location: write.location,
        address,
        call_chain: write.call_chain.clone(),
    }
}

fn push_reason(reasons: &mut Vec<AccessUnknownReason>, reason: AccessUnknownReason) {
    if !reasons.contains(&reason) {
        reasons.push(reason);
    }
}

fn compare_actual_address(left: &ActualAddress, right: &ActualAddress) -> Ordering {
    compare_base(&left.base, &right.base).then_with(|| left.offset.cmp(&right.offset))
}

fn compare_base(left: &BaseId, right: &BaseId) -> Ordering {
    base_rank(left)
        .cmp(&base_rank(right))
        .then_with(|| match (left, right) {
            (
                BaseId::Param {
                    local: left_local,
                    slot: left_slot,
                },
                BaseId::Param {
                    local: right_local,
                    slot: right_slot,
                },
            ) => (left_local.index(), left_slot).cmp(&(right_local.index(), right_slot)),
            (
                BaseId::LocalArray { local: left }
                | BaseId::LocalVec { local: left }
                | BaseId::LocalScalar { local: left },
                BaseId::LocalArray { local: right }
                | BaseId::LocalVec { local: right }
                | BaseId::LocalScalar { local: right },
            ) => left.index().cmp(&right.index()),
            (
                BaseId::RawBorrow {
                    target: left_target,
                    location: left_location,
                },
                BaseId::RawBorrow {
                    target: right_target,
                    location: right_location,
                },
            ) => left_target
                .cmp(right_target)
                .then_with(|| compare_location(*left_location, *right_location)),
            (
                BaseId::HeapAlloc {
                    location: left_location,
                }
                | BaseId::OpaqueReturn {
                    location: left_location,
                }
                | BaseId::IntToPtr {
                    location: left_location,
                },
                BaseId::HeapAlloc {
                    location: right_location,
                }
                | BaseId::OpaqueReturn {
                    location: right_location,
                }
                | BaseId::IntToPtr {
                    location: right_location,
                },
            ) => compare_location(*left_location, *right_location),
            (BaseId::Static { def_id: left }, BaseId::Static { def_id: right }) => {
                (left.krate, left.index).cmp(&(right.krate, right.index))
            }
            (
                BaseId::Unknown {
                    location: left_location,
                    reason: left_reason,
                },
                BaseId::Unknown {
                    location: right_location,
                    reason: right_reason,
                },
            ) => compare_location(*left_location, *right_location)
                .then_with(|| compare_unknown_reason(left_reason, right_reason)),
            _ => Ordering::Equal,
        })
}

fn base_rank(base: &BaseId) -> u8 {
    match base {
        BaseId::Param { .. } => 0,
        BaseId::LocalArray { .. } => 1,
        BaseId::LocalVec { .. } => 2,
        BaseId::LocalScalar { .. } => 3,
        BaseId::RawBorrow { .. } => 4,
        BaseId::HeapAlloc { .. } => 5,
        BaseId::OpaqueReturn { .. } => 6,
        BaseId::IntToPtr { .. } => 7,
        BaseId::Static { .. } => 8,
        BaseId::Unknown { .. } => 9,
    }
}

fn compare_location(left: Location, right: Location) -> Ordering {
    (left.block.index(), left.statement_index).cmp(&(right.block.index(), right.statement_index))
}

fn compare_unknown_reason(left: &UnknownReason, right: &UnknownReason) -> Ordering {
    left.cmp(right)
}
