#[cfg(test)]
mod domain {
    use rustc_hash::FxHashSet;
    use rustc_middle::mir::{BasicBlock, Location};

    use super::super::{
        AccessEffect, AccessEvent, AccessFootprint, AccessKind, AccessOrigin, AccessUnknownReason,
        HazardOrder, Invalidation, OffsetExpr, ParamScope, PotentialHazard, SymbolicAddress,
        WidthExpr,
    };

    fn location(statement_index: usize) -> Location {
        Location {
            block: BasicBlock::from_u32(0),
            statement_index,
        }
    }

    fn footprint(origin: usize, offset: i64, statement_index: usize) -> AccessFootprint {
        AccessFootprint {
            address: SymbolicAddress {
                origin,
                offset: OffsetExpr::Const(offset),
            },
            width: WidthExpr::Const(4),
            location: location(statement_index),
            call_chain: vec![],
        }
    }

    fn invalidation(scope: ParamScope, statement_index: usize) -> Invalidation {
        Invalidation {
            scope,
            reason: AccessUnknownReason::UnresolvedOrigin,
            location: location(statement_index),
            call_chain: vec![],
        }
    }

    #[test]
    fn read_then_write_has_no_cross_hazard() {
        let effect =
            AccessEffect::read(footprint(1, 0, 0)).then(AccessEffect::write(footprint(0, 0, 1)));

        assert!(effect.hazards.is_empty());
    }

    #[test]
    fn write_then_read_creates_cross_hazard() {
        let write = footprint(0, 4, 0);
        let read = footprint(1, 8, 1);

        let effect = AccessEffect::write(write.clone()).then(AccessEffect::read(read.clone()));

        assert_eq!(
            effect.hazards,
            vec![PotentialHazard {
                write,
                read,
                order: HazardOrder::Sequential,
            }]
        );
    }

    #[test]
    fn effect_composition_preserves_internal_hazards() {
        let first_hazard = PotentialHazard {
            write: footprint(0, 0, 0),
            read: footprint(1, 0, 1),
            order: HazardOrder::Sequential,
        };
        let second_hazard = PotentialHazard {
            write: footprint(2, 0, 2),
            read: footprint(3, 0, 3),
            order: HazardOrder::Sequential,
        };
        let first = AccessEffect {
            hazards: vec![first_hazard.clone()],
            ..AccessEffect::empty()
        };
        let second = AccessEffect {
            hazards: vec![second_hazard.clone()],
            ..AccessEffect::empty()
        };

        let composed = first.then(second);

        assert_eq!(composed.hazards, vec![first_hazard, second_hazard]);
    }

    #[test]
    fn effect_composition_unions_invalidations() {
        let first = invalidation(ParamScope::Known(FxHashSet::from_iter([0])), 0);
        let second = invalidation(ParamScope::All, 1);
        let left = AccessEffect {
            invalidations: vec![first.clone(), first.clone()],
            ..AccessEffect::empty()
        };
        let right = AccessEffect {
            invalidations: vec![second.clone()],
            contains_repetition: true,
            ..AccessEffect::empty()
        };

        let composed = left.then(right);

        assert_eq!(composed.invalidations, vec![first, second]);
        assert!(composed.contains_repetition);
    }

    #[test]
    fn mixed_parameter_and_unknown_origin_retains_both() {
        let address = SymbolicAddress {
            origin: 1,
            offset: OffsetExpr::Const(12),
        };

        let event = AccessEvent {
            kind: AccessKind::Read,
            origins: vec![
                AccessOrigin::Parameter(address.clone()),
                AccessOrigin::MayAliasParameters,
            ],
            width: Some(WidthExpr::Const(4)),
            location: location(0),
            call_chain: vec![],
        };

        assert_eq!(
            event.origins,
            vec![
                AccessOrigin::Parameter(address),
                AccessOrigin::MayAliasParameters,
            ]
        );
    }

    #[test]
    fn scoped_invalidation_intersects_only_named_params() {
        let scope = ParamScope::Known(FxHashSet::from_iter([1, 3]));

        assert!(scope.intersects(&[3, 4]));
        assert!(!scope.intersects(&[0, 2]));
        assert!(ParamScope::All.intersects(&[]));
    }
}

#[cfg(test)]
mod reachable_cycles {
    use super::super::solver::reachable_graph_has_cycle;

    #[test]
    fn deep_acyclic_chain_is_not_a_cycle() {
        const NODE_COUNT: usize = 100_000;
        let mut successors = vec![Vec::new(); NODE_COUNT];
        for (node, edges) in successors.iter_mut().enumerate().take(NODE_COUNT - 1) {
            edges.push(node + 1);
        }

        assert!(!reachable_graph_has_cycle(&successors, 0));
    }

    #[test]
    fn acyclic_diamond_ignores_disconnected_cycle() {
        let successors = vec![vec![1, 2], vec![3], vec![3], vec![], vec![5], vec![4]];

        assert!(!reachable_graph_has_cycle(&successors, 0));
    }

    #[test]
    fn reachable_cycle_is_detected() {
        let successors = vec![vec![1], vec![2], vec![1]];

        assert!(reachable_graph_has_cycle(&successors, 0));
    }

    #[test]
    fn reachable_self_loop_is_detected() {
        let successors = vec![vec![1], vec![1]];

        assert!(reachable_graph_has_cycle(&successors, 0));
    }
}

#[cfg(test)]
mod ordinary {
    use rustc_hash::FxHashSet;
    use rustc_middle::mir::{Location, START_BLOCK};

    use super::super::{
        ACCESS_SUMMARY_BUDGET, AccessEffect, AccessFootprint, AccessUnknownReason, HazardOrder,
        OffsetExpr, ParamScope, SymbolicAddress, WidthExpr,
        extractor::{LocationEffect, extract_body_effects},
        solver::solve_body,
    };
    use crate::{analyses::pointer_flow::pointer_flow_analysis, rewriter::collect_input};

    fn analyze(code: &str, fn_name: &str) -> AccessEffect {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let input = collect_input(tcx);
            let flows = pointer_flow_analysis(&input, &FxHashSet::default());
            let def_id = input
                .functions
                .iter()
                .copied()
                .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == fn_name)
                .unwrap_or_else(|| panic!("missing function {fn_name}"));
            let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
            let effects = extract_body_effects(tcx, def_id, &body, &flows[&def_id]);

            solve_body(&body, &effects, &[]).effect
        })
        .unwrap()
    }

    fn footprint_origins(footprints: &[AccessFootprint]) -> FxHashSet<usize> {
        footprints
            .iter()
            .map(|footprint| footprint.address.origin)
            .collect()
    }

    fn extracted_effects(code: &str, fn_name: &str) -> Vec<(Location, AccessEffect)> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let input = collect_input(tcx);
            let flows = pointer_flow_analysis(&input, &FxHashSet::default());
            let def_id = input
                .functions
                .iter()
                .copied()
                .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == fn_name)
                .unwrap_or_else(|| panic!("missing function {fn_name}"));
            let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();

            let mut effects: Vec<_> = extract_body_effects(tcx, def_id, &body, &flows[&def_id])
                .into_iter()
                .filter_map(|(location, effect)| match effect {
                    LocationEffect::Effect(effect) => Some((location, effect)),
                    LocationEffect::Call(_) => None,
                })
                .collect();
            effects.sort_by_key(|(location, _)| (location.block, location.statement_index));
            effects
        })
        .unwrap()
    }

    #[test]
    fn over_budget_solving_degrades_to_all_parameter_invalidation() {
        let effect = ::utils::compilation::run_compiler_on_str(
            r#"
            pub unsafe fn target(out: *mut i32, src: *const i32) {
                *out = *src;
            }
            "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let def_id = input
                    .functions
                    .iter()
                    .copied()
                    .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == "target")
                    .expect("missing function target");
                let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
                let mut effects = extract_body_effects(tcx, def_id, &body, &flows[&def_id]);
                let oversized = AccessEffect {
                    reads: (0..=ACCESS_SUMMARY_BUDGET as i64)
                        .map(|offset| AccessFootprint {
                            address: SymbolicAddress {
                                origin: 1,
                                offset: OffsetExpr::Const(offset),
                            },
                            width: WidthExpr::Const(1),
                            location: Location {
                                block: START_BLOCK,
                                statement_index: 0,
                            },
                            call_chain: vec![],
                        })
                        .collect(),
                    ..AccessEffect::empty()
                };
                effects.insert(
                    Location {
                        block: START_BLOCK,
                        statement_index: 0,
                    },
                    LocationEffect::Effect(oversized),
                );

                solve_body(&body, &effects, &[]).effect
            },
        )
        .unwrap();

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(effect.hazards.is_empty());
        assert!(effect.contains_repetition);
        assert_eq!(effect.invalidations.len(), 1);
        assert_eq!(effect.invalidations[0].scope, ParamScope::All);
        assert_eq!(
            effect.invalidations[0].reason,
            AccessUnknownReason::SummaryBudgetExceeded
        );
    }

    #[test]
    fn assignment_reads_rhs_before_writing_destination() {
        let effect = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, src: *const i32) {
                *out = *src;
            }
            "#,
            "target",
        );

        assert_eq!(footprint_origins(&effect.reads), FxHashSet::from_iter([1]));
        assert_eq!(footprint_origins(&effect.writes), FxHashSet::from_iter([0]));
        assert!(effect.hazards.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn write_before_read_is_reported() {
        let effect = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, src: *const i32) -> i32 {
                *out = 1;
                *src
            }
            "#,
            "target",
        );

        assert!(effect.hazards.iter().any(|hazard| {
            hazard.write.address.origin == 0
                && hazard.read.address.origin == 1
                && hazard.order == HazardOrder::Sequential
        }));
    }

    #[test]
    fn conditional_write_followed_by_read_is_reported() {
        let effect = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, src: *const i32, write: bool) -> i32 {
                if write {
                    *out = 1;
                }
                *src
            }
            "#,
            "target",
        );

        assert!(
            effect.hazards.iter().any(|hazard| {
                hazard.write.address.origin == 0 && hazard.read.address.origin == 1
            })
        );
    }

    #[test]
    fn exclusive_non_rejoining_paths_do_not_compose() {
        let effect = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, src: *const i32, write: bool) -> i32 {
                if write {
                    *out = 1;
                    loop {}
                } else {
                    *src
                }
            }
            "#,
            "target",
        );

        assert_eq!(footprint_origins(&effect.reads), FxHashSet::from_iter([1]));
        assert_eq!(footprint_origins(&effect.writes), FxHashSet::from_iter([0]));
        assert!(effect.hazards.is_empty());
    }

    #[test]
    fn pointer_copy_and_mut_to_const_cast_keep_origin() {
        let effect = analyze(
            r#"
            pub unsafe fn target(ptr: *mut i32) -> i32 {
                let copied = ptr;
                let immutable = copied as *const i32;
                *immutable
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 0);
        assert_eq!(effect.reads[0].address.offset, OffsetExpr::Const(0));
        assert_eq!(effect.reads[0].width, WidthExpr::Const(4));
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn multiple_parameter_origins_emit_alternatives() {
        let effect = analyze(
            r#"
            pub unsafe fn target(first: *const i32, second: *const i32, choose: bool) -> i32 {
                let mut ptr = first;
                if choose {
                    ptr = second;
                }
                *ptr
            }
            "#,
            "target",
        );

        assert_eq!(
            footprint_origins(&effect.reads),
            FxHashSet::from_iter([0, 1])
        );
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn local_array_and_scalar_pointees_are_disjoint() {
        let effect = analyze(
            r#"
            pub unsafe fn target() {
                let mut array = [1_i32, 2];
                let mut scalar = 3_i32;
                let array_ptr = &raw mut array[0];
                let scalar_ptr = &raw mut scalar;
                *array_ptr = 4;
                *scalar_ptr = 5;
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(effect.hazards.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn unknown_pointer_origin_adds_invalidation() {
        let effect = analyze(
            r#"
            pub unsafe fn target(address: usize) {
                let ptr = address as *mut i32;
                *ptr = 1;
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert_eq!(effect.invalidations.len(), 1);
        assert_eq!(effect.invalidations[0].scope, ParamScope::All);
    }

    #[test]
    fn mixed_param_and_unknown_adds_event_and_invalidation() {
        let effect = analyze(
            r#"
            pub unsafe fn target(param: *const i32, address: usize, choose: bool) -> i32 {
                let mut ptr = param;
                if choose {
                    ptr = address as *const i32;
                }
                *ptr
            }
            "#,
            "target",
        );

        assert_eq!(footprint_origins(&effect.reads), FxHashSet::from_iter([0]));
        assert_eq!(effect.invalidations.len(), 1);
        assert_eq!(effect.invalidations[0].scope, ParamScope::All);
    }

    #[test]
    fn write_on_nonreturning_path_is_exported() {
        let effect = analyze(
            r#"
            pub unsafe fn target(out: *mut i32) -> ! {
                *out = 1;
                loop {}
            }
            "#,
            "target",
        );

        assert_eq!(footprint_origins(&effect.writes), FxHashSet::from_iter([0]));
    }

    #[test]
    fn unrecognized_loop_reaches_finite_fixpoint() {
        let effect = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, src: *const i32, mut index: usize, end: usize) {
                while index < end {
                    *out = *src;
                    index += 2;
                }
            }
            "#,
            "target",
        );

        assert!(
            effect.hazards.iter().any(|hazard| {
                hazard.write.address.origin == 0 && hazard.read.address.origin == 1
            })
        );
    }

    #[test]
    fn post_deref_field_uses_layout_offset() {
        let effect = analyze(
            r#"
            #[repr(C)]
            pub struct Pair {
                pub first: u8,
                pub second: u32,
            }

            pub unsafe fn target(pair: *const Pair) -> u32 {
                (*pair).second
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 0);
        assert_eq!(effect.reads[0].address.offset, OffsetExpr::Const(4));
        assert_eq!(effect.reads[0].width, WidthExpr::Const(4));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn post_deref_constant_index_uses_element_offset() {
        let effect = analyze(
            r#"
            pub unsafe fn target(array: *const [u16; 4]) -> u16 {
                let [_, _, value, _] = *array;
                value
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 0);
        assert_eq!(effect.reads[0].address.offset, OffsetExpr::Const(4));
        assert_eq!(effect.reads[0].width, WidthExpr::Const(2));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn dynamic_post_deref_index_invalidates_parameter_offset() {
        let effect = analyze(
            r#"
            pub unsafe fn target(array: *const [u16; 4], index: usize) -> u16 {
                (*array)[index]
            }
            "#,
            "target",
        );

        assert!(effect.reads.iter().all(|read| {
            read.address.origin != 0 || read.address.offset == OffsetExpr::Unknown
        }));
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownOffset
                && invalidation.scope.intersects(&[0])
        }));
    }

    #[test]
    fn nested_deref_segments_keep_evaluation_order_and_widths() {
        let effects = extracted_effects(
            r#"
            pub unsafe fn target(pointer: *const *const u32) -> u32 {
                **pointer
            }
            "#,
            "target",
        );
        let reads: Vec<_> = effects
            .iter()
            .flat_map(|(_, effect)| effect.reads.iter())
            .collect();

        assert_eq!(reads.len(), 2);
        assert_eq!(reads[0].address.origin, 0);
        assert_eq!(reads[0].width, WidthExpr::Const(8));
        assert_eq!(reads[1].address.origin, 0);
        assert_eq!(reads[1].width, WidthExpr::Const(4));
    }

    #[test]
    fn deref_rooted_raw_borrow_is_not_disjoint() {
        let effect = analyze(
            r#"
            #[repr(C)]
            pub struct Holder {
                pub padding: u32,
                pub pointer_field: *mut i32,
            }

            pub unsafe fn target(holder: *mut Holder, value: *mut i32) {
                let field = &raw mut (*holder).pointer_field;
                *field = value;
            }
            "#,
            "target",
        );

        assert!(
            effect.writes.iter().any(|write| write.address.origin == 0)
                || effect
                    .invalidations
                    .iter()
                    .any(|invalidation| invalidation.scope.intersects(&[0]))
        );
    }

    #[test]
    fn parameter_rooted_array_borrow_is_not_disjoint() {
        let effect = analyze(
            r#"
            pub unsafe fn target(array: *mut [i32; 4], index: usize) {
                let element = &raw mut (*array)[index];
                *element = 1;
            }
            "#,
            "target",
        );

        assert!(
            effect.writes.iter().any(|write| write.address.origin == 0)
                || effect
                    .invalidations
                    .iter()
                    .any(|invalidation| invalidation.scope.intersects(&[0]))
        );
    }
}

#[cfg(test)]
mod interprocedural {
    use rustc_hash::FxHashSet;

    use super::super::{
        AccessEffect, AccessOrderAnalysis, AccessUnknownReason, OffsetExpr, ParamScope, WidthExpr,
    };
    use crate::{analyses::pointer_flow::pointer_flow_analysis, rewriter::collect_input};

    fn analyze(code: &str, fn_name: &str) -> AccessEffect {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let input = collect_input(tcx);
            let flows = pointer_flow_analysis(&input, &FxHashSet::default());
            let analysis = AccessOrderAnalysis::analyze(&input, &flows);
            let def_id = input
                .functions
                .iter()
                .copied()
                .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == fn_name)
                .unwrap_or_else(|| panic!("missing function {fn_name}"));

            analysis
                .summary(def_id)
                .unwrap_or_else(|| panic!("missing summary for {fn_name}"))
                .effect
                .clone()
        })
        .unwrap()
    }

    #[test]
    fn one_local_helper_substitutes_parameter_effects() {
        let effect = analyze(
            r#"
            unsafe fn helper(dst: *mut i32, src: *const i32) {
                *dst = *src;
            }

            pub unsafe fn target(out: *mut i32, input: *const i32) {
                helper(out, input);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn multiple_helper_layers_compose_symbolically() {
        let effect = analyze(
            r#"
            unsafe fn leaf(dst: *mut i32, src: *const i32) {
                *dst = *src;
            }

            unsafe fn middle(dst: *mut i32, src: *const i32) {
                leaf(dst, src);
            }

            pub unsafe fn target(out: *mut i32, input: *const i32) {
                middle(out, input);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].call_chain.len(), 2);
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].call_chain.len(), 2);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn helper_parameter_permutation_and_duplication() {
        let effect = analyze(
            r#"
            unsafe fn helper(first: *mut i32, second: *const i32, third: *const i32) -> i32 {
                *first = 1;
                *second + *third
            }

            pub unsafe fn target(left: *mut i32, right: *mut i32) -> i32 {
                helper(right, left, left)
            }
            "#,
            "target",
        );

        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 1);
        assert_eq!(effect.reads.len(), 2);
        assert!(effect.reads.iter().all(|read| read.address.origin == 0));
        assert!(
            effect.hazards.iter().all(|hazard| {
                hazard.write.address.origin == 1 && hazard.read.address.origin == 0
            })
        );
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn constant_offset_call_arguments_compose() {
        let effect = analyze(
            r#"
            unsafe fn helper(dst: *mut i32, src: *const i32) {
                *dst = *src;
            }

            pub unsafe fn target(out: *mut i32, input: *const i32) {
                helper(out.add(1), input.add(2));
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].address.offset, OffsetExpr::Const(8));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].address.offset, OffsetExpr::Const(4));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn helper_witness_retains_call_chain() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn helper(dst: *mut i32, src: *const i32) -> i32 {
                *dst = 1;
                *src
            }

            pub unsafe fn target(out: *mut i32, input: *const i32) -> i32 {
                helper(out, input)
            }
            "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let analysis = AccessOrderAnalysis::analyze(&input, &flows);
                let target = input
                    .functions
                    .iter()
                    .copied()
                    .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == "target")
                    .unwrap();
                let helper = input
                    .functions
                    .iter()
                    .copied()
                    .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == "helper")
                    .unwrap();
                let effect = &analysis.summary(target).unwrap().effect;
                let hazard = effect.hazards.first().expect("missing helper hazard");

                assert_eq!(hazard.write.call_chain.len(), 1);
                assert_eq!(hazard.write.call_chain[0].caller, target);
                assert_eq!(hazard.write.call_chain[0].callee, helper);
                assert_eq!(hazard.read.call_chain, hazard.write.call_chain);
            },
        )
        .unwrap();
    }

    #[test]
    fn recursive_self_call_invalidates_reachable_params() {
        let effect = analyze(
            r#"
            pub unsafe fn target(pointer: *mut i32, depth: usize) {
                if depth != 0 {
                    target(pointer, depth - 1);
                }
            }
            "#,
            "target",
        );

        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::RecursiveCall
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0]))
        }));
    }

    #[test]
    fn mutual_recursion_invalidates_reachable_params() {
        let effect = analyze(
            r#"
            pub unsafe fn first(pointer: *mut i32, depth: usize) {
                if depth != 0 {
                    second(pointer, depth - 1);
                }
            }

            unsafe fn second(pointer: *mut i32, depth: usize) {
                if depth != 0 {
                    first(pointer, depth - 1);
                }
            }
            "#,
            "first",
        );

        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::RecursiveCall
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0]))
        }));
    }

    #[test]
    fn recursive_call_scope_does_not_block_unrelated_params() {
        let effect = analyze(
            r#"
            pub unsafe fn target(first: *mut i32, unrelated: *mut i32, depth: usize) {
                if depth != 0 {
                    let mut local = 0_i32;
                    target(first, &raw mut local, depth - 1);
                }
                *unrelated = 1;
            }
            "#,
            "target",
        );

        let recursive = effect
            .invalidations
            .iter()
            .find(|invalidation| invalidation.reason == AccessUnknownReason::RecursiveCall)
            .expect("missing recursive invalidation");
        assert!(recursive.scope.intersects(&[0]));
        assert!(!recursive.scope.intersects(&[1]));
    }

    #[test]
    fn ptr_copy_reads_source_then_writes_destination() {
        let effect = analyze(
            r#"
            pub unsafe fn target(destination: *mut u32, source: *const u32) {
                core::ptr::copy(source, destination, 3);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(12));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(12));
        assert!(effect.hazards.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn write_bytes_writes_only_destination() {
        let effect = analyze(
            r#"
            pub unsafe fn target(destination: *mut u32) {
                core::ptr::write_bytes(destination, 0, 2);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(8));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn unknown_foreign_call_invalidates_reachable_params() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn mystery(pointer: *mut i32);
            }

            pub unsafe fn target(first: *mut i32, unrelated: *mut i32) {
                mystery(first);
                *unrelated = 1;
            }
            "#,
            "target",
        );

        let foreign = effect
            .invalidations
            .iter()
            .find(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
            .expect("missing foreign-call invalidation");
        assert!(foreign.scope.intersects(&[0]));
        assert!(!foreign.scope.intersects(&[1]));
    }

    #[test]
    fn unknown_call_without_bounded_origins_invalidates_all() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn mystery();
            }

            pub unsafe fn target(pointer: *mut i32) {
                mystery();
                *pointer = 1;
            }
            "#,
            "target",
        );

        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::ForeignCall
                && invalidation.scope == ParamScope::All
        }));
    }

    #[test]
    fn nested_pointer_actual_unions_all_pointer_slots() {
        let effect = analyze(
            r#"
            unsafe fn helper(pointer: *mut *mut i32) {
                **pointer = 1;
            }

            pub unsafe fn target(output: *mut i32) {
                let mut local_pointer = output;
                helper(&raw mut local_pointer);
            }
            "#,
            "target",
        );

        assert!(effect.reads.iter().any(|read| read.address.origin == 0));
        assert!(effect.writes.iter().any(|write| write.address.origin == 0));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn aggregate_actual_unions_non_head_pointer_field() {
        let effect = analyze(
            r#"
            #[derive(Copy, Clone)]
            struct Pair {
                left: *mut i32,
                right: *mut i32,
            }

            unsafe fn helper(pair: Pair) {
                *pair.right = 1;
            }

            pub unsafe fn target(left: *mut i32, right: *mut i32) {
                let pair = Pair { left, right };
                helper(pair);
            }
            "#,
            "target",
        );

        assert_eq!(
            effect
                .writes
                .iter()
                .map(|write| write.address.origin)
                .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter([0, 1])
        );
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn unknown_call_scope_unions_direct_and_aggregate_origins() {
        let effect = analyze(
            r#"
            #[repr(C)]
            #[derive(Copy, Clone)]
            struct Pair {
                left: *mut i32,
                right: *mut i32,
            }

            unsafe extern "C" {
                fn mystery(direct: *mut i32, carried: Pair);
            }

            pub unsafe fn target(
                direct: *mut i32,
                carried: Pair,
                unrelated: *mut i32,
            ) {
                mystery(direct, carried);
                *unrelated = 1;
            }
            "#,
            "target",
        );

        let foreign = effect
            .invalidations
            .iter()
            .find(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
            .expect("missing foreign-call invalidation");
        assert_eq!(
            foreign.scope,
            ParamScope::Known(FxHashSet::from_iter([0, 1]))
        );
    }

    #[test]
    fn recursive_call_scope_unions_direct_and_aggregate_origins() {
        let effect = analyze(
            r#"
            #[derive(Copy, Clone)]
            pub struct Pair {
                left: *mut i32,
                right: *mut i32,
            }

            pub unsafe fn target(
                direct: *mut i32,
                carried: Pair,
                unrelated: *mut i32,
                depth: usize,
            ) {
                if depth != 0 {
                    let mut local = 0_i32;
                    let next = Pair {
                        left: &raw mut local,
                        right: carried.right,
                    };
                    target(direct, next, &raw mut local, depth - 1);
                }
                *unrelated = 1;
            }
            "#,
            "target",
        );

        let recursive = effect
            .invalidations
            .iter()
            .find(|invalidation| invalidation.reason == AccessUnknownReason::RecursiveCall)
            .expect("missing recursive invalidation");
        assert_eq!(
            recursive.scope,
            ParamScope::Known(FxHashSet::from_iter([0, 1]))
        );
        assert!(!recursive.scope.intersects(&[2]));
    }

    #[test]
    fn effective_custom_link_name_does_not_model_memcpy() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                #[link_name = "custom_copy"]
                fn memcpy(destination: *mut u8, source: *const u8, count: usize) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::ForeignCall
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0, 1]))
        }));
    }

    #[test]
    fn effective_memcpy_link_name_models_custom_declaration() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                #[link_name = "memcpy"]
                fn custom_copy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = custom_copy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(4));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(4));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memmove_reads_then_writes_constant_bytes() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memmove(
                    destination: *mut u16,
                    source: *const u32,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u16, source: *const u32) {
                let _ = memmove(destination, source, 7);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(7));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(7));
        assert!(effect.hazards.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memset_writes_constant_bytes() {
        let effect = analyze(
            r#"
            unsafe extern "C-unwind" {
                fn memset(destination: *mut u16, value: i32, count: usize) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u16) {
                let _ = memset(destination, 0, 9);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(9));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memcmp_reads_both_constant_byte_ranges() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcmp(left: *const u8, right: *mut u32, count: usize) -> i32;
            }

            pub unsafe fn target(left: *const u8, right: *mut u32) -> i32 {
                memcmp(left, right, 11)
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 2);
        assert_eq!(
            effect
                .reads
                .iter()
                .map(|read| read.address.origin)
                .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter([0, 1])
        );
        assert!(
            effect
                .reads
                .iter()
                .all(|read| read.width == WidthExpr::Const(11))
        );
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn malformed_foreign_memcpy_return_is_not_builtin() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(destination: *mut u8, source: *const u8, count: usize) -> i32;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn unsupported_foreign_memcpy_abi_is_not_builtin() {
        let effect = analyze(
            r#"
            unsafe extern "system" {
                fn memcpy(destination: *mut u8, source: *const u8, count: usize) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn malformed_foreign_memset_value_is_not_builtin() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memset(destination: *mut u8, value: u8, count: usize) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8) {
                let _ = memset(destination, 0, 4);
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn malformed_foreign_memset_count_is_not_builtin() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memset(destination: *mut u8, value: i32, count: u32) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8) {
                let _ = memset(destination, 0, 4);
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn malformed_foreign_memset_return_is_not_builtin() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memset(destination: *mut u8, value: i32, count: usize) -> i32;
            }

            pub unsafe fn target(destination: *mut u8) {
                let _ = memset(destination, 0, 4);
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_parameter_count_yields_linear_width() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(
                destination: *mut u8,
                source: *const u8,
                count: usize,
            ) {
                let _ = memcpy(destination, source, count);
            }
            "#,
            "target",
        );

        let width = WidthExpr::Linear {
            param: 2,
            scale: 1,
            offset: 0,
        };
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, width);
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, width);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memcpy_wrapping_mul_count_scales_linear_width() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8, blocks: u32) {
                let _ = memcpy(destination, source, blocks.wrapping_mul(16) as usize);
            }
            "#,
            "target",
        );

        let width = WidthExpr::Linear {
            param: 2,
            scale: 16,
            offset: 0,
        };
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].width, width);
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].width, width);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memcpy_wrapping_add_count_offsets_linear_width() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8, count: usize) {
                let _ = memcpy(destination, source, count.wrapping_add(8));
            }
            "#,
            "target",
        );

        let width = WidthExpr::Linear {
            param: 2,
            scale: 1,
            offset: 8,
        };
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].width, width);
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].width, width);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memcpy_literal_cast_count_folds_to_constant() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, 16i32 as usize);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(16));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(16));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn loaded_foreign_copy_count_still_invalidates_both_origins() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(
                destination: *mut u8,
                source: *const u8,
                count: *const usize,
            ) {
                let _ = memcpy(destination, source, *count);
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0, 1]))
        }));
    }

    #[test]
    fn two_parameter_foreign_copy_count_invalidates_both_origins() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(
                destination: *mut u8,
                source: *const u8,
                a: usize,
                b: usize,
            ) {
                let _ = memcpy(destination, source, a.wrapping_mul(b));
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0, 1]))
        }));
    }

    #[test]
    fn call_result_foreign_copy_count_invalidates_both_origins() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            fn opaque() -> usize {
                4
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, opaque());
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0, 1]))
        }));
    }

    #[test]
    fn reassigned_parameter_foreign_copy_count_invalidates_both_origins() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(
                destination: *mut u8,
                source: *const u8,
                mut count: usize,
            ) {
                count = count.wrapping_add(1);
                let _ = memcpy(destination, source, count);
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0, 1]))
        }));
    }

    #[test]
    fn foreign_memset_parameter_count_yields_linear_width() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memset(destination: *mut u8, value: i32, count: usize) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, count: usize) {
                let _ = memset(destination, 0, count);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(
            effect.writes[0].width,
            WidthExpr::Linear {
                param: 1,
                scale: 1,
                offset: 0,
            }
        );
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memcmp_parameter_count_yields_linear_widths() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcmp(left: *const u8, right: *const u8, count: usize) -> i32;
            }

            pub unsafe fn target(left: *const u8, right: *const u8, count: usize) -> i32 {
                memcmp(left, right, count)
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 2);
        assert!(effect.reads.iter().all(|read| {
            read.width
                == WidthExpr::Linear {
                    param: 2,
                    scale: 1,
                    offset: 0,
                }
        }));
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn multiple_helper_layers_record_exact_outer_to_inner_frames() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn leaf(pointer: *mut i32) {
                *pointer = 1;
            }

            unsafe fn middle(pointer: *mut i32) {
                leaf(pointer);
            }

            pub unsafe fn target(pointer: *mut i32) {
                middle(pointer);
            }
            "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let analysis = AccessOrderAnalysis::analyze(&input, &flows);
                let named = |name: &str| {
                    input
                        .functions
                        .iter()
                        .copied()
                        .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == name)
                        .unwrap_or_else(|| panic!("missing function {name}"))
                };
                let target = named("target");
                let middle = named("middle");
                let leaf = named("leaf");
                let chain = &analysis.summary(target).unwrap().effect.writes[0].call_chain;

                assert_eq!(chain.len(), 2);
                assert_eq!(chain[0].caller, target);
                assert_eq!(chain[0].callee, middle);
                assert_eq!(chain[1].caller, middle);
                assert_eq!(chain[1].callee, leaf);
            },
        )
        .unwrap();
    }

    #[test]
    fn substituted_unknown_offset_retains_inner_call_frames() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn leaf(pointer: *mut i32, offset: usize) {
                *pointer.add(offset) = 1;
            }

            unsafe fn middle(pointer: *mut i32, offset: usize) {
                leaf(pointer, offset);
            }

            pub unsafe fn target(pointer: *mut i32, offset: usize) {
                middle(pointer, offset);
            }
            "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let analysis = AccessOrderAnalysis::analyze(&input, &flows);
                let named = |name: &str| {
                    input
                        .functions
                        .iter()
                        .copied()
                        .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == name)
                        .unwrap_or_else(|| panic!("missing function {name}"))
                };
                let target = named("target");
                let middle = named("middle");
                let leaf = named("leaf");
                let effect = &analysis.summary(target).unwrap().effect;
                let invalidations: Vec<_> = effect
                    .invalidations
                    .iter()
                    .filter(|invalidation| {
                        invalidation.reason == AccessUnknownReason::UnknownOffset
                            && invalidation
                                .call_chain
                                .first()
                                .is_some_and(|frame| frame.caller == target)
                    })
                    .collect();

                assert!(!invalidations.is_empty());
                assert!(invalidations.iter().all(|invalidation| {
                    invalidation.call_chain.len() == 2
                        && invalidation.call_chain[0].callee == middle
                        && invalidation.call_chain[1].caller == middle
                        && invalidation.call_chain[1].callee == leaf
                }));
            },
        )
        .unwrap();
    }

    #[test]
    fn substituted_unresolved_origin_retains_inner_call_frames() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn leaf(pointer: *mut i32) {
                *pointer = 1;
            }

            unsafe fn middle(pointer: *mut i32) {
                leaf(pointer);
            }

            pub unsafe fn target(pointer: *mut i32, choose_parameter: bool) {
                let selected = if choose_parameter {
                    pointer
                } else {
                    1_usize as *mut i32
                };
                middle(selected);
            }
            "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let analysis = AccessOrderAnalysis::analyze(&input, &flows);
                let named = |name: &str| {
                    input
                        .functions
                        .iter()
                        .copied()
                        .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == name)
                        .unwrap_or_else(|| panic!("missing function {name}"))
                };
                let target = named("target");
                let middle = named("middle");
                let leaf = named("leaf");
                let effect = &analysis.summary(target).unwrap().effect;
                let unresolved = effect
                    .invalidations
                    .iter()
                    .find(|invalidation| {
                        invalidation.reason == AccessUnknownReason::UnresolvedOrigin
                            && invalidation
                                .call_chain
                                .first()
                                .is_some_and(|frame| frame.caller == target)
                    })
                    .expect("missing unresolved-origin invalidation");

                assert_eq!(unresolved.call_chain.len(), 2);
                assert_eq!(unresolved.call_chain[0].callee, middle);
                assert_eq!(unresolved.call_chain[1].caller, middle);
                assert_eq!(unresolved.call_chain[1].callee, leaf);
            },
        )
        .unwrap();
    }

    #[test]
    fn core_ptr_read_and_write_variants_have_typed_effects() {
        let effect = analyze(
            r#"
            pub unsafe fn target(destination: *mut u32, source: *const u32) {
                let first = core::ptr::read(source);
                let second = core::ptr::read_unaligned(source);
                let third = core::ptr::read_volatile(source);
                core::ptr::write(destination, first);
                core::ptr::write_unaligned(destination, second);
                core::ptr::write_volatile(destination, third);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 3);
        assert!(
            effect
                .reads
                .iter()
                .all(|read| read.address.origin == 1 && read.width == WidthExpr::Const(4))
        );
        assert_eq!(effect.writes.len(), 3);
        assert!(
            effect
                .writes
                .iter()
                .all(|write| write.address.origin == 0 && write.width == WidthExpr::Const(4))
        );
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn mir_copy_nonoverlapping_intrinsic_reads_then_writes() {
        let effect = analyze(
            r#"
            #![feature(core_intrinsics)]
            #![allow(internal_features)]

            pub unsafe fn target(destination: *mut u32, source: *const u32) {
                core::intrinsics::copy_nonoverlapping(source, destination, 3);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(12));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(12));
        assert!(effect.hazards.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn local_substitution_marks_hidden_union_pointer_unresolved() {
        let effect = analyze(
            r#"
            #[repr(C)]
            #[derive(Copy, Clone)]
            union Hidden {
                pointer: *mut i32,
                number: usize,
            }

            #[repr(C)]
            #[derive(Copy, Clone)]
            struct Carried {
                direct: *mut i32,
                hidden: Hidden,
            }

            unsafe fn helper(carried: Carried) {
                *carried.direct = 1;
            }

            pub unsafe fn target(direct: *mut i32, hidden: *mut i32) {
                helper(Carried {
                    direct,
                    hidden: Hidden { pointer: hidden },
                });
            }
            "#,
            "target",
        );

        assert!(effect.writes.iter().any(|write| write.address.origin == 0));
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnresolvedOrigin
                && invalidation.scope == ParamScope::All
        }));
    }

    #[test]
    fn unknown_call_with_hidden_enum_pointer_and_direct_origin_invalidates_all() {
        let effect = analyze(
            r#"
            #[repr(C)]
            pub enum Hidden {
                Pointer(*mut i32),
                Number(usize),
            }

            unsafe extern "C" {
                fn mystery(direct: *mut i32, hidden: Hidden);
            }

            pub unsafe fn target(direct: *mut i32, hidden: Hidden) {
                mystery(direct, hidden);
            }
            "#,
            "target",
        );

        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::ForeignCall
                && invalidation.scope == ParamScope::All
        }));
    }

    #[test]
    fn recursive_call_with_hidden_union_pointer_and_direct_origin_invalidates_all() {
        let effect = analyze(
            r#"
            #[repr(C)]
            #[derive(Copy, Clone)]
            pub union Hidden {
                pointer: *mut i32,
                number: usize,
            }

            pub unsafe fn target(direct: *mut i32, hidden: Hidden, depth: usize) {
                if depth != 0 {
                    target(direct, hidden, depth - 1);
                }
            }
            "#,
            "target",
        );

        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::RecursiveCall
                && invalidation.scope == ParamScope::All
        }));
    }

    #[test]
    fn pointer_free_aggregate_does_not_widen_known_unknown_call_scope() {
        let effect = analyze(
            r#"
            #[repr(C)]
            #[derive(Copy, Clone)]
            pub struct Plain {
                number: usize,
                flags: (bool, u8),
            }

            unsafe extern "C" {
                fn mystery(direct: *mut i32, plain: Plain);
            }

            pub unsafe fn target(
                direct: *mut i32,
                unrelated: *mut i32,
                plain: Plain,
            ) {
                mystery(direct, plain);
                *unrelated = 1;
            }
            "#,
            "target",
        );

        let foreign = effect
            .invalidations
            .iter()
            .find(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
            .expect("missing foreign-call invalidation");
        assert_eq!(foreign.scope, ParamScope::Known(FxHashSet::from_iter([0])));
    }

    #[test]
    fn dynamic_ptr_copy_scopes_unknown_width_to_head_pointers() {
        let effect = analyze(
            r#"
            pub unsafe fn target(output: *mut i32, count: usize) {
                let mut cell = output;
                core::ptr::copy(&raw const cell, &raw mut cell, count);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memmove_rejects_fat_slice_source() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memmove(
                    destination: *mut u8,
                    source: *const [u8],
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const [u8]) {
                let _ = memmove(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_nested_unsafe_binder_tail_falls_back() {
        let effect = analyze(
            r#"
            #![feature(unsafe_binders)]

            struct Tail<T: ?Sized>(T);

            unsafe extern "C" {
                fn memcpy(
                    destination: *mut Tail<unsafe<'a> &'a u8>,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(
                destination: *mut Tail<unsafe<'a> &'a u8>,
                source: *const u8,
            ) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_no_bound_unsafe_binder_dst_tail_falls_back() {
        let effect = analyze(
            r#"
            #![feature(unsafe_binders)]

            struct Tail<T: ?Sized>(T);

            unsafe extern "C" {
                fn memcpy(
                    destination: *mut Tail<unsafe<> core::mem::ManuallyDrop<[u8]>>,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(
                destination: *mut Tail<unsafe<> core::mem::ManuallyDrop<[u8]>>,
                source: *const u8,
            ) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_unsafe_binder_in_concrete_field_falls_back() {
        let effect = analyze(
            r#"
            #![feature(unsafe_binders)]

            struct Tail<T: ?Sized>(T);
            struct Outer(Tail<unsafe<> core::mem::ManuallyDrop<[u8]>>);

            unsafe extern "C" {
                fn memcpy(
                    destination: *mut Outer,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut Outer, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_repeated_acyclic_fields_exhaust_work_budget() {
        let effect = analyze(
            r#"
            struct A0(A1, A1);
            struct A1(A2, A2);
            struct A2(A3, A3);
            struct A3(A4, A4);
            struct A4(A5, A5);
            struct A5(A6, A6);
            struct A6(u8);

            unsafe extern "C" {
                fn memcpy(
                    destination: *mut A0,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut A0, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_models_layout_proven_extern_thin_pointer() {
        let effect = analyze(
            r#"
            #![feature(extern_types)]

            unsafe extern "C" {
                type Opaque;

                fn memcpy(
                    destination: *mut Opaque,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut Opaque, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(4));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(4));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn foreign_memcpy_rejects_fat_slice_return() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut [u8];
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memset_rejects_fat_str_destination() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memset(destination: *mut str, value: i32, count: usize) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut str) {
                let _ = memset(destination, 0, 4);
            }
            "#,
            "target",
        );

        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcmp_rejects_fat_dyn_source() {
        let effect = analyze(
            r#"
            pub trait Marker {}

            unsafe extern "C" {
                fn memcmp(
                    left: *const dyn Marker,
                    right: *const u8,
                    count: usize,
                ) -> i32;
            }

            pub unsafe fn target(left: *const dyn Marker, right: *const u8) -> i32 {
                memcmp(left, right, 4)
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn foreign_memcpy_rejects_variadic_signature() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                    ...
                ) -> *mut u8;
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                let _ = memcpy(destination, source, 4);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason == AccessUnknownReason::ForeignCall)
        );
    }

    #[test]
    fn substitution_folds_linear_width_with_constant_actual() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            unsafe fn helper(destination: *mut u8, source: *const u8, blocks: usize) {
                let _ = memcpy(destination, source, blocks.wrapping_mul(4));
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                helper(destination, source, 3);
            }
            "#,
            "target",
        );

        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].address.origin, 1);
        assert_eq!(effect.reads[0].width, WidthExpr::Const(12));
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].address.origin, 0);
        assert_eq!(effect.writes[0].width, WidthExpr::Const(12));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn substitution_composes_linear_width_with_linear_actual() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            unsafe fn helper(destination: *mut u8, source: *const u8, blocks: usize) {
                let _ = memcpy(destination, source, blocks.wrapping_mul(4));
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8, blocks: usize) {
                helper(destination, source, blocks.wrapping_add(2));
            }
            "#,
            "target",
        );

        let width = WidthExpr::Linear {
            param: 2,
            scale: 4,
            offset: 8,
        };
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.reads[0].width, width);
        assert_eq!(effect.writes.len(), 1);
        assert_eq!(effect.writes[0].width, width);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn substitution_with_unresolvable_actual_count_invalidates() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            fn opaque() -> usize {
                3
            }

            unsafe fn helper(destination: *mut u8, source: *const u8, blocks: usize) {
                let _ = memcpy(destination, source, blocks.wrapping_mul(4));
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                helper(destination, source, opaque());
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0]))
        }));
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([1]))
        }));
    }

    #[test]
    fn substitution_overflow_during_fold_invalidates() {
        let effect = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            unsafe fn helper(destination: *mut u8, source: *const u8, blocks: usize) {
                let _ = memcpy(destination, source, blocks.wrapping_mul(0x8000_0000_0000_0000));
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8) {
                helper(destination, source, 3);
            }
            "#,
            "target",
        );

        assert!(effect.reads.is_empty());
        assert!(effect.writes.is_empty());
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([0]))
        }));
        assert!(effect.invalidations.iter().any(|invalidation| {
            invalidation.reason == AccessUnknownReason::UnknownWidth
                && invalidation.scope == ParamScope::Known(FxHashSet::from_iter([1]))
        }));
    }
}

#[cfg(test)]
mod query {
    use rustc_hash::FxHashSet;
    use rustc_hir::def_id::LocalDefId;
    use rustc_middle::{
        mir::{Location, TerminatorKind},
        ty::{self, TyCtxt},
    };

    use super::super::{
        AccessOrderAnalysis, AccessOrderVerdict, AccessUnknownReason, HazardOrder, OffsetExpr,
        WriteVerdict,
    };
    use crate::{
        analyses::pointer_flow::{
            graph::{BaseId, UnknownReason},
            pointer_flow_analysis,
        },
        rewriter::collect_input,
    };

    enum RequestedQuery {
        AccessOrder {
            writers: Vec<usize>,
            readers: Vec<usize>,
        },
        Writes(Vec<usize>),
    }

    enum QueryResult {
        AccessOrder(AccessOrderVerdict),
        Writes(WriteVerdict),
    }

    fn named_function(tcx: TyCtxt<'_>, functions: &[LocalDefId], name: &str) -> LocalDefId {
        functions
            .iter()
            .copied()
            .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == name)
            .unwrap_or_else(|| panic!("missing function {name}"))
    }

    fn direct_call_location(tcx: TyCtxt<'_>, caller: LocalDefId, callee: LocalDefId) -> Location {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        body.basic_blocks
            .iter_enumerated()
            .find_map(|(block, block_data)| {
                let TerminatorKind::Call { func, .. } = &block_data.terminator().kind else {
                    return None;
                };
                let constant = func.constant()?;
                let ty::TyKind::FnDef(def_id, _) = constant.ty().kind() else {
                    return None;
                };
                (*def_id == callee.to_def_id()).then_some(Location {
                    block,
                    statement_index: block_data.statements.len(),
                })
            })
            .unwrap_or_else(|| {
                panic!(
                    "missing direct call to {}",
                    tcx.item_name(callee.to_def_id())
                )
            })
    }

    fn query_call(
        code: &str,
        caller_name: &str,
        callee_name: &str,
        query: RequestedQuery,
    ) -> QueryResult {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let input = collect_input(tcx);
            let flows = pointer_flow_analysis(&input, &FxHashSet::default());
            let analysis = AccessOrderAnalysis::analyze(&input, &flows);
            let caller = named_function(tcx, &input.functions, caller_name);
            let callee = named_function(tcx, &input.functions, callee_name);
            let location = direct_call_location(tcx, caller, callee);
            let call = analysis
                .at_call(caller, location)
                .expect("valid local call");

            match query {
                RequestedQuery::AccessOrder { writers, readers } => {
                    QueryResult::AccessOrder(call.reads_precede_writes(&writers, &readers))
                }
                RequestedQuery::Writes(params) => QueryResult::Writes(call.never_written(&params)),
            }
        })
        .unwrap()
    }

    fn reads_precede_writes(
        code: &str,
        caller: &str,
        callee: &str,
        writers: &[usize],
        readers: &[usize],
    ) -> AccessOrderVerdict {
        let QueryResult::AccessOrder(verdict) = query_call(
            code,
            caller,
            callee,
            RequestedQuery::AccessOrder {
                writers: writers.to_vec(),
                readers: readers.to_vec(),
            },
        ) else {
            unreachable!()
        };
        verdict
    }

    fn never_written(code: &str, caller: &str, callee: &str, params: &[usize]) -> WriteVerdict {
        let QueryResult::Writes(verdict) = query_call(
            code,
            caller,
            callee,
            RequestedQuery::Writes(params.to_vec()),
        ) else {
            unreachable!()
        };
        verdict
    }

    #[test]
    fn equal_offset_fma_call_is_proven() {
        let verdict = reads_precede_writes(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut f64, input: *const f64, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *input.add(i) * 2.0;
                    i += 1;
                }
            }

            pub unsafe fn caller(base: *mut f64, len: usize) {
                f(base, base, len);
            }
            "#,
            "caller",
            "f",
            &[0],
            &[1],
        );

        assert_eq!(verdict, AccessOrderVerdict::Proven);
    }

    #[test]
    fn shifted_same_base_fma_call_has_later_iteration_witness() {
        let verdict = reads_precede_writes(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut f64, input: *const f64, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *input.add(i) * 2.0;
                    i += 1;
                }
            }

            pub unsafe fn caller(base: *mut f64, len: usize) {
                f(base.add(1), base, len);
            }
            "#,
            "caller",
            "f",
            &[0],
            &[1],
        );

        let AccessOrderVerdict::MayReadAfterWrite { witness } = verdict else {
            panic!("expected modeled hazard, got {verdict:?}");
        };
        assert!(matches!(witness.order, HazardOrder::LaterIteration(_)));
        assert_eq!(witness.write_address.base, witness.read_address.base);
        assert!(matches!(
            witness.write_address.offset,
            OffsetExpr::LoopAffine {
                stride_bytes: 8,
                constant_bytes: 8,
                ..
            }
        ));
        assert!(matches!(
            witness.read_address.offset,
            OffsetExpr::LoopAffine {
                stride_bytes: 8,
                constant_bytes: 0,
                ..
            }
        ));
    }

    #[test]
    fn dynamic_argument_offset_is_unknown() {
        let verdict = reads_precede_writes(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut f64, input: *const f64, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *input.add(i) * 2.0;
                    i += 1;
                }
            }

            pub unsafe fn caller(base: *mut f64, shift: usize, len: usize) {
                f(base.add(shift), base, len);
            }
            "#,
            "caller",
            "f",
            &[0],
            &[1],
        );

        let AccessOrderVerdict::Unknown { reasons } = verdict else {
            panic!("expected unknown verdict, got {verdict:?}");
        };
        assert!(reasons.contains(&AccessUnknownReason::UnknownOffset));
    }

    #[test]
    fn modeled_write_through_immutable_formal_is_may_be_written() {
        let verdict = never_written(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut i32, immutable: *mut i32) {
                *immutable = *out;
            }

            pub unsafe fn caller(base: *mut i32) {
                f(base, base);
            }
            "#,
            "caller",
            "f",
            &[1],
        );

        let WriteVerdict::MayBeWritten { witness } = verdict else {
            panic!("expected modeled write, got {verdict:?}");
        };
        assert_eq!(witness.address.offset, OffsetExpr::Const(0));
    }

    #[test]
    fn modeled_write_with_dynamic_actual_offset_is_may_be_written() {
        let verdict = never_written(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut i32) {
                *out = 1;
            }

            pub unsafe fn caller(base: *mut i32, shift: usize) {
                f(base.add(shift));
            }
            "#,
            "caller",
            "f",
            &[0],
        );

        let WriteVerdict::MayBeWritten { witness } = verdict else {
            panic!("expected modeled write, got {verdict:?}");
        };
        assert!(matches!(witness.address.base, BaseId::Param { .. }));
        assert_eq!(witness.address.offset, OffsetExpr::Unknown);
    }

    #[test]
    fn modeled_write_with_unresolved_actual_is_may_be_written() {
        let verdict = never_written(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut i32) {
                *out = 1;
            }

            const UNRESOLVED: *mut i32 = core::ptr::null_mut();

            pub unsafe fn caller() {
                f(UNRESOLVED);
            }
            "#,
            "caller",
            "f",
            &[0],
        );

        let WriteVerdict::MayBeWritten { witness } = verdict else {
            panic!("expected modeled write, got {verdict:?}");
        };
        assert!(matches!(
            witness.address.base,
            BaseId::Unknown {
                reason: UnknownReason::ConstantPointer,
                ..
            }
        ));
        assert_eq!(witness.address.offset, OffsetExpr::Unknown);
    }

    #[test]
    fn incomplete_relevant_write_is_unknown() {
        let verdict = never_written(
            r#"
            unsafe extern "C" {
                fn mystery(pointer: *mut i32);
            }

            #[inline(never)]
            unsafe fn f(out: *mut i32, immutable: *mut i32) {
                let _ = out;
                mystery(immutable);
            }

            pub unsafe fn caller(first: *mut i32, second: *mut i32) {
                f(first, second);
            }
            "#,
            "caller",
            "f",
            &[1],
        );

        let WriteVerdict::Unknown { reasons } = verdict else {
            panic!("expected unknown write verdict, got {verdict:?}");
        };
        assert!(reasons.contains(&AccessUnknownReason::ForeignCall));
    }

    #[test]
    fn unsupported_param_three_does_not_block_zero_one_query() {
        let verdict = reads_precede_writes(
            r#"
            unsafe extern "C" {
                fn mystery(pointer: *mut f64);
            }

            #[inline(never)]
            unsafe fn f(
                out: *mut f64,
                input: *const f64,
                len: usize,
                unsupported: *mut f64,
            ) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *input.add(i) * 2.0;
                    i += 1;
                }
                mystery(unsupported);
            }

            pub unsafe fn caller(base: *mut f64, unrelated: *mut f64, len: usize) {
                f(base, base, len, unrelated);
            }
            "#,
            "caller",
            "f",
            &[0],
            &[1],
        );

        assert_eq!(verdict, AccessOrderVerdict::Proven);
    }

    #[test]
    fn modeled_hazard_precedes_relevant_unknown() {
        let verdict = reads_precede_writes(
            r#"
            unsafe extern "C" {
                fn mystery(pointer: *mut f64);
            }

            #[inline(never)]
            unsafe fn f(out: *mut f64, input: *const f64, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *input.add(i) * 2.0;
                    i += 1;
                }
                mystery(out);
            }

            pub unsafe fn caller(base: *mut f64, len: usize) {
                f(base.add(1), base, len);
            }
            "#,
            "caller",
            "f",
            &[0],
            &[1],
        );

        assert!(matches!(
            verdict,
            AccessOrderVerdict::MayReadAfterWrite { .. }
        ));
    }

    #[test]
    fn constant_access_repetition_detects_cross_iteration_hazard() {
        let verdict = reads_precede_writes(
            r#"
            #[inline(never)]
            unsafe fn f(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out = *input;
                    i += 1;
                }
            }

            pub unsafe fn caller(base: *mut i32, len: usize) {
                f(base, base, len);
            }
            "#,
            "caller",
            "f",
            &[0],
            &[1],
        );

        let AccessOrderVerdict::MayReadAfterWrite { witness } = verdict else {
            panic!("expected repeated-access hazard, got {verdict:?}");
        };
        assert!(matches!(witness.order, HazardOrder::LaterIteration(_)));
        assert_eq!(witness.write_address.offset, OffsetExpr::Const(0));
        assert_eq!(witness.read_address.offset, OffsetExpr::Const(0));
    }

    #[test]
    fn folded_memcpy_width_proves_unrelated_parameter_never_written() {
        let verdict = never_written(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut u8,
                    source: *const u8,
                    count: usize,
                ) -> *mut u8;
            }

            unsafe fn helper(
                destination: *mut u8,
                source: *const u8,
                out: *mut u8,
                blocks: usize,
            ) {
                let _ = memcpy(destination, source, blocks.wrapping_mul(4));
            }

            pub unsafe fn target(destination: *mut u8, source: *const u8, out: *mut u8) {
                helper(destination, source, out, 2);
            }
            "#,
            "target",
            "helper",
            &[2],
        );

        assert!(matches!(verdict, WriteVerdict::NeverWritten));
    }

    #[test]
    fn symbolic_width_hazard_yields_unresolved_symbolic_width_reason() {
        let verdict = reads_precede_writes(
            r#"
            unsafe extern "C" {
                fn memset(destination: *mut u8, value: i32, count: usize) -> *mut u8;
                fn memcmp(left: *const u8, right: *const u8, count: usize) -> i32;
            }

            unsafe fn helper(buffer: *mut u8, other: *const u8, count: usize) {
                let _ = memset(buffer, 0, count);
                let _ = memcmp(buffer, other, count);
            }

            pub unsafe fn target(buffer: *mut u8, other: *const u8, count: usize) {
                helper(buffer, other, count);
            }
            "#,
            "target",
            "helper",
            &[0],
            &[0],
        );

        let AccessOrderVerdict::Unknown { reasons } = verdict else {
            panic!("expected unknown verdict, got {verdict:?}");
        };
        assert!(reasons.contains(&AccessUnknownReason::UnresolvedSymbolicWidth));
    }
}

#[cfg(test)]
mod loops {
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::def_id::LocalDefId;

    use super::super::{
        AccessEffect, AccessOrderAnalysis, AccessUnknownReason, HazardOrder, OffsetExpr,
    };
    use crate::{analyses::pointer_flow::pointer_flow_analysis, rewriter::collect_input};

    fn analyze(code: &str) -> FxHashMap<String, (LocalDefId, AccessEffect)> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let input = collect_input(tcx);
            let flows = pointer_flow_analysis(&input, &FxHashSet::default());
            let analysis = AccessOrderAnalysis::analyze(&input, &flows);

            input
                .functions
                .iter()
                .copied()
                .map(|def_id| {
                    let name = tcx.item_name(def_id.to_def_id()).to_string();
                    let effect = analysis
                        .summary(def_id)
                        .unwrap_or_else(|| panic!("missing summary for {name}"))
                        .effect
                        .clone();
                    (name, (def_id, effect))
                })
                .collect()
        })
        .unwrap()
    }

    fn function_effect<'a>(
        effects: &'a FxHashMap<String, (LocalDefId, AccessEffect)>,
        name: &str,
    ) -> (LocalDefId, &'a AccessEffect) {
        let (def_id, effect) = effects
            .get(name)
            .unwrap_or_else(|| panic!("missing function {name}"));
        (*def_id, effect)
    }

    fn loop_ids(effect: &AccessEffect) -> FxHashSet<crate::analyses::loop_recognizer::LoopId> {
        effect
            .hazards
            .iter()
            .filter_map(|hazard| match hazard.order {
                HazardOrder::SameIteration(loop_id) | HazardOrder::LaterIteration(loop_id) => {
                    Some(loop_id)
                }
                HazardOrder::Sequential => None,
            })
            .collect()
    }

    #[test]
    fn fma_read_then_write_builds_atomic_effect() {
        let effects = analyze(
            r#"
            pub unsafe fn target(
                out: *mut f64,
                left: *const f64,
                right: *const f64,
                len: usize,
            ) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *left.add(i) * *right.add(i);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert_eq!(effect.reads.len(), 2);
        assert_eq!(effect.writes.len(), 1);
        assert!(effect.invalidations.is_empty());
        assert!(effect.hazards.iter().all(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert_eq!(effect.hazards.len(), 2);
        assert!(
            effect
                .reads
                .iter()
                .chain(&effect.writes)
                .all(|footprint| matches!(
                    footprint.address.offset,
                    OffsetExpr::LoopAffine {
                        loop_id,
                        stride_bytes: 8,
                        constant_bytes: 0,
                    } if loop_id.function == target
                ))
        );
    }

    #[test]
    fn same_iteration_write_then_read_records_hazard() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) -> i32 {
                let mut result = 0;
                let mut i = 0;
                while i < len {
                    *out.add(i) = i as i32;
                    result += *input.add(i);
                    i += 1;
                }
                result
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(effect.hazards.iter().any(|hazard| {
            matches!(hazard.order, HazardOrder::SameIteration(loop_id) if loop_id.function == target)
        }));
        assert!(effect.hazards.iter().any(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert!(
            effect
                .hazards
                .iter()
                .all(|hazard| hazard.order != HazardOrder::Sequential)
        );
    }

    #[test]
    fn read_then_shifted_write_records_later_iteration_hazard() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    let value = *input.add(i);
                    *out.add(i + 1) = value;
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(effect.hazards.iter().any(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert!(!effect.hazards.iter().any(|hazard| {
            matches!(hazard.order, HazardOrder::SameIteration(loop_id) if loop_id.function == target)
        }));
        assert!(effect.writes.iter().any(|write| matches!(
            write.address.offset,
            OffsetExpr::LoopAffine {
                loop_id,
                stride_bytes: 4,
                constant_bytes: 4,
            } if loop_id.function == target
        )));
    }

    #[test]
    fn constant_parameter_access_inside_loop_is_supported() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = *input;
                    i += 1;
                }
            }
            "#,
        );
        let (_, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            effect
                .reads
                .iter()
                .any(|read| read.address.offset == OffsetExpr::Const(0))
        );
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn local_buffer_access_inside_loop_is_disjoint() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, len: usize) {
                let local = [1_i32, 2, 3, 4];
                let local_ptr = &raw const local as *const i32;
                let mut i = 0;
                while i < len {
                    *out.add(i) = *local_ptr.add(i);
                    i += 1;
                }
            }
            "#,
        );
        let (_, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(effect.reads.is_empty());
        assert_eq!(effect.writes.len(), 1);
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn affine_i_plus_one_records_constant_term() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i + 1) = *input.add(i);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(effect.writes.iter().any(|write| matches!(
            write.address.offset,
            OffsetExpr::LoopAffine {
                loop_id,
                stride_bytes: 4,
                constant_bytes: 4,
            } if loop_id.function == target
        )));
    }

    #[test]
    fn affine_nonzero_init_records_constant_term() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 1;
                while i < len {
                    *out.add(i) = *input.add(i);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            effect
                .reads
                .iter()
                .chain(&effect.writes)
                .all(|footprint| matches!(
                    footprint.address.offset,
                    OffsetExpr::LoopAffine {
                        loop_id,
                        stride_bytes: 4,
                        constant_bytes: 4,
                    } if loop_id.function == target
                ))
        );
    }

    #[test]
    fn affine_constant_cast_uses_the_cast_value() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, limit: u16) {
                let mut i: u16 = -2_i8 as u16;
                while i < limit {
                    *out.add(i as usize) = *input.add(i as usize);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            effect
                .reads
                .iter()
                .chain(&effect.writes)
                .all(|footprint| matches!(
                    footprint.address.offset,
                    OffsetExpr::LoopAffine {
                        loop_id,
                        stride_bytes: 4,
                        constant_bytes: 262_136,
                    } if loop_id.function == target
                ))
        );
    }

    #[test]
    fn sign_changing_induction_casts_reject() {
        let effects = analyze(
            r#"
            pub unsafe fn signed_to_unsigned(
                out: *mut i32,
                input: *const i32,
                len: i16,
            ) {
                let mut i: i16 = 0;
                while i < len {
                    let index = (i as u16) as usize;
                    *out.add(index) = *input.add(index);
                    i += 1;
                }
            }

            pub unsafe fn same_width_unsigned_to_signed(
                out: *mut i32,
                input: *const i32,
                len: usize,
            ) {
                let mut i: usize = 0;
                while i < len {
                    let index = (i as isize) as usize;
                    *out.add(index) = *input.add(index);
                    i += 1;
                }
            }
            "#,
        );

        for name in ["signed_to_unsigned", "same_width_unsigned_to_signed"] {
            let (def_id, effect) = function_effect(&effects, name);
            assert!(effect.contains_repetition);
            assert!(
                !loop_ids(effect)
                    .iter()
                    .any(|loop_id| loop_id.function == def_id),
                "{name} was certified"
            );
            assert_eq!(effect.reads.len(), 1);
            assert_eq!(effect.writes.len(), 1);
        }
    }

    #[test]
    fn finite_helper_composes_at_loop_phase() {
        let effects = analyze(
            r#"
            #[inline(never)]
            unsafe fn helper(destination: *mut i32, source: *const i32) {
                *destination = *source;
            }

            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    helper(out.add(i), input.add(i));
                    i += 1;
                }
            }
            "#,
        );
        let (helper, _) = function_effect(&effects, "helper");
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.writes.len(), 1);
        assert!(
            effect.reads[0]
                .call_chain
                .iter()
                .any(|frame| { frame.caller == target && frame.callee == helper })
        );
        assert_eq!(effect.reads[0].call_chain, effect.writes[0].call_chain);
        assert!(!effect.hazards.is_empty());
        assert!(effect.hazards.iter().all(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn complete_builtin_composes_at_loop_phase() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    core::ptr::copy(input.add(i), out.add(i), 1);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.writes.len(), 1);
        assert!(!effect.hazards.is_empty());
        assert!(effect.hazards.iter().all(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn complete_intrinsic_builtin_composes_at_loop_phase() {
        let effects = analyze(
            r#"
            #![feature(core_intrinsics)]
            #![allow(internal_features)]

            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    core::intrinsics::copy_nonoverlapping(input.add(i), out.add(i), 1);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.writes.len(), 1);
        assert!(!effect.hazards.is_empty());
        assert!(effect.hazards.iter().all(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn complete_foreign_builtin_composes_at_loop_phase() {
        let effects = analyze(
            r#"
            unsafe extern "C" {
                fn memcpy(
                    destination: *mut i32,
                    source: *const i32,
                    count: usize,
                ) -> *mut i32;
            }

            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    let _ = memcpy(out.add(i), input.add(i), 4);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.writes.len(), 1);
        assert!(!effect.hazards.is_empty());
        assert!(effect.hazards.iter().all(|hazard| {
            matches!(hazard.order, HazardOrder::LaterIteration(loop_id) if loop_id.function == target)
        }));
        assert!(effect.invalidations.is_empty());
    }

    #[test]
    fn loop_containing_helper_rejects_outer_atomic_effect() {
        let effects = analyze(
            r#"
            #[inline(never)]
            unsafe fn helper(destination: *mut i32, source: *const i32, len: usize) {
                let mut j = 0;
                while j < len {
                    *destination.add(j) = *source.add(j);
                    j += 1;
                }
            }

            pub unsafe fn target(
                out: *mut i32,
                input: *const i32,
                len: usize,
                repeats: usize,
            ) {
                let mut i = 0;
                while i < repeats {
                    helper(out, input, len);
                    i += 1;
                }
            }
            "#,
        );
        let (helper, _) = function_effect(&effects, "helper");
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == helper)
        );
        assert!(
            !loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
    }

    #[test]
    fn unrecognized_helper_cycle_rejects_outer_atomic_effect() {
        let effects = analyze(
            r#"
            #[inline(never)]
            unsafe fn helper(
                destination: *mut i32,
                source: *const i32,
                len: usize,
                flag: bool,
            ) {
                let mut j = 0;
                while j < len {
                    if flag {
                        *destination = *source;
                    } else {
                        *destination.add(1) = *source.add(1);
                    }
                    j += 2;
                }
            }

            pub unsafe fn target(
                out: *mut i32,
                input: *const i32,
                len: usize,
                repeats: usize,
                flag: bool,
            ) {
                let mut i = 0;
                while i < repeats {
                    helper(out, input, len, flag);
                    i += 1;
                }
            }
            "#,
        );
        let (helper, helper_effect) = function_effect(&effects, "helper");
        let (target, target_effect) = function_effect(&effects, "target");

        assert!(helper_effect.contains_repetition);
        assert!(target_effect.contains_repetition);
        assert!(loop_ids(helper_effect).is_empty());
        assert!(
            !loop_ids(target_effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert!(!target_effect.reads.is_empty());
        assert!(!target_effect.writes.is_empty());
        assert!(target_effect.invalidations.is_empty());
        assert!(target_effect.hazards.iter().any(|hazard| {
            hazard.order == HazardOrder::Sequential
                && hazard
                    .write
                    .call_chain
                    .iter()
                    .any(|frame| frame.caller == target && frame.callee == helper)
        }));
    }

    #[test]
    fn branch_early_exit_nonunit_nonlinear_variable_stride_reject() {
        let effects = analyze(
            r#"
            pub unsafe fn branch(out: *mut i32, len: usize, flag: bool) {
                let mut i = 0;
                while i < len {
                    if flag { *out.add(i) = 1; } else { *out.add(i) = 2; }
                    i += 1;
                }
            }

            pub unsafe fn early_exit(out: *mut i32, len: usize, stop: usize) {
                let mut i = 0;
                while i < len {
                    if i == stop { break; }
                    *out.add(i) = 1;
                    i += 1;
                }
            }

            pub unsafe fn nonunit(out: *mut i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i) = 1;
                    i += 2;
                }
            }

            pub unsafe fn nonlinear(out: *mut i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i * i) = 1;
                    i += 1;
                }
            }

            pub unsafe fn variable_stride(out: *mut i32, len: usize, stride: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i * stride) = 1;
                    i += 1;
                }
            }

            pub unsafe fn noninteger_cast(out: *mut i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add((i as f64) as usize) = 1;
                    i += 1;
                }
            }
            "#,
        );

        for name in [
            "branch",
            "early_exit",
            "nonunit",
            "nonlinear",
            "variable_stride",
            "noninteger_cast",
        ] {
            let (def_id, effect) = function_effect(&effects, name);
            assert!(effect.contains_repetition, "{name} lost its CFG cycle");
            assert!(
                !loop_ids(effect)
                    .iter()
                    .any(|loop_id| loop_id.function == def_id),
                "{name} was certified"
            );
            assert!(!effect.writes.is_empty(), "{name} lost its ordinary write");
        }
    }

    #[test]
    fn reassigned_formal_pointer_rejects() {
        let effects = analyze(
            r#"
            pub unsafe fn target(mut out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out = *input.add(i);
                    out = out.add(1);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            !loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert!(!effect.reads.is_empty());
        assert!(!effect.writes.is_empty());
    }

    #[test]
    fn walking_pointer_rejects() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut cursor = out;
                let mut i = 0;
                while i < len {
                    *cursor = *input.add(i);
                    cursor = cursor.add(1);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            !loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert!(!effect.reads.is_empty());
        assert!(!effect.writes.is_empty());
    }

    #[test]
    fn nested_loop_rejects() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, rows: usize, cols: usize) {
                let mut i = 0;
                while i < rows {
                    let mut j = 0;
                    while j < cols {
                        *out = *input;
                        j += 1;
                    }
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            !loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.writes.len(), 1);
    }

    #[test]
    fn unknown_call_rejects() {
        let effects = analyze(
            r#"
            unsafe extern "C" {
                fn mystery(pointer: *mut i32);
            }

            pub unsafe fn target(out: *mut i32, len: usize) {
                let mut i = 0;
                while i < len {
                    mystery(out.add(i));
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            !loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert!(
            effect
                .invalidations
                .iter()
                .any(|invalidation| { invalidation.reason == AccessUnknownReason::ForeignCall })
        );
    }

    #[test]
    fn cleanup_successor_rejects_atomic_replacement_and_remains_reachable() {
        let (target, effect, has_cleanup_invalidation) = ::utils::compilation::run_compiler_on_str(
            r#"
                struct Guard(*mut i32);

                impl Drop for Guard {
                    fn drop(&mut self) {
                        unsafe { *self.0 = 9; }
                    }
                }

                #[inline(never)]
                unsafe fn helper(destination: *mut i32, source: *const i32) {
                    *destination = *source;
                }

                pub unsafe fn target(
                    out: *mut i32,
                    input: *const i32,
                    cleanup: *mut i32,
                    len: usize,
                ) {
                    let guard = Guard(cleanup);
                    let mut i = 0;
                    while i < len {
                        helper(out.add(i), input.add(i));
                        i += 1;
                    }
                    core::mem::forget(guard);
                }
                "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let analysis = AccessOrderAnalysis::analyze(&input, &flows);
                let target = input
                    .functions
                    .iter()
                    .copied()
                    .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == "target")
                    .unwrap();
                let effect = analysis.summary(target).unwrap().effect.clone();
                let body = tcx.mir_drops_elaborated_and_const_checked(target).borrow();
                let has_cleanup_invalidation = effect.invalidations.iter().any(|invalidation| {
                    body.basic_blocks[invalidation.location.block].is_cleanup
                        && invalidation.reason == AccessUnknownReason::UnsupportedTerminator
                });
                (target, effect, has_cleanup_invalidation)
            },
        )
        .unwrap();

        assert!(effect.contains_repetition);
        assert!(
            !loop_ids(&effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert!(!effect.reads.is_empty());
        assert!(!effect.writes.is_empty());
        // Drop terminators deliberately contribute no effect: Crat's input
        // domain is C2Rust output, which has no user `Drop` impls, so drop
        // glue only frees the droppee's own allocation. This waives the
        // hostile case that `Guard` models here — a user `Drop` writing
        // through a raw-pointer field. See
        // docs/superpowers/specs/2026-08-17-drop-terminator-narrowing-design.md.
        assert!(!has_cleanup_invalidation);
    }

    #[test]
    fn vec_local_drop_does_not_invalidate_parameters() {
        let effect = ::utils::compilation::run_compiler_on_str(
            r#"
                pub unsafe fn target(out: *mut i32, input: *const i32) {
                    let scratch: Vec<u8> = ::std::vec::from_elem(0u8, 16);
                    *out = *input + scratch.len() as i32;
                }
                "#,
            |tcx| {
                let input = collect_input(tcx);
                let flows = pointer_flow_analysis(&input, &FxHashSet::default());
                let analysis = AccessOrderAnalysis::analyze(&input, &flows);
                let target = input
                    .functions
                    .iter()
                    .copied()
                    .find(|def_id| tcx.item_name(def_id.to_def_id()).as_str() == "target")
                    .unwrap();
                analysis.summary(target).unwrap().effect.clone()
            },
        )
        .unwrap();

        // The `Vec<u8>` local produces a MIR Drop terminator. Before the
        // Drop-terminator narrowing this emitted a `ParamScope::All`
        // invalidation that poisoned the entire summary. `std::vec::from_elem`
        // and `Vec::len` still produce `UnsupportedCall` invalidations, which
        // is a known, separate blocker out of scope for this change.
        assert!(
            !effect
                .invalidations
                .iter()
                .any(|invalidation| invalidation.reason
                    == AccessUnknownReason::UnsupportedTerminator),
            "expected no Drop-terminator invalidation, got {:?}",
            effect.invalidations
        );
        assert!(!effect.reads.is_empty());
        assert!(!effect.writes.is_empty());
    }

    #[test]
    fn rejected_loop_falls_back_to_all_ordinary_events() {
        let effects = analyze(
            r#"
            pub unsafe fn target(out: *mut i32, input: *const i32, len: usize) {
                let mut i = 0;
                while i < len {
                    *out.add(i * i) = *input.add(i * i);
                    i += 1;
                }
            }
            "#,
        );
        let (target, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert!(
            !loop_ids(effect)
                .iter()
                .any(|loop_id| loop_id.function == target)
        );
        assert_eq!(effect.reads.len(), 1);
        assert_eq!(effect.writes.len(), 1);
        assert!(
            effect
                .hazards
                .iter()
                .any(|hazard| hazard.order == HazardOrder::Sequential)
        );
    }

    #[test]
    fn sequential_atomic_loops_compose() {
        let effects = analyze(
            r#"
            pub unsafe fn target(
                first: *mut i32,
                second: *mut i32,
                input: *const i32,
                len: usize,
            ) {
                let mut i = 0;
                while i < len {
                    *first.add(i) = *input.add(i);
                    i += 1;
                }

                let mut j = 0;
                while j < len {
                    *second.add(j) = *first.add(j);
                    j += 1;
                }
            }
            "#,
        );
        let (_, effect) = function_effect(&effects, "target");

        assert!(effect.contains_repetition);
        assert_eq!(loop_ids(effect).len(), 2);
        assert!(effect.hazards.iter().any(|hazard| {
            hazard.order == HazardOrder::Sequential
                && hazard.write.address.origin == 0
                && hazard.read.address.origin == 0
        }));
    }
}
