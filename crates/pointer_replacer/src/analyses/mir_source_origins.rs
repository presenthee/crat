//! Source-level binding and expression evidence for MIR locals.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, Node};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, Local, Location},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;
use utils::ir::{hir_to_thir::HirToThir, thir_to_mir::ThirToMir};

use super::mir_local_facts::{
    MirLocalDefinition, MirLocalDefinitionKind, MirLocalFacts, collect_mir_local_facts,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BindingOriginKind {
    Direct,
    Copy,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BindingOrigin {
    pub hir_id: HirId,
    pub source_local: Local,
    pub kind: BindingOriginKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BindingOriginIssue {
    MixedDefinitions,
    CopyCycle,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpressionOrigin {
    pub hir_id: HirId,
    pub covered_definitions: Vec<Location>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct MirLocalSourceEvidence {
    pub definitions: Vec<MirLocalDefinition>,
    pub binding_origins: Vec<BindingOrigin>,
    pub binding_issue: Option<BindingOriginIssue>,
    pub expression_origins: Vec<ExpressionOrigin>,
}

#[derive(Clone, Copy)]
enum ResolutionState {
    Unvisited,
    Visiting,
    Resolved,
}

fn resolve_binding_origins(
    facts: &MirLocalFacts,
    direct_bindings: &IndexVec<Local, Vec<HirId>>,
) -> IndexVec<Local, MirLocalSourceEvidence> {
    fn resolve(
        local: Local,
        facts: &MirLocalFacts,
        direct_bindings: &IndexVec<Local, Vec<HirId>>,
        states: &mut IndexVec<Local, ResolutionState>,
        evidence: &mut IndexVec<Local, MirLocalSourceEvidence>,
    ) -> MirLocalSourceEvidence {
        match states[local] {
            ResolutionState::Resolved => return evidence[local].clone(),
            ResolutionState::Visiting => {
                return MirLocalSourceEvidence {
                    definitions: facts.definitions[local].clone(),
                    binding_issue: Some(BindingOriginIssue::CopyCycle),
                    ..MirLocalSourceEvidence::default()
                };
            }
            ResolutionState::Unvisited => {}
        }

        states[local] = ResolutionState::Visiting;
        let mut result = MirLocalSourceEvidence {
            definitions: facts.definitions[local].clone(),
            ..MirLocalSourceEvidence::default()
        };

        if !direct_bindings[local].is_empty() {
            result.binding_origins = direct_bindings[local]
                .iter()
                .copied()
                .map(|hir_id| BindingOrigin {
                    hir_id,
                    source_local: local,
                    kind: BindingOriginKind::Direct,
                })
                .collect();
        } else {
            let has_copy = result
                .definitions
                .iter()
                .any(|definition| matches!(definition.kind, MirLocalDefinitionKind::Copy(_)));
            let has_non_copy = result
                .definitions
                .iter()
                .any(|definition| !matches!(definition.kind, MirLocalDefinitionKind::Copy(_)));
            if has_copy && has_non_copy {
                result.binding_issue = Some(BindingOriginIssue::MixedDefinitions);
            }

            for definition in &result.definitions {
                let MirLocalDefinitionKind::Copy(source) = definition.kind else {
                    continue;
                };
                let source_result = resolve(source, facts, direct_bindings, states, evidence);
                result.binding_origins.extend(source_result.binding_origins);
                if source_result.binding_issue == Some(BindingOriginIssue::CopyCycle) {
                    result.binding_issue = Some(BindingOriginIssue::CopyCycle);
                } else if source_result.binding_issue == Some(BindingOriginIssue::MixedDefinitions)
                    && result.binding_issue.is_none()
                {
                    result.binding_issue = Some(BindingOriginIssue::MixedDefinitions);
                }
            }
            for origin in &mut result.binding_origins {
                origin.kind = BindingOriginKind::Copy;
            }
        }

        result
            .binding_origins
            .sort_by_key(|origin| (origin.hir_id.local_id.index(), origin.source_local.index()));
        result
            .binding_origins
            .dedup_by_key(|origin| (origin.hir_id, origin.source_local));
        states[local] = ResolutionState::Resolved;
        evidence[local] = result.clone();
        result
    }

    assert_eq!(facts.definitions.len(), direct_bindings.len());
    let mut states = IndexVec::from_elem_n(ResolutionState::Unvisited, facts.definitions.len());
    let mut evidence =
        IndexVec::from_elem_n(MirLocalSourceEvidence::default(), facts.definitions.len());
    for local in facts.definitions.indices() {
        resolve(local, facts, direct_bindings, &mut states, &mut evidence);
    }
    evidence
}

pub(crate) struct MirSourceOrigins {
    hir_to_thir: HirToThir,
    by_function: FxHashMap<LocalDefId, IndexVec<Local, MirLocalSourceEvidence>>,
}

impl MirSourceOrigins {
    pub(crate) fn new(tcx: TyCtxt<'_>) -> Self {
        Self {
            hir_to_thir: utils::ir::hir_to_thir::map_hir_to_thir(tcx),
            by_function: FxHashMap::default(),
        }
    }

    pub(crate) fn analyze_function<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        body: &Body<'tcx>,
        thir_to_mir: &ThirToMir,
    ) {
        if self.by_function.contains_key(&def_id) {
            return;
        }

        let facts = collect_mir_local_facts(body);
        let mut direct_bindings = IndexVec::from_elem_n(Vec::new(), body.local_decls.len());
        for (&hir_id, &local) in &thir_to_mir.binding_to_local {
            if local.index() < direct_bindings.len() {
                direct_bindings[local].push(hir_id);
            }
        }
        for hir_ids in &mut direct_bindings {
            hir_ids.sort_by_key(|hir_id| hir_id.local_id.index());
            hir_ids.dedup();
        }
        let mut evidence = resolve_binding_origins(&facts, &direct_bindings);

        let mut definition_locals = FxHashMap::<Location, Option<Local>>::default();
        for (local, definitions) in facts.definitions.iter_enumerated() {
            for definition in definitions {
                if matches!(definition.kind, MirLocalDefinitionKind::Unsupported) {
                    continue;
                }
                definition_locals
                    .entry(definition.location)
                    .and_modify(|existing| {
                        if *existing != Some(local) {
                            *existing = None;
                        }
                    })
                    .or_insert(Some(local));
            }
        }

        let mut direct_expression_seeds = FxHashMap::<(Local, Location), Vec<HirId>>::default();
        for (&hir_id, &thir_id) in &self.hir_to_thir.exprs {
            if hir_id.owner.def_id != def_id {
                continue;
            }
            let Some(locations) = thir_to_mir.expr_to_locs.get(&thir_id) else {
                continue;
            };
            let Node::Expr(hir_expr) = tcx.hir_node(hir_id) else {
                continue;
            };
            for &location in locations {
                let Some(Some(local)) = definition_locals.get(&location) else {
                    continue;
                };
                if tcx.typeck(hir_id.owner).expr_ty(hir_expr) != body.local_decls[*local].ty {
                    continue;
                }
                direct_expression_seeds
                    .entry((*local, location))
                    .or_default()
                    .push(hir_id);
            }
        }
        for hir_ids in direct_expression_seeds.values_mut() {
            hir_ids.sort_by_key(|hir_id| hir_id.local_id.index());
            hir_ids.dedup();
        }

        #[derive(Clone, Copy)]
        enum ExpressionResolutionState {
            Unvisited,
            Visiting,
            Resolved,
        }

        fn resolve_expressions(
            local: Local,
            facts: &MirLocalFacts,
            direct_expression_seeds: &FxHashMap<(Local, Location), Vec<HirId>>,
            binding_evidence: &IndexVec<Local, MirLocalSourceEvidence>,
            states: &mut IndexVec<Local, ExpressionResolutionState>,
            resolved: &mut IndexVec<Local, Vec<ExpressionOrigin>>,
        ) -> Vec<ExpressionOrigin> {
            match states[local] {
                ExpressionResolutionState::Resolved => return resolved[local].clone(),
                ExpressionResolutionState::Visiting => return Vec::new(),
                ExpressionResolutionState::Unvisited => {}
            }
            states[local] = ExpressionResolutionState::Visiting;

            if binding_evidence[local].binding_issue.is_none()
                && binding_evidence[local].binding_origins.len() == 1
            {
                states[local] = ExpressionResolutionState::Resolved;
                return Vec::new();
            }

            let mut by_hir = FxHashMap::<HirId, Vec<Location>>::default();
            for definition in &facts.definitions[local] {
                match definition.kind {
                    MirLocalDefinitionKind::Value => {
                        if let Some(hir_ids) =
                            direct_expression_seeds.get(&(local, definition.location))
                        {
                            for &hir_id in hir_ids {
                                by_hir.entry(hir_id).or_default().push(definition.location);
                            }
                        }
                    }
                    MirLocalDefinitionKind::Copy(source) => {
                        for origin in resolve_expressions(
                            source,
                            facts,
                            direct_expression_seeds,
                            binding_evidence,
                            states,
                            resolved,
                        ) {
                            by_hir
                                .entry(origin.hir_id)
                                .or_default()
                                .push(definition.location);
                        }
                    }
                    MirLocalDefinitionKind::Unsupported => {}
                }
            }

            let mut origins = by_hir
                .into_iter()
                .map(|(hir_id, mut covered_definitions)| {
                    covered_definitions
                        .sort_by_key(|location| (location.block.index(), location.statement_index));
                    covered_definitions.dedup();
                    ExpressionOrigin {
                        hir_id,
                        covered_definitions,
                    }
                })
                .collect::<Vec<_>>();
            origins.sort_by_key(|origin| origin.hir_id.local_id.index());
            states[local] = ExpressionResolutionState::Resolved;
            resolved[local] = origins.clone();
            origins
        }

        let binding_evidence = evidence.clone();
        let mut expression_states =
            IndexVec::from_elem_n(ExpressionResolutionState::Unvisited, body.local_decls.len());
        let mut expression_origins = IndexVec::from_elem_n(Vec::new(), body.local_decls.len());
        for local in body.local_decls.indices() {
            evidence[local].expression_origins = resolve_expressions(
                local,
                &facts,
                &direct_expression_seeds,
                &binding_evidence,
                &mut expression_states,
                &mut expression_origins,
            );
        }

        self.by_function.insert(def_id, evidence);
    }

    pub(crate) fn evidence(
        &self,
        def_id: LocalDefId,
        local: Local,
    ) -> Option<&MirLocalSourceEvidence> {
        self.by_function
            .get(&def_id)
            .and_then(|evidence| evidence.get(local))
    }
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ExprKind, HirId, Node};
    use rustc_index::IndexVec;
    use rustc_middle::mir::{BasicBlock, Local, Location};

    use super::{BindingOriginIssue, BindingOriginKind, MirSourceOrigins, resolve_binding_origins};
    use crate::{
        analyses::mir_local_facts::{MirLocalDefinition, MirLocalDefinitionKind, MirLocalFacts},
        rewriter::collect_input,
    };

    fn location(statement_index: usize) -> Location {
        Location {
            block: BasicBlock::from_usize(0),
            statement_index,
        }
    }

    fn facts(
        local_count: usize,
        definitions: impl IntoIterator<Item = (Local, Vec<MirLocalDefinitionKind>)>,
    ) -> MirLocalFacts {
        let mut facts = MirLocalFacts {
            definitions: IndexVec::from_elem_n(Vec::new(), local_count),
        };
        let mut statement_index = 0;
        for (local, kinds) in definitions {
            for kind in kinds {
                facts.definitions[local].push(MirLocalDefinition {
                    location: location(statement_index),
                    kind,
                });
                statement_index += 1;
            }
        }
        facts
    }

    fn with_two_bindings(test: impl FnOnce(HirId, HirId, Local, Local) + Send) {
        ::utils::compilation::run_compiler_on_str(
            "unsafe fn f(p: *mut i32, q: *mut i32) {}",
            |tcx| {
                let program = collect_input(tcx);
                let function = program.functions[0];
                let mapping = utils::ir::map_thir_to_mir(function, false, tcx);
                let mut bindings = mapping
                    .binding_to_local
                    .into_iter()
                    .collect::<Vec<(HirId, Local)>>();
                bindings.sort_by_key(|(_, local)| local.index());
                assert_eq!(bindings.len(), 2);
                test(bindings[0].0, bindings[1].0, bindings[0].1, bindings[1].1);
            },
        )
        .unwrap();
    }

    fn direct_bindings(
        local_count: usize,
        bindings: impl IntoIterator<Item = (Local, HirId)>,
    ) -> IndexVec<Local, Vec<HirId>> {
        let mut direct = IndexVec::from_elem_n(Vec::new(), local_count);
        for (local, hir_id) in bindings {
            direct[local].push(hir_id);
        }
        direct
    }

    #[test]
    fn binding_transitive_copy_resolves_to_one_endpoint() {
        with_two_bindings(|p_hir, _, p, _| {
            let middle = Local::from_usize(3);
            let destination = Local::from_usize(4);
            let facts = facts(
                5,
                [
                    (middle, vec![MirLocalDefinitionKind::Copy(p)]),
                    (destination, vec![MirLocalDefinitionKind::Copy(middle)]),
                ],
            );
            let resolved = resolve_binding_origins(&facts, &direct_bindings(5, [(p, p_hir)]));

            assert_eq!(resolved[destination].binding_origins.len(), 1);
            assert_eq!(
                resolved[destination].binding_origins[0].kind,
                BindingOriginKind::Copy
            );
            assert_eq!(resolved[destination].binding_origins[0].source_local, p);
            assert_eq!(resolved[destination].binding_issue, None);
        });
    }

    #[test]
    fn binding_divergent_copies_preserve_both_endpoints() {
        with_two_bindings(|p_hir, q_hir, p, q| {
            let destination = Local::from_usize(3);
            let facts = facts(
                4,
                [(
                    destination,
                    vec![
                        MirLocalDefinitionKind::Copy(p),
                        MirLocalDefinitionKind::Copy(q),
                    ],
                )],
            );
            let resolved =
                resolve_binding_origins(&facts, &direct_bindings(4, [(p, p_hir), (q, q_hir)]));

            assert_eq!(resolved[destination].binding_origins.len(), 2);
            assert_eq!(resolved[destination].binding_issue, None);
        });
    }

    #[test]
    fn binding_copy_cycle_is_reported() {
        with_two_bindings(|_, _, _, _| {
            let left = Local::from_usize(3);
            let right = Local::from_usize(4);
            let facts = facts(
                5,
                [
                    (left, vec![MirLocalDefinitionKind::Copy(right)]),
                    (right, vec![MirLocalDefinitionKind::Copy(left)]),
                ],
            );
            let resolved = resolve_binding_origins(&facts, &direct_bindings(5, []));

            assert_eq!(
                resolved[left].binding_issue,
                Some(BindingOriginIssue::CopyCycle)
            );
            assert!(resolved[left].binding_origins.is_empty());
        });
    }

    #[test]
    fn binding_mixed_definitions_preserve_endpoint_and_issue() {
        with_two_bindings(|p_hir, _, p, _| {
            let destination = Local::from_usize(3);
            let facts = facts(
                4,
                [(
                    destination,
                    vec![
                        MirLocalDefinitionKind::Copy(p),
                        MirLocalDefinitionKind::Value,
                    ],
                )],
            );
            let resolved = resolve_binding_origins(&facts, &direct_bindings(4, [(p, p_hir)]));

            assert_eq!(resolved[destination].binding_origins.len(), 1);
            assert_eq!(
                resolved[destination].binding_issue,
                Some(BindingOriginIssue::MixedDefinitions)
            );
        });
    }

    #[test]
    fn expression_offset_method_is_preserved() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn consume(_: *mut i32) {}
            unsafe fn offset(p: *mut i32, i: isize) {
                unsafe { consume(p.offset(i)) };
            }
            "#,
            |tcx| {
                let program = collect_input(tcx);
                let function = program
                    .functions
                    .iter()
                    .copied()
                    .find(|&function| tcx.item_name(function.to_def_id()).as_str() == "offset")
                    .unwrap();
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let thir_to_mir = utils::ir::map_thir_to_mir(function, false, tcx);
                let mut origins = MirSourceOrigins::new(tcx);
                origins.analyze_function(tcx, function, &body, &thir_to_mir);

                assert!(body.local_decls.indices().any(|local| {
                    origins.evidence(function, local).is_some_and(|evidence| {
                        evidence.expression_origins.iter().any(|origin| {
                            matches!(
                                tcx.hir_node(origin.hir_id),
                                Node::Expr(expr)
                                    if matches!(
                                        expr.kind,
                                        ExprKind::MethodCall(segment, ..)
                                            if segment.ident.name.as_str() == "offset"
                                    )
                            )
                        })
                    })
                }));
            },
        )
        .unwrap();
    }

    #[test]
    fn expression_explicit_cast_preserves_offset_and_cast_candidates() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn consume(_: *const i32) {}
            unsafe fn explicit_cast(p: *mut i32, i: isize) {
                unsafe { consume(p.offset(i) as *const i32) };
            }
            "#,
            |tcx| {
                let program = collect_input(tcx);
                let function = program
                    .functions
                    .iter()
                    .copied()
                    .find(|&function| {
                        tcx.item_name(function.to_def_id()).as_str() == "explicit_cast"
                    })
                    .unwrap();
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let thir_to_mir = utils::ir::map_thir_to_mir(function, false, tcx);
                let mut origins = MirSourceOrigins::new(tcx);
                origins.analyze_function(tcx, function, &body, &thir_to_mir);

                let mut saw_offset = false;
                let mut saw_cast = false;
                for local in body.local_decls.indices() {
                    let Some(evidence) = origins.evidence(function, local) else {
                        continue;
                    };
                    for origin in &evidence.expression_origins {
                        let Node::Expr(expr) = tcx.hir_node(origin.hir_id) else {
                            continue;
                        };
                        saw_offset |= matches!(
                            expr.kind,
                            ExprKind::MethodCall(segment, ..)
                                if segment.ident.name.as_str() == "offset"
                        );
                        saw_cast |= matches!(expr.kind, ExprKind::Cast(..));
                    }
                }
                assert!(saw_offset);
                assert!(saw_cast);
            },
        )
        .unwrap();
    }

    #[test]
    fn expression_implicit_adjustment_does_not_change_origin_type() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn consume(_: *const i32) {}
            unsafe fn implicit_adjustment(p: *mut i32) {
                unsafe { consume(p) };
            }
            "#,
            |tcx| {
                let program = collect_input(tcx);
                let function = program
                    .functions
                    .iter()
                    .copied()
                    .find(|&function| {
                        tcx.item_name(function.to_def_id()).as_str() == "implicit_adjustment"
                    })
                    .unwrap();
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let thir_to_mir = utils::ir::map_thir_to_mir(function, false, tcx);
                let mut origins = MirSourceOrigins::new(tcx);
                origins.analyze_function(tcx, function, &body, &thir_to_mir);

                for local in body.local_decls.indices() {
                    let Some(evidence) = origins.evidence(function, local) else {
                        continue;
                    };
                    for origin in &evidence.expression_origins {
                        let Node::Expr(expr) = tcx.hir_node(origin.hir_id) else {
                            continue;
                        };
                        assert_eq!(
                            tcx.typeck(expr.hir_id.owner).expr_ty(expr),
                            body.local_decls[local].ty
                        );
                    }
                }
            },
        )
        .unwrap();
    }
}
