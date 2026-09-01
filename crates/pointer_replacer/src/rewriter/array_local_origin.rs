//! Classification and reporting support for anonymous array-local members.

use rustc_ast::{
    Crate, Expr,
    visit::{self, Visitor},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ExprKind, HirId, Node};
use rustc_middle::{
    mir::{Body, Local, Location},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;
use utils::ir::{AstToHir, thir_to_mir::ThirToMir};

use crate::{
    analyses::{
        array_local_provenance::{ArrayLocalProvenance, RewriteGroup},
        mir_local_facts::MirLocalDefinitionKind,
        mir_source_origins::{
            BindingOriginIssue, BindingOriginKind, MirLocalSourceEvidence, MirSourceOrigins,
        },
    },
    rewriter::array_local_trace::{RewriteTrace, TraceDecision, TraceStage, TraceSubject},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExpressionShape {
    OffsetLike,
    PointerArithmetic,
    Cast,
    RawAddress,
    Path,
    OtherCall,
    Other,
}

impl ExpressionShape {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            ExpressionShape::OffsetLike => "offset",
            ExpressionShape::PointerArithmetic => "pointer-arithmetic",
            ExpressionShape::Cast => "cast",
            ExpressionShape::RawAddress => "raw-address",
            ExpressionShape::Path => "path",
            ExpressionShape::OtherCall => "call",
            ExpressionShape::Other => "other",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AnonymousOriginFailure {
    MultipleBindingOrigins,
    MixedBindingAndExpressionDefinitions,
    PartialExpressionCoverage,
    MultipleExpressionOrigins,
    NoExpressionEvidence,
    UnsupportedDefinitions,
    CopyCycle,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AnonymousMemberStatus {
    BindingCopy {
        binding_hir_id: HirId,
        source_local: Local,
        represented: bool,
    },
    UniqueAstExpression {
        hir_id: HirId,
        definitions: Vec<Location>,
        shape: ExpressionShape,
    },
    UniqueHirExpressionWithoutAst {
        hir_id: HirId,
        definitions: Vec<Location>,
        shape: ExpressionShape,
    },
    Unresolved(AnonymousOriginFailure),
}

fn expression_shape(tcx: TyCtxt<'_>, hir_id: HirId) -> ExpressionShape {
    let Node::Expr(hir_expr) = tcx.hir_node(hir_id) else {
        return ExpressionShape::Other;
    };
    match hir_expr.kind {
        ExprKind::MethodCall(segment, ..) => match segment.ident.name.as_str() {
            "offset" | "wrapping_offset" | "byte_offset" | "wrapping_byte_offset" => {
                ExpressionShape::OffsetLike
            }
            "add" | "sub" | "wrapping_add" | "wrapping_sub" | "byte_add" | "byte_sub"
            | "wrapping_byte_add" | "wrapping_byte_sub" => ExpressionShape::PointerArithmetic,
            _ => ExpressionShape::OtherCall,
        },
        ExprKind::Call(..) => ExpressionShape::OtherCall,
        ExprKind::Cast(..) => ExpressionShape::Cast,
        ExprKind::AddrOf(..) => ExpressionShape::RawAddress,
        ExprKind::Path(..) => ExpressionShape::Path,
        _ => ExpressionShape::Other,
    }
}

pub(crate) fn classify_anonymous_member(
    evidence: &MirLocalSourceEvidence,
    ast_expression_hir_ids: &FxHashSet<HirId>,
    represented_bindings: &FxHashSet<HirId>,
    tcx: TyCtxt<'_>,
) -> AnonymousMemberStatus {
    match evidence.binding_issue {
        Some(BindingOriginIssue::MixedDefinitions) => {
            return AnonymousMemberStatus::Unresolved(
                AnonymousOriginFailure::MixedBindingAndExpressionDefinitions,
            );
        }
        Some(BindingOriginIssue::CopyCycle) => {
            return AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::CopyCycle);
        }
        None => {}
    }

    if evidence.binding_origins.len() > 1 {
        return AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::MultipleBindingOrigins);
    }
    if let [origin] = evidence.binding_origins.as_slice()
        && origin.kind == BindingOriginKind::Copy
    {
        return AnonymousMemberStatus::BindingCopy {
            binding_hir_id: origin.hir_id,
            source_local: origin.source_local,
            represented: represented_bindings.contains(&origin.hir_id),
        };
    }

    if evidence
        .definitions
        .iter()
        .any(|definition| definition.kind == MirLocalDefinitionKind::Unsupported)
    {
        return AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::UnsupportedDefinitions);
    }

    let mut definition_locations = evidence
        .definitions
        .iter()
        .map(|definition| definition.location)
        .collect::<Vec<_>>();
    definition_locations.sort_by_key(|location| (location.block.index(), location.statement_index));
    definition_locations.dedup();

    let fully_covering = evidence
        .expression_origins
        .iter()
        .filter(|origin| {
            let mut covered = origin.covered_definitions.clone();
            covered.sort_by_key(|location| (location.block.index(), location.statement_index));
            covered.dedup();
            covered == definition_locations
        })
        .collect::<Vec<_>>();

    match fully_covering.as_slice() {
        [origin] => {
            let shape = expression_shape(tcx, origin.hir_id);
            if ast_expression_hir_ids.contains(&origin.hir_id) {
                AnonymousMemberStatus::UniqueAstExpression {
                    hir_id: origin.hir_id,
                    definitions: origin.covered_definitions.clone(),
                    shape,
                }
            } else {
                AnonymousMemberStatus::UniqueHirExpressionWithoutAst {
                    hir_id: origin.hir_id,
                    definitions: origin.covered_definitions.clone(),
                    shape,
                }
            }
        }
        [_, _, ..] => {
            AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::MultipleExpressionOrigins)
        }
        [] if !evidence.expression_origins.is_empty() => {
            AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::PartialExpressionCoverage)
        }
        [] => AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::NoExpressionEvidence),
    }
}

pub(crate) fn collect_ast_expression_hir_ids(
    krate: &Crate,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
) -> FxHashSet<HirId> {
    struct ExpressionCollector<'map, 'tcx> {
        ast_to_hir: &'map AstToHir,
        tcx: TyCtxt<'tcx>,
        hir_ids: FxHashSet<HirId>,
    }

    impl<'ast> Visitor<'ast> for ExpressionCollector<'_, '_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) {
                self.hir_ids.insert(hir_expr.hir_id);
            }
            visit::walk_expr(self, expr);
        }
    }

    let mut collector = ExpressionCollector {
        ast_to_hir,
        tcx,
        hir_ids: FxHashSet::default(),
    };
    collector.visit_crate(krate);
    collector.hir_ids
}

pub(crate) struct AnonymousOriginReporter {
    origins: MirSourceOrigins,
    ast_expression_hir_ids: FxHashSet<HirId>,
}

impl AnonymousOriginReporter {
    pub(crate) fn new(krate: &Crate, ast_to_hir: &AstToHir, tcx: TyCtxt<'_>) -> Self {
        Self {
            origins: MirSourceOrigins::new(tcx),
            ast_expression_hir_ids: collect_ast_expression_hir_ids(krate, ast_to_hir, tcx),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_ready_group<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        body: &Body<'tcx>,
        thir_to_mir: &ThirToMir,
        provenance: &ArrayLocalProvenance,
        group: &RewriteGroup,
        local_to_hir: &FxHashMap<Local, HirId>,
        trace: &mut RewriteTrace,
    ) {
        if !local_to_hir.contains_key(&group.base_local) {
            return;
        }

        let mut represented_bindings = FxHashSet::default();
        let mut anonymous_occurrences = Vec::new();
        for &slot_index in &group.members {
            let Some(info) = provenance.slot_table().slot_infos.get(slot_index) else {
                continue;
            };
            if !info.path.is_empty()
                || !matches!(
                    body.local_decls[info.root].ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(..)
                )
            {
                continue;
            }
            if let Some(&hir_id) = local_to_hir.get(&info.root) {
                represented_bindings.insert(hir_id);
            } else if info.root != group.base_local {
                anonymous_occurrences.push(info.root);
            }
        }
        if anonymous_occurrences.is_empty() {
            return;
        }

        self.origins
            .analyze_function(tcx, def_id, body, thir_to_mir);
        let occurrence_count = anonymous_occurrences.len();
        anonymous_occurrences.sort_by_key(|local| local.index());
        anonymous_occurrences.dedup();

        let mut unique_ast_hir_ids = FxHashSet::default();
        let mut all_unique_ast = true;
        for &local in &anonymous_occurrences {
            let missing = MirLocalSourceEvidence::default();
            let evidence = self.origins.evidence(def_id, local).unwrap_or(&missing);
            let status = classify_anonymous_member(
                evidence,
                &self.ast_expression_hir_ids,
                &represented_bindings,
                tcx,
            );
            let (decision, reason) = match &status {
                AnonymousMemberStatus::BindingCopy {
                    source_local,
                    represented,
                    ..
                } => (
                    TraceDecision::Skipped,
                    format!(
                        "origin=binding-copy source={source_local:?} represented={}",
                        if *represented { "yes" } else { "no" }
                    ),
                ),
                AnonymousMemberStatus::UniqueAstExpression {
                    hir_id,
                    definitions,
                    shape,
                } => {
                    unique_ast_hir_ids.insert(*hir_id);
                    (
                        TraceDecision::Kept,
                        format!(
                            "origin=expression ast=yes shape={} definitions={} hir={}",
                            shape.as_str(),
                            definitions.len(),
                            hir_id.local_id.index()
                        ),
                    )
                }
                AnonymousMemberStatus::UniqueHirExpressionWithoutAst {
                    hir_id,
                    definitions,
                    shape,
                } => (
                    TraceDecision::Dropped,
                    format!(
                        "origin=expression ast=no shape={} definitions={} hir={}",
                        shape.as_str(),
                        definitions.len(),
                        hir_id.local_id.index()
                    ),
                ),
                AnonymousMemberStatus::Unresolved(failure) => {
                    let reason = match failure {
                        AnonymousOriginFailure::MultipleBindingOrigins => {
                            "origin=unresolved reason=multiple-bindings".to_string()
                        }
                        AnonymousOriginFailure::MixedBindingAndExpressionDefinitions => {
                            "origin=unresolved reason=mixed-definitions".to_string()
                        }
                        AnonymousOriginFailure::PartialExpressionCoverage => {
                            "origin=unresolved reason=partial-expression".to_string()
                        }
                        AnonymousOriginFailure::MultipleExpressionOrigins => format!(
                            "origin=unresolved reason=multiple-expressions candidates={}",
                            evidence.expression_origins.len()
                        ),
                        AnonymousOriginFailure::NoExpressionEvidence => {
                            "origin=unresolved reason=no-expression".to_string()
                        }
                        AnonymousOriginFailure::UnsupportedDefinitions => {
                            "origin=unresolved reason=unsupported-definitions".to_string()
                        }
                        AnonymousOriginFailure::CopyCycle => {
                            "origin=unresolved reason=copy-cycle".to_string()
                        }
                    };
                    (TraceDecision::Dropped, reason)
                }
            };
            all_unique_ast &= matches!(status, AnonymousMemberStatus::UniqueAstExpression { .. });
            trace.record(
                def_id,
                TraceSubject::Member(format!("{local:?}")),
                TraceStage::Origin,
                decision,
                || reason,
            );
        }

        let unique_local_count = anonymous_occurrences.len();
        let unique_ast_count = unique_ast_hir_ids.len();
        trace.record(
            def_id,
            TraceSubject::Group(format!("{:?}", group.base_local)),
            TraceStage::Origin,
            if unique_ast_count > 0 {
                TraceDecision::Kept
            } else {
                TraceDecision::Skipped
            },
            || {
                format!(
                    "origin-summary anonymous-occurrences={occurrence_count} unique-locals={unique_local_count} unique-ast={unique_ast_count} all-unique-ast={}",
                    if all_unique_ast { "yes" } else { "no" }
                )
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;
    use rustc_hir::{ExprKind, HirId, Node};
    use rustc_middle::{
        mir::{BasicBlock, Local, Location},
        ty,
    };

    use super::{
        AnonymousMemberStatus, AnonymousOriginFailure, classify_anonymous_member,
        collect_ast_expression_hir_ids,
    };
    use crate::{
        analyses::{
            mir_local_facts::{MirLocalDefinition, MirLocalDefinitionKind},
            mir_source_origins::{
                BindingOrigin, BindingOriginIssue, BindingOriginKind, ExpressionOrigin,
                MirLocalSourceEvidence,
            },
        },
        rewriter::collect_input,
    };

    fn location(statement_index: usize) -> Location {
        Location {
            block: BasicBlock::from_usize(0),
            statement_index,
        }
    }

    fn definition(statement_index: usize, kind: MirLocalDefinitionKind) -> MirLocalDefinition {
        MirLocalDefinition {
            location: location(statement_index),
            kind,
        }
    }

    fn expression(hir_id: HirId, covered: &[usize]) -> ExpressionOrigin {
        ExpressionOrigin {
            hir_id,
            covered_definitions: covered.iter().copied().map(location).collect(),
        }
    }

    fn binding(hir_id: HirId, source_local: Local) -> BindingOrigin {
        BindingOrigin {
            hir_id,
            source_local,
            kind: BindingOriginKind::Copy,
        }
    }

    fn with_origins(
        test: impl FnOnce(rustc_middle::ty::TyCtxt<'_>, HirId, HirId, HirId, HirId, Local, Local) + Send,
    ) {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn f(
                p: *mut i32,
                q: *mut i32,
                i: isize,
            ) -> (*mut i32, *mut i32) {
                unsafe { (p.offset(i), q.offset(i)) }
            }
            "#,
            |tcx| {
                let program = collect_input(tcx);
                let function = program.functions[0];
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let thir_to_mir = utils::ir::map_thir_to_mir(function, false, tcx);
                let mut bindings = thir_to_mir
                    .binding_to_local
                    .iter()
                    .filter_map(|(&hir_id, &local)| {
                        matches!(body.local_decls[local].ty.kind(), ty::TyKind::RawPtr(..))
                            .then_some((hir_id, local))
                    })
                    .collect::<Vec<_>>();
                bindings.sort_by_key(|(_, local)| local.index());
                assert_eq!(bindings.len(), 2);

                let mut offsets = utils::ir::hir_to_thir::map_hir_to_thir(tcx)
                    .exprs
                    .keys()
                    .copied()
                    .filter(|hir_id| hir_id.owner.def_id == function)
                    .filter(|&hir_id| {
                        matches!(
                            tcx.hir_node(hir_id),
                            Node::Expr(expr)
                                if matches!(
                                    expr.kind,
                                    ExprKind::MethodCall(segment, ..)
                                        if segment.ident.name.as_str() == "offset"
                                )
                        )
                    })
                    .collect::<Vec<_>>();
                offsets.sort_by_key(|hir_id| hir_id.local_id.index());
                assert_eq!(offsets.len(), 2);

                test(
                    tcx,
                    bindings[0].0,
                    bindings[1].0,
                    offsets[0],
                    offsets[1],
                    bindings[0].1,
                    bindings[1].1,
                );
            },
        )
        .unwrap();
    }

    #[test]
    fn classify_precedence_is_exclusive_and_conservative() {
        with_origins(|tcx, p_hir, q_hir, first_expr, second_expr, p, q| {
            let all_ast = FxHashSet::from_iter([first_expr, second_expr]);
            let represented = FxHashSet::from_iter([p_hir]);

            let mixed = MirLocalSourceEvidence {
                definitions: vec![definition(0, MirLocalDefinitionKind::Copy(p))],
                binding_origins: vec![binding(p_hir, p)],
                binding_issue: Some(BindingOriginIssue::MixedDefinitions),
                expression_origins: vec![expression(first_expr, &[0])],
            };
            assert_eq!(
                classify_anonymous_member(&mixed, &all_ast, &represented, tcx),
                AnonymousMemberStatus::Unresolved(
                    AnonymousOriginFailure::MixedBindingAndExpressionDefinitions
                )
            );

            let cycle = MirLocalSourceEvidence {
                binding_issue: Some(BindingOriginIssue::CopyCycle),
                ..MirLocalSourceEvidence::default()
            };
            assert_eq!(
                classify_anonymous_member(&cycle, &all_ast, &represented, tcx),
                AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::CopyCycle)
            );

            let multiple_bindings = MirLocalSourceEvidence {
                binding_origins: vec![binding(p_hir, p), binding(q_hir, q)],
                ..MirLocalSourceEvidence::default()
            };
            assert_eq!(
                classify_anonymous_member(&multiple_bindings, &all_ast, &represented, tcx),
                AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::MultipleBindingOrigins)
            );

            let one_binding = MirLocalSourceEvidence {
                binding_origins: vec![binding(p_hir, p)],
                expression_origins: vec![expression(first_expr, &[0])],
                ..MirLocalSourceEvidence::default()
            };
            assert!(matches!(
                classify_anonymous_member(&one_binding, &all_ast, &represented, tcx),
                AnonymousMemberStatus::BindingCopy {
                    binding_hir_id,
                    source_local,
                    represented: true,
                } if binding_hir_id == p_hir && source_local == p
            ));

            let unsupported = MirLocalSourceEvidence {
                definitions: vec![definition(0, MirLocalDefinitionKind::Unsupported)],
                expression_origins: vec![expression(first_expr, &[0])],
                ..MirLocalSourceEvidence::default()
            };
            assert_eq!(
                classify_anonymous_member(&unsupported, &all_ast, &represented, tcx),
                AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::UnsupportedDefinitions)
            );

            let unique = MirLocalSourceEvidence {
                definitions: vec![definition(0, MirLocalDefinitionKind::Value)],
                expression_origins: vec![expression(first_expr, &[0])],
                ..MirLocalSourceEvidence::default()
            };
            assert!(matches!(
                classify_anonymous_member(&unique, &all_ast, &represented, tcx),
                AnonymousMemberStatus::UniqueAstExpression { hir_id, .. }
                    if hir_id == first_expr
            ));

            let partial = MirLocalSourceEvidence {
                definitions: vec![
                    definition(0, MirLocalDefinitionKind::Value),
                    definition(1, MirLocalDefinitionKind::Value),
                ],
                expression_origins: vec![expression(first_expr, &[0])],
                ..MirLocalSourceEvidence::default()
            };
            assert_eq!(
                classify_anonymous_member(&partial, &all_ast, &represented, tcx),
                AnonymousMemberStatus::Unresolved(
                    AnonymousOriginFailure::PartialExpressionCoverage
                )
            );

            let multiple_expressions = MirLocalSourceEvidence {
                definitions: vec![definition(0, MirLocalDefinitionKind::Value)],
                expression_origins: vec![
                    expression(first_expr, &[0]),
                    expression(second_expr, &[0]),
                ],
                ..MirLocalSourceEvidence::default()
            };
            assert_eq!(
                classify_anonymous_member(&multiple_expressions, &all_ast, &represented, tcx),
                AnonymousMemberStatus::Unresolved(
                    AnonymousOriginFailure::MultipleExpressionOrigins
                )
            );

            assert_eq!(
                classify_anonymous_member(
                    &MirLocalSourceEvidence::default(),
                    &all_ast,
                    &represented,
                    tcx,
                ),
                AnonymousMemberStatus::Unresolved(AnonymousOriginFailure::NoExpressionEvidence)
            );
        });
    }

    #[test]
    fn ast_expression_reachability_changes_unique_status() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn f(p: *mut i32, i: isize) -> *mut i32 {
                unsafe { p.offset(i) }
            }
            "#,
            |tcx| {
                let mut krate = utils::ast::expanded_ast(tcx);
                let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
                let ast_expressions = collect_ast_expression_hir_ids(&krate, &ast_to_hir, tcx);
                let function = collect_input(tcx).functions[0];
                let offset_hir_id = utils::ir::hir_to_thir::map_hir_to_thir(tcx)
                    .exprs
                    .keys()
                    .copied()
                    .find(|hir_id| {
                        hir_id.owner.def_id == function
                            && matches!(
                                tcx.hir_node(*hir_id),
                                Node::Expr(expr)
                                    if matches!(
                                        expr.kind,
                                        ExprKind::MethodCall(segment, ..)
                                            if segment.ident.name.as_str() == "offset"
                                    )
                            )
                    })
                    .expect("missing HIR offset expression");
                assert!(ast_expressions.contains(&offset_hir_id));

                let evidence = MirLocalSourceEvidence {
                    definitions: vec![definition(0, MirLocalDefinitionKind::Value)],
                    expression_origins: vec![expression(offset_hir_id, &[0])],
                    ..MirLocalSourceEvidence::default()
                };
                assert!(matches!(
                    classify_anonymous_member(
                        &evidence,
                        &ast_expressions,
                        &FxHashSet::default(),
                        tcx,
                    ),
                    AnonymousMemberStatus::UniqueAstExpression { .. }
                ));
                assert!(matches!(
                    classify_anonymous_member(
                        &evidence,
                        &FxHashSet::default(),
                        &FxHashSet::default(),
                        tcx,
                    ),
                    AnonymousMemberStatus::UniqueHirExpressionWithoutAst { .. }
                ));
            },
        )
        .unwrap();
    }
}
