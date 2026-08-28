use ::utils::unsafety::{self, UnsafeOpKind, UnsafetyHandler};
use etrace::some_or;
use points_to::andersen;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{Local, VarDebugInfoContents},
    ty::{self, TyCtxt},
};
use rustc_span::def_id::LocalDefId;
use serde::Deserialize;
use transform::TransformVisitor;

use crate::{
    analyses::{
        self,
        borrow::{
            BorrowPromotionResults, PromotedMutRefs as PromotedMutRefResult,
            lifetime_flow::LifetimeFlowResults,
        },
        fn_ptr_groups::FnPtrGroups,
        fn_ptr_rewrite_decision::FnPtrRewriteDecision,
        offset_sign::sign::OffsetSignResult,
        output_params::OutputParams,
        ownership::{
            AnalysisKind as OwnershipAnalysisKind, CrateCtxt, solidify::SolidifiedOwnershipSchemes,
            whole_program::WholeProgramAnalysis,
        },
        struct_copy::StructCopyAnalysisResult,
        type_qualifier::foster::{fatness::FatnessResult, mutability::MutabilityResult},
    },
    utils::rustc::RustProgram,
};

pub(crate) mod array_local_index_rewriter;
pub(crate) mod array_local_trace;
pub(crate) mod collector;
pub(crate) mod decision;
pub(crate) mod diagnostics;
mod epoch_split;
mod lifetimes;
pub mod profitability;
mod snapshot_rewriter;
mod struct_array_field_pre;
mod struct_param_field_spec;
mod transform;

#[allow(unused_imports)]
pub use epoch_split::{
    EpochSplitCandidateRecord, EpochSplitRewriteResult, EpochSplitTrialPlan, GeneratedEpoch,
    analyze_epoch_split_candidates, rewrite_epoch_split, rewrite_epoch_split_with_allowlist,
};

pub struct Analysis {
    #[allow(dead_code)]
    pub(crate) borrow_promotion_result: BorrowPromotionResults,
    #[allow(dead_code)]
    pub(crate) borrow_lifetime_flows: LifetimeFlowResults,
    pub(crate) promoted_mut_ref_result: PromotedMutRefResult,
    pub(crate) promoted_shared_ref_result: PromotedMutRefResult,
    pub(crate) mutability_result: MutabilityResult,
    pub(crate) fatness_result: FatnessResult,
    pub(crate) aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
    pub(crate) output_params: OutputParams,
    pub(crate) ownership_schemes: Option<SolidifiedOwnershipSchemes>,
    pub(crate) offset_sign_result: OffsetSignResult,
    pub(crate) nullity_result: analyses::nullity::NullityResult,
    pub(crate) struct_copy_result: StructCopyAnalysisResult,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CandidateObservation {
    pub candidate: profitability::CandidateId,
    pub artifacts: Vec<profitability::ArtifactFootprint>,
    pub metrics: profitability::ProfitabilityMetrics,
    pub unknown_attributions: usize,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct PromotionReport {
    pub observations: Vec<CandidateObservation>,
    pub unknown_attributions: usize,
    pub unsafe_operations: usize,
    pub raw_dereferences: usize,
}

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
    #[serde(default)]
    pub verbose: bool,
    #[cfg(test)]
    pub force_ownership_analysis_failure: bool,
    #[cfg(test)]
    pub force_gated_prepass_trial_failure: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GatedPrepassPhase {
    EpochTrial,
    AliasingTrial,
    ArrayTrial,
    DownstreamReport,
    ArraySelection,
    EpochSelection,
    RestoreCheckpoint,
    EpochReplay,
    AliasingReplay,
    ArrayReplay,
    AliasingFallback,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GatedCandidateDecision {
    pub candidate: profitability::CandidateId,
    pub decision: profitability::ProfitabilityDecision,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GatedPrepassResult {
    pub source: String,
    pub accepted_epochs: usize,
    pub rejected_epochs: usize,
    pub accepted_arrays: usize,
    pub rejected_arrays: usize,
    pub decisions: Vec<GatedCandidateDecision>,
    pub trial_time: std::time::Duration,
    pub combined_trial_failed: bool,
    pub phases: Vec<GatedPrepassPhase>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BytemuckDependency {
    None,
    Runtime,
    Derive,
}

impl BytemuckDependency {
    pub fn from_flags(runtime: bool, derive: bool) -> Self {
        match (runtime, derive) {
            (_, true) => Self::Derive,
            (true, false) => Self::Runtime,
            (false, false) => Self::None,
        }
    }

    pub fn needs_runtime(self) -> bool {
        !matches!(self, Self::None)
    }

    pub fn needs_derive(self) -> bool {
        matches!(self, Self::Derive)
    }
}

pub fn replace_local_borrows(config: &Config, tcx: TyCtxt<'_>) -> (String, BytemuckDependency) {
    let started = std::time::Instant::now();
    let progress = |step: &str| {
        if config.verbose {
            println!("Pointer replace: {step} ({:?})", started.elapsed());
        }
    };
    progress("build expanded AST");
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let (input, analysis_results, pre_points_to, points_to_solutions) =
        build_promotion_analysis(config, tcx, &progress);

    progress("build function-pointer groups");
    let fn_ptr_groups = FnPtrGroups::build(
        &pre_points_to,
        &points_to_solutions,
        &input,
        &analysis_results,
    );
    progress("decide function-pointer rewrites");
    let fn_ptr_rewrite = FnPtrRewriteDecision::build(
        &pre_points_to,
        &points_to_solutions,
        &input,
        &analysis_results,
        &tss,
        &fn_ptr_groups,
    );

    progress("rewrite AST");
    let diagnostics = diagnostics::DecisionDiagnostics::from_env();
    let mut visitor = TransformVisitor::new(
        config,
        &input,
        &analysis_results,
        ast_to_hir,
        fn_ptr_groups,
        fn_ptr_rewrite,
        diagnostics,
    );
    visitor.visit_crate(&mut krate);

    // add SliceCursor module to the crate if it was used
    progress("print transformed AST");
    let slice_cursor_used = visitor.slice_cursor.get();
    let mut code = pprust::crate_to_string_for_macros(&krate);
    if slice_cursor_used {
        code.push('\n');
        code.push_str(slice_cursor_mod_str());
    }

    visitor.emit_diagnostics();
    progress("done");

    (code, visitor.bytemuck_dependency())
}

pub fn rewrite_struct_arrays(config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let points_to = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(&andersen_config, pre_points_to, points_to, &tss, tcx);

    let candidates = analyses::struct_array_field::find_candidates(&input, &points_to);
    let changed = struct_array_field_pre::apply_struct_array_transform(
        &mut krate,
        &candidates,
        tcx,
        &ast_to_hir,
    );

    (pprust::crate_to_string_for_macros(&krate), changed)
}

pub fn rewrite_struct_param_fields(
    config: &Config,
    tcx: TyCtxt<'_>,
) -> (String, bool, utils::field_spec::FieldSpecMap) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let alloc_fns = pre_points_to.alloc_fns.clone();
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(
        &andersen_config,
        pre_points_to,
        points_to_solutions,
        &tss,
        tcx,
    );
    let nullity = analyses::nullity::analyze(&input, &points_to);
    let flows = analyses::pointer_flow::pointer_flow_analysis(&input, &alloc_fns);
    let plan = analyses::struct_param_field_spec::find_plan(
        &input,
        &flows,
        &nullity,
        &config.c_exposed_fns,
    );

    let (changed, field_specs) =
        struct_param_field_spec::apply_struct_param_field_spec(&mut krate, &plan, tcx, &ast_to_hir);
    (
        pprust::crate_to_string_for_macros(&krate),
        changed,
        field_specs,
    )
}

/// Snapshot-isolation sub-pass: inserts immutable copies of read-only
/// pointer arguments at call sites where they share a base with a mutable
/// argument, so `replace_local_borrows` can later promote the callee's
/// read-only parameters out of their mutable alias cluster. Decision prints
/// go to stderr under `CRAT_SNAPSHOT_TRACE`; `CRAT_SNAPSHOT_VALIDATE` adds a
/// `debug_assert_eq!` after each exact-prefix copy.
pub fn rewrite_aliasing(config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let result =
        rewrite_aliasing_with_lineage(config, tcx, &profitability::LineageCatalog::default());
    (result.source, result.changed)
}

pub(crate) struct AliasRewriteResult {
    pub(crate) source: String,
    pub(crate) changed: bool,
    pub(crate) lineage: profitability::LineageCatalog,
}

pub(crate) fn rewrite_aliasing_with_lineage(
    config: &Config,
    tcx: TyCtxt<'_>,
    input_lineage: &profitability::LineageCatalog,
) -> AliasRewriteResult {
    let started = std::time::Instant::now();
    let progress = |step: &str| {
        if config.verbose {
            println!("Pointer aliasing: {step} ({:?})", started.elapsed());
        }
    };
    progress("build expanded AST");
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    progress("build type shapes");
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    progress("pre-analyze points-to");
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let alloc_fns = pre_points_to.alloc_fns.clone();
    progress("solve points-to");
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);

    let trace = snapshot_rewriter::trace_enabled();

    // Debug check: the site-attributed alias pairs must agree with
    // `find_param_aliases`.
    if std::env::var_os("CRAT_SNAPSHOT_AO_EQUIV").is_some() {
        let aliases = find_param_aliases(&pre_points_to, &points_to_solutions, tcx);
        let sites =
            analyses::aliasing::attribute_alias_pairs(tcx, &pre_points_to, &points_to_solutions);
        let mut expected: FxHashMap<LocalDefId, FxHashSet<(usize, usize)>> = FxHashMap::default();
        for (callee, aliases) in &aliases {
            let set = expected.entry(*callee).or_default();
            for (a, bs) in aliases {
                for b in bs {
                    let (a, b) = (a.index() - 1, b.index() - 1);
                    set.insert((a.min(b), a.max(b)));
                }
            }
        }
        let actual: FxHashMap<LocalDefId, FxHashSet<(usize, usize)>> = sites
            .pairs
            .iter()
            .map(|(callee, pairs)| (*callee, pairs.keys().copied().collect()))
            .collect();
        assert_eq!(expected, actual);
        eprintln!("SNAPSHOT_EQUIV ok ({} callees)", expected.len());
    }

    progress("analyze pointer flow");
    let flows = analyses::pointer_flow::pointer_flow_analysis(&input, &alloc_fns);
    progress("classify array provenance");
    let provenances = analyses::array_local_provenance::array_local_provenance_from_flows(&flows);
    progress("analyze access order");
    let access_order = analyses::access_order::AccessOrderAnalysis::analyze(&input, &flows);
    progress("detect snapshot candidates");
    let candidates =
        analyses::aliasing::detect_snapshot_candidates(&input, &provenances, &access_order, trace);
    if trace {
        for candidate in &candidates {
            eprintln!(
                "SNAPSHOT caller={} callee={} mut={:?} imm={:?}",
                tcx.def_path_str(candidate.caller.to_def_id()),
                tcx.def_path_str(candidate.callee.to_def_id()),
                candidate.mut_params,
                candidate.imm_params,
            );
        }
    }

    progress("plan snapshot rewrites");
    let rewrite = if candidates.is_empty() {
        snapshot_rewriter::SnapshotIsolationResult {
            changed: false,
            generated: Vec::new(),
        }
    } else {
        let mut extents = analyses::read_extent::ReadExtentAnalysis::new(tcx);
        let gated = analyses::aliasing::gate_candidates(
            tcx,
            candidates,
            &access_order,
            &mut extents,
            trace,
        );
        let (feasible, sites) =
            snapshot_rewriter::plan_sites(tcx, gated, &krate, &ast_to_hir, trace);
        let pair_sites =
            analyses::aliasing::attribute_alias_pairs(tcx, &pre_points_to, &points_to_solutions);
        let selected = analyses::aliasing::select_callees(tcx, &feasible, &pair_sites, trace);
        if trace {
            let mut names: Vec<_> = selected
                .iter()
                .map(|c| tcx.def_path_str(c.to_def_id()))
                .collect();
            names.sort();
            for name in names {
                eprintln!("SNAPSHOT_SELECT callee={name}");
            }
        }
        let sites: Vec<_> = sites
            .into_iter()
            .filter(|s| selected.contains(&s.callee))
            .collect();
        if trace {
            eprintln!("SNAPSHOT_EMIT sites={}", sites.len());
        }
        let validate = std::env::var_os("CRAT_SNAPSHOT_VALIDATE").is_some();
        snapshot_rewriter::apply_snapshot_isolation(&mut krate, &sites, &ast_to_hir, validate)
    };

    progress("print transformed AST");
    let mut lineage = input_lineage.clone();
    for generated in rewrite.generated {
        let Some(origin_name) = generated.origin_name else {
            lineage.mark_unknown(generated.function, generated.name);
            continue;
        };
        let Some(origins) = input_lineage.lookup_all(generated.function, &origin_name) else {
            continue;
        };
        for (parent, ordinal) in origins {
            lineage.insert(
                generated.function,
                generated.name.clone(),
                parent.clone(),
                *ordinal,
            );
        }
    }
    AliasRewriteResult {
        source: pprust::crate_to_string_for_macros(&krate),
        changed: rewrite.changed,
        lineage,
    }
}

pub fn rewrite_array_local_provenance(config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let alloc_fns = pre_points_to.alloc_fns.clone();
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(
        &andersen_config,
        pre_points_to,
        points_to_solutions,
        &tss,
        tcx,
    );
    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
    nullity_result.non_null_locals =
        source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
    let provenances =
        analyses::array_local_provenance::array_local_provenance_analysis(&input, &alloc_fns);

    let changed = array_local_index_rewriter::apply_array_local_index_rewrite(
        &mut krate,
        &input,
        &provenances,
        &mutability_result,
        &nullity_result,
        &points_to,
        &ast_to_hir,
        &config.c_exposed_fns,
    );

    (pprust::crate_to_string_for_macros(&krate), changed)
}

/// runs the array-local adapter in either combined-trial mode (`accepted = None`)
/// or explicit allowlisted replay mode.
pub(crate) fn rewrite_array_local_provenance_with_allowlist(
    config: &Config,
    tcx: TyCtxt<'_>,
    accepted: Option<&FxHashSet<profitability::CandidateId>>,
    lineage: &profitability::LineageCatalog,
) -> array_local_index_rewriter::ArrayLocalRewriteResult {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let alloc_fns = pre_points_to.alloc_fns.clone();
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(
        &andersen_config,
        pre_points_to,
        points_to_solutions,
        &tss,
        tcx,
    );
    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
    nullity_result.non_null_locals =
        source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
    let provenances =
        analyses::array_local_provenance::array_local_provenance_analysis(&input, &alloc_fns);

    array_local_index_rewriter::apply_array_local_index_rewrite_with_allowlist(
        &mut krate,
        &input,
        &provenances,
        &mutability_result,
        &nullity_result,
        &points_to,
        &ast_to_hir,
        &config.c_exposed_fns,
        accepted,
        lineage,
    )
}

/// runs the profitability-gated pointer prepasses entirely in memory, then
/// restores the supplied checkpoint and replays only stable accepted IDs.
pub fn run_gated_pointer_prepasses(config: &Config, checkpoint_source: &str) -> GatedPrepassResult {
    let started = std::time::Instant::now();
    let mut phases = Vec::new();

    phases.push(GatedPrepassPhase::EpochTrial);
    let epoch_trial = match run_gated_compiler(checkpoint_source, |tcx| {
        rewrite_epoch_split_with_allowlist(config, tcx, None)
    }) {
        Some(result) => result,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let epoch_trial_source = if epoch_trial.changed {
        epoch_trial.source.as_str()
    } else {
        checkpoint_source
    };

    phases.push(GatedPrepassPhase::AliasingTrial);
    let alias_trial = match run_gated_compiler(epoch_trial_source, |tcx| {
        rewrite_aliasing_with_lineage(config, tcx, &epoch_trial.lineage)
    }) {
        Some(result) => result,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let alias_trial_source = if alias_trial.changed {
        alias_trial.source.as_str()
    } else {
        epoch_trial_source
    };

    phases.push(GatedPrepassPhase::ArrayTrial);
    let array_trial = match run_gated_compiler(alias_trial_source, |tcx| {
        rewrite_array_local_provenance_with_allowlist(config, tcx, None, &alias_trial.lineage)
    }) {
        Some(result) => result,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let array_trial_source = if array_trial.changed {
        array_trial.source.as_str()
    } else {
        alias_trial_source
    };

    phases.push(GatedPrepassPhase::DownstreamReport);
    let epoch_baseline_footprints = report_footprints(
        epoch_trial
            .artifacts
            .iter()
            .filter(|artifact| artifact.ownership == profitability::ArtifactOwnership::Baseline),
        true,
    );
    let epoch_trial_footprints = report_footprints(
        epoch_trial
            .artifacts
            .iter()
            .filter(|artifact| artifact.ownership == profitability::ArtifactOwnership::Trial),
        false,
    );
    let array_baseline_footprints = report_footprints(
        array_trial
            .artifacts
            .iter()
            .filter(|artifact| artifact.ownership == profitability::ArtifactOwnership::Baseline),
        true,
    );
    let array_trial_footprints = report_footprints(
        array_trial
            .artifacts
            .iter()
            .filter(|artifact| artifact.ownership == profitability::ArtifactOwnership::Trial),
        false,
    );
    let epoch_baseline_report = match run_gated_compiler(checkpoint_source, |tcx| {
        #[cfg(test)]
        if config.force_gated_prepass_trial_failure {
            std::panic::resume_unwind(Box::new("forced gated prepass analysis failure"));
        }
        collect_promotion_report(
            config,
            tcx,
            &profitability::LineageCatalog::default(),
            &epoch_baseline_footprints,
        )
    }) {
        Some(report) => report,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let epoch_pre_array_report = match run_gated_compiler(alias_trial_source, |tcx| {
        collect_promotion_report(config, tcx, &alias_trial.lineage, &epoch_trial_footprints)
    }) {
        Some(report) => report,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let array_baseline_report = match run_gated_compiler(alias_trial_source, |tcx| {
        collect_promotion_report(
            config,
            tcx,
            &alias_trial.lineage,
            &array_baseline_footprints,
        )
    }) {
        Some(report) => report,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let array_trial_report = match run_gated_compiler(array_trial_source, |tcx| {
        collect_promotion_report(config, tcx, &alias_trial.lineage, &array_trial_footprints)
    }) {
        Some(report) => report,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let trial_time = started.elapsed();

    phases.push(GatedPrepassPhase::ArraySelection);
    let array_measurements: FxHashMap<_, _> = array_trial
        .candidates
        .iter()
        .map(|candidate| {
            let baseline = array_baseline_report
                .observations
                .iter()
                .find(|observation| observation.candidate == candidate.id);
            let trial = array_trial_report
                .observations
                .iter()
                .find(|observation| observation.candidate == candidate.id);
            (
                candidate.id.clone(),
                array_candidate_measurement(candidate, baseline, trial),
            )
        })
        .collect();
    let mut array_decisions: FxHashMap<_, _> = array_measurements
        .iter()
        .map(|(candidate, measurement)| {
            (
                candidate.clone(),
                profitability::decide(measurement.clone()),
            )
        })
        .collect();
    for candidate in &array_trial.candidates {
        if candidate.upstream_origins.len() > 1
            && let Some(decision) = array_decisions.get_mut(&candidate.id)
        {
            let mut measurement = decision_measurement(decision).clone();
            measurement.unknown_promotions += 1;
            *decision = profitability::decide(measurement);
        }
    }
    let initially_accepted_arrays: FxHashSet<_> = array_decisions
        .iter()
        .filter(|(_, decision)| {
            matches!(
                decision,
                profitability::ProfitabilityDecision::Accept { .. }
            )
        })
        .map(|(candidate, _)| candidate.clone())
        .collect();

    phases.push(GatedPrepassPhase::EpochSelection);
    let epoch_decisions: FxHashMap<_, _> = epoch_trial
        .candidates
        .iter()
        .map(|candidate| {
            let baseline = epoch_baseline_report
                .observations
                .iter()
                .find(|observation| observation.candidate == candidate.id);
            let pre_array = epoch_pre_array_report
                .observations
                .iter()
                .find(|observation| observation.candidate == candidate.id);
            let measurement = epoch_candidate_measurement(
                candidate,
                baseline,
                pre_array,
                &array_trial.candidates,
                &initially_accepted_arrays,
                &array_measurements,
            );
            (candidate.id.clone(), profitability::decide(measurement))
        })
        .collect();
    let accepted_epochs: FxHashSet<_> = epoch_decisions
        .iter()
        .filter(|(_, decision)| {
            matches!(
                decision,
                profitability::ProfitabilityDecision::Accept { .. }
            )
        })
        .map(|(candidate, _)| candidate.clone())
        .collect();

    // array groups are selected first, but any selected group whose complete
    // upstream lineage cannot be replayed is rejected before allowlists escape.
    for candidate in &array_trial.candidates {
        let Some(decision) = array_decisions.get_mut(&candidate.id) else {
            continue;
        };
        *decision = gate_array_decision_by_upstream(
            decision.clone(),
            &candidate.upstream_origins,
            &accepted_epochs,
        );
    }
    let accepted_arrays: FxHashSet<_> = array_decisions
        .iter()
        .filter(|(_, decision)| {
            matches!(
                decision,
                profitability::ProfitabilityDecision::Accept { .. }
            )
        })
        .map(|(candidate, _)| candidate.clone())
        .collect();

    let mut decisions = Vec::with_capacity(array_decisions.len() + epoch_decisions.len());
    for candidate in &array_trial.candidates {
        if let Some(decision) = array_decisions.remove(&candidate.id) {
            decisions.push(GatedCandidateDecision {
                candidate: candidate.id.clone(),
                decision,
            });
        }
    }
    for candidate in &epoch_trial.candidates {
        if let Some(decision) = epoch_decisions.get(&candidate.id) {
            decisions.push(GatedCandidateDecision {
                candidate: candidate.id.clone(),
                decision: decision.clone(),
            });
        }
    }

    if config.verbose {
        for record in &decisions {
            println!(
                "Pointer profitability: candidate={:?} decision={:?}",
                record.candidate, record.decision
            );
        }
        println!("Pointer profitability: combined trial ({trial_time:?})");
    }

    phases.push(GatedPrepassPhase::RestoreCheckpoint);
    phases.push(GatedPrepassPhase::EpochReplay);
    let epoch_replay = match run_gated_compiler(checkpoint_source, |tcx| {
        rewrite_epoch_split_with_allowlist(config, tcx, Some(&accepted_epochs))
    }) {
        Some(result) => result,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let epoch_replay_source = if epoch_replay.changed {
        epoch_replay.source.as_str()
    } else {
        checkpoint_source
    };

    phases.push(GatedPrepassPhase::AliasingReplay);
    let alias_replay = match run_gated_compiler(epoch_replay_source, |tcx| {
        rewrite_aliasing_with_lineage(config, tcx, &epoch_replay.lineage)
    }) {
        Some(result) => result,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let alias_replay_source = if alias_replay.changed {
        alias_replay.source.as_str()
    } else {
        epoch_replay_source
    };

    phases.push(GatedPrepassPhase::ArrayReplay);
    let replay_allowlist: FxHashSet<_> = accepted_epochs
        .iter()
        .chain(accepted_arrays.iter())
        .cloned()
        .collect();
    let array_replay = match run_gated_compiler(alias_replay_source, |tcx| {
        rewrite_array_local_provenance_with_allowlist(
            config,
            tcx,
            Some(&replay_allowlist),
            &alias_replay.lineage,
        )
    }) {
        Some(result) => result,
        None => return gated_prepass_fallback(config, checkpoint_source, phases, started),
    };
    let source = if array_replay.changed {
        array_replay.source
    } else {
        alias_replay_source.to_string()
    };

    let accepted_epoch_count = accepted_epochs.len();
    let accepted_array_count = accepted_arrays.len();
    GatedPrepassResult {
        source,
        accepted_epochs: accepted_epoch_count,
        rejected_epochs: epoch_trial.candidates.len() - accepted_epoch_count,
        accepted_arrays: accepted_array_count,
        rejected_arrays: array_trial.candidates.len() - accepted_array_count,
        decisions,
        trial_time,
        combined_trial_failed: false,
        phases,
    }
}

fn report_footprints<'a>(
    artifacts: impl Iterator<Item = &'a profitability::ArtifactFootprint>,
    materialize_baseline: bool,
) -> Vec<profitability::ArtifactFootprint> {
    artifacts
        .map(|artifact| {
            let mut artifact = artifact.clone();
            if materialize_baseline {
                artifact.ownership = profitability::ArtifactOwnership::Trial;
                artifact.fate = profitability::ArtifactFate::RemainsRaw;
            }
            artifact
        })
        .collect()
}

pub(crate) fn array_candidate_measurement(
    candidate: &array_local_index_rewriter::ArrayLocalCandidateRecord,
    baseline_observation: Option<&CandidateObservation>,
    trial_observation: Option<&CandidateObservation>,
) -> profitability::CandidateMeasurement {
    let baseline = baseline_observation
        .map(|observation| observation.metrics.clone())
        .unwrap_or_else(zero_profitability_metrics);
    let mut trial = trial_observation
        .map(|observation| observation.metrics.clone())
        .unwrap_or_else(zero_profitability_metrics);
    let mut unknown_promotions = candidate.counts.unknown
        + candidate
            .artifacts
            .iter()
            .filter(|artifact| matches!(artifact.fate, profitability::ArtifactFate::Unknown))
            .count()
        + baseline_observation.map_or(1, |observation| observation.unknown_attributions)
        + trial_observation.map_or(1, |observation| observation.unknown_attributions);
    match trial
        .raw_materializations
        .checked_add(candidate.counts.reconstructions)
    {
        Some(raw_materializations) => trial.raw_materializations = raw_materializations,
        None => unknown_promotions += 1,
    }
    profitability::CandidateMeasurement {
        baseline,
        trial,
        unknown_promotions,
    }
}

pub(crate) fn epoch_candidate_measurement(
    candidate: &EpochSplitCandidateRecord,
    baseline_observation: Option<&CandidateObservation>,
    pre_array_observation: Option<&CandidateObservation>,
    arrays: &[array_local_index_rewriter::ArrayLocalCandidateRecord],
    accepted_arrays: &FxHashSet<profitability::CandidateId>,
    array_measurements: &FxHashMap<profitability::CandidateId, profitability::CandidateMeasurement>,
) -> profitability::CandidateMeasurement {
    let baseline = baseline_observation
        .map(|observation| observation.metrics.clone())
        .unwrap_or_else(zero_profitability_metrics);
    let mut trial = pre_array_observation
        .map(|observation| observation.metrics.clone())
        .unwrap_or_else(zero_profitability_metrics);
    let mut unknown_promotions = candidate
        .artifacts
        .iter()
        .filter(|artifact| matches!(artifact.fate, profitability::ArtifactFate::Unknown))
        .count()
        + baseline_observation.map_or(1, |observation| observation.unknown_attributions)
        + pre_array_observation.map_or(1, |observation| observation.unknown_attributions);
    for array in arrays.iter().filter(|array| {
        accepted_arrays.contains(&array.id) && array.upstream_origins.contains(&candidate.id)
    }) {
        let Some(measurement) = array_measurements.get(&array.id) else {
            unknown_promotions += 1;
            continue;
        };
        unknown_promotions += measurement.unknown_promotions;
        let deltas =
            profitability::metric_deltas(measurement.baseline.clone(), measurement.trial.clone());
        if !add_metric_delta(&mut trial.raw_materializations, deltas.raw_materializations)
            || !add_metric_delta(&mut trial.unsafe_operations, deltas.unsafe_operations)
            || !add_metric_delta(&mut trial.dereferences, deltas.dereferences)
        {
            unknown_promotions += 1;
        }
    }
    profitability::CandidateMeasurement {
        baseline,
        trial,
        unknown_promotions,
    }
}

fn zero_profitability_metrics() -> profitability::ProfitabilityMetrics {
    profitability::ProfitabilityMetrics {
        raw_materializations: 0,
        unsafe_operations: 0,
        dereferences: 0,
    }
}

fn add_metric_delta(value: &mut usize, delta: i128) -> bool {
    let Ok(value_i128) = i128::try_from(*value) else {
        return false;
    };
    let Some(adjusted) = value_i128.checked_add(delta) else {
        return false;
    };
    let Ok(adjusted) = usize::try_from(adjusted) else {
        return false;
    };
    *value = adjusted;
    true
}

fn decision_measurement(
    decision: &profitability::ProfitabilityDecision,
) -> &profitability::CandidateMeasurement {
    match decision {
        profitability::ProfitabilityDecision::Accept { measurement, .. }
        | profitability::ProfitabilityDecision::Reject { measurement, .. } => measurement,
    }
}

pub(crate) fn gate_array_decision_by_upstream(
    decision: profitability::ProfitabilityDecision,
    upstream_origins: &[profitability::CandidateId],
    accepted_epochs: &FxHashSet<profitability::CandidateId>,
) -> profitability::ProfitabilityDecision {
    if !matches!(
        decision,
        profitability::ProfitabilityDecision::Accept { .. }
    ) || (upstream_origins.len() <= 1
        && upstream_origins
            .iter()
            .all(|origin| accepted_epochs.contains(origin)))
    {
        return decision;
    }
    let mut measurement = decision_measurement(&decision).clone();
    measurement.unknown_promotions += 1;
    profitability::decide(measurement)
}

fn gated_prepass_fallback(
    config: &Config,
    checkpoint_source: &str,
    mut phases: Vec<GatedPrepassPhase>,
    started: std::time::Instant,
) -> GatedPrepassResult {
    phases.push(GatedPrepassPhase::AliasingFallback);
    let source = match run_gated_compiler(checkpoint_source, |tcx| rewrite_aliasing(config, tcx)) {
        Some((source, true)) => source,
        Some((_, false)) | None => checkpoint_source.to_string(),
    };
    let trial_time = started.elapsed();
    if config.verbose {
        println!("Pointer profitability: combined trial failed ({trial_time:?})");
    }
    GatedPrepassResult {
        source,
        accepted_epochs: 0,
        rejected_epochs: 0,
        accepted_arrays: 0,
        rejected_arrays: 0,
        decisions: Vec::new(),
        trial_time,
        combined_trial_failed: true,
        phases,
    }
}

fn run_gated_compiler<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    source: &str,
    callback: F,
) -> Option<R> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ::utils::compilation::run_compiler_on_str(source, callback)
    }))
    .ok()?
    .ok()
}

/// Test-only entry point that runs the array-local pass with the decision trace
/// forced on (`enabled = true`) or off (`enabled = false`) and returns both the
/// rewritten source and the collected events. Mirrors
/// `rewrite_array_local_provenance`'s setup. Returning the source lets tests
/// assert the trace is behavior-neutral (enabled vs disabled output is equal).
#[cfg(test)]
pub(crate) fn rewrite_array_local_provenance_trace(
    config: &Config,
    tcx: TyCtxt<'_>,
    enabled: bool,
) -> (String, Vec<array_local_trace::TraceEvent>) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let input = collect_input(tcx);
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let alloc_fns = pre_points_to.alloc_fns.clone();
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let points_to = andersen::post_analyze(
        &andersen_config,
        pre_points_to,
        points_to_solutions,
        &tss,
        tcx,
    );
    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
    nullity_result.non_null_locals =
        source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
    let provenances =
        analyses::array_local_provenance::array_local_provenance_analysis(&input, &alloc_fns);

    let events = array_local_index_rewriter::apply_array_local_index_rewrite_traced(
        &mut krate,
        &input,
        &provenances,
        &mutability_result,
        &nullity_result,
        &points_to,
        &ast_to_hir,
        &config.c_exposed_fns,
        enabled,
    );
    (pprust::crate_to_string_for_macros(&krate), events)
}

pub(crate) fn collect_input(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    let mut structs = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        };
    }

    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn build_promotion_analysis<'tcx>(
    config: &Config,
    tcx: TyCtxt<'tcx>,
    progress: &dyn Fn(&str),
) -> (
    RustProgram<'tcx>,
    Analysis,
    andersen::PreAnalysisData<'tcx>,
    andersen::Solutions,
) {
    let input = collect_input(tcx);
    progress("build type shapes");
    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: config.c_exposed_fns.clone(),
    };
    progress("pre-analyze points-to");
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    progress("solve points-to");
    let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    progress("find parameter aliases");
    let aliases = find_param_aliases(&pre_points_to, &points_to_solutions, tcx);
    progress("post-analyze points-to");
    let points_to = andersen::post_analyze(
        &andersen_config,
        pre_points_to.clone(),
        points_to_solutions.clone(),
        &tss,
        tcx,
    );

    progress("analyze mutability");
    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    progress("compute output parameters");
    let output_params =
        analyses::output_params::compute_output_params(&input, &mutability_result, &aliases);
    progress("analyze ownership");
    let ownership_schemes = maybe_solidified_ownership(config, &input, &output_params);
    progress("group source variables");
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
    progress("analyze borrow promotion");
    let borrow_promotion_result =
        analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
    let borrow_lifetime_flows = borrow_promotion_result.lifetime_flows.clone();
    progress("analyze struct copies");
    let struct_copy_result =
        analyses::struct_copy::analyze(&input, &borrow_promotion_result.mutable_fields);
    let promoted_mut_ref_result = source_var_groups
        .postprocess_promoted_mut_refs(borrow_promotion_result.mutable_locals.clone());
    let promoted_shared_ref_result = source_var_groups
        .postprocess_promoted_mut_refs(borrow_promotion_result.shared_locals.clone());
    progress("analyze pointer fatness");
    let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
    progress("analyze offset signs");
    let mut offset_sign_result = analyses::offset_sign::sign::offset_sign_analysis(&input);
    offset_sign_result.access_signs =
        source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
    progress("analyze nullity");
    let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
    nullity_result.non_null_locals =
        source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
    (
        input,
        Analysis {
            borrow_promotion_result,
            borrow_lifetime_flows,
            promoted_mut_ref_result,
            promoted_shared_ref_result,
            mutability_result,
            fatness_result,
            aliases,
            output_params,
            ownership_schemes,
            offset_sign_result,
            nullity_result,
            struct_copy_result,
        },
        pre_points_to,
        points_to_solutions,
    )
}

/// Runs the same downstream decision analysis as `replace_local_borrows` without
/// rewriting the AST. All returned records are owned and session-independent.
pub(crate) fn collect_promotion_report(
    config: &Config,
    tcx: TyCtxt<'_>,
    lineage: &profitability::LineageCatalog,
    footprints: &[profitability::ArtifactFootprint],
) -> PromotionReport {
    let (input, analysis, _, _) = build_promotion_analysis(config, tcx, &no_promotion_progress);
    let mut report = PromotionReport::default();
    let mut observations: FxHashMap<profitability::CandidateId, CandidateObservation> =
        FxHashMap::default();
    for footprint in footprints {
        observations
            .entry(footprint.id.candidate.clone())
            .or_insert_with(|| CandidateObservation {
                candidate: footprint.id.candidate.clone(),
                artifacts: Vec::new(),
                metrics: profitability::ProfitabilityMetrics {
                    raw_materializations: 0,
                    unsafe_operations: 0,
                    dereferences: 0,
                },
                unknown_attributions: 0,
            })
            .artifacts
            .push(footprint.clone());
    }

    for did in &input.functions {
        let function = tcx.def_path_hash(did.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(*did).borrow();
        let maker = decision::DecisionMaker::new(&analysis, *did, tcx);
        for (local, decl) in body.local_decls.iter_enumerated() {
            let Some(name) = local_source_name(&body, local) else { continue };
            let aliases = analysis
                .aliases
                .get(did)
                .and_then(|aliases| aliases.get(&local));
            let info = maker.decide_with_info(local, decl, aliases);
            for observation in observations.values_mut() {
                for artifact in &mut observation.artifacts {
                    if matches!(artifact.fate, profitability::ArtifactFate::Eliminated) {
                        continue;
                    }
                    if !artifact_matches_local(artifact, function, &name, lineage) {
                        continue;
                    }
                    artifact.fate = match info.kind {
                        Some(decision::PtrKind::Raw(_)) => profitability::ArtifactFate::RemainsRaw,
                        Some(kind) => profitability::ArtifactFate::Promoted(kind),
                        None => profitability::ArtifactFate::Unknown,
                    };
                }
            }
        }
    }

    for observation in observations.values_mut() {
        for artifact in &mut observation.artifacts {
            let matches = artifact_match_count(artifact, tcx, &input, lineage);
            if !matches!(artifact.fate, profitability::ArtifactFate::Eliminated)
                && (matches != 1 || matches!(artifact.fate, profitability::ArtifactFate::Unknown))
            {
                artifact.fate = profitability::ArtifactFate::Unknown;
                observation.unknown_attributions += 1;
                report.unknown_attributions += 1;
            }
            if artifact.ownership == profitability::ArtifactOwnership::Trial
                && matches!(artifact.fate, profitability::ArtifactFate::RemainsRaw)
            {
                observation.metrics.raw_materializations += 1;
            }
        }
    }

    let mut unsafe_events = UnsafeEventCounter::default();
    for did in &input.functions {
        unsafe_events.function = Some(tcx.def_path_hash(did.to_def_id()));
        unsafety::check_unsafety(*did, &mut unsafe_events, tcx);
    }
    report.unsafe_operations = unsafe_events.events.len();
    report.raw_dereferences = unsafe_events
        .events
        .iter()
        .filter(|event| event.raw_dereference)
        .count();
    for event in &unsafe_events.events {
        let mut matches = FxHashSet::default();
        for observation in observations.values() {
            for artifact in &observation.artifacts {
                if unsafe_event_matches_artifact(event, artifact, lineage) {
                    matches.insert(observation.candidate.clone());
                }
            }
        }
        if matches.len() == 1 {
            let candidate = matches.iter().next().expect("one unsafe-event match");
            let observation = observations
                .get_mut(candidate)
                .expect("observation disappeared");
            observation.metrics.unsafe_operations += 1;
            if event.raw_dereference {
                observation.metrics.dereferences += 1;
            }
        } else if !matches.is_empty() {
            report.unknown_attributions += 1;
            for candidate in matches {
                observations
                    .get_mut(&candidate)
                    .expect("observation disappeared")
                    .unknown_attributions += 1;
            }
        }
    }
    report.observations = observations.into_values().collect();
    report
        .observations
        .sort_by(|a, b| format!("{:?}", a.candidate).cmp(&format!("{:?}", b.candidate)));
    report
}

fn no_promotion_progress(_: &str) {}

fn local_source_name(body: &rustc_middle::mir::Body<'_>, local: Local) -> Option<String> {
    body.var_debug_info.iter().find_map(|info| {
        let VarDebugInfoContents::Place(place) = &info.value else { return None };
        (place.local == local && place.projection.is_empty()).then(|| info.name.to_string())
    })
}

fn artifact_matches_local(
    artifact: &profitability::ArtifactFootprint,
    function: rustc_span::def_id::DefPathHash,
    name: &str,
    lineage: &profitability::LineageCatalog,
) -> bool {
    let Some(source_name) = artifact.source_name.as_deref() else { return false };
    if source_name != name {
        return false;
    }
    match &artifact.id.candidate {
        profitability::CandidateId::Epoch {
            function: candidate_function,
            binding,
        } => {
            if lineage.lookup_all(function, name).is_some() {
                return lineage
                    .lookup(function, name)
                    .is_some_and(|(candidate, ordinal)| {
                        candidate == &artifact.id.candidate && ordinal == artifact.id.ordinal
                    });
            }
            *candidate_function == function && binding.name == name
        }
        profitability::CandidateId::ArrayLocal {
            function: candidate_function,
            base,
            members,
        } => {
            *candidate_function == function
                && (base.name == name || members.iter().any(|member| member.name == name))
        }
    }
}

fn artifact_match_count(
    artifact: &profitability::ArtifactFootprint,
    tcx: TyCtxt<'_>,
    input: &RustProgram<'_>,
    lineage: &profitability::LineageCatalog,
) -> usize {
    input
        .functions
        .iter()
        .map(|did| {
            let function = tcx.def_path_hash(did.to_def_id());
            let body = tcx.mir_drops_elaborated_and_const_checked(*did).borrow();
            body.local_decls
                .indices()
                .filter(|local| {
                    local_source_name(&body, *local).is_some_and(|name| {
                        artifact_matches_local(artifact, function, &name, lineage)
                    })
                })
                .count()
        })
        .sum()
}

#[derive(Default)]
struct UnsafeEventCounter {
    function: Option<rustc_span::def_id::DefPathHash>,
    events: Vec<UnsafeEvent>,
}

struct UnsafeEvent {
    function: rustc_span::def_id::DefPathHash,
    span: String,
    snippet: Option<String>,
    line_snippet: Option<String>,
    raw_dereference: bool,
}

fn unsafe_event_matches_artifact(
    event: &UnsafeEvent,
    artifact: &profitability::ArtifactFootprint,
    lineage: &profitability::LineageCatalog,
) -> bool {
    if candidate_function(&artifact.id.candidate) != event.function {
        return false;
    }
    if artifact.source_span.as_deref() == Some(event.span.as_str()) {
        return true;
    }
    let mut names = Vec::new();
    if let Some(name) = artifact.source_name.as_deref() {
        names.push(name);
    }
    match &artifact.id.candidate {
        profitability::CandidateId::Epoch { binding, .. } => names.push(&binding.name),
        profitability::CandidateId::ArrayLocal { base, members, .. } => {
            names.push(&base.name);
            names.extend(members.iter().map(|member| member.name.as_str()));
        }
    }
    names.sort_unstable();
    names.dedup();
    event
        .snippet
        .iter()
        .chain(event.line_snippet.iter())
        .any(|snippet| {
            names
                .iter()
                .any(|name| contains_binding_name(snippet, name))
        })
        || artifact.source_name.as_deref().is_some_and(|name| {
            lineage
                .lookup(event.function, name)
                .is_some_and(|(candidate, ordinal)| {
                    candidate == &artifact.id.candidate
                        && ordinal == artifact.id.ordinal
                        && event
                            .line_snippet
                            .as_deref()
                            .is_some_and(|snippet| contains_binding_name(snippet, name))
                })
        })
}

fn candidate_function(candidate: &profitability::CandidateId) -> rustc_span::def_id::DefPathHash {
    match candidate {
        profitability::CandidateId::Epoch { function, .. }
        | profitability::CandidateId::ArrayLocal { function, .. } => *function,
    }
}

fn contains_binding_name(snippet: &str, name: &str) -> bool {
    snippet.match_indices(name).any(|(start, _)| {
        let before = snippet[..start].chars().next_back();
        let after = snippet[start + name.len()..].chars().next();
        !before.is_some_and(|ch| ch == '_' || ch.is_ascii_alphanumeric())
            && !after.is_some_and(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    })
}

impl UnsafetyHandler for UnsafeEventCounter {
    fn handle_unsafety(&mut self, kind: UnsafeOpKind, span: rustc_span::Span, tcx: TyCtxt<'_>) {
        let source_map = tcx.sess.source_map();
        let function = self
            .function
            .expect("unsafe-event counter function must be set");
        let line_span = source_map.span_extend_to_line(span);
        self.events.push(UnsafeEvent {
            function,
            span: source_map.span_to_string(span, rustc_span::FileNameDisplayPreference::Local),
            snippet: source_map.span_to_snippet(span).ok(),
            line_snippet: source_map.span_to_snippet(line_span).ok(),
            raw_dereference: matches!(kind, UnsafeOpKind::DerefOfRawPointer),
        });
    }
}

fn maybe_solidified_ownership<'tcx>(
    _config: &Config,
    input: &RustProgram<'tcx>,
    output_params: &OutputParams,
) -> Option<SolidifiedOwnershipSchemes> {
    #[cfg(test)]
    if _config.force_ownership_analysis_failure {
        return None;
    }

    let _verbose_guard = crate::analyses::ownership::whole_program::set_verbose(_config.verbose);
    let crate_ctxt = CrateCtxt::new(input);
    <WholeProgramAnalysis as OwnershipAnalysisKind>::analyze(crate_ctxt, output_params)
        .ok()
        .map(|results| results.solidify(input))
}

pub(crate) fn find_param_aliases<'tcx>(
    pre: &andersen::PreAnalysisData<'tcx>,
    points_to: &andersen::Solutions,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> {
    let mut param_aliases = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        let calls = some_or!(pre.call_args.get(&def_id), continue);
        let mut aliases: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        for call_args in calls {
            for i in 0..body.arg_count {
                for j in 0..i {
                    let arg_i = some_or!(call_args[i], continue);
                    let arg_j = some_or!(call_args[j], continue);
                    let mut sol_i = points_to[arg_i].clone();
                    sol_i.intersect(&points_to[arg_j]);
                    if !sol_i.is_empty() {
                        let i = Local::from_usize(i + 1);
                        let j = Local::from_usize(j + 1);
                        aliases.entry(i).or_default().insert(j);
                        aliases.entry(j).or_default().insert(i);
                    }
                }
            }
        }
        if !aliases.is_empty() {
            param_aliases.insert(def_id, aliases);
        }
    }
    param_aliases
}

#[allow(unused)]
fn print_nullity_counts(
    input: &RustProgram<'_>,
    nullity_result: &analyses::nullity::NullityResult,
) {
    for &did in &input.functions {
        let body = input
            .tcx
            .mir_drops_elaborated_and_const_checked(did)
            .borrow();
        let raw_pointer_params = body
            .args_iter()
            .filter(|&local| matches!(body.local_decls[local].ty.kind(), ty::TyKind::RawPtr(..)))
            .collect::<Vec<_>>();
        let total = raw_pointer_params.len();
        if total == 0 {
            continue;
        }

        let non_null = nullity_result
            .non_null_params
            .get(&did)
            .map(|params| {
                raw_pointer_params
                    .iter()
                    .filter(|&&local| params.contains(local))
                    .count()
            })
            .unwrap_or(0);

        println!(
            "crat_nullity\t{}\t{}\t{}",
            input.tcx.def_path_str(did.to_def_id()),
            total,
            non_null
        );
    }
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::ty::TyCtxt;
    use rustc_span::def_id::DefPathHash;

    use super::{
        Config, collect_promotion_report,
        profitability::{
            ArtifactFootprint, ArtifactId, ArtifactOwnership, CandidateId, LineageCatalog,
            SourceBindingKey,
        },
    };

    fn footprint(name: &str) -> ArtifactFootprint {
        ArtifactFootprint {
            id: ArtifactId {
                candidate: CandidateId::epoch(
                    DefPathHash::default(),
                    SourceBindingKey::new("candidate", 0),
                ),
                ordinal: 0,
            },
            source_name: Some(name.to_owned()),
            source_span: None,
            ownership: ArtifactOwnership::Trial,
            fate: super::profitability::ArtifactFate::Unknown,
        }
    }

    fn test_function(tcx: TyCtxt<'_>) -> rustc_span::def_id::LocalDefId {
        test_function_named(tcx, "f")
    }

    fn test_function_named(tcx: TyCtxt<'_>, name: &str) -> rustc_span::def_id::LocalDefId {
        tcx.hir_crate(())
            .owners
            .iter()
            .filter_map(|owner| {
                let OwnerNode::Item(item) = owner.as_owner()?.node() else {
                    return None;
                };
                (matches!(item.kind, ItemKind::Fn { .. })
                    && tcx.item_name(item.owner_id.def_id.into()).as_str() == name)
                    .then_some(item.owner_id.def_id)
            })
            .next()
            .expect("expected test function")
    }

    fn artifact_for_binding(
        tcx: TyCtxt<'_>,
        did: rustc_span::def_id::LocalDefId,
        name: &str,
    ) -> ArtifactFootprint {
        let mut artifact = footprint(name);
        artifact.id.candidate = CandidateId::epoch(
            tcx.def_path_hash(did.to_def_id()),
            SourceBindingKey::new(name, 0),
        );
        artifact
    }

    #[test]
    fn promotion_report_marks_unmatched_artifacts_unknown() {
        ::utils::compilation::run_compiler_on_str(
            "pub unsafe fn f(p: *const i32) { let _ = p; }",
            |tcx| {
                let report = collect_promotion_report(
                    &Config::default(),
                    tcx,
                    &LineageCatalog::default(),
                    &[footprint("not_a_binding")],
                );
                assert_eq!(report.unknown_attributions, 1);
                assert!(matches!(
                    report.observations[0].artifacts[0].fate,
                    super::profitability::ArtifactFate::Unknown
                ));
            },
        )
        .unwrap();
    }

    #[test]
    fn promotion_report_counts_raw_dereferences_as_normalized_unsafe_operations() {
        ::utils::compilation::run_compiler_on_str(
            "pub unsafe fn f(p: *const i32) -> i32 { *p }",
            |tcx| {
                let report = collect_promotion_report(
                    &Config::default(),
                    tcx,
                    &LineageCatalog::default(),
                    &[],
                );
                assert_eq!(report.unsafe_operations, 1);
                assert_eq!(report.raw_dereferences, 1);
            },
        )
        .unwrap();
    }

    #[test]
    fn promotion_report_counts_a_matched_non_pointer_local_as_unknown() {
        ::utils::compilation::run_compiler_on_str("pub fn f() { let x = 1i32; }", |tcx| {
            let did = test_function(tcx);
            let mut artifact = footprint("x");
            artifact.id.candidate = CandidateId::epoch(
                tcx.def_path_hash(did.to_def_id()),
                SourceBindingKey::new("x", 0),
            );
            let report = collect_promotion_report(
                &Config::default(),
                tcx,
                &LineageCatalog::default(),
                &[artifact],
            );
            assert_eq!(report.unknown_attributions, 1);
            assert_eq!(report.observations[0].unknown_attributions, 1);
        })
        .unwrap();
    }

    #[test]
    fn promotion_report_rejects_ambiguous_lineage_without_name_fallback() {
        ::utils::compilation::run_compiler_on_str("pub unsafe fn f(p: *const i32) {}", |tcx| {
            let did = test_function(tcx);
            let function = tcx.def_path_hash(did.to_def_id());
            let candidate = CandidateId::epoch(function, SourceBindingKey::new("p", 0));
            let mut lineage = LineageCatalog::default();
            lineage.insert(function, "p", candidate.clone(), 0);
            lineage.insert(function, "p", candidate.clone(), 1);
            let mut artifact = footprint("p");
            artifact.id.candidate = candidate;
            let report = collect_promotion_report(&Config::default(), tcx, &lineage, &[artifact]);
            assert_eq!(report.unknown_attributions, 1);
            assert!(matches!(
                report.observations[0].artifacts[0].fate,
                super::profitability::ArtifactFate::Unknown
            ));
        })
        .unwrap();
    }

    #[test]
    fn promotion_report_marks_ambiguous_unsafe_events_unknown_for_each_candidate() {
        ::utils::compilation::run_compiler_on_str(
            "pub unsafe fn f(p: *const i32) -> i32 { *p }",
            |tcx| {
                let did = test_function(tcx);
                let function = tcx.def_path_hash(did.to_def_id());
                let mut first = footprint("p");
                first.id.candidate = CandidateId::epoch(function, SourceBindingKey::new("p", 0));
                let mut second = footprint("p");
                second.id.candidate = CandidateId::epoch(function, SourceBindingKey::new("p", 1));
                let report = collect_promotion_report(
                    &Config::default(),
                    tcx,
                    &LineageCatalog::default(),
                    &[first, second],
                );
                assert!(report.unknown_attributions >= 1);
                assert_eq!(report.observations.len(), 2);
                assert!(
                    report
                        .observations
                        .iter()
                        .all(|observation| observation.unknown_attributions >= 1)
                );
            },
        )
        .unwrap();
    }

    #[test]
    fn promotion_report_attributes_generated_binding_unsafe_events_through_lineage() {
        ::utils::compilation::run_compiler_on_str(
            "pub unsafe fn f(p: *const i32) -> i32 { let p__epoch_0 = p; *p__epoch_0 }",
            |tcx| {
                let did = test_function(tcx);
                let function = tcx.def_path_hash(did.to_def_id());
                let candidate = CandidateId::epoch(function, SourceBindingKey::new("p", 0));
                let mut lineage = LineageCatalog::default();
                lineage.insert(function, "p__epoch_0", candidate.clone(), 0);
                let mut artifact = footprint("p__epoch_0");
                artifact.id.candidate = candidate;
                let report =
                    collect_promotion_report(&Config::default(), tcx, &lineage, &[artifact]);
                assert_eq!(report.observations[0].metrics.unsafe_operations, 1);
                assert_eq!(report.observations[0].metrics.dereferences, 1);
            },
        )
        .unwrap();
    }

    #[test]
    fn promotion_report_distinguishes_promoted_and_raw_locals() {
        ::utils::compilation::run_compiler_on_str(
            r#"
pub unsafe fn f() -> i32 {
    let mut x = 42i32;
    let mut p: *mut i32 = &mut x;
    *p = 10;
    let mut q: *mut i32 = p;
    *p = 20;
    *q
}
"#,
            |tcx| {
                let did = test_function(tcx);
                let report = collect_promotion_report(
                    &Config::default(),
                    tcx,
                    &LineageCatalog::default(),
                    &[
                        artifact_for_binding(tcx, did, "p"),
                        artifact_for_binding(tcx, did, "q"),
                    ],
                );
                let artifacts = &report.observations;
                assert!(artifacts.iter().any(|observation| matches!(
                    observation.artifacts[0].fate,
                    super::profitability::ArtifactFate::Promoted(super::decision::PtrKind::Ref(
                        true
                    ))
                )));
                assert!(artifacts.iter().any(|observation| matches!(
                    observation.artifacts[0].fate,
                    super::profitability::ArtifactFate::RemainsRaw
                )));
            },
        )
        .unwrap();
    }

    #[test]
    fn promotion_report_marks_alias_forced_local_raw() {
        ::utils::compilation::run_compiler_on_str(
            r#"
pub unsafe fn keep_alias_raw(a: *mut i32, b: *mut i32) -> *mut i32 {
    *a = 1;
    *b = 2;
    a
}
pub unsafe fn caller() -> *mut i32 {
    let mut x = 7i32;
    let p: *mut i32 = &mut x;
    keep_alias_raw(p, p)
}
"#,
            |tcx| {
                let did = test_function_named(tcx, "keep_alias_raw");
                let report = collect_promotion_report(
                    &Config::default(),
                    tcx,
                    &LineageCatalog::default(),
                    &[artifact_for_binding(tcx, did, "a")],
                );
                assert_eq!(
                    report.observations[0].artifacts[0].fate,
                    super::profitability::ArtifactFate::RemainsRaw
                );
            },
        )
        .unwrap();
    }
}

fn slice_cursor_mod_str() -> &'static str {
    r#"pub mod slice_cursor {
    use std::ops::Index;
    use std::ops::IndexMut;
    use std::ops::Range;
    use std::ops::RangeFrom;
    use std::ops::RangeFull;
    use std::ops::RangeTo;

    pub struct SliceCursorMut<'a, T> {
        base: &'a mut [T],
        pos: usize,
    }

    impl<'a, T> SliceCursorMut<'a, T> {
        pub fn new(base: &'a mut [T]) -> Self {
            Self { base, pos: 0 }
        }

        pub fn with_pos(base: &'a mut [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &mut [], pos: 0 }
        }

        pub fn from_mut(val: &'a mut T) -> Self {
            Self { base: std::slice::from_mut(val), pos: 0 }
        }

        pub unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            unsafe { Self::from_raw_parts_mut(ptr as *mut T, len) }
        }

        pub unsafe fn from_raw_parts_mut(ptr: *mut T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts_mut(ptr, len) }, pos: 0 }
        }

        pub fn as_deref_mut(&mut self) -> SliceCursorMut<'_, T> {
            SliceCursorMut { base: &mut self.base[..], pos: self.pos }
        }

        pub fn as_deref(&self) -> SliceCursor<'_, T> {
            SliceCursor { base: &self.base[..], pos: self.pos }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub fn offset_by(mut self, offset: isize) -> Self {
            self.seek(offset);
            self
        }

        pub fn is_empty(&self) -> bool {
            self.pos >= self.base.len()
        }

        pub fn as_mut_ptr(&mut self) -> *mut T {
            self.base[self.pos..].as_mut_ptr()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn first_mut(&mut self) -> Option<&mut T> {
            self.base.get_mut(self.pos)
        }

        pub fn as_slice(&self) -> &[T] {
            &self.base[self.pos..]
        }

        pub fn as_slice_mut(&mut self) -> &mut [T] {
            &mut self.base[self.pos..]
        }

        pub fn into_slice_mut(self) -> &'a mut [T] {
            &mut self.base[self.pos..]
        }
    }

    pub struct SliceCursor<'a, T> {
        base: &'a [T],
        pos: usize,
    }

    impl<'a, T> Copy for SliceCursor<'a, T> {}

    impl<'a, T> Clone for SliceCursor<'a, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub fn new(slice: &'a [T]) -> Self {
            Self { base: slice, pos: 0 }
        }

        pub fn with_pos(base: &'a [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &[], pos: 0 }
        }

        pub fn from_ref(val: &'a T) -> Self {
            Self { base: std::slice::from_ref(val), pos: 0 }
        }

        pub unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts(ptr, len) }, pos: 0 }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub fn offset_by(mut self, offset: isize) -> Self {
            self.seek(offset);
            self
        }

        pub fn is_empty(&self) -> bool {
            self.pos >= self.base.len()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn as_slice(&self) -> &'a [T] {
            &self.base[self.pos..]
        }
    }

    #[inline(always)]
    fn abs_idx(pos: usize, index: isize) -> usize {
        pos.wrapping_add_signed(index)
    }

    macro_rules! impl_readable_index {
        ($cursor_type:ident, $($idx_type:ty),*) => {
            $(
                impl<T> Index<$idx_type> for $cursor_type<'_, T> {
                    type Output = T;
                    #[inline]
                    fn index(&self, index: $idx_type) -> &Self::Output {
                        &self.base[abs_idx(self.pos, index as isize)]
                    }
                }

                impl<T> Index<Range<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: Range<$idx_type>) -> &Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &self.base[start..end]
                    }
                }

                impl<T> Index<RangeFrom<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: RangeFrom<$idx_type>) -> &Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &self.base[start..]
                    }
                }

                impl<T> Index<RangeTo<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: RangeTo<$idx_type>) -> &Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &self.base[self.pos..end]
                    }
                }
            )*

            impl<T> Index<RangeFull> for $cursor_type<'_, T> {
                type Output = [T];
                #[inline]
                fn index(&self, _: RangeFull) -> &Self::Output {
                    &self.base[self.pos..]
                }
            }
        };
    }

    macro_rules! impl_mutable_index {
        ($($idx_type:ty),*) => {
            $(
                impl<T> IndexMut<$idx_type> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, index: $idx_type) -> &mut Self::Output {
                        let i = abs_idx(self.pos, index as isize);
                        &mut self.base[i]
                    }
                }

                impl<T> IndexMut<Range<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: Range<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[start..end]
                    }
                }

                impl<T> IndexMut<RangeFrom<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeFrom<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &mut self.base[start..]
                    }
                }

                impl<T> IndexMut<RangeTo<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeTo<$idx_type>) -> &mut Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[self.pos..end]
                    }
                }
            )*

            impl<T> IndexMut<RangeFull> for SliceCursorMut<'_, T> {
                #[inline]
                fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                    &mut self.base[self.pos..]
                }
            }
        };
    }

    impl_readable_index!(SliceCursorMut, isize, usize, i32);
    impl_readable_index!(SliceCursor, isize, usize, i32);
    impl_mutable_index!(isize, usize, i32);
}"#
}
