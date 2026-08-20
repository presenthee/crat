use points_to::andersen;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Location, TerminatorKind},
    ty::{self, TyCtxt},
};
use typed_arena::Arena;
use utils::ty_shape;

use super::{
    CopyPlan, access_order_rejection_evidence, attribute_alias_pairs, detect_snapshot_candidates,
    gate_candidates, query_error_evidence, select_callees,
};
use crate::{
    analyses::{
        access_order::{AccessOrderAnalysis, AccessUnknownReason, QueryError},
        array_local_provenance,
        pointer_flow::pointer_flow_analysis,
        read_extent::ReadExtentAnalysis,
    },
    rewriter::collect_input,
};

/// (caller_name, callee_name, mut_params, imm_params) for each detected candidate.
fn run_detection(code: &str) -> Vec<(String, String, Vec<usize>, Vec<usize>)> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let input = collect_input(tcx);
        let arena = Arena::new();
        let tss = ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre = andersen::pre_analyze(&andersen_config, &tss, tcx);
        let alloc_fns = pre.alloc_fns.clone();
        let flows = pointer_flow_analysis(&input, &alloc_fns);
        let provenances = array_local_provenance::array_local_provenance_from_flows(&flows);
        let access_order = AccessOrderAnalysis::analyze(&input, &flows);
        let mut out: Vec<_> =
            detect_snapshot_candidates(&input, &provenances, &access_order, false)
                .into_iter()
                .map(|c| {
                    (
                        tcx.item_name(c.caller.to_def_id()).to_string(),
                        tcx.item_name(c.callee.to_def_id()).to_string(),
                        c.mut_params,
                        c.imm_params,
                    )
                })
                .collect();
        out.sort();
        out
    })
    .unwrap()
}

/// (callee_name, pair, sorted caller_names of the pair's call sites) for each
/// attributed alias pair.
fn run_attribution(code: &str) -> Vec<(String, (usize, usize), Vec<String>)> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let arena = Arena::new();
        let tss = ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre = andersen::pre_analyze(&andersen_config, &tss, tcx);
        let solutions = andersen::analyze(&andersen_config, &pre, &tss, tcx);
        let sites = attribute_alias_pairs(tcx, &pre, &solutions);
        let mut out: Vec<_> = sites
            .pairs
            .into_iter()
            .flat_map(|(callee, pairs)| {
                let callee = tcx.item_name(callee.to_def_id()).to_string();
                pairs.into_iter().map(move |(pair, sites)| {
                    let mut callers: Vec<_> = sites
                        .iter()
                        .map(|(caller, _)| tcx.item_name(caller.to_def_id()).to_string())
                        .collect();
                    callers.sort();
                    (callee.clone(), pair, callers)
                })
            })
            .collect();
        out.sort();
        out
    })
    .unwrap()
}

/// Runs detection, gating, and selection. Returns the gated candidates as
/// (caller_name, callee_name, plan summaries) and the sorted names of the
/// selected callees. Plans render as `prefix(<arg>, <elems>)`,
/// `whole(<arg>, <len>)`, and `runtime(<arg>, <len_param>)`.
#[expect(clippy::type_complexity)]
fn run_planning(code: &str) -> (Vec<(String, String, Vec<String>)>, Vec<String>) {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        let input = collect_input(tcx);
        let arena = Arena::new();
        let tss = ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre = andersen::pre_analyze(&andersen_config, &tss, tcx);
        let alloc_fns = pre.alloc_fns.clone();
        let solutions = andersen::analyze(&andersen_config, &pre, &tss, tcx);
        let flows = pointer_flow_analysis(&input, &alloc_fns);
        let provenances = array_local_provenance::array_local_provenance_from_flows(&flows);
        let access_order = AccessOrderAnalysis::analyze(&input, &flows);

        let candidates = detect_snapshot_candidates(&input, &provenances, &access_order, false);
        let mut extents = ReadExtentAnalysis::new(tcx);
        let gated = gate_candidates(tcx, candidates, &access_order, &mut extents, false);
        let pair_sites = attribute_alias_pairs(tcx, &pre, &solutions);
        let selected = select_callees(tcx, &gated, &pair_sites, false);

        let mut gated_out: Vec<_> = gated
            .iter()
            .map(|g| {
                (
                    tcx.item_name(g.candidate.caller.to_def_id()).to_string(),
                    tcx.item_name(g.candidate.callee.to_def_id()).to_string(),
                    g.copies
                        .iter()
                        .map(|c| match c {
                            CopyPlan::ExactPrefix { arg_index, elems } => {
                                format!("prefix({arg_index}, {elems})")
                            }
                            CopyPlan::WholeArray { arg_index, len, .. } => {
                                format!("whole({arg_index}, {len})")
                            }
                            CopyPlan::RuntimePrefix {
                                arg_index,
                                len_param,
                            } => format!("runtime({arg_index}, {len_param})"),
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        gated_out.sort();
        let mut selected: Vec<_> = selected
            .iter()
            .map(|c| tcx.item_name(c.to_def_id()).to_string())
            .collect();
        selected.sort();
        (gated_out, selected)
    })
    .unwrap()
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

fn run_access_order_rejection_evidence(code: &str, caller_name: &str, callee_name: &str) -> String {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let input = collect_input(tcx);
        let flows = pointer_flow_analysis(&input, &FxHashSet::default());
        let access_order = AccessOrderAnalysis::analyze(&input, &flows);
        let caller = named_function(tcx, &input.functions, caller_name);
        let callee = named_function(tcx, &input.functions, callee_name);
        let location = direct_call_location(tcx, caller, callee);
        let call = access_order
            .at_call(caller, location)
            .expect("valid local call");
        let verdict = call.reads_precede_writes(&[0], &[1]);
        access_order_rejection_evidence(tcx, &verdict)
            .expect("fixture must produce a rejecting verdict")
    })
    .unwrap()
}

#[test]
fn detects_same_base_mut_and_const_args() {
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = a.as_ptr();
            callee(p, q, len);
        }
        "#,
    );

    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0usize],
            vec![1usize]
        )],
        "expected one candidate with mutable arg 0 and immutable arg 1"
    );
}

#[test]
fn different_arrays_are_not_same_base() {
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let mut b: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = b.as_ptr();
            callee(p, q, len);
        }
        "#,
    );

    assert!(
        candidates.is_empty(),
        "distinct array bases must not be same-base: {candidates:#?}"
    );
}

#[test]
fn mismatched_pointee_types_are_rejected() {
    // out: *mut i32 and src: *const u8 are not a compatible element type pair even
    // if they share a base, so the call site is rejected.
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const u8, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = a.as_ptr() as *const u8;
            callee(p, q, len);
        }
        "#,
    );

    assert!(
        candidates.is_empty(),
        "mismatched pointee types must be rejected: {candidates:#?}"
    );
}

#[test]
fn non_rewriteable_base_is_rejected_when_access_order_is_unknown() {
    // The opaque external allocation prevents a call-site access-order proof,
    // so the conservative snapshot detector rejects the otherwise same-base call.
    let candidates = run_detection(
        r#"
        extern "C" {
            fn xalloc(n: usize) -> *mut i32;
        }
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let base = xalloc(64);
            let p = base;
            let q = base as *const i32;
            callee(p, q, len);
        }
        "#,
    );

    assert!(
        candidates.is_empty(),
        "unknown access-order evidence must reject snapshotting: {candidates:#?}"
    );
}

#[test]
fn vec_backed_base_is_detected() {
    // Both arguments are offsets into the same `Vec` buffer, so they must
    // resolve to one base and make the call site a candidate.
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut v: Vec<u8> = vec![0; 64];
            let p = v.as_mut_ptr().offset(2);
            let q = v.as_mut_ptr().offset(2) as *const u8;
            callee(p, q, len);
        }
        "#,
    );

    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0usize],
            vec![1usize]
        )],
        "vec-backed same-base arguments must be detected: {candidates:#?}"
    );
}

#[test]
fn indirect_calls_are_rejected() {
    let candidates = run_detection(
        r#"
        pub unsafe fn driver(len: i32, f: unsafe fn(*mut i32, *const i32, i32)) {
            let mut a: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = a.as_ptr();
            f(p, q, len);
        }
        "#,
    );

    assert!(
        candidates.is_empty(),
        "indirect calls must be rejected: {candidates:#?}"
    );
}

#[test]
fn null_initialized_pointer_still_resolves_to_its_array_base() {
    // `p` retains a null provenance alternative, but a null pointer cannot be
    // dereferenced, so it does not obscure the array base the access-order
    // analysis needs.
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let mut p: *mut i32 = core::ptr::null_mut();
            p = a.as_mut_ptr();
            let q = a.as_ptr();
            callee(p, q, len);
        }
        "#,
    );

    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0usize],
            vec![1usize]
        )],
        "the null alternative must not reject the snapshot candidate: {candidates:#?}"
    );
}

#[test]
fn mixed_call_sites_keep_only_the_same_base_site() {
    // callee is called twice: once with same-base args, once with distinct arrays.
    // Only the same-base call site is a candidate.
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let mut b: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = a.as_ptr();
            callee(p, q, len);
            let r = a.as_mut_ptr();
            let s = b.as_ptr();
            callee(r, s, len);
        }
        "#,
    );

    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0usize],
            vec![1usize]
        )],
        "exactly one same-base call site should be a candidate: {candidates:#?}"
    );
}

#[test]
fn snapshot_detection_accepts_only_proven_order() {
    // All reads through `src` happen before the store through `out`.
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc += *src.offset(i as isize); i += 1; }
            *out = acc;
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = a.as_ptr();
            callee(p, q, len);
        }
        "#,
    );
    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0usize],
            vec![1usize]
        )],
    );
}

#[test]
fn alias_pair_attributed_to_both_call_sites() {
    // Two callers each pass same-base argument pairs to one callee: the pair
    // (0, 1) must map to both calls.
    let pairs = run_attribution(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn caller_a(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            callee(a.as_mut_ptr(), a.as_ptr(), len);
        }
        pub unsafe fn caller_b(len: i32) {
            let mut b: [i32; 8] = [0; 8];
            callee(b.as_mut_ptr(), b.as_ptr(), len);
        }
        "#,
    );
    assert_eq!(
        pairs,
        vec![(
            "callee".to_string(),
            (0usize, 1usize),
            vec!["caller_a".to_string(), "caller_b".to_string()],
        )],
        "expected one pair attributed to both call sites"
    );
}

#[test]
fn distinct_bases_contribute_no_pair() {
    let pairs = run_attribution(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = (*out, *src, len);
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            let mut b: [i32; 16] = [0; 16];
            callee(a.as_mut_ptr(), b.as_ptr(), len);
        }
        "#,
    );
    assert!(
        pairs.is_empty(),
        "distinct bases must contribute no pair: {pairs:#?}"
    );
}

#[test]
fn indirect_call_contributes_no_pair() {
    let pairs = run_attribution(
        r#"
        pub unsafe fn driver(len: i32, f: unsafe fn(*mut i32, *const i32, i32)) {
            let mut a: [i32; 16] = [0; 16];
            f(a.as_mut_ptr(), a.as_ptr(), len);
        }
        "#,
    );
    assert!(
        pairs.is_empty(),
        "indirect calls must contribute no pair: {pairs:#?}"
    );
}

#[test]
fn snapshot_detection_rejects_hazard_witness() {
    let candidates = run_detection(
        r#"
        #[inline(never)]
        pub unsafe fn callee(out: *mut f64, src: *const f64, len: usize) {
            let mut i = 0;
            while i < len {
                *out.add(i) = *src.add(i) * 2.0;
                i += 1;
            }
        }
        pub unsafe fn driver(len: usize) {
            let mut a: [f64; 16] = [0.0; 16];
            callee(a.as_mut_ptr().add(1), a.as_ptr(), len);
        }
        "#,
    );
    assert!(
        candidates.is_empty(),
        "a modeled cross-iteration hazard must reject snapshotting: {candidates:#?}"
    );
}

#[test]
fn snapshot_detection_rejects_unknown_reason() {
    let candidates = run_detection(
        r#"
        #[inline(never)]
        pub unsafe fn callee(out: *mut f64, src: *const f64, len: usize) {
            let mut i = 0;
            while i < len {
                *out.add(i) = *src.add(i) * 2.0;
                i += 1;
            }
        }
        pub unsafe fn driver(shift: usize, len: usize) {
            let mut a: [f64; 16] = [0.0; 16];
            callee(a.as_mut_ptr().add(shift), a.as_ptr(), len);
        }
        "#,
    );
    assert!(
        candidates.is_empty(),
        "an unknown actual offset must reject snapshotting: {candidates:#?}"
    );
}

#[test]
fn snapshot_gate_accepts_only_never_written() {
    let (gated, selected) = run_planning(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let _ = len;
            *out = *src;
        }
        pub unsafe fn driver(len: i32) {
            let mut a: [i32; 16] = [0; 16];
            callee(a.as_mut_ptr(), a.as_ptr(), len);
        }
        "#,
    );
    assert_eq!(
        gated,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec!["prefix(1, 1)".to_string()],
        )],
    );
    assert_eq!(selected, vec!["callee".to_string()]);
}

#[test]
fn snapshot_gate_rejects_modeled_immutable_write() {
    let (gated, selected) = run_planning(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32) {
            let value = *src;
            *(src as *mut i32) = value;
            *out = value;
        }
        pub unsafe fn driver() {
            let mut a: [i32; 16] = [0; 16];
            callee(a.as_mut_ptr(), a.as_ptr());
        }
        "#,
    );
    assert!(
        gated.is_empty(),
        "a modeled write through the immutable formal must reject the site: {gated:#?}"
    );
    assert!(
        selected.is_empty(),
        "a rejected site must not select its callee: {selected:#?}"
    );
}

#[test]
fn snapshot_trace_prints_specific_witness_or_reason() {
    let hazard = run_access_order_rejection_evidence(
        r#"
        #[inline(never)]
        unsafe fn callee(out: *mut f64, src: *const f64, len: usize) {
            let mut i = 0;
            while i < len {
                *out.add(i) = *src.add(i) * 2.0;
                i += 1;
            }
        }
        pub unsafe fn driver(base: *mut f64, len: usize) {
            callee(base.add(1), base, len);
        }
        "#,
        "driver",
        "callee",
    );
    assert!(hazard.contains("hazard"), "missing hazard kind: {hazard}");
    assert!(
        hazard.contains("write_location=bb") && hazard.contains("read_location=bb"),
        "missing stable witness locations: {hazard}"
    );
    assert!(
        hazard.contains("write_offset=") && hazard.contains("read_offset="),
        "missing substituted offsets: {hazard}"
    );
    assert!(
        hazard.contains("write_call_chain=") && hazard.contains("read_call_chain="),
        "missing witness call chains: {hazard}"
    );

    let unknown = run_access_order_rejection_evidence(
        r#"
        #[inline(never)]
        unsafe fn callee(out: *mut f64, src: *const f64, len: usize) {
            let mut i = 0;
            while i < len {
                *out.add(i) = *src.add(i) * 2.0;
                i += 1;
            }
        }
        pub unsafe fn driver(base: *mut f64, shift: usize, len: usize) {
            callee(base.add(shift), base, len);
        }
        "#,
        "driver",
        "callee",
    );
    assert_eq!(unknown, "unknown reasons=[UnknownOffset]");

    ::utils::compilation::run_compiler_on_str(
        "pub unsafe fn caller(base: *mut i32) { let _ = base; }",
        |tcx| {
            let input = collect_input(tcx);
            let caller = named_function(tcx, &input.functions, "caller");
            let evidence = query_error_evidence(tcx, &QueryError::MissingCallerFlow { caller });
            assert!(
                evidence.contains("missing_caller_flow") && evidence.contains("caller=caller"),
                "missing specific query-error evidence: {evidence}"
            );
        },
    )
    .unwrap();

    assert!(
        unknown.contains(&format!("{:?}", AccessUnknownReason::UnknownOffset)),
        "unknown reason must be named: {unknown}"
    );
}

#[test]
fn same_base_different_offsets_remain_one_candidate_group() {
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, left: *const i32, right: *const i32) {
            let _ = (out, left, right);
        }
        pub unsafe fn driver() {
            let mut a: [i32; 16] = [0; 16];
            callee(
                a.as_mut_ptr().add(1),
                a.as_ptr(),
                a.as_ptr().add(2),
            );
        }
        "#,
    );
    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0],
            vec![1, 2],
        )],
        "offsets must not split one provenance base into separate candidate groups"
    );
}

#[test]
fn whole_array_fallback_is_selected_when_count_is_a_linear_parameter() {
    // The foreign memcpy count `n` is linear in a callee parameter, so
    // access-order now proves the effect instead of invalidating it; the
    // whole-array copy fallback applies since the exact count isn't known
    // to `ReadExtentAnalysis` and the callee never observes the pointer's
    // address.
    let (gated, selected) = run_planning(
        r#"
        extern "C" {
            fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8;
        }
        pub unsafe fn callee(out: *mut u8, src: *const u8, n: usize) {
            memcpy(out, src, n);
        }
        pub unsafe fn driver(n: usize) {
            let mut a: [u8; 32] = [0; 32];
            callee(a.as_mut_ptr(), a.as_ptr(), n);
        }
        "#,
    );
    assert_eq!(
        gated,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec!["whole(1, 32)".to_string()],
        )]
    );
    assert_eq!(selected, vec!["callee".to_string()]);
}

#[test]
fn address_observing_callee_gets_no_plan() {
    // No exact prefix (runtime length), and the whole-array fallback is
    // blocked because the callee compares the pointer.
    let (gated, selected) = run_planning(
        r#"
        extern "C" {
            fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8;
        }
        pub unsafe fn callee(out: *mut u8, src: *const u8, n: usize) {
            if src == out as *const u8 {
                return;
            }
            memcpy(out, src, n);
        }
        pub unsafe fn driver(n: usize) {
            let mut a: [u8; 32] = [0; 32];
            callee(a.as_mut_ptr(), a.as_ptr(), n);
        }
        "#,
    );
    assert!(gated.is_empty(), "no copy plan must gate out: {gated:#?}");
    assert!(
        selected.is_empty(),
        "uncovered pair must not select: {selected:#?}"
    );
}

/// The fors chain in miniature: `outer` passes one array twice into `mid`,
/// which forwards both of its parameters straight to `leaf`. The chain must
/// root in a concrete allocation — a parameter with no callers above it has
/// an empty points-to set, and no pairs would form anywhere.
const FORS_CHAIN: &str = r#"
pub unsafe fn leaf(out: *mut i32, src: *const i32, _n: i32) {
    *out = *src;
}
pub unsafe fn mid(a: *mut i32, b: *const i32) {
    leaf(a, b, 1);
}
pub unsafe fn outer() {
    let mut arr: [i32; 4] = [0; 4];
    mid(arr.as_mut_ptr(), arr.as_ptr());
}
"#;

#[test]
fn forwarding_chain_selects_caller_and_callee() {
    // outer's site is the only candidate; leaf's pair is created by mid's
    // internal forwarding call and discharges through mid's own covered pair.
    let (gated, selected) = run_planning(FORS_CHAIN);
    assert_eq!(
        gated,
        vec![(
            "outer".to_string(),
            "mid".to_string(),
            vec!["prefix(1, 1)".to_string()],
        )],
    );
    assert_eq!(selected, vec!["leaf".to_string(), "mid".to_string()]);
}

#[test]
fn genuinely_aliasing_site_blocks_only_its_callee() {
    // A third caller feeds leaf an aliasing pair that is neither a candidate
    // (the source pointer has two possible bases) nor a parameter forward,
    // so leaf must not select; mid's own pair is still covered.
    let code = format!(
        "{FORS_CHAIN}
        pub unsafe fn evil(flag: i32) {{
            let mut a: [i32; 4] = [0; 4];
            let mut b: [i32; 4] = [0; 4];
            let p = a.as_mut_ptr();
            let q = if flag != 0 {{ a.as_ptr() }} else {{ b.as_ptr() }};
            leaf(p, q, 2);
        }}
        "
    );
    let (_, selected) = run_planning(&code);
    assert_eq!(selected, vec!["mid".to_string()]);
}

#[test]
fn callee_with_one_ungated_site_selects_nothing() {
    let (gated, selected) = run_planning(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32) {
            *out = *src;
        }
        pub unsafe fn good() {
            let mut a: [i32; 8] = [0; 8];
            callee(a.as_mut_ptr(), a.as_ptr());
        }
        pub unsafe fn evil(flag: i32) {
            let mut a: [i32; 4] = [0; 4];
            let mut b: [i32; 4] = [0; 4];
            let p = a.as_mut_ptr();
            let q = if flag != 0 { a.as_ptr() } else { b.as_ptr() };
            callee(p, q);
        }
        "#,
    );
    assert_eq!(gated.len(), 1, "good's site must still gate: {gated:#?}");
    assert!(
        selected.is_empty(),
        "one unresolved site must block selection: {selected:#?}"
    );
}

const RUNTIME_FMA: &str = r#"
pub unsafe fn fma_array(
    out: *mut i32,
    mul1: *const i32,
    mul2: *const i32,
    add: *const i32,
    len: i32,
) {
    let mut i = 0i32;
    while i < len {
        *out.offset(i as isize) = *mul1.offset(i as isize)
            * *mul2.offset(i as isize)
            + *add.offset(i as isize);
        i += 1;
    }
}
pub unsafe fn driver(out: *mut i32, len: i32) {
    fma_array(out, out, out, out, len);
}
pub unsafe fn root(len: i32) {
    let mut values = [0i32; 16];
    driver(values.as_mut_ptr(), len);
}
"#;

#[test]
fn runtime_prefix_is_selected_for_direct_caller_parameter() {
    let (gated, selected) = run_planning(RUNTIME_FMA);
    assert_eq!(
        gated,
        vec![(
            "driver".to_string(),
            "fma_array".to_string(),
            vec![
                "runtime(1, 4)".to_string(),
                "runtime(2, 4)".to_string(),
                "runtime(3, 4)".to_string(),
            ],
        )],
    );
    assert_eq!(selected, vec!["fma_array".to_string()]);
}

#[test]
fn runtime_extent_still_prefers_whole_array() {
    let code = RUNTIME_FMA.replace(
        "pub unsafe fn driver(out: *mut i32, len: i32) {\n    fma_array(out, out, out, out, len);\n}",
        "pub unsafe fn driver(_out: *mut i32, len: i32) { let mut values = [0i32; 16]; fma_array(values.as_mut_ptr(), values.as_ptr(), values.as_ptr(), values.as_ptr(), len); }",
    );
    let (gated, _) = run_planning(&code);
    assert_eq!(
        gated[0].2,
        vec![
            "whole(1, 16)".to_string(),
            "whole(2, 16)".to_string(),
            "whole(3, 16)".to_string(),
        ],
    );
}

#[test]
fn constant_length_keeps_exact_prefix() {
    let code = RUNTIME_FMA.replace(
        "fma_array(out, out, out, out, len);",
        "fma_array(out, out, out, out, 4);",
    );
    let (gated, _) = run_planning(&code);
    assert_eq!(
        gated[0].2,
        vec![
            "prefix(1, 4)".to_string(),
            "prefix(2, 4)".to_string(),
            "prefix(3, 4)".to_string(),
        ],
    );
}

#[test]
fn runtime_length_must_be_a_direct_caller_parameter() {
    for replacement in [
        "let count = len; fma_array(out, out, out, out, count);",
        "fma_array(out, out, out, out, len.wrapping_add(0));",
    ] {
        let code = RUNTIME_FMA.replace("fma_array(out, out, out, out, len);", replacement);
        let (gated, selected) = run_planning(&code);
        assert!(
            gated.is_empty(),
            "unexpected runtime plan for: {replacement}"
        );
        assert!(
            selected.is_empty(),
            "unexpected selected callee for: {replacement}"
        );
    }

    let cast = RUNTIME_FMA
        .replace(
            "pub unsafe fn driver(out: *mut i32, len: i32)",
            "pub unsafe fn driver(out: *mut i32, len: i64)",
        )
        .replace(
            "fma_array(out, out, out, out, len);",
            "fma_array(out, out, out, out, len as i32);",
        )
        .replace(
            "pub unsafe fn root(len: i32)",
            "pub unsafe fn root(len: i64)",
        );
    let (gated, selected) = run_planning(&cast);
    assert!(gated.is_empty());
    assert!(selected.is_empty());
}

#[test]
fn runtime_length_from_branching_temp_is_rejected() {
    // The length argument is an inline two-armed conditional over two
    // different caller parameters, so the compiler lowers it to an
    // anonymous (no `debug` entry) join temp with two definitions, one per
    // arm. `skip_anonymous_copies` must not walk through a temp with more
    // than one definition: doing so would silently pick whichever arm's
    // assignment happens to appear first in block order, regardless of
    // `flag`, and could plan a copy of the wrong length.
    let code = RUNTIME_FMA
        .replace(
            "pub unsafe fn driver(out: *mut i32, len: i32) {\n    fma_array(out, out, out, out, len);\n}",
            "pub unsafe fn driver(out: *mut i32, n: i32, m: i32, flag: i32) {\n    fma_array(out, out, out, out, if flag != 0 { n } else { m });\n}",
        )
        .replace(
            "pub unsafe fn root(len: i32) {\n    let mut values = [0i32; 16];\n    driver(values.as_mut_ptr(), len);\n}",
            "pub unsafe fn root(n: i32, m: i32, flag: i32) {\n    let mut values = [0i32; 16];\n    driver(values.as_mut_ptr(), n, m, flag);\n}",
        );
    let (gated, selected) = run_planning(&code);
    assert!(gated.is_empty(), "unexpected runtime plan: {gated:#?}");
    assert!(
        selected.is_empty(),
        "unexpected selected callee: {selected:#?}"
    );
}

#[test]
fn runtime_prefix_rejects_non_copy_pointee() {
    let code = r#"
#[repr(C)]
pub struct NonCopy { value: i32 }
pub unsafe fn callee(out: *mut NonCopy, src: *const NonCopy, n: i32) {
    let mut i = 0i32;
    while i < n {
        (*out.offset(i as isize)).value = (*src.offset(i as isize)).value;
        i += 1;
    }
}
pub unsafe fn driver(base: *mut NonCopy, n: i32) { callee(base, base, n); }
pub unsafe fn root(n: i32) {
    let mut values = [NonCopy { value: 0 }, NonCopy { value: 0 }];
    driver(values.as_mut_ptr(), n);
}
"#;
    let (gated, selected) = run_planning(code);
    assert!(gated.is_empty());
    assert!(selected.is_empty());
}

#[test]
fn runtime_prefix_rejects_zero_sized_pointee() {
    let code = r#"
#[derive(Clone, Copy)]
pub struct Z;
pub unsafe fn callee(out: *mut Z, src: *const Z, n: i32) {
    let mut i = 0i32;
    while i < n {
        *out.offset(i as isize) = *src.offset(i as isize);
        i += 1;
    }
}
pub unsafe fn driver(base: *mut Z, n: i32) { callee(base, base, n); }
pub unsafe fn root(n: i32) { let mut value = Z; driver(&mut value, n); }
"#;
    let (gated, selected) = run_planning(code);
    assert!(gated.is_empty());
    assert!(selected.is_empty());
}

#[test]
fn runtime_prefix_rejects_two_length_parameters_at_one_site() {
    let code = r#"
pub unsafe fn callee(out: *mut i32, left: *const i32, right: *const i32, a: i32, b: i32) {
    let mut left_sum = 0i32;
    let mut i = 0i32;
    while i < a { left_sum = left_sum.wrapping_add(*left.offset(i as isize)); i += 1; }
    let mut right_sum = 0i32;
    let mut j = 0i32;
    while j < b { right_sum = right_sum.wrapping_add(*right.offset(j as isize)); j += 1; }
    *out = left_sum.wrapping_add(right_sum);
}
pub unsafe fn driver(base: *mut i32, a: i32, b: i32) { callee(base, base, base, a, b); }
pub unsafe fn root(a: i32, b: i32) {
    let mut values = [0i32; 16];
    driver(values.as_mut_ptr(), a, b);
}
"#;
    let (gated, selected) = run_planning(code);
    assert!(gated.is_empty());
    assert!(selected.is_empty());
}
