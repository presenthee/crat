use points_to::andersen;
use rustc_hash::FxHashSet;
use typed_arena::Arena;
use utils::ty_shape;

use super::{
    CopyPlan, attribute_alias_pairs, detect_snapshot_candidates, gate_candidates, select_callees,
};
use crate::{
    analyses::{array_local_provenance, read_extent::ReadExtentAnalysis},
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
        let provenances =
            array_local_provenance::array_local_provenance_analysis(&input, &alloc_fns);

        let access_order = outparam_replacer::ai::access_order::analyze_access_order(tcx);
        let mut out: Vec<_> = detect_snapshot_candidates(&input, &provenances, &access_order)
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
/// selected callees. Plans render as `prefix(<arg>, <elems>)` and
/// `whole(<arg>, <len>)`.
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
        let provenances =
            array_local_provenance::array_local_provenance_analysis(&input, &alloc_fns);
        let access_order = outparam_replacer::ai::access_order::analyze_access_order(tcx);

        let candidates = detect_snapshot_candidates(&input, &provenances, &access_order);
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
fn non_rewriteable_base_is_detected() {
    // Both arguments share a single non-directly-rewriteable base (an opaque/heap
    // pointer from an extern allocation). The call site still feeds the callee's
    // alias cluster, so it must be detected; whether a copy can be planned for it
    // is decided later from the recorded admissibility.
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

    assert_eq!(
        candidates,
        vec![(
            "driver".to_string(),
            "callee".to_string(),
            vec![0usize],
            vec![1usize]
        )],
        "non-directly-rewriteable base must still be detected: {candidates:#?}"
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
fn null_initialized_pointer_still_resolves_to_base() {
    // `p` is null-initialized then assigned the array pointer; the null must be
    // seen through so `p` resolves to the same base as `q`.
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
        "null-initialized pointer must still resolve to the array base: {candidates:#?}"
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
fn read_before_write_callee_is_kept() {
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
fn read_after_write_callee_is_dropped() {
    // The second store reads through `src` after writing through `out`. A bare
    // `let _ = *src` is eliminated from MIR for Copy types, so the read is
    // anchored as the rvalue of a subsequent store to ensure it appears in MIR.
    let candidates = run_detection(
        r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32) {
            *out = 5;
            *out = *src;
        }
        pub unsafe fn driver() {
            let mut a: [i32; 16] = [0; 16];
            let p = a.as_mut_ptr();
            let q = a.as_ptr();
            callee(p, q);
        }
        "#,
    );
    assert!(
        candidates.is_empty(),
        "read-after-write callee must be dropped: {candidates:#?}"
    );
}

#[test]
fn exact_prefix_planned_for_known_extent() {
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
fn whole_array_planned_when_extent_unknown() {
    // The memcpy length is a runtime parameter, so no exact prefix exists;
    // the base is a caller-local array and the callee never observes the
    // pointer's address, so the whole array is copied instead.
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
        )],
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
