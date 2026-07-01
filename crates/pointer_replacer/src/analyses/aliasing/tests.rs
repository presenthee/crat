use points_to::andersen;
use rustc_hash::FxHashSet;
use typed_arena::Arena;
use utils::ty_shape;

use super::detect_snapshot_candidates;
use crate::{analyses::array_local_provenance, rewriter::collect_input};

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

        let mut out: Vec<_> = detect_snapshot_candidates(&input, &provenances)
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
fn non_rewriteable_base_is_rejected() {
    // Both arguments share a single non-directly-rewriteable base (an opaque/heap
    // pointer from an extern allocation), so the call site is rejected.
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
        "non-directly-rewriteable base must be rejected: {candidates:#?}"
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
