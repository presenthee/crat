use points_to::andersen;
use rustc_hash::FxHashSet;
use typed_arena::Arena;
use utils::ty_shape;

use super::detect_pattern2_candidates;
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

        let mut out: Vec<_> = detect_pattern2_candidates(&input, &provenances)
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
