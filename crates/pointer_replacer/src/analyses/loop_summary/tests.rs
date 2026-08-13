use rustc_hir::ItemKind;
use rustc_middle::ty::TyCtxt;

use super::summarize_loops;

fn find_fn(tcx: TyCtxt<'_>, name: &str) -> rustc_hir::def_id::LocalDefId {
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if let ItemKind::Fn { ident, .. } = item.kind
            && ident.name.as_str() == name
        {
            return item.owner_id.def_id;
        }
    }
    panic!("no function named {name}");
}

fn run(code: &str, fn_name: &str) -> Vec<outparam_replacer::ai::access_order::LoopSummary> {
    let fn_name = fn_name.to_string();
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        summarize_loops(tcx, find_fn(tcx, &fn_name))
    })
    .unwrap()
}

#[test]
fn recognizes_counted_loop_without_param_accesses() {
    // A counted loop touching only a local scalar: recognizable, empty
    // sets. `buf[i as usize % 8]` was tried first, but `%` lowers to an
    // extra div-by-zero `Assert` block ahead of the bounds-check `Assert`,
    // which breaks the single-chain body this test wants to exercise; a
    // plain scalar increment keeps the body branch-free.
    let summaries = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0i32;
            let mut i = 0;
            while i < len { acc += 1; i += 1; }
            acc
        }
        "#,
        "f",
    );
    assert_eq!(summaries.len(), 1);
    let s = &summaries[0];
    assert!(s.reads.is_empty() && s.writes.is_empty() && s.internal_pairs.is_empty());
    assert!(!s.blocks.is_empty());
}

#[test]
fn refuses_loop_with_call_in_body() {
    let summaries = run(
        r#"
        pub unsafe fn helper(x: i32) -> i32 { x + 1 }
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc = helper(acc); i += 1; }
            acc
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

#[test]
fn refuses_loop_with_branchy_body() {
    let summaries = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len {
                if i % 2 == 0 { acc += 1; }
                i += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

#[test]
fn refuses_non_unit_step() {
    let summaries = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc += 1; i += 2; }
            acc
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

#[test]
fn refuses_double_increment() {
    // Two `i += 1` statements in the same block net a stride of +2; the
    // step count must be totaled over statements, not blocks, or this
    // wrongly passes as a stride-1 loop.
    let summaries = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc += 1; i += 1; i += 1; }
            acc
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

#[test]
fn fma_loop_reads_and_writes_classified_no_internal_pairs() {
    // Reads of args 1,2,3 precede the write of arg 0 within each iteration.
    let summaries = run(
        r#"
        pub unsafe fn fma(out: *mut i32, m1: *const i32, m2: *const i32,
                          a: *const i32, len: i32) {
            let mut i = 0;
            while i < len {
                *out.offset(i as isize) =
                    *m1.offset(i as isize) * *m2.offset(i as isize) + *a.offset(i as isize);
                i += 1;
            }
        }
        "#,
        "fma",
    );
    assert_eq!(summaries.len(), 1);
    let s = &summaries[0];
    assert_eq!(s.writes, [0].into_iter().collect());
    assert_eq!(s.reads, [1, 2, 3].into_iter().collect());
    assert!(s.internal_pairs.is_empty());
}

#[test]
fn write_before_read_in_body_yields_internal_pair() {
    let summaries = run(
        r#"
        pub unsafe fn f(out: *mut i32, src: *const i32, len: i32) {
            let mut i = 0;
            let mut acc = 0;
            while i < len {
                *out.offset(i as isize) = 1;
                acc += *src.offset(i as isize);
                i += 1;
            }
            *out = acc;
        }
        "#,
        "f",
    );
    assert_eq!(summaries.len(), 1);
    let s = &summaries[0];
    assert!(s.internal_pairs.contains(&(1, 0)));
}

#[test]
fn refuses_non_iv_subscript() {
    // src is read at i - 1: not the plain IV, so the loop is refused.
    let summaries = run(
        r#"
        pub unsafe fn f(out: *mut i32, src: *const i32, len: i32) {
            let mut i = 1;
            while i < len {
                *out.offset(i as isize) = *src.offset((i - 1) as isize);
                i += 1;
            }
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

#[test]
fn refuses_untraceable_indirect_access() {
    // Write through a pointer loaded from memory: not the recognized pattern.
    let summaries = run(
        r#"
        pub unsafe fn f(tbl: *mut *mut i32, len: i32) {
            let mut i = 0;
            while i < len {
                **tbl.offset(i as isize) = 0;
                i += 1;
            }
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

#[test]
fn refuses_copy_nonoverlapping_intrinsic() {
    // `copy_nonoverlapping` lowers to a `StatementKind::Intrinsic`, which
    // reads `src` and writes `out` without going through an `Assign`
    // statement; classify_accesses must not silently skip it.
    let summaries = run(
        r#"
        pub unsafe fn f(out: *mut i32, src: *const i32, len: i32) {
            let mut i = 0;
            while i < len {
                core::intrinsics::copy_nonoverlapping(src.offset(i as isize), out.offset(i as isize), 1);
                i += 1;
            }
        }
        "#,
        "f",
    );
    assert!(summaries.is_empty());
}

use outparam_replacer::ai::access_order::{AccessOrderSummary, analyze_access_order};
use rustc_hash::FxHashMap;

/// Run the recognizer on every local fn, then the access-order analysis with
/// the resulting summaries.
fn run_access_order(code: &str) -> FxHashMap<String, AccessOrderSummary> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut summaries = FxHashMap::default();
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            if let ItemKind::Fn { .. } = item.kind {
                let def_id = item.owner_id.def_id;
                summaries.insert(def_id, summarize_loops(tcx, def_id));
            }
        }
        analyze_access_order(tcx, &summaries)
            .into_iter()
            .map(|(def_id, s)| (tcx.item_name(def_id.to_def_id()).to_string(), s))
            .collect()
    })
    .unwrap()
}

#[test]
fn interleaved_fma_is_ordered_with_summaries() {
    let s = run_access_order(
        r#"
        pub unsafe fn fma(out: *mut i32, m1: *const i32, m2: *const i32,
                          a: *const i32, len: i32) {
            let mut i = 0;
            while i < len {
                *out.offset(i as isize) =
                    *m1.offset(i as isize) * *m2.offset(i as isize) + *a.offset(i as isize);
                i += 1;
            }
        }
        "#,
    );
    let fma = &s["fma"];
    assert!(!fma.unanalyzable);
    assert!(fma.reads_precede_writes(&[0], &[1, 2, 3]));
    assert!(fma.may_write_params.contains(&0));
}

#[test]
fn write_before_summarized_loop_pairs_with_its_reads() {
    let s = run_access_order(
        r#"
        pub unsafe fn f(out: *mut i32, src: *const i32, len: i32) {
            *out = 0;
            let mut i = 0;
            let mut acc = 0;
            while i < len { acc += *src.offset(i as isize); i += 1; }
            *out = acc;
        }
        "#,
    );
    // The loop's read of src follows the first write of out.
    assert!(!s["f"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn sequential_summarized_loops_pair_across_loops() {
    let s = run_access_order(
        r#"
        pub unsafe fn f(out: *mut i32, src: *const i32, len: i32) {
            let mut i = 0;
            while i < len { *out.offset(i as isize) = 0; i += 1; }
            let mut acc = 0;
            i = 0;
            while i < len { acc += *src.offset(i as isize); i += 1; }
            *out = acc;
        }
        "#,
    );
    // Loop 2 reads src after loop 1 wrote out.
    assert!(!s["f"].reads_precede_writes(&[0], &[1]));
}
