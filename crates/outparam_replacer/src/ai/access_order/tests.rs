use rustc_hash::FxHashMap;

use super::{AccessOrderSummary, analyze_access_order};

/// Map function name -> its summary, for assertions.
fn run(code: &str) -> FxHashMap<String, AccessOrderSummary> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        analyze_access_order(tcx)
            .into_iter()
            .map(|(def_id, summary)| (tcx.item_name(def_id.to_def_id()).to_string(), summary))
            .collect()
    })
    .unwrap()
}

#[test]
fn reads_all_inputs_before_writing_output() {
    // Reads through `src` all happen before the store through `out`.
    let s = run(r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let mut i = 0;
            let mut acc = 0;
            while i < len { acc += *src.offset(i as isize); i += 1; }
            *out = acc;
        }
        "#);
    let callee = &s["callee"];
    assert!(!callee.unanalyzable);
    // out is arg 0, src is arg 1: no read of src after the write to out.
    assert!(callee.reads_precede_writes(&[0], &[1]));
}

#[test]
fn write_then_read_is_flagged() {
    // The assignment *out = *src reads through src after the write to *out.
    // The read is placed in the second store's rvalue because a bare
    // `let _ = *src` is elided from MIR for Copy types.
    let s = run(r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32) {
            *out = 5;
            *out = *src;
        }
        "#);
    assert!(!s["callee"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn shifted_loop_is_flagged() {
    // Iteration i writes out[i]; a later iteration reads src[i-1]; with out and
    // src aliased this is a read that may observe a prior write.
    let s = run(r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, len: i32) {
            let mut i = 1;
            while i < len { *out.offset(i as isize) = *src.offset((i - 1) as isize) + 1; i += 1; }
        }
        "#);
    assert!(!s["callee"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn store_through_unknown_pointer_is_unanalyzable() {
    let s = run(r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, sel: *mut *mut i32) {
            let p = *sel;
            *p = *src;
        }
        "#);
    assert!(s["callee"].unanalyzable || !s["callee"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn read_only_helper_call_does_not_write() {
    // `validate` only reads its parameter; composing its summary must not treat
    // `out` as written, so the later read of `src` produces no pair.
    let s = run(r#"
        pub unsafe fn validate(p: *const i32) -> i32 { *p }
        pub unsafe fn callee(out: *mut i32, src: *const i32) {
            let _ = validate(out as *const i32);
            *out = *src;
        }
        "#);
    assert!(!s["callee"].unanalyzable);
    assert!(s["callee"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn helper_write_then_read_is_flagged() {
    // `store` writes through its parameter. After `store(out, ...)`, reading
    // `src` is a read that may observe that write.
    let s = run(r#"
        pub unsafe fn store(p: *mut i32, v: i32) { *p = v; }
        pub unsafe fn callee(out: *mut i32, src: *const i32) {
            store(out, 5);
            *out = *src;
        }
        "#);
    assert!(!s["callee"].unanalyzable);
    assert!(!s["callee"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn branchy_read_after_conditional_write() {
    // On one path `out` is written before `src` is read, so the read of `src`
    // may observe that write. The final store uses `*src` as its rvalue so the
    // read appears in MIR (a bare `let _ = *src` is eliminated for Copy types).
    let s = run(r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32, cond: bool) {
            if cond { *out = 5; }
            *out = *src;
        }
        "#);
    assert!(!s["callee"].unanalyzable);
    assert!(!s["callee"].reads_precede_writes(&[0], &[1]));
}

#[test]
fn write_through_effect_intrinsic_is_tracked() {
    // A volatile write to `out` is a real write; a later read of `src` (as
    // the return value) may observe it. The callee must stay analyzable AND
    // flag the pair (src read after out written).
    let s = run(r#"
        pub unsafe fn callee(out: *mut i32, src: *const i32) -> i32 {
            core::ptr::write_volatile(out, 5);
            *src
        }
        "#);
    assert!(!s["callee"].unanalyzable);
    assert!(!s["callee"].reads_precede_writes(&[0], &[1]));
}
