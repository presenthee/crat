use rustc_hir::ItemKind;
use rustc_middle::ty::TyCtxt;

use super::{Ctx, Extent, ReadExtentAnalysis};

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

/// Queries the read extent of `fn_name`'s parameter `param` under `ctx`.
fn run_extent(code: &str, fn_name: &str, param: usize, ctx: &[(usize, u128)]) -> Extent {
    let fn_name = fn_name.to_string();
    let ctx: Ctx = ctx.iter().copied().collect();
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        ReadExtentAnalysis::new(tcx).extent(find_fn(tcx, &fn_name), param, &ctx)
    })
    .unwrap()
}

/// Queries whether `fn_name` may observe the identity of parameter `param`.
fn run_identity(code: &str, fn_name: &str, param: usize) -> bool {
    let fn_name = fn_name.to_string();
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        ReadExtentAnalysis::new(tcx)
            .classify_param_uses(find_fn(tcx, &fn_name), param)
            .identity_observed
    })
    .unwrap()
}

const MEMCPY: &str = r#"
extern "C" {
    fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8;
}
"#;

#[test]
fn const_length_memcpy_is_exact() {
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8) {{
            memcpy(out, src, 32);
        }}
        "
    );
    assert_eq!(run_extent(&code, "callee", 1, &[]), Extent::Const(32));
}

#[test]
fn adjacent_loads_form_a_prefix() {
    // Two single-byte loads at offsets 0 and 1 union to the prefix [0, 2).
    let code = r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            *out = *src;
            *out.offset(1) = *src.offset(1);
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Const(2));
}

/// The thash shape: a VLA allocation whose length involves the block-count
/// parameter, then a memcpy of `n * 16` bytes from the queried pointer. The
/// allocation and the `Vec` pointer methods must be survived as
/// non-diverging, and the length must const-evaluate through the wrapping
/// call under the context.
const THASH: &str = r#"
extern "C" {
    fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8;
}
pub unsafe fn thash(out: *mut u8, input: *const u8, n: u32) {
    let mut buf: Vec<u8> = ::std::vec::from_elem(0, (22 + n * 16) as usize);
    memcpy(buf.as_mut_ptr().offset(22), input, n.wrapping_mul(16) as usize);
    *out = *buf.as_ptr();
}
"#;

#[test]
fn vla_then_memcpy_specializes_to_context() {
    assert_eq!(run_extent(THASH, "thash", 1, &[(2, 1)]), Extent::Const(16));
    assert_eq!(run_extent(THASH, "thash", 1, &[(2, 2)]), Extent::Const(32));
}

/// The guarded haraka shape: the branch on the block count is pruned under
/// the context, leaving a single live arm whose memcpy dominates the exit in
/// the pruned CFG.
const GUARDED: &str = r#"
extern "C" {
    fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8;
}
pub unsafe fn guarded(out: *mut u8, src: *const u8, n: u32) {
    if n == 1 {
        memcpy(out, src, 16);
    } else {
        memcpy(out, src, n.wrapping_mul(16) as usize);
    }
}
"#;

#[test]
fn guard_on_context_parameter_is_pruned() {
    assert_eq!(
        run_extent(GUARDED, "guarded", 1, &[(2, 1)]),
        Extent::Const(16)
    );
    assert_eq!(
        run_extent(GUARDED, "guarded", 1, &[(2, 2)]),
        Extent::Const(32)
    );
}

#[test]
fn unresolved_branch_with_agreeing_arms_is_exact() {
    // The guard cannot be evaluated (its operand is not in the context), but
    // both arms read the same 16 bytes, so the reads certify at the branch.
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8, flag: u32) {{
            if flag != 0 {{
                memcpy(out, src, 16);
            }} else {{
                memcpy(out.offset(16), src, 16);
            }}
        }}
        "
    );
    assert_eq!(run_extent(&code, "callee", 1, &[]), Extent::Const(16));
}

/// The fors shape: a wrapper forwards its pointer whole to a thash-shaped
/// callee with a literal block count, so the wrapper's extent is the callee's
/// under the forwarded context.
#[test]
fn forwarding_with_literal_scalar_recurses() {
    let code = r#"
extern "C" {
    fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8;
}
pub unsafe fn thash(out: *mut u8, input: *const u8, n: u32) {
    let mut buf: Vec<u8> = ::std::vec::from_elem(0, (22 + n * 16) as usize);
    memcpy(buf.as_mut_ptr().offset(22), input, n.wrapping_mul(16) as usize);
    *out = *buf.as_ptr();
}
pub unsafe fn wrapper(out: *mut u8, input: *const u8) {
    thash(out, input, 1);
}
"#;
    assert_eq!(run_extent(code, "wrapper", 1, &[]), Extent::Const(16));
}

#[test]
fn unresolved_branch_with_differing_arms_is_unknown() {
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8, flag: u32) {{
            if flag != 0 {{
                memcpy(out, src, 16);
            }} else {{
                memcpy(out, src, 32);
            }}
        }}
        "
    );
    assert_eq!(run_extent(&code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn non_prefix_load_is_unknown() {
    // A single load at byte offset 4 leaves a gap at 0, so no contiguous
    // prefix exists.
    let code = r#"
        pub unsafe fn callee(out: *mut u32, src: *const u32) {
            *out = *src.offset(1);
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn length_with_uncovered_parameter_is_unknown() {
    // The length is a product of two scalar parameters and only one is in
    // the context.
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8, a: u32, b: u32) {{
            memcpy(out, src, a.wrapping_mul(b) as usize);
        }}
        "
    );
    assert_eq!(run_extent(&code, "callee", 1, &[(2, 2)]), Extent::Unknown);
}

#[test]
fn pointer_passed_to_extern_is_unknown() {
    let code = r#"
        extern "C" {
            fn consume(p: *const u8);
        }
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            consume(src);
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn pointer_comparison_is_unknown() {
    // Comparing the pointer observes its identity, which a snapshot copy
    // would change.
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8) {{
            if src == out as *const u8 {{
                return;
            }}
            memcpy(out, src, 16);
        }}
        "
    );
    assert_eq!(run_extent(&code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn pointer_cast_to_integer_is_unknown() {
    let code = r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            *out = (src as usize) as u8;
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn mutual_recursion_is_unknown() {
    let code = format!(
        "{MEMCPY}
        pub unsafe fn ping(out: *mut u8, src: *const u8) {{
            memcpy(out, src, 16);
            pong(out, src);
        }}
        pub unsafe fn pong(out: *mut u8, src: *const u8) {{
            ping(out, src);
        }}
        "
    );
    assert_eq!(run_extent(&code, "ping", 1, &[]), Extent::Unknown);
}

#[test]
fn opaque_call_before_read_is_unknown() {
    // The unknown local callee may diverge, so the read after it does not
    // happen on every execution.
    let code = format!(
        "{MEMCPY}
        pub fn helper() {{}}
        pub unsafe fn callee(out: *mut u8, src: *const u8) {{
            helper();
            memcpy(out, src, 16);
        }}
        "
    );
    assert_eq!(run_extent(&code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn context_cap_stops_the_seventeenth_query() {
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8, n: u32) {{
            memcpy(out, src, n as usize);
        }}
        "
    );
    let results = ::utils::compilation::run_compiler_on_str(&code, move |tcx| {
        let mut analysis = ReadExtentAnalysis::new(tcx);
        let def_id = find_fn(tcx, "callee");
        (1..=17u128)
            .map(|n| analysis.extent(def_id, 1, &[(2, n)].into_iter().collect()))
            .collect::<Vec<_>>()
    })
    .unwrap();
    for (i, result) in results.iter().enumerate().take(16) {
        assert_eq!(*result, Extent::Const(i as u64 + 1));
    }
    assert_eq!(results[16], Extent::Unknown);
}

/// The wots-checksum shape: an indexed loop reading one element per
/// iteration up to a constant bound.
#[test]
fn indexed_loop_with_constant_bound_is_exact() {
    let code = r#"
        pub unsafe fn checksum(out: *mut u32, msg: *const u32) {
            let mut csum: u32 = 0;
            let mut i: u32 = 0;
            while i < 8 {
                csum = csum.wrapping_add(*msg.offset(i as isize));
                i = i.wrapping_add(1);
            }
            *out = csum;
        }
        "#;
    // 8 elements of 4 bytes each; 32 divides evenly into `[u32; 8]` for a
    // caller-side element conversion.
    assert_eq!(run_extent(code, "checksum", 1, &[]), Extent::Const(32));
}

#[test]
fn indexed_loop_with_context_bound_is_exact() {
    let code = r#"
        pub unsafe fn checksum(out: *mut u32, msg: *const u32, n: u32) {
            let mut csum: u32 = 0;
            let mut i: u32 = 0;
            while i < n {
                csum = csum.wrapping_add(*msg.offset(i as isize));
                i = i.wrapping_add(1);
            }
            *out = csum;
        }
        "#;
    assert_eq!(
        run_extent(code, "checksum", 1, &[(2, 8)]),
        Extent::Const(32)
    );
    // Without the bound in the context the iteration count is unknown.
    assert_eq!(run_extent(code, "checksum", 1, &[]), Extent::Unknown);
}

#[test]
fn doubly_zero_initialized_index_is_exact() {
    // C2Rust lowers `unsigned i; for (i = 0; ...)` to a default-initialized
    // declaration plus a separate zero assignment; both are zeros, so the
    // loop still matches.
    let code = r#"
        pub unsafe fn checksum(out: *mut u32, msg: *const u32) {
            let mut csum: u32 = 0;
            let mut i: u32 = 0;
            i = 0 as u32;
            while i < 8 {
                csum = csum.wrapping_add(*msg.offset(i as isize));
                i = i.wrapping_add(1);
            }
            *out = csum;
        }
        "#;
    assert_eq!(run_extent(code, "checksum", 1, &[]), Extent::Const(32));
}

#[test]
fn stride_two_loop_is_unknown() {
    // Every other element is skipped, so the footprint is not a contiguous
    // prefix read on every iteration.
    let code = r#"
        pub unsafe fn callee(out: *mut u32, msg: *const u32) {
            let mut acc: u32 = 0;
            let mut i: u32 = 0;
            while i < 8 {
                acc = acc.wrapping_add(*msg.offset(i as isize));
                i = i.wrapping_add(2);
            }
            *out = acc;
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn displaced_index_load_is_unknown() {
    // The load sits at `i + 1`, so offset 0 is never read.
    let code = r#"
        pub unsafe fn callee(out: *mut u32, msg: *const u32) {
            let mut acc: u32 = 0;
            let mut i: u32 = 0;
            while i < 8 {
                acc = acc.wrapping_add(*msg.offset(i.wrapping_add(1) as isize));
                i = i.wrapping_add(1);
            }
            *out = acc;
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn loop_with_data_dependent_break_is_unknown() {
    // The break is a second way out of the loop, so the later iterations'
    // reads are not guaranteed.
    let code = r#"
        pub unsafe fn callee(out: *mut u32, msg: *const u32) {
            let mut acc: u32 = 0;
            let mut i: u32 = 0;
            while i < 8 {
                if *msg.offset(i as isize) == 42 {
                    break;
                }
                acc = acc.wrapping_add(1);
                i = i.wrapping_add(1);
            }
            *out = acc;
        }
        "#;
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

/// The dec32le leaf shape: four adjacent single-byte loads assembled into a
/// word, expressible with plain constant-offset loads.
#[test]
fn four_byte_loads_form_the_leaf_prefix() {
    let code = r#"
        pub unsafe fn dec32le(src: *const u8) -> u32 {
            (*src.offset(0) as u32)
                | (*src.offset(1) as u32) << 8
                | (*src.offset(2) as u32) << 16
                | (*src.offset(3) as u32) << 24
        }
        "#;
    assert_eq!(run_extent(code, "dec32le", 0, &[]), Extent::Const(4));
}

#[test]
fn leaf_with_missing_offset_is_unknown() {
    // Offsets 0, 1, 3 leave a hole at byte 2.
    let code = r#"
        pub unsafe fn dec_gap(src: *const u8) -> u32 {
            (*src.offset(0) as u32)
                | (*src.offset(1) as u32) << 8
                | (*src.offset(3) as u32) << 24
        }
        "#;
    assert_eq!(run_extent(code, "dec_gap", 0, &[]), Extent::Unknown);
}

/// The br_range_dec32le shape: a pre-tested count-down loop walking a
/// cursor over the source four bytes at a time, reading each group through
/// a leaf callee.
const RANGE_READ: &str = r#"
pub unsafe fn leaf(dst: *mut u32, src: *const u8) {
    *dst = (*src.offset(0) as u32)
        | (*src.offset(1) as u32) << 8
        | (*src.offset(2) as u32) << 16
        | (*src.offset(3) as u32) << 24;
}
pub unsafe fn range_read(v: *mut u32, src: *const u8) {
    let mut buf: *const u8 = src;
    let mut out: *mut u32 = v;
    let mut num: usize = 16;
    loop {
        let fresh = num;
        num = num.wrapping_sub(1);
        if !(fresh > 0) {
            break;
        }
        leaf(out, buf);
        out = out.offset(1);
        buf = buf.offset(4);
    }
}
"#;

#[test]
fn walking_countdown_loop_with_literal_count_is_exact() {
    assert_eq!(
        run_extent(RANGE_READ, "range_read", 1, &[]),
        Extent::Const(64)
    );
}

/// The full haraka chain: a wrapper forwards the pointer to the range
/// reader with a literal count of 16, whose loop walks the cursor in
/// four-byte steps read by the leaf.
const CHAIN: &str = r#"
pub unsafe fn leaf(dst: *mut u32, src: *const u8) {
    *dst = (*src.offset(0) as u32)
        | (*src.offset(1) as u32) << 8
        | (*src.offset(2) as u32) << 16
        | (*src.offset(3) as u32) << 24;
}
pub unsafe fn range_read(v: *mut u32, mut num: usize, src: *const u8) {
    let mut buf: *const u8 = src;
    let mut out: *mut u32 = v;
    loop {
        let fresh = num;
        num = num.wrapping_sub(1);
        if !(fresh > 0) {
            break;
        }
        leaf(out, buf);
        out = out.offset(1);
        buf = buf.offset(4);
    }
}
pub unsafe fn perm(out: *mut u32, src: *const u8) {
    range_read(out, 16, src);
}
"#;

#[test]
fn three_level_walking_chain_is_exact() {
    assert_eq!(run_extent(CHAIN, "perm", 1, &[]), Extent::Const(64));
}

/// The real haraka `br_range_dec32le` shape: the source parameter itself is
/// the walking cursor (`src = src.offset(4)`), the output pointer walks too,
/// and the per-iteration read is a value-returning leaf.
#[test]
fn parameter_as_walking_cursor_is_exact() {
    let code = r#"
pub unsafe fn leaf(src: *const u8) -> u32 {
    (*src.offset(0) as u32)
        | (*src.offset(1) as u32) << 8
        | (*src.offset(2) as u32) << 16
        | (*src.offset(3) as u32) << 24
}
pub unsafe fn range_read(mut v: *mut u32, mut num: usize, mut src: *const u8) {
    loop {
        let fresh = num;
        num = num.wrapping_sub(1);
        if !(fresh > 0) {
            break;
        }
        *v = leaf(src);
        v = v.offset(1);
        src = src.offset(4);
    }
}
pub unsafe fn perm(out: *mut u8, in_0: *const u8) {
    let mut w: [u32; 16] = [0; 16];
    range_read(w.as_mut_ptr(), 16, in_0);
    *out = w[0] as u8;
}
"#;
    assert_eq!(
        run_extent(code, "range_read", 2, &[(1, 16)]),
        Extent::Const(64)
    );
    assert_eq!(run_extent(code, "perm", 1, &[]), Extent::Const(64));
}

#[test]
fn walking_count_not_in_context_is_unknown() {
    // Queried directly with nothing bound, the count parameter has no
    // value, so the iteration count is unknown.
    assert_eq!(run_extent(CHAIN, "range_read", 2, &[]), Extent::Unknown);
    assert_eq!(
        run_extent(CHAIN, "range_read", 2, &[(1, 16)]),
        Extent::Const(64)
    );
}

#[test]
fn cursor_stepped_twice_is_unknown() {
    let code = r#"
pub unsafe fn leaf(dst: *mut u32, src: *const u8) {
    *dst = (*src.offset(0) as u32)
        | (*src.offset(1) as u32) << 8
        | (*src.offset(2) as u32) << 16
        | (*src.offset(3) as u32) << 24;
}
pub unsafe fn range_read(v: *mut u32, src: *const u8) {
    let mut buf: *const u8 = src;
    let mut out: *mut u32 = v;
    let mut num: usize = 16;
    loop {
        let fresh = num;
        num = num.wrapping_sub(1);
        if !(fresh > 0) {
            break;
        }
        leaf(out, buf);
        out = out.offset(1);
        buf = buf.offset(4);
        buf = buf.offset(4);
    }
}
"#;
    assert_eq!(run_extent(code, "range_read", 1, &[]), Extent::Unknown);
}

#[test]
fn callee_extent_differing_from_step_is_unknown() {
    // The leaf reads four bytes but the cursor advances by eight, so the
    // walked range is not a contiguous prefix.
    let code = r#"
pub unsafe fn leaf(dst: *mut u32, src: *const u8) {
    *dst = (*src.offset(0) as u32)
        | (*src.offset(1) as u32) << 8
        | (*src.offset(2) as u32) << 16
        | (*src.offset(3) as u32) << 24;
}
pub unsafe fn range_read(v: *mut u32, src: *const u8) {
    let mut buf: *const u8 = src;
    let mut out: *mut u32 = v;
    let mut num: usize = 16;
    loop {
        let fresh = num;
        num = num.wrapping_sub(1);
        if !(fresh > 0) {
            break;
        }
        leaf(out, buf);
        out = out.offset(1);
        buf = buf.offset(8);
    }
}
"#;
    assert_eq!(run_extent(code, "range_read", 1, &[]), Extent::Unknown);
}

#[test]
fn identity_ignores_load_offsets() {
    // A load at a non-constant offset defeats the extent walk but never
    // observes the address.
    let code = r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8, i: isize) {
            *out = *src.offset(i);
            *out.offset(1) = *src.offset(4);
        }
        "#;
    assert!(!run_identity(code, "callee", 1));
    assert_eq!(run_extent(code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn identity_ignores_unknown_memcpy_length() {
    let code = format!(
        "{MEMCPY}
        pub unsafe fn callee(out: *mut u8, src: *const u8, n: usize) {{
            memcpy(out, src, n);
        }}
        "
    );
    assert!(!run_identity(&code, "callee", 1));
    assert_eq!(run_extent(&code, "callee", 1, &[]), Extent::Unknown);
}

#[test]
fn identity_ignores_walking_cursor() {
    // A multi-definition cursor with an unknown count matches no loop
    // schema, but the address never escapes.
    let code = r#"
        pub unsafe fn sum(src: *const u8, n: usize) -> u8 {
            let mut q: *const u8 = src;
            let mut num: usize = n;
            let mut acc: u8 = 0;
            while num > 0 {
                acc = acc.wrapping_add(*q);
                q = q.offset(1);
                num = num.wrapping_sub(1);
            }
            acc
        }
        "#;
    assert!(!run_identity(code, "sum", 0));
}

#[test]
fn identity_ignores_writes_through() {
    // Writing through the pointer is the never-written gate's business; the
    // address itself is not observed.
    let code = r#"
        pub unsafe fn callee(dst: *mut u8) {
            *dst = 0;
            *dst.offset(1) = 1;
        }
        "#;
    assert!(!run_identity(code, "callee", 0));
}

#[test]
fn identity_recursion_depth_is_bounded() {
    // The sha2 shape needs three forwarding levels (sha256 → inc_finalize →
    // crypto_hashblocks → load_bigendian); a fourth exhausts the budget.
    let code = r#"
        pub unsafe fn leaf(dst: *mut u8, src: *const u8) {
            *dst = *src;
        }
        pub unsafe fn mid(dst: *mut u8, src: *const u8) {
            leaf(dst, src);
        }
        pub unsafe fn outer(dst: *mut u8, src: *const u8) {
            mid(dst, src);
        }
        pub unsafe fn top(dst: *mut u8, src: *const u8) {
            outer(dst, src);
        }
        pub unsafe fn apex(dst: *mut u8, src: *const u8) {
            top(dst, src);
        }
        "#;
    assert!(!run_identity(code, "outer", 1));
    assert!(!run_identity(code, "top", 1));
    assert!(run_identity(code, "apex", 1));
}

#[test]
fn identity_observed_by_pointer_comparison() {
    let code = r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            if src == out as *const u8 {
                return;
            }
            *out = *src;
        }
        "#;
    assert!(run_identity(code, "callee", 1));
}

#[test]
fn identity_observed_by_null_check() {
    // A snapshot pointer is never null, so branching on nullness observes
    // the address.
    let code = r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            if src.is_null() {
                return;
            }
            *out = *src;
        }
        "#;
    assert!(run_identity(code, "callee", 1));
}

#[test]
fn identity_observed_by_store_into_static() {
    let code = r#"
        static mut STASH: *const u8 = std::ptr::null();
        pub unsafe fn callee(src: *const u8) {
            STASH = src;
        }
        "#;
    assert!(run_identity(code, "callee", 0));
}

#[test]
fn identity_observed_by_extern_call() {
    let code = r#"
        extern "C" {
            fn consume(p: *const u8);
        }
        pub unsafe fn callee(src: *const u8) {
            consume(src);
        }
        "#;
    assert!(run_identity(code, "callee", 0));
}

#[test]
fn identity_observed_by_return() {
    let code = r#"
        pub unsafe fn callee(src: *const u8) -> *const u8 {
            src
        }
        "#;
    assert!(run_identity(code, "callee", 0));
}

#[test]
fn identity_observed_by_integer_cast() {
    let code = r#"
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            *out = src as usize as u8;
        }
        "#;
    assert!(run_identity(code, "callee", 1));
}

#[test]
fn identity_observed_through_forwarding() {
    let code = r#"
        pub unsafe fn compare(a: *const u8, b: *const u8) -> i32 {
            (a == b) as i32
        }
        pub unsafe fn caller(a: *const u8, b: *const u8) {
            compare(a, b);
        }
        "#;
    assert!(run_identity(code, "caller", 0));
}
