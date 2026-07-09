use super::{ReadExtents, ScalarCtx};
use crate::rewriter::collect_input;

/// Read extent in bytes of `fn_name`'s `param` (0-based) under `ctx` entries
/// of (param index, constant bits).
fn extent_of(code: &str, fn_name: &str, param: usize, ctx: &[(usize, u128)]) -> Option<u64> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let input = collect_input(tcx);
        let def_id = input
            .functions
            .iter()
            .copied()
            .find(|d| tcx.item_name(d.to_def_id()).as_str() == fn_name)
            .unwrap_or_else(|| panic!("function {fn_name} not found"));
        let ctx: ScalarCtx = ctx.iter().copied().collect();
        ReadExtents::new(tcx).extent_bytes(def_id, param, &ctx)
    })
    .unwrap()
}

const MEMCPY_DECL: &str = r#"
extern "C" {
    fn memcpy(
        dst: *mut core::ffi::c_void,
        src: *const core::ffi::c_void,
        n: usize,
    ) -> *mut core::ffi::c_void;
}
"#;

#[test]
fn const_memcpy_len_is_exact_extent() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn callee(out: *mut u8, src: *const u8) {{
            let mut buf: [u8; 16] = [0; 16];
            memcpy(
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                16,
            );
            *out = buf[0];
        }}
        "
    );
    assert_eq!(extent_of(&code, "callee", 1, &[]), Some(16));
}

/// The thash shape: a VLA allocated with `vec::from_elem` before the read (the
/// curated non-diverging set must let the walk pass it), and a memcpy length
/// computed from a parameter through wrapping-arithmetic calls, resolved by
/// the call-site context.
#[test]
fn param_scaled_memcpy_len_resolves_under_context() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn thash_like(out: *mut u8, in_0: *const u8, inblocks: u32) {{
            let vla = (22u32).wrapping_add(inblocks.wrapping_mul(16u32)) as usize;
            let mut buf: Vec<u8> = ::std::vec::from_elem(0, vla);
            memcpy(
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                in_0 as *const core::ffi::c_void,
                inblocks.wrapping_mul(16u32) as usize,
            );
            *out = buf[0];
        }}
        "
    );
    assert_eq!(extent_of(&code, "thash_like", 1, &[(2, 1)]), Some(16));
    assert_eq!(extent_of(&code, "thash_like", 1, &[(2, 2)]), Some(32));
    assert_eq!(
        extent_of(&code, "thash_like", 1, &[]),
        None,
        "length must stay unknown without a context"
    );
}

/// The haraka thash shape: branches on the block-count parameter with a
/// different memcpy in each arm. Context pruning resolves the branch; without
/// a context the arms disagree and there is no exact footprint.
#[test]
fn context_prunes_block_count_branch() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn thash_branch(out: *mut u8, in_0: *const u8, inblocks: u32) {{
            let mut small: [u8; 64] = [0; 64];
            if inblocks == 1u32 {{
                memcpy(
                    small.as_mut_ptr() as *mut core::ffi::c_void,
                    in_0 as *const core::ffi::c_void,
                    16,
                );
            }} else {{
                memcpy(
                    small.as_mut_ptr() as *mut core::ffi::c_void,
                    in_0 as *const core::ffi::c_void,
                    inblocks.wrapping_mul(16u32) as usize,
                );
            }}
            *out = small[0];
        }}
        "
    );
    assert_eq!(extent_of(&code, "thash_branch", 1, &[(2, 1)]), Some(16));
    assert_eq!(extent_of(&code, "thash_branch", 1, &[(2, 2)]), Some(32));
    assert_eq!(extent_of(&code, "thash_branch", 1, &[]), None);
}

/// The fors_sk_to_leaf shape: the pointer is forwarded whole to a callee with
/// a literal block count; the extent comes from the recursive query.
#[test]
fn forwarding_with_literal_scalar_recurses() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn inner(out: *mut u8, src: *const u8, n: u32) {{
            let mut buf: [u8; 64] = [0; 64];
            memcpy(
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                n.wrapping_mul(16u32) as usize,
            );
            *out = buf[0];
        }}
        pub unsafe fn fwd(out: *mut u8, src: *const u8) {{
            inner(out, src, 1u32);
        }}
        "
    );
    assert_eq!(extent_of(&code, "fwd", 1, &[]), Some(16));
    assert_eq!(extent_of(&code, "inner", 1, &[(2, 2)]), Some(32));
}

#[test]
fn escaping_pointer_is_rejected() {
    let code = format!(
        "{MEMCPY_DECL}
        extern \"C\" {{
            fn stash(p: *const u8);
        }}
        pub unsafe fn callee(out: *mut u8, src: *const u8) {{
            stash(src);
            let mut buf: [u8; 16] = [0; 16];
            memcpy(
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                16,
            );
            *out = buf[0];
        }}
        "
    );
    assert_eq!(extent_of(&code, "callee", 1, &[]), None);
}

#[test]
fn pointer_identity_observation_is_rejected() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn callee(out: *mut u8, src: *const u8) {{
            let addr = src as usize;
            let mut buf: [u8; 16] = [0; 16];
            memcpy(
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                16,
            );
            *out = buf[0].wrapping_add(addr as u8);
        }}
        "
    );
    assert_eq!(extent_of(&code, "callee", 1, &[]), None);
}

#[test]
fn write_through_queried_pointer_is_rejected() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn callee(dst: *const u8, src: *const u8) {{
            memcpy(
                dst as *mut u8 as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                16,
            );
        }}
        "
    );
    assert_eq!(extent_of(&code, "callee", 0, &[]), None);
}

/// A read reached on only one arm of a branch the context cannot resolve has
/// no exact footprint even though the other arm reads nothing.
#[test]
fn conditional_read_is_rejected() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn callee(out: *mut u8, src: *const u8, flag: u32) {{
            let mut buf: [u8; 16] = [0; 16];
            if flag != 0 {{
                memcpy(
                    buf.as_mut_ptr() as *mut core::ffi::c_void,
                    src as *const core::ffi::c_void,
                    16,
                );
            }}
            *out = buf[0];
        }}
        "
    );
    assert_eq!(extent_of(&code, "callee", 1, &[]), None);
    assert_eq!(
        extent_of(&code, "callee", 1, &[(2, 1)]),
        Some(16),
        "the same branch resolves once the context pins the flag"
    );
}

/// Direct loads are not classified yet (they arrive with the loop schemas), so
/// a plain deref defeats the walk for now.
#[test]
fn direct_load_is_not_yet_classified() {
    let code = "
        pub unsafe fn callee(out: *mut u8, src: *const u8) {
            *out = *src;
        }
        ";
    assert_eq!(extent_of(code, "callee", 1, &[]), None);
}

/// A faithful reduction of SPHINCS+ `thash_sha2_simple::SPX_thash` and
/// `fors::fors_sk_to_leaf`: VLA allocation, unrelated memcpys (ctx state and
/// the address prefix), an `offset`-computed destination, a finalize call
/// after the read, and the whole-pointer forwarding chain with a literal
/// block count.
#[test]
fn sphincs_thash_and_fors_chain_shapes_resolve() {
    let code = format!(
        "{MEMCPY_DECL}
        extern \"C\" {{
            fn finalize(out: *mut u8, state: *mut u8, in_0: *const u8, inlen: usize);
        }}
        pub struct spx_ctx {{
            pub state_seeded: [u8; 40],
        }}
        pub unsafe fn spx_thash(
            out: *mut u8,
            in_0: *const u8,
            inblocks: u32,
            ctx: *const spx_ctx,
            addr: *mut u32,
        ) {{
            let mut outbuf: [u8; 32] = [0; 32];
            let mut sha2_state: [u8; 40] = [0; 40];
            let vla = (22u32).wrapping_add(inblocks.wrapping_mul(16u32)) as usize;
            let mut buf: Vec<u8> = ::std::vec::from_elem(0, vla);
            memcpy(
                sha2_state.as_mut_ptr() as *mut core::ffi::c_void,
                ((*ctx).state_seeded).as_ptr() as *const core::ffi::c_void,
                40,
            );
            memcpy(
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                addr as *const core::ffi::c_void,
                22,
            );
            memcpy(
                buf.as_mut_ptr().offset(22) as *mut core::ffi::c_void,
                in_0 as *const core::ffi::c_void,
                inblocks.wrapping_mul(16u32) as usize,
            );
            finalize(
                outbuf.as_mut_ptr(),
                sha2_state.as_mut_ptr(),
                buf.as_mut_ptr(),
                (22u32).wrapping_add(inblocks.wrapping_mul(16u32)) as usize,
            );
            memcpy(
                out as *mut core::ffi::c_void,
                outbuf.as_ptr() as *const core::ffi::c_void,
                16,
            );
        }}
        pub unsafe fn fors_sk_to_leaf(
            leaf: *mut u8,
            sk: *const u8,
            ctx: *const spx_ctx,
            addr: *mut u32,
        ) {{
            spx_thash(leaf, sk, 1u32, ctx, addr);
        }}
        "
    );
    assert_eq!(extent_of(&code, "spx_thash", 1, &[(2, 1)]), Some(16));
    assert_eq!(extent_of(&code, "spx_thash", 1, &[(2, 2)]), Some(32));
    assert_eq!(extent_of(&code, "fors_sk_to_leaf", 1, &[]), Some(16));
}

#[test]
fn recursive_forwarding_is_rejected() {
    let code = format!(
        "{MEMCPY_DECL}
        pub unsafe fn ping(out: *mut u8, src: *const u8) {{
            pong(out, src);
        }}
        pub unsafe fn pong(out: *mut u8, src: *const u8) {{
            ping(out, src);
        }}
        "
    );
    assert_eq!(extent_of(&code, "ping", 1, &[]), None);
}
