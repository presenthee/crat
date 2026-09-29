use super::*;

fn inventory(code: &str) -> Inventory {
    crate::compilation::run_compiler_on_str(code, |tcx| {
        collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap()
}

#[test]
fn counts_declarations_and_nested_slots() {
    let inv = inventory(
        r#"
        struct S { ptr: *mut u8 }
        unsafe fn f(p: *mut *const u8) -> *const u8 {
            let q = 0usize as *mut u8;
            *p
        }
    "#,
    );
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    let raw: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
        .collect();
    assert_eq!(raw.len(), 4);
    assert_eq!(
        raw.iter()
            .flat_map(|d| &inv.observations[&d.declaration_id].slots)
            .filter(|s| s.kind.is_raw())
            .count(),
        5
    );
    for site in [Site::Param, Site::Return, Site::Field, Site::Local] {
        assert_eq!(raw.iter().filter(|d| d.site == site).count(), 1, "{site:?}");
    }
}

#[test]
fn normalizes_aliases_optional_wrappers_and_nested_rawness() {
    let inv = inventory(
        r#"
        type Raw = *mut u8;
        fn f(a: Raw, b: &u8, c: &mut u8, d: Option<&u8>, e: Option<&mut u8>,
             f: Box<u8>, g: Option<Box<u8>>, h: Box<[u8]>, i: Option<Box<[u8]>>,
             j: &[u8], k: &mut [u8], l: &mut *const u8, m: Option<Raw>,
             n: Option<&[u8]>, o: [*const u8; 100]) {}
    "#,
    );
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    let params: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| d.site == Site::Param)
        .collect();
    let kinds: Vec<_> = params.iter().map(|d| inv.observations[&d.declaration_id].slots[0].kind).collect();
    assert_eq!(
        kinds,
        [
            PointerKind::RawMut,
            PointerKind::Ref,
            PointerKind::RefMut,
            PointerKind::OptRef,
            PointerKind::OptRefMut,
            PointerKind::Box,
            PointerKind::OptBox,
            PointerKind::BoxedSlice,
            PointerKind::OptBoxedSlice,
            PointerKind::Slice,
            PointerKind::SliceMut,
            PointerKind::RefMut,
            PointerKind::RawMut,
            PointerKind::Slice,
            PointerKind::RawConst
        ]
    );
    assert_eq!(endpoint_state(&inv.observations[&params[11].declaration_id]), EndpointState::Raw);
    assert_eq!(inv.observations[&params[11].declaration_id].slots.len(), 2);
    assert!(inv.observations[&params[12].declaration_id].slots[0].optional);
    assert!(inv.observations[&params[13].declaration_id].slots[0].optional);
    assert_eq!(inv.observations[&params[14].declaration_id].slots.len(), 1);
}

#[test]
fn patterns_and_signatures_are_counted_once() {
    let inv = inventory(
        r#"
        unsafe fn f((a,b): (*mut u8, *mut u8), _: *const u8) {
            let p = a;
            let p = b;
            match Some(p) { Some(q) | Some(q) => (), _ => () }
        }
    "#,
    );
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    let params: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| d.site == Site::Param)
        .collect();
    assert_eq!(params.len(), 2);
    assert_eq!(inv.observations[&params[0].declaration_id].slots.len(), 2);
    let locals: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| d.site == Site::Local)
        .collect();
    assert_eq!(locals.len(), 3);
    assert_eq!(
        locals
            .iter()
            .filter(|d| d.name.as_deref() == Some("p"))
            .count(),
        2
    );
    assert_eq!(
        locals
            .iter()
            .filter(|d| d.name.as_deref() == Some("q"))
            .count(),
        1
    );
    assert_ne!(locals[0].declaration_id, locals[1].declaration_id);
}

#[test]
fn includes_methods_closures_constants_and_foreign_signatures() {
    let inv = inventory(
        r#"
        struct S;
        impl S {
            const P: *const u8 = 0 as _;
            fn m(&self, p: *mut u8) -> *mut u8 { p }
        }
        static mut P: *mut u8 = 0 as _;
        extern "C" { fn external(p: *mut u8) -> *mut u8; static mut X: *mut u8; }
        fn f() { let f = |p: *mut u8| -> *mut u8 { p }; }
    "#,
    );
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| d.scope == Scope::Foreign && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
            .count(),
        3
    );
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| d.site == Site::Const && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
            .count(),
        1
    );
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| d.site == Site::Param
                && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw
                && d.scope == Scope::Application)
            .count(),
        2
    );
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| d.site == Site::Return
                && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw
                && d.scope == Scope::Application)
            .count(),
        2
    );
}

#[test]
fn excludes_phantom_storage_and_function_signature_payloads() {
    let inv = inventory(
        r#"
        fn f(a: std::marker::PhantomData<*mut u8>, b: fn(*mut u8) -> *mut u8,
             c: Option<unsafe fn(*mut u8)>, d: *const u8) {}
    "#,
    );
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    let params: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| d.site == Site::Param)
        .collect();
    assert!(inv.observations[&params[0].declaration_id].slots.is_empty());
    assert_eq!(inv.observations[&params[1].declaration_id].slots.len(), 1);
    assert_eq!(inv.observations[&params[1].declaration_id].slots[0].kind, PointerKind::FnPtr);
    assert_eq!(inv.observations[&params[2].declaration_id].slots[0].kind, PointerKind::OptFnPtr);
    assert_eq!(
        params
            .iter()
            .filter(|d| endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
            .count(),
        1
    );
}

#[test]
fn opaque_wrappers_are_not_silently_removed() {
    let inv = inventory(r#"fn f(p: std::ptr::NonNull<u8>) {}"#);
    assert!(inv.structural_errors.is_empty());
    let d = inv.declarations.iter().find(|d| d.site == Site::Param).unwrap();
    assert_eq!(endpoint_state(&inv.observations[&d.declaration_id]), EndpointState::Unknown);
    assert_eq!(inv.observations[&d.declaration_id].diagnostics.len(),1);
}

#[test]
fn cursor_kinds_use_registered_type_identity() {
    crate::compilation::run_compiler_on_str(
        r#"
        struct Cursor<'a, T> { base: &'a [T], pos: usize }
        struct CursorMut<'a, T> { base: &'a mut [T], pos: usize }
        mod other { pub struct Cursor; }
        fn f(a: Cursor<'_, u8>, b: CursorMut<'_, u8>, c: other::Cursor) {}
    "#,
        |tcx| {
            let f = tcx
                .hir_free_items()
                .find(|id| {
                    matches!(tcx.hir_item(*id).kind, rustc_hir::ItemKind::Fn { .. })
                        && tcx.item_name(id.owner_id.to_def_id()).as_str() == "f"
                })
                .unwrap();
            let sig = tcx.fn_sig(f.owner_id).instantiate_identity().skip_binder();
            let mut roles = TypeRoles::default();
            for (ty, mutable) in [(sig.inputs()[0], false), (sig.inputs()[1], true)] {
                let rustc_middle::ty::Adt(def, _) = ty.kind() else { panic!() };
                roles.cursors.insert(def.did(), mutable);
            }
            assert_eq!(
                observe_type(sig.inputs()[0], tcx, &roles).slots[0].kind,
                PointerKind::SliceCursor
            );
            assert_eq!(
                observe_type(sig.inputs()[1], tcx, &roles).slots[0].kind,
                PointerKind::SliceCursorMut
            );
            assert!(
                observe_type(sig.inputs()[2], tcx, &roles).slots
                    .is_empty()
            );
        },
    )
    .unwrap();
}

#[test]
fn ignores_desugared_iterator_bindings_and_counts_variant_fields_once() {
    let inv = inventory(
        r#"
        enum E { A(*mut u8), B { p: *const u8 } }
        fn f() { for p in [0usize as *mut u8] { let q = p; } }
    "#,
    );
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    let fields: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| d.site == Site::Field)
        .collect();
    assert_eq!(fields.len(), 2);
    let locals: Vec<_> = inv
        .declarations
        .iter()
        .filter(|d| d.site == Site::Local)
        .collect();
    assert_eq!(locals.len(), 2, "{locals:?}");
    assert!(locals.iter().all(|d| endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw));
}

#[test]
fn opaque_c_void_pointee_is_not_an_unknown_wrapper() {
    let inv = inventory("fn f(p: *mut core::ffi::c_void) {} ");
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    assert_eq!(endpoint_state(&inv.observations[&inv.declarations[0].declaration_id]), EndpointState::Raw);
}

#[test]
fn unsupported_issues_keep_distinct_structural_locators() {
    let inv = inventory(
        "fn a(p: std::ptr::NonNull<u8>) {} fn b(q: std::ptr::NonNull<u8>) {} fn c(r: std::ptr::NonNull<u8>) {}",
    );
    let expected: std::collections::BTreeSet<_> = inv
        .declarations
        .iter()
        .filter(|d| endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Unknown)
        .map(|d| d.locator.clone())
        .collect();
    let actual: std::collections::BTreeSet<_> = inv.declarations.iter()
        .filter(|d| !inv.observations[&d.declaration_id].diagnostics.is_empty())
        .map(|d| d.locator.clone()).collect();
    assert_eq!(actual.len(),3);
    assert_eq!(actual, expected);
}

#[test]
fn distinct_anonymous_const_owners_have_distinct_signature_sites() {
    let inv = inventory("const _: () = { fn check() {} }; const _: () = { fn check() {} };");
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| d.site == Site::Return)
            .count(),
        2
    );
}

#[test]
fn anonymous_constants_are_not_named_pointer_declarations() {
    let inv =
        inventory("const _: *const u8 = 0 as *const u8; const KEEP: *const u8 = 0 as *const u8;");
    assert!(inv.structural_errors.is_empty(), "{:?}", inv.structural_errors);
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
            .count(),
        1
    );
    assert!(
        inv.declarations
            .iter()
            .all(|d| d.name.as_deref() != Some("_"))
    );
}
