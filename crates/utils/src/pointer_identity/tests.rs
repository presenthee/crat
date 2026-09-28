use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::*;
use crate::pointer_inventory::{PointerState, Site, StageId, collect_inventory};

fn inventory(code: &str) -> Inventory {
    crate::compilation::run_compiler_on_str(code, |tcx| {
        collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap()
}
fn mapped(
    code: &str,
    map: &DeclarationMap,
    hashes: &SourceHashes,
) -> Result<Inventory, MeasurementError> {
    crate::compilation::run_compiler_on_str(code, |tcx| reconcile(tcx, map, hashes)).unwrap()
}

#[test]
fn roundtrip_preserves_shadowed_and_anonymous_ids() {
    let code = "mod m { fn f(p: *mut u8) { let p = p; let p = p; let c = |q: *mut u8| q; } }";
    let before = inventory(code);
    let map = seed_map(&before);
    let printed = crate::compilation::run_compiler_on_str(code, |tcx| {
        let mut ast = crate::ast::expanded_ast(tcx);
        crate::ast::remove_unnecessary_items_from_ast(&mut ast);
        rustc_ast_pretty::pprust::crate_to_string_for_macros(&ast)
    })
    .unwrap();
    let after = mapped(&printed, &map, &SourceHashes::new()).unwrap();
    assert_eq!(
        before
            .declarations
            .iter()
            .map(|d| &d.declaration_id)
            .collect::<Vec<_>>(),
        after
            .declarations
            .iter()
            .map(|d| &d.declaration_id)
            .collect::<Vec<_>>()
    );
    let ps: Vec<_> = after
        .declarations
        .iter()
        .filter(|d| d.site == Site::Local && d.name.as_deref() == Some("p"))
        .collect();
    assert_eq!(ps.len(), 2);
    assert_ne!(ps[0].declaration_id, ps[1].declaration_id);
}

#[test]
fn changed_source_and_duplicate_clone_ids_are_rejected() {
    let code = "fn f(p: *mut u8) { let q = p; }";
    let mut inv = inventory(code);
    inv.source_hashes
        .insert("src/lib.rs".into(), "original".into());
    let map = seed_map(&inv);
    assert!(matches!(
        mapped(code, &map, &SourceHashes::new()),
        Err(MeasurementError::HashMismatch(_))
    ));
    let mut duplicate = map.clone();
    duplicate.entries[1].id = duplicate.entries[0].id.clone();
    assert!(matches!(
        mapped(code, &duplicate, &inv.source_hashes),
        Err(MeasurementError::DuplicateId(_))
    ));
    let mut duplicate = map.clone();
    duplicate.entries[1].locator = duplicate.entries[0].locator.clone();
    assert!(matches!(
        mapped(code, &duplicate, &inv.source_hashes),
        Err(MeasurementError::AmbiguousLocator(_))
    ));
    let mut missing = map.clone();
    missing.entries.pop();
    assert!(matches!(
        mapped(code, &missing, &inv.source_hashes),
        Err(MeasurementError::MissingId(_))
    ));
}

#[test]
fn explicit_output_map_preserves_renamed_identity_and_support_scope() {
    let before = inventory("fn f(p: *mut u8) {}");
    let after = inventory("fn f(renamed: *mut u8) {} mod support { pub fn g(q: *mut u8) {} }");
    let mut map = seed_map(&after);
    map.entries[0].id = before.declarations[0].declaration_id.clone();
    for entry in &mut map.entries[2..] {
        entry.scope = Scope::Support;
    }
    let out = mapped(
        "fn f(renamed: *mut u8) {} mod support { pub fn g(q: *mut u8) {} }",
        &map,
        &SourceHashes::new(),
    )
    .unwrap();
    assert_eq!(
        out.declarations[0].declaration_id,
        before.declarations[0].declaration_id
    );
    assert_eq!(out.declarations[0].name.as_deref(), Some("renamed"));
    assert_eq!(
        out.declarations
            .iter()
            .filter(|d| d.scope == Scope::Application && d.pointer_state == PointerState::Raw)
            .count(),
        1
    );
    assert!(
        out.declarations[2..]
            .iter()
            .all(|d| d.scope == Scope::Support)
    );
}

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct TestDir(PathBuf);
impl TestDir {
    fn new() -> Self {
        let p = std::env::temp_dir().join(format!(
            "crat-pointer-identity-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&p).unwrap();
        Self(p)
    }
}
impl Drop for TestDir {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn hashes_are_relative_reproducible_and_confined() {
    let a = TestDir::new();
    let b = TestDir::new();
    fs::write(a.0.join("lib.rs"), "abc").unwrap();
    fs::write(b.0.join("lib.rs"), "abc").unwrap();
    let h = hash_sources(&a.0, &["lib.rs".into()]).unwrap();
    assert_eq!(
        h["lib.rs"],
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(h, hash_sources(&b.0, &["lib.rs".into()]).unwrap());
    assert!(hash_sources(&a.0, &["../lib.rs".into()]).is_err());
    assert!(hash_sources(&a.0, &["lib.rs".into(), "lib.rs".into()]).is_err());
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(b.0.join("lib.rs"), a.0.join("escape.rs")).unwrap();
        assert!(hash_sources(&a.0, &["escape.rs".into()]).is_err());
    }
}

#[test]
fn ast_bindings_cover_source_declarations_before_type_queries() {
    let code = "struct S { p: *mut u8 } unsafe extern \"C\" { fn foreign(_: *mut u8); } fn f(p: *mut u8) { let p = p; let c = |q: *mut u8| q; }";
    crate::compilation::run_compiler_on_str(code, |tcx| {
        let mut ast = crate::ast::expanded_ast(tcx);
        let mapper = crate::ast::make_ast_to_hir(&mut ast, tcx);
        let (inv, nodes) = crate::pointer_inventory::collect_bound_inventory(
            tcx,
            &ast,
            &mapper,
            "fixture",
            StageId("input".into()),
        );
        assert!(inv.issues.is_empty(), "{:?}", inv.issues);
        assert_eq!(nodes.len(), inv.declarations.len());
        assert_eq!(
            nodes.iter().collect::<std::collections::HashSet<_>>().len(),
            nodes.len()
        );
        assert!(nodes.iter().all(|n| *n != rustc_ast::DUMMY_NODE_ID));
    })
    .unwrap();
}

#[test]
fn hashes_include_legitimate_measurement_and_reports_modules() {
    let dir = TestDir::new();
    for name in ["measurement", "reports"] {
        fs::create_dir(dir.0.join(name)).unwrap();
        fs::write(dir.0.join(name).join("mod.rs"), "pub fn f() {}").unwrap();
    }
    assert_eq!(crate_source_paths(&dir.0).unwrap(), vec![PathBuf::from("measurement/mod.rs"), PathBuf::from("reports/mod.rs")]);
}
