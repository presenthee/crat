use ::utils::{
    compilation::run_compiler_on_str,
    pointer_identity::seed_map,
    pointer_inventory::{PointerState, collect_bound_inventory},
};
use rustc_ast::{self as ast, mut_visit::MutVisitor};

use super::*;
fn fixture<R: Send>(
    action: impl FnOnce(&mut ast::Crate, &mut Measurement, NodeId) -> R + Send,
) -> R {
    run_compiler_on_str("fn f(p: *mut u8) { let q = p; }", |tcx| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let mapper = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        let (inventory, nodes) =
            collect_bound_inventory(tcx, &krate, &mapper, "fixture", StageId("input".into()));
        let q = nodes[inventory
            .declarations
            .iter()
            .position(|d| d.name.as_deref() == Some("q"))
            .unwrap()];
        assert_eq!(
            inventory
                .declarations
                .iter()
                .filter(|d| d.pointer_state == PointerState::Raw)
                .count(),
            2
        );
        let mut measurement = Measurement::new(seed_map(&inventory));
        measurement.start_stage(StageId("rewrite".into()), Phase::Committed);
        measurement.bind(&krate, &mapper, tcx).unwrap();
        action(&mut krate, &mut measurement, q)
    })
    .unwrap()
}
fn source(krate: &ast::Crate) -> String {
    let mut krate = krate.clone();
    ::utils::ast::remove_unnecessary_items_from_ast(&mut krate);
    rustc_ast_pretty::pprust::crate_to_string_for_macros(&krate)
}
struct CloneLocal {
    fresh: bool,
}
impl MutVisitor for CloneLocal {
    fn visit_block(&mut self, b: &mut ast::Block) {
        if let Some(first) = b.stmts.first() {
            let mut second = first.clone();
            if let ast::StmtKind::Let(local) = &mut second.kind {
                if self.fresh {
                    local.pat.id = NodeId::from_u32(100000);
                }
            }
            b.stmts.push(second);
        }
    }
}
#[test]
fn preserve_copy_and_clone_differ() {
    fixture(|krate, measurement, q| {
        let old = measurement.id(q).unwrap().clone();
        let emission = measurement.finish(krate, source(krate)).unwrap();
        assert!(
            emission
                .delta
                .events
                .iter()
                .all(|e| e.operation == Operation::Preserve)
        );
        assert!(emission.delta.map.entries.iter().any(|e| e.id == old));
    });
    fixture(|krate, measurement, q| {
        let old = measurement.id(q).unwrap().clone();
        let checkpoint = measurement.checkpoint();
        CloneLocal { fresh: true }.visit_crate(krate);
        measurement.record(
            Operation::Split,
            &[old.clone()],
            &[q, NodeId::from_u32(100000)],
            "split local",
        );
        let emission = measurement.finish(krate, source(krate)).unwrap();
        let split = emission
            .delta
            .events
            .iter()
            .find(|e| e.operation == Operation::Split)
            .unwrap();
        assert_eq!(split.outputs.len(), 2);
        assert!(split.outputs.iter().all(|id| id != &old));
        let finals = emission
            .delta
            .map
            .entries
            .iter()
            .map(|e| e.id.clone())
            .collect();
        assert_eq!(
            measurement
                .ledger()
                .descendants(&old, &finals)
                .unwrap()
                .len(),
            2
        );
        measurement.restore(checkpoint);
        assert!(measurement.take_emissions().unwrap().is_empty());
        assert_eq!(measurement.ledger().current_map().stage.0, "input");
    });
}
#[test]
fn unrecorded_insertions_deletions_and_duplicate_nodes_fail() {
    fixture(|krate, measurement, _| {
        CloneLocal { fresh: true }.visit_crate(krate);
        assert!(measurement.finish(krate, source(krate)).is_err());
    });
    fixture(|krate, measurement, _| {
        CloneLocal { fresh: false }.visit_crate(krate);
        assert!(measurement.finish(krate, source(krate)).is_err());
    });
    fixture(|krate, measurement, _| {
        struct Remove;
        impl MutVisitor for Remove {
            fn visit_block(&mut self, b: &mut ast::Block) {
                b.stmts.clear();
            }
        }
        Remove.visit_crate(krate);
        assert!(measurement.finish(krate, source(krate)).is_err());
    });
    fixture(|krate, measurement, q| {
        measurement.record(
            Operation::Replace,
            &[DeclId("missing".into())],
            &[q],
            "invalid parent",
        );
        assert!(measurement.finish(krate, source(krate)).is_err());
        assert!(measurement.take_emissions().is_err());
    });
}

#[test]
fn emitted_map_reconciles_reparsed_split_source() {
    let emission = fixture(|krate, measurement, q| {
        let parent = measurement.id(q).unwrap().clone();
        CloneLocal { fresh: true }.visit_crate(krate);
        measurement.record(
            Operation::Split,
            &[parent],
            &[q, NodeId::from_u32(100000)],
            "split local",
        );
        measurement
            .set_output_scope(NodeId::from_u32(100000), Scope::Support)
            .unwrap();
        measurement.finish(krate, source(krate)).unwrap()
    });
    let inv = run_compiler_on_str(&emission.source, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emission.delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    assert_eq!(inv.declarations.len(), 4);
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| d.scope == Scope::Support)
            .count(),
        1
    );
}

fn measure_struct(
    code: &str,
    config: &super::super::Config,
    arrays: bool,
) -> (
    ::utils::pointer_inventory::Inventory,
    ::utils::pointer_inventory::Inventory,
    Measurement,
    Emission,
) {
    let baseline = run_compiler_on_str(code, |tcx| {
        ::utils::pointer_inventory::collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap();
    let ordinary = run_compiler_on_str(code, |tcx| {
        if arrays {
            super::super::rewrite_struct_arrays(config, tcx).0
        } else {
            super::super::rewrite_struct_param_fields(config, tcx).0
        }
    })
    .unwrap();
    let mut measurement = Measurement::new(seed_map(&baseline));
    let observed = run_compiler_on_str(code, |tcx| {
        if arrays {
            super::super::rewrite_struct_arrays_observed(config, tcx, Some(&mut measurement)).0
        } else {
            super::super::rewrite_struct_param_fields_observed(config, tcx, Some(&mut measurement))
                .0
        }
    })
    .unwrap();
    assert_eq!(ordinary, observed);
    let emissions = measurement.take_emissions().unwrap();
    assert_eq!(emissions.len(), 1);
    let emission = emissions.into_iter().next().unwrap();
    let final_inventory = run_compiler_on_str(&observed, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emission.delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    (baseline, final_inventory, measurement, emission)
}
#[test]
fn measurement_struct_array_fields() {
    let code = r#"
#[repr(C)] pub struct Group { pub a: *mut i32, pub b: *mut i32, pub c: *mut i32 }
pub unsafe fn f() -> *mut i32 {
    let mut s = Group { a: 0 as *mut i32, b: 0 as *mut i32, c: 0 as *mut i32 };
    let p: *mut *mut i32 = &raw mut s.a;
    *p.offset(1)
}
"#;
    let (before, after, measurement, emission) = measure_struct(code, &Default::default(), true);
    let merged = emission
        .delta
        .events
        .iter()
        .find(|e| e.operation == Operation::Merge)
        .expect(&emission.source);
    assert_eq!(merged.parents.len(), 3);
    assert_eq!(merged.outputs.len(), 1);
    let finals = after
        .declarations
        .iter()
        .map(|d| d.declaration_id.clone())
        .collect();
    for field in before
        .declarations
        .iter()
        .filter(|d| d.site == ::utils::pointer_inventory::Site::Field)
    {
        assert_eq!(
            measurement
                .ledger()
                .descendants(&field.declaration_id, &finals)
                .unwrap(),
            merged.outputs.iter().cloned().collect()
        );
    }
}
#[test]
fn measurement_struct_param_specialization() {
    let mut config = super::super::Config::default();
    config.c_exposed_fns.insert("build".into());
    let code = r#"
pub mod a {
    pub type myint_t = u16;
    #[repr(C)] pub struct st { pub lookup: [myint_t; 4], pub lit: [u32; 4] }
    pub unsafe extern "C" fn build(mut s: *mut st, mut tree: *mut u32) -> i32 {
        if !s.is_null() { (*s).lookup[0] = 1; }
        *tree.offset(0) = 0; 0
    }
    pub unsafe extern "C" fn fixed(mut s: *mut st) -> i32 { build(s, ((*s).lit).as_mut_ptr()) }
}
pub mod b {
    use crate::a::{build, st};
    pub unsafe extern "C" fn stranger(mut s: *mut st, mut tree: *mut u32, flag: i32) -> i32 {
        let mut p: *mut st = 0 as *mut st;
        if flag != 0 { p = s; }
        build(p, tree); 0
    }
}
"#;
    // Keep the fixture's import simple, as required by the existing rewrite.
    let code = code.replace(
        "use crate::a::{build, st};",
        "use crate::a::build; use crate::a::st;",
    );
    let (before, after, _, emission) = measure_struct(&code, &config, false);
    assert!(emission.source.contains("build_field"));
    let generated: Vec<_> = after
        .declarations
        .iter()
        .filter(|d| d.name.as_deref().is_some_and(|n| n.starts_with("__crat_g")))
        .collect();
    assert_eq!(generated.len(), 2, "{}", emission.source);
    assert!(generated.iter().all(|d| d.scope == Scope::Application));
    assert_eq!(
        emission
            .delta
            .events
            .iter()
            .filter(|e| e.operation == Operation::Create)
            .flat_map(|e| &e.outputs)
            .count(),
        2
    );
    for original in &before.declarations {
        assert!(
            after
                .declarations
                .iter()
                .any(|d| d.declaration_id == original.declaration_id)
        );
    }
}
