use ::utils::{
    compilation::run_compiler_on_str,
    pointer_identity::seed_map,
    pointer_inventory::{EndpointState, endpoint_state, collect_bound_inventory},
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
                .filter(|d| endpoint_state(&inventory.observations[&d.declaration_id]) == EndpointState::Raw)
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

const EPOCH_SOURCE: &str = r#"
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    let c: i8 = *x;
    x = b;
    x
}
"#;
#[test]
fn measurement_epoch_split_records_one_structural_split() {
    let baseline = run_compiler_on_str(EPOCH_SOURCE, |tcx| {
        ::utils::pointer_inventory::collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap();
    let origin = baseline
        .declarations
        .iter()
        .find(|d| d.name.as_deref() == Some("x"))
        .unwrap()
        .declaration_id
        .clone();
    let mut measurement = Measurement::new(seed_map(&baseline));
    let config = super::super::Config::default();
    let result = run_compiler_on_str(EPOCH_SOURCE, |tcx| {
        super::super::epoch_split::rewrite_epoch_split_with_allowlist_observed(
            &config,
            tcx,
            None,
            Some(&mut measurement),
        )
    })
    .unwrap();
    let emissions = measurement.take_emissions().unwrap();
    assert_eq!(emissions.len(), 1);
    assert_eq!(
        emissions[0]
            .delta
            .events
            .iter()
            .filter(|e| e.operation == Operation::Split)
            .count(),
        1
    );
    assert!(
        emissions[0]
            .delta
            .events
            .iter()
            .filter(|e| e.operation == Operation::Split)
            .all(|e| e.candidate_id.is_some())
    );
    let inv = run_compiler_on_str(&result.source, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emissions[0].delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    let finals = inv
        .declarations
        .iter()
        .map(|d| d.declaration_id.clone())
        .collect();
    assert_eq!(
        measurement
            .ledger()
            .descendants(&origin, &finals)
            .unwrap()
            .len(),
        2
    );
    let ordinary = run_compiler_on_str(EPOCH_SOURCE, |tcx| {
        super::super::rewrite_epoch_split(&config, tcx).0
    })
    .unwrap();
    assert_eq!(ordinary, result.source);
}

#[test]
fn generated_reconstruction_keeps_original_ancestry() {
    let emission = fixture(|krate, measurement, q| {
        let parent = measurement.id(q).unwrap().clone();
        let mut stmt =
            ::utils::stmt!("let n = Some(0isize).map_or(0 as *mut u8, |idx| idx as *mut u8);");
        measurement.generated_stmt(&mut stmt, Some(q), "reconstruct pointer from index");
        let ast::ItemKind::Fn(f) = &mut krate
            .items
            .iter_mut()
            .find(|i| matches!(i.kind, ast::ItemKind::Fn(_)))
            .unwrap()
            .kind
        else {
            unreachable!()
        };
        f.body.as_mut().unwrap().stmts.push(stmt);
        let emission = measurement.finish(krate, source(krate)).unwrap();
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
                .descendants(&parent, &finals)
                .unwrap()
                .len(),
            4
        );
        emission
    });
    let inv = run_compiler_on_str(&emission.source, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emission.delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    assert_eq!(
        inv.declarations
            .iter()
            .filter(|d| endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
            .count(),
        4
    );
}

#[test]
fn measurement_snapshot_alias_has_explicit_structural_parent() {
    let code = r#"
pub unsafe fn callee(out: *mut i32, src: *const i32) { *out = *src; }
pub unsafe fn driver(q: *mut i32) { callee(q, q); }
"#;
    let baseline = run_compiler_on_str(code, |tcx| {
        ::utils::pointer_inventory::collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap();
    let q = baseline
        .declarations
        .iter()
        .find(|d| d.name.as_deref() == Some("q"))
        .unwrap()
        .declaration_id
        .clone();
    let mut measurement = Measurement::new(seed_map(&baseline));
    let config = super::super::Config::default();
    let result = run_compiler_on_str(code, |tcx| {
        super::super::rewrite_aliasing_with_lineage_observed(
            &config,
            tcx,
            &Default::default(),
            Some(&mut measurement),
        )
    })
    .unwrap();
    assert!(result.changed, "{}", result.source);
    let emissions = measurement.take_emissions().unwrap();
    let inv = run_compiler_on_str(&result.source, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emissions[0].delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    let finals = inv
        .declarations
        .iter()
        .map(|d| d.declaration_id.clone())
        .collect();
    let descendants = measurement.ledger().descendants(&q, &finals).unwrap();
    let snapshot = inv
        .declarations
        .iter()
        .find(|d| d.name.as_deref() == Some("__crat_snap_0"))
        .unwrap();
    assert!(descendants.contains(&snapshot.declaration_id));
    assert_eq!(descendants.len(), 2);
    let ordinary =
        run_compiler_on_str(code, |tcx| super::super::rewrite_aliasing(&config, tcx).0).unwrap();
    assert_eq!(ordinary, result.source);
}

#[test]
fn measurement_array_index_reconstruction_preserves_ancestry() {
    let code = r#"
pub unsafe fn f(p: *mut i32, take: bool) -> *mut i32 {
    let mut q: *mut i32 = std::ptr::null_mut();
    if take { q = p.add(2); }
    q
}
"#;
    let baseline = run_compiler_on_str(code, |tcx| {
        ::utils::pointer_inventory::collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap();
    let q = baseline
        .declarations
        .iter()
        .find(|d| d.name.as_deref() == Some("q"))
        .unwrap()
        .declaration_id
        .clone();
    let mut measurement = Measurement::new(seed_map(&baseline));
    let config = super::super::Config::default();
    let result = run_compiler_on_str(code, |tcx| {
        super::super::rewrite_array_local_provenance_with_allowlist_observed(
            &config,
            tcx,
            None,
            &Default::default(),
            Some(&mut measurement),
        )
    })
    .unwrap();
    assert!(result.changed, "{}", result.source);
    let emissions = measurement.take_emissions().unwrap();
    let inv = run_compiler_on_str(&result.source, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emissions[0].delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    let finals = inv
        .declarations
        .iter()
        .map(|d| d.declaration_id.clone())
        .collect();
    let descendants = measurement.ledger().descendants(&q, &finals).unwrap();
    assert!(
        inv.declarations
            .iter()
            .any(|d| descendants.contains(&d.declaration_id)
                && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Nonpointer
                && d.name.as_deref() == Some("q_idx"))
    );
    assert!(
        inv.declarations
            .iter()
            .any(|d| descendants.contains(&d.declaration_id)
                && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw
                && d.site == ::utils::pointer_inventory::Site::Return)
    );
    let ordinary = run_compiler_on_str(code, |tcx| {
        super::super::rewrite_array_local_provenance(&config, tcx).0
    })
    .unwrap();
    assert_eq!(ordinary, result.source);
}

const GATE_SOURCE: &str = r#"
pub unsafe fn foo(mut p: *mut i32, mut r: *mut i32) -> i32 {
    let mut q: *mut i32 = 0 as *mut i32;
    q = p.offset(3); *p = 1; *q = 3;
    let a: i32 = *q;
    q = r.offset(1); *r = 2; *q = 5;
    a
}
"#;
fn measured_gate(
    code: &str,
    config: &super::super::Config,
) -> (super::super::GatedPrepassResult, Measurement, Vec<Emission>) {
    let baseline = run_compiler_on_str(code, |tcx| {
        ::utils::pointer_inventory::collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap();
    let ordinary = super::super::run_gated_pointer_prepasses(config, code);
    let mut observer = Measurement::new(seed_map(&baseline));
    let observed =
        super::super::run_gated_pointer_prepasses_observed(config, code, Some(&mut observer));
    assert_eq!(observed.source, ordinary.source);
    assert_eq!(observed.phases, ordinary.phases);
    assert_eq!(
        (observed.accepted_epochs, observed.accepted_arrays),
        (ordinary.accepted_epochs, ordinary.accepted_arrays)
    );
    let emissions = observer.take_emissions().unwrap();
    run_compiler_on_str(&observed.source, |tcx| {
        ::utils::pointer_identity::reconcile(
            tcx,
            observer.ledger().current_map(),
            &Default::default(),
        )
    })
    .unwrap()
    .unwrap();
    (observed, observer, emissions)
}
#[test]
fn measurement_gate_trial_replay_isolation() {
    let (result, _, emissions) = measured_gate(GATE_SOURCE, &Default::default());
    assert_eq!((result.accepted_epochs, result.accepted_arrays), (1, 2));
    assert_eq!(emissions.len(), 3);
    assert!(
        emissions
            .iter()
            .flat_map(|e| &e.delta.events)
            .all(|e| e.phase == Phase::Committed)
    );
    assert_eq!(
        emissions
            .iter()
            .flat_map(|e| &e.delta.events)
            .filter(|e| e.stage.0 == "epoch" && e.operation == Operation::Split)
            .count(),
        1
    );
    let rejected = r#"
pub unsafe fn f(a: *mut core::ffi::c_void, b: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let mut x: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
    x = a; let is_null = x.is_null(); x = b; x
}
"#;
    let (result, _, emissions) = measured_gate(rejected, &Default::default());
    assert_eq!(result.accepted_epochs, 0);
    assert_eq!(result.rejected_epochs, 1);
    assert!(
        emissions
            .iter()
            .flat_map(|e| &e.delta.events)
            .all(|e| e.operation == Operation::Preserve)
    );
}
#[test]
fn measurement_gate_replay_failure_restores_lineage() {
    let mut config = super::super::Config::default();
    config.force_gated_prepass_replay_failure = true;
    let (result, _, emissions) = measured_gate(GATE_SOURCE, &config);
    assert!(result.combined_trial_failed);
    assert!(
        result
            .phases
            .contains(&super::super::GatedPrepassPhase::EpochReplay)
    );
    assert_eq!(emissions.len(), 1);
    assert_eq!(emissions[0].delta.map.stage.0, "aliasing");
    assert!(
        emissions[0]
            .delta
            .events
            .iter()
            .all(|e| e.operation == Operation::Preserve)
    );
}

#[test]
fn measurement_array_materialized_binding_and_base_counter() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, n: isize) -> i32 {
    let mut prev: *mut i32 = p;
    p = p.offset(n);
    *prev + *p
}
"#;
    let baseline = run_compiler_on_str(code, |tcx| {
        ::utils::pointer_inventory::collect_inventory(tcx, "fixture", StageId("input".into()))
    })
    .unwrap();
    assert_eq!(baseline.declarations.len(), 4);
    let mut measurement = Measurement::new(seed_map(&baseline));
    let config = super::super::Config::default();
    let result = run_compiler_on_str(code, |tcx| {
        super::super::rewrite_array_local_provenance_with_allowlist_observed(
            &config,
            tcx,
            None,
            &Default::default(),
            Some(&mut measurement),
        )
    })
    .unwrap();
    let emissions = measurement.take_emissions().unwrap();
    let inv = run_compiler_on_str(&result.source, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emissions[0].delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    let finals = inv
        .declarations
        .iter()
        .map(|d| d.declaration_id.clone())
        .collect();
    for name in ["p", "prev"] {
        let origin = baseline
            .declarations
            .iter()
            .find(|d| d.name.as_deref() == Some(name))
            .unwrap();
        let descendants = measurement
            .ledger()
            .descendants(&origin.declaration_id, &finals)
            .unwrap();
        assert_eq!(descendants.len(), 2);
        assert_eq!(
            inv.declarations
                .iter()
                .filter(|d| descendants.contains(&d.declaration_id)
                    && endpoint_state(&inv.observations[&d.declaration_id]) == EndpointState::Raw)
                .count(),
            1
        );
    }
    let ordinary = run_compiler_on_str(code, |tcx| {
        super::super::rewrite_array_local_provenance(&config, tcx).0
    })
    .unwrap();
    assert_eq!(ordinary, result.source);
}

fn measure_borrow(
    code: &str,
) -> (
    ::utils::pointer_inventory::Inventory,
    ::utils::pointer_inventory::Inventory,
    Measurement,
    Emission,
) {
    measure_borrow_config(code, &super::super::Config::default())
}

fn measure_borrow_config(
    code: &str,
    config: &super::super::Config,
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
        super::super::replace_local_borrows(&config, tcx)
    })
    .unwrap();
    let mut measurement = Measurement::new(seed_map(&baseline));
    let observed = run_compiler_on_str(code, |tcx| {
        super::super::replace_local_borrows_observed(&config, tcx, Some(&mut measurement))
    })
    .unwrap();
    assert_eq!(ordinary, observed);
    let emissions = measurement.take_emissions().unwrap();
    assert_eq!(emissions.len(), 1);
    let emission = emissions.into_iter().next().unwrap();
    let final_inventory = run_compiler_on_str(&observed.0, |tcx| {
        ::utils::pointer_identity::reconcile(tcx, &emission.delta.map, &Default::default())
    })
    .unwrap()
    .unwrap();
    (baseline, final_inventory, measurement, emission)
}
#[test]
fn measurement_borrow_final_type_wins() {
    let code = r#"
#[repr(C)] pub struct Holder { pub p: *mut i32 }
pub unsafe fn conflict() -> i32 {
    let mut x = 0; let mut h = Holder { p: &raw mut x };
    x = 1; *h.p = 2; x
}
pub unsafe fn identity(x: *mut i32) -> *mut i32 { x }
"#;
    let (before, after, _, _) = measure_borrow(code);
    let field = before
        .declarations
        .iter()
        .find(|d| d.site == ::utils::pointer_inventory::Site::Field)
        .unwrap();
    let final_field = after
        .declarations
        .iter()
        .find(|d| d.declaration_id == field.declaration_id)
        .unwrap();
    assert_eq!(endpoint_state(&after.observations[&final_field.declaration_id]), EndpointState::Raw);
    for original in before.declarations {
        assert!(
            after
                .declarations
                .iter()
                .any(|d| d.declaration_id == original.declaration_id)
        );
    }
    assert!(
        after
            .declarations
            .iter()
            .any(|d| d.owner.ends_with("identity") && endpoint_state(&after.observations[&d.declaration_id]) == EndpointState::Promoted)
    );
}
#[test]
fn measurement_borrow_alias_retains_parent() {
    let code = r#"
#[repr(C)] pub struct State { pub buflen: i32, pub t: [u32; 2] }
unsafe extern "C" { fn touch_state(state: *mut State); fn touch_words(words: *mut u32); }
pub unsafe extern "C" fn update(mut S: *mut State) -> i32 {
    let mut left = (*S).buflen;
    (*S).t[0] = ((*S).t[0]).wrapping_add(1);
    let words: *mut u32 = ((*S).t).as_mut_ptr();
    touch_words(words); touch_state(S);
    left + (*S).t[0] as i32
}
"#;
    let (before, after, measurement, _) = measure_borrow(code);
    let origin = before
        .declarations
        .iter()
        .find(|d| d.name.as_deref() == Some("S"))
        .unwrap();
    let alias = after
        .declarations
        .iter()
        .find(|d| d.name.as_deref() == Some("__crat_borrowed_S"))
        .unwrap();
    let finals = after
        .declarations
        .iter()
        .map(|d| d.declaration_id.clone())
        .collect();
    assert!(
        measurement
            .ledger()
            .descendants(&origin.declaration_id, &finals)
            .unwrap()
            .contains(&alias.declaration_id)
    );
}
#[test]
fn measurement_cursor_support_is_separate() {
    let code = r#"
pub mod user { pub struct SliceCursor<T>(pub T); }
pub fn user_type(x: user::SliceCursor<u8>) {}
pub unsafe fn write_offset(p: *mut i32, a: isize, b: isize) { *p.offset(a).offset(b) = 1; }
"#;
    let (_, after, _, emission) = measure_borrow(code);
    assert!(emission.source.contains("pub mod slice_cursor"));
    let p = after
        .declarations
        .iter()
        .find(|d| d.scope == Scope::Application && d.name.as_deref() == Some("p"))
        .unwrap();
    assert_eq!(endpoint_state(&after.observations[&p.declaration_id]), EndpointState::Promoted);
    assert_eq!(
        after.observations[&p.declaration_id].slots[0].kind,
        ::utils::pointer_inventory::PointerKind::SliceCursorMut
    );
    let user = after
        .declarations
        .iter()
        .find(|d| d.owner.ends_with("user_type") && d.name.as_deref() == Some("x"))
        .unwrap();
    assert_eq!(endpoint_state(&after.observations[&user.declaration_id]), EndpointState::Nonpointer);
    assert!(
        after
            .declarations
            .iter()
            .any(|d| d.scope == Scope::Support && endpoint_state(&after.observations[&d.declaration_id]) == EndpointState::Raw)
    );
    assert_eq!(
        after
            .declarations
            .iter()
            .filter(|d| d.scope == Scope::Application && endpoint_state(&after.observations[&d.declaration_id]) == EndpointState::Raw)
            .count(),
        0
    );
    assert!(
        after
            .declarations
            .iter()
            .filter(|d| d.owner.starts_with("slice_cursor::"))
            .all(|d| d.scope == Scope::Support)
    );
}

#[test]
fn measurement_config_defaults_and_stage_controls() {
    use crate::rewriter::{Config, GatedPrepassPhase as P, run_gated_pointer_prepasses};
    let default: Config = toml::from_str("").unwrap();
    assert_eq!([default.enable_struct_arrays, default.enable_struct_param_fields,
        default.enable_epoch_split, default.enable_aliasing,
        default.enable_array_local_provenance, default.enable_slice_cursor], [true; 6]);
    assert!(toml::from_str::<Config>("enable_epoch_splt = false").is_err());
    assert!(toml::from_str::<Config>("c_exposed_fns = ['foo']\nverbose = true").is_ok());
    for selected in 0..=3 {
        let config = Config { enable_epoch_split: selected == 1,
            enable_aliasing: selected == 2, enable_array_local_provenance: selected == 3,
            ..Config::default() };
        let result = run_gated_pointer_prepasses(&config, "fn f() {}");
        for (enabled, phases) in [(config.enable_epoch_split, vec![P::EpochTrial,P::EpochReplay,P::EpochSelection]),
            (config.enable_aliasing, vec![P::AliasingTrial,P::AliasingReplay]),
            (config.enable_array_local_provenance, vec![P::ArrayTrial,P::ArrayReplay,P::ArraySelection])] {
            for phase in phases { assert_eq!(result.phases.contains(&phase), enabled); }
        }
        assert!(result.decisions.is_empty());
        if selected == 0 { assert!(result.phases.is_empty()); assert_eq!(result.source, "fn f() {}"); }
    }
    let config = Config { enable_aliasing: false, force_gated_prepass_trial_failure: true, ..Config::default() };
    let result = run_gated_pointer_prepasses(&config, "fn f() {}");
    assert!(result.combined_trial_failed);
    assert!(!result.phases.contains(&P::AliasingFallback));
    assert_eq!(result.source, "fn f() {}");
}

#[test]
fn measurement_cursor_off_retains_backward_offset_raw() {
    use ::utils::pointer_inventory::PointerKind;
    let config = super::super::Config { enable_slice_cursor: false, ..Default::default() };
    let code = "pub unsafe fn write_offset(p: *mut i32, a: isize, b: isize) { *p.offset(a).offset(b) = 1; }";
    let (_, on, _, on_emission) = measure_borrow(code);
    assert!(on_emission.source.contains("crate::slice_cursor::"));
    assert!(on.declarations.iter().any(|d| on.observations[&d.declaration_id].slots.iter().any(|s| s.kind == PointerKind::SliceCursorMut)));
    let (_, off, _, emission) = measure_borrow_config(code, &config);
    assert!(!emission.source.contains("crate::slice_cursor::"));
    assert_eq!(endpoint_state(&off.observations[&off.declarations.iter().find(|d| d.name.as_deref() == Some("p")).unwrap().declaration_id]), EndpointState::Raw);
    let (_, forward, _, _) = measure_borrow_config("pub unsafe fn f(p: *const u8) -> u8 { *p.offset(1) }", &config);
    assert!(forward.observations[&forward.declarations.iter().find(|d| d.name.as_deref() == Some("p")).unwrap().declaration_id].slots.iter().any(|s| s.kind == PointerKind::Slice));
}

#[test]
fn measurement_cursor_off_fields_returns_callbacks_and_aliases() {
    let config = super::super::Config { enable_slice_cursor: false, ..Default::default() };
    for code in [
        "pub struct Holder { pub p: *const i32 } pub unsafe fn f(buf: [i32;4]) -> i32 { let h = Holder { p: buf.as_ptr().offset(3) }; *h.p.offset(-1) }",
        "pub struct State { pub words: *mut u32, pub index: i32, pub count: i32 } pub unsafe fn f(s: *const State) -> *const i8 { (((*s).words.offset((*s).index as isize)) as *mut i8).offset(-(((*s).count / 8) as isize)) as *const i8 }",
        "pub struct Bs { pub buf: *const u8, pub pos: i32 } pub unsafe fn f(bs: *const Bs) -> u8 { let mut p = (*bs).buf.offset((*bs).pos as isize); let first = *p; p = p.offset(1); first + *p }",
        "pub unsafe fn back(p: *const u8) -> u8 { *p.offset(-1) } pub unsafe fn front(p: *const u8) -> u8 { *p.add(1) } pub unsafe fn call(p: *const u8, b: bool) -> u8 { let f: unsafe fn(*const u8)->u8 = if b { back } else { front }; f(p) }",
    ] {
        let (_, inventory, _, emission) = measure_borrow_config(code, &config);
        assert!(!emission.source.contains("crate::slice_cursor::"), "{}", emission.source);
        assert!(!emission.source.contains("pub mod slice_cursor"));
        for d in inventory.declarations.iter().filter(|d| d.site == ::utils::pointer_inventory::Site::Field && matches!(d.name.as_deref(), Some("p" | "words" | "buf"))) {
            assert_eq!(endpoint_state(&inventory.observations[&d.declaration_id]), EndpointState::Raw);
        }
    }
}

#[test]
fn measurement_borrow_bytemuck_derive_support_is_mapped() {
    let code = r#"
#![feature(derive_clone_copy)]
#[repr(C)] #[derive(Clone, Copy)] pub struct House { pub a: u32, pub b: u32 }
pub unsafe fn first(p: *const u8) -> u8 { *p.offset(0) }
pub unsafe fn bytes(h: House) -> u8 { first(&h as *const House as *const u8) }
"#;
    let (_, inventory, _, emission) = measure_borrow(code);
    assert!(emission.source.contains("bytemuck::NoUninit"), "{}", emission.source);
    assert!(inventory.declarations.iter().any(|d| d.scope == Scope::Support));
}
