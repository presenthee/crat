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
