use super::*;
use crate::pointer_inventory::{DeclarationLocator, MappedDeclaration, Scope, Site, SourceHashes};
fn id(s: &str) -> DeclId {
    DeclId(s.into())
}
fn map(stage: &str, names: &[&str]) -> DeclarationMap {
    DeclarationMap {
        schema_version: 1,
        case_id: "fixture".into(),
        profile: Some("base".into()),
        stage: StageId(stage.into()),
        source_hashes: SourceHashes::new(),
        entries: names
            .iter()
            .enumerate()
            .map(|(i, n)| MappedDeclaration {
                id: id(n),
                locator: DeclarationLocator {
                    owner_path: vec![i as u32],
                    site: Site::Local,
                    ordinal: 0,
                    pattern_path: vec![],
                },
                scope: Scope::Application,
                shape: "local".into(),
            })
            .collect(),
    }
}
fn event(
    stage: &str,
    n: usize,
    operation: Operation,
    parents: &[&str],
    outputs: &[&str],
) -> LineageEvent {
    LineageEvent {
        schema_version: 1,
        event_id: format!("{stage}:{n}"),
        stage: StageId(stage.into()),
        phase: Phase::Committed,
        operation,
        parents: parents.iter().map(|p| id(p)).collect(),
        outputs: outputs.iter().map(|p| id(p)).collect(),
        reason: "fixture".into(),
        candidate_id: None,
    }
}
fn delta(stage: &str, names: &[&str], events: Vec<LineageEvent>, deleted: &[&str]) -> StageDelta {
    StageDelta {
        map: map(stage, names),
        events,
        deleted: deleted.iter().map(|p| id(p)).collect(),
    }
}
#[test]
fn split_merge_and_nonpointer_roundtrip() {
    let mut ledger = Ledger::new(map("input", &["p", "q"]));
    ledger
        .commit(delta(
            "split",
            &["p1", "index", "q", "new"],
            vec![
                event("split", 0, Operation::Split, &["p"], &["p1", "index"]),
                event("split", 1, Operation::Preserve, &["q"], &["q"]),
                event("split", 2, Operation::Create, &[], &["new"]),
            ],
            &["p"],
        ))
        .unwrap();
    let finals = [id("p1"), id("index"), id("q"), id("new")]
        .into_iter()
        .collect();
    assert_eq!(ledger.descendants(&id("p"), &finals).unwrap().len(), 2);
    assert!(
        !ledger
            .descendants(&id("p"), &finals)
            .unwrap()
            .contains(&id("new"))
    );
    let checkpoint = ledger.checkpoint();
    ledger
        .commit(delta(
            "merge",
            &["out"],
            vec![
                event(
                    "merge",
                    0,
                    Operation::Merge,
                    &["p1", "index", "q"],
                    &["out"],
                ),
                event("merge", 1, Operation::Delete, &["new"], &[]),
            ],
            &["p1", "index", "q", "new"],
        ))
        .unwrap();
    let finals = [id("out")].into_iter().collect();
    assert_eq!(ledger.descendants(&id("p"), &finals).unwrap(), finals);
    assert_eq!(ledger.descendants(&id("q"), &finals).unwrap(), finals);
    assert_eq!(checkpoint.current_map().stage.0, "split");
    let mut ledger = Ledger::new(map("input", &["p"]));
    ledger
        .commit(delta(
            "index",
            &["index"],
            vec![event("index", 0, Operation::Replace, &["p"], &["index"])],
            &["p"],
        ))
        .unwrap();
    ledger
        .commit(delta(
            "pointer",
            &["restored"],
            vec![event(
                "pointer",
                0,
                Operation::Replace,
                &["index"],
                &["restored"],
            )],
            &["index"],
        ))
        .unwrap();
    assert_eq!(
        ledger
            .descendants(&id("p"), &[id("restored")].into_iter().collect())
            .unwrap()
            .len(),
        1
    );
}
#[test]
fn invalid_and_trial_deltas_are_atomic() {
    let initial = map("input", &["p"]);
    let good = delta(
        "output",
        &["p"],
        vec![event("output", 0, Operation::Preserve, &["p"], &["p"])],
        &[],
    );
    let mut bads = vec![];
    let mut d = good.clone();
    d.events[0].phase = Phase::Trial;
    bads.push(d);
    let mut d = good.clone();
    d.events.clear();
    bads.push(d);
    let mut d = good.clone();
    d.events[0].parents = vec![id("missing")];
    bads.push(d);
    let mut d = good.clone();
    d.events.push(d.events[0].clone());
    bads.push(d);
    let mut d = good.clone();
    d.deleted.push(id("p"));
    bads.push(d);
    let mut d = good.clone();
    d.map.case_id = "other".into();
    bads.push(d);
    for d in bads {
        let mut ledger = Ledger::new(initial.clone());
        assert!(ledger.commit(d).is_err());
        assert_eq!(ledger.current_map(), &initial);
        ledger.commit(good.clone()).unwrap();
    }
}

#[test]
fn retired_identity_cannot_be_recreated() {
    let mut ledger = Ledger::new(map("input", &["p"]));
    ledger
        .commit(delta(
            "delete",
            &[],
            vec![event("delete", 0, Operation::Delete, &["p"], &[])],
            &["p"],
        ))
        .unwrap();
    assert!(
        ledger
            .commit(delta(
                "create",
                &["p"],
                vec![event("create", 0, Operation::Create, &[], &["p"])],
                &[]
            ))
            .is_err()
    );
}
