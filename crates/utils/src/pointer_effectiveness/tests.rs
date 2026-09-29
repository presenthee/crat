use std::collections::BTreeMap;

use super::*;
use crate::{
    pointer_identity::seed_map,
    pointer_inventory::*,
    pointer_lineage::{Ledger, LineageEvent, Operation, Phase, StageDelta},
};

fn observation(raw: Presence, data: Presence) -> TypeObservation {
    let mut o = TypeObservation {
        raw_presence: raw,
        data_representation: data,
        slots: vec![],
        slots_complete: raw != Presence::Unknown && data != Presence::Unknown,
        raw_slots_complete: raw != Presence::Unknown,
        diagnostics: vec![],
    };
    if raw == Presence::Present {
        o.slots.push(PointerSlot {
            path: "root".into(),
            kind: PointerKind::RawMut,
            optional: false,
        });
    } else if data == Presence::Present {
        o.slots.push(PointerSlot {
            path: "root".into(),
            kind: PointerKind::RefMut,
            optional: false,
        });
    }
    let affects: Vec<_> = [
        (raw == Presence::Unknown, ObservationFact::RawPresence),
        (
            data == Presence::Unknown,
            ObservationFact::DataRepresentation,
        ),
        (!o.slots_complete, ObservationFact::Slots),
        (!o.raw_slots_complete, ObservationFact::RawSlots),
    ]
    .into_iter()
    .filter_map(|(yes, f)| yes.then_some(f))
    .collect();
    if !affects.is_empty() {
        o.diagnostics.push(TypeDiagnostic {
            code: "fixture_unknown".into(),
            path: "root".into(),
            ty: "unknown".into(),
            affects,
        });
    }
    o
}
fn inv(stage: &str, rows: &[(&str, TypeObservation)]) -> Inventory {
    Inventory {
        schema_version: 2,
        counting_contract: COUNTING_CONTRACT.into(),
        case_id: "fixture".into(),
        profile: Some("base".into()),
        stage: StageId(stage.into()),
        source_hashes: BTreeMap::new(),
        structural_errors: vec![],
        observations: rows
            .iter()
            .map(|(id, o)| (DeclId((*id).into()), o.clone()))
            .collect(),
        declarations: rows
            .iter()
            .enumerate()
            .map(|(i, (id, _))| Declaration {
                declaration_id: DeclId((*id).into()),
                site: Site::Local,
                scope: Scope::Application,
                owner: "f".into(),
                name: Some((*id).into()),
                location: SourceLocation {
                    file: "lib.rs".into(),
                    line: 1,
                    column: 1,
                },
                resolved_type: "fixture".into(),
                locator: DeclarationLocator {
                    owner_path: vec![i as u32],
                    site: Site::Local,
                    ordinal: 0,
                    pattern_path: vec![],
                },
            })
            .collect(),
    }
}
fn event(
    stage: &str,
    i: usize,
    operation: Operation,
    parents: &[&str],
    outputs: &[&str],
) -> LineageEvent {
    LineageEvent {
        schema_version: 2,
        event_id: format!("{stage}:{i}"),
        stage: StageId(stage.into()),
        phase: Phase::Committed,
        operation,
        parents: parents.iter().map(|id| DeclId((*id).into())).collect(),
        outputs: outputs.iter().map(|id| DeclId((*id).into())).collect(),
        reason: "test".into(),
        candidate_id: None,
    }
}
fn preserve(ledger: &mut Ledger, inventory: &Inventory) {
    ledger
        .commit(StageDelta {
            map: seed_map(inventory),
            deleted: vec![],
            events: inventory
                .declarations
                .iter()
                .enumerate()
                .map(|(i, d)| {
                    event(
                        &inventory.stage.0,
                        i,
                        Operation::Preserve,
                        &[&d.declaration_id.0],
                        &[&d.declaration_id.0],
                    )
                })
                .collect(),
        })
        .unwrap();
}
#[test]
fn availability_depends_on_required_facts() {
    let baseline = inv(
        "input",
        &[
            ("p", observation(Presence::Present, Presence::Present)),
            ("x", observation(Presence::Absent, Presence::Unknown)),
        ],
    );
    assert_eq!(origin_set(&baseline).unwrap().n, Some(1));
    let mut final_inv = baseline.clone();
    final_inv.stage = StageId("borrow".into());
    let mut ledger = Ledger::new(seed_map(&baseline));
    preserve(&mut ledger, &final_inv);
    let check = |f: &Inventory| assess_availability(&baseline, &[f.clone()], f, &ledger).unwrap();
    let a = check(&final_inv);
    assert_eq!(a.origin_categories.status, AvailabilityStatus::Complete);
    assert_eq!(a.final_raw_definitions.status, AvailabilityStatus::Complete);
    assert_eq!(a.raw_slots.status, AvailabilityStatus::Complete);
    assert_eq!(
        a.whole_program_kinds.status,
        AvailabilityStatus::Unavailable
    );
    assert_eq!(
        a.representation_growth.status,
        AvailabilityStatus::Unavailable
    );
    final_inv.observations.insert(
        DeclId("p".into()),
        observation(Presence::Unknown, Presence::Unknown),
    );
    assert_eq!(
        check(&final_inv).origin_categories.status,
        AvailabilityStatus::Unavailable
    );
    final_inv.observations.insert(
        DeclId("p".into()),
        observation(Presence::Present, Presence::Present),
    );
    final_inv.observations.insert(
        DeclId("x".into()),
        observation(Presence::Unknown, Presence::Unknown),
    );
    assert_eq!(
        check(&final_inv).final_raw_definitions.status,
        AvailabilityStatus::Unavailable
    );
    let mut support = baseline.clone();
    support.declarations[1].scope = Scope::Support;
    let mut output = support.clone();
    output.stage = StageId("borrow".into());
    let mut l = Ledger::new(seed_map(&support));
    preserve(&mut l, &output);
    assert_eq!(
        assess_availability(&support, &[output.clone()], &output, &l)
            .unwrap()
            .whole_program_kinds
            .status,
        AvailabilityStatus::Complete
    );
}
#[test]
fn partial_stage_resolves_at_final() {
    let b = inv(
        "input",
        &[("p", observation(Presence::Present, Presence::Present))],
    );
    let middle = inv(
        "epoch",
        &[("p", observation(Presence::Unknown, Presence::Unknown))],
    );
    let f = inv(
        "borrow",
        &[("p", observation(Presence::Absent, Presence::Absent))],
    );
    let mut l = Ledger::new(seed_map(&b));
    preserve(&mut l, &middle);
    preserve(&mut l, &f);
    let a = assess_availability(&b, &[middle, f.clone()], &f, &l).unwrap();
    assert_eq!(a.origin_categories.status, AvailabilityStatus::Complete);
    assert_eq!(a.stage_type_changes.status, AvailabilityStatus::Unavailable);
    assert_eq!(a.tracked_kinds.status, AvailabilityStatus::Unavailable);
}
#[test]
fn outer_raw_needs_no_complete_slot_total() {
    let mut o = observation(Presence::Present, Presence::Present);
    o.slots_complete = false;
    o.raw_slots_complete = false;
    o.diagnostics.push(TypeDiagnostic {
        code: "nested_unknown".into(),
        path: "root.pointee".into(),
        ty: "opaque".into(),
        affects: vec![ObservationFact::Slots, ObservationFact::RawSlots],
    });
    let b = inv("input", &[("p", o.clone())]);
    let f = inv("borrow", &[("p", o)]);
    let mut l = Ledger::new(seed_map(&b));
    preserve(&mut l, &f);
    let a = assess_availability(&b, &[f.clone()], &f, &l).unwrap();
    assert_eq!(a.origin_categories.status, AvailabilityStatus::Complete);
    assert_eq!(a.raw_slots.status, AvailabilityStatus::Unavailable);
    let mut diagnostic = f.clone();
    diagnostic
        .observations
        .get_mut(&DeclId("p".into()))
        .unwrap()
        .diagnostics[0]
        .ty = "different display text".into();
    assess_availability(&b, &[f], &diagnostic, &l).unwrap();
}
#[test]
fn new_raw_creation_and_merged_ancestry() {
    let raw = observation(Presence::Present, Presence::Present);
    let b = inv("input", &[("p", raw.clone()), ("q", raw.clone())]);
    let f = inv("borrow", &[("merged", raw.clone()), ("new", raw)]);
    let mut l = Ledger::new(seed_map(&b));
    l.commit(StageDelta {
        map: seed_map(&f),
        deleted: vec![DeclId("p".into()), DeclId("q".into())],
        events: vec![
            event("borrow", 0, Operation::Merge, &["p", "q"], &["merged"]),
            event("borrow", 1, Operation::Create, &[], &["new"]),
        ],
    })
    .unwrap();
    let a = assess_availability(&b, &[f.clone()], &f, &l).unwrap();
    assert_eq!(origin_set(&b).unwrap().n, Some(2));
    assert_eq!(a.origin_categories.status, AvailabilityStatus::Complete);
    assert_eq!(a.final_raw_definitions.status, AvailabilityStatus::Complete);
}
#[test]
fn invalid_lineage_is_not_partial() {
    let b = inv(
        "input",
        &[("p", observation(Presence::Present, Presence::Present))],
    );
    let mut f = b.clone();
    f.stage = StageId("borrow".into());
    let mut l = Ledger::new(seed_map(&b));
    preserve(&mut l, &f);
    let mut broken = f.clone();
    broken.declarations[0].declaration_id = DeclId("missing".into());
    assert!(assess_availability(&b, &[f.clone()], &broken, &l).is_err());
    let mut wrong = f.clone();
    wrong.observations.insert(
        DeclId("p".into()),
        observation(Presence::Absent, Presence::Absent),
    );
    assert!(assess_availability(&b, &[f], &wrong, &l).is_err());
}
