//! Required measurement facts are independent of optional representation detail.
use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::{
    pointer_identity::{MeasurementError, seed_map},
    pointer_inventory::*,
    pointer_lineage::Ledger,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OriginSet {
    pub origin_ids: Vec<DeclId>,
    pub unknown_declaration_ids: Vec<DeclId>,
    pub exact: bool,
    pub n: Option<usize>,
    pub known_raw_count: usize,
}
fn primary(d: &Declaration) -> bool {
    d.scope != Scope::Support
}
pub fn origin_set(inventory: &Inventory) -> Result<OriginSet, MeasurementError> {
    validate_inventory(inventory)?;
    let mut origin_ids = Vec::new();
    let mut unknown_declaration_ids = Vec::new();
    for d in inventory.declarations.iter().filter(|d| primary(d)) {
        match inventory.observations[&d.declaration_id].raw_presence {
            Presence::Present => origin_ids.push(d.declaration_id.clone()),
            Presence::Unknown => unknown_declaration_ids.push(d.declaration_id.clone()),
            Presence::Absent => (),
        }
    }
    origin_ids.sort();
    unknown_declaration_ids.sort();
    let exact = unknown_declaration_ids.is_empty();
    let known_raw_count = origin_ids.len();
    Ok(OriginSet {
        origin_ids,
        unknown_declaration_ids,
        exact,
        n: exact.then_some(known_raw_count),
        known_raw_count,
    })
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AvailabilityStatus {
    Complete,
    Unavailable,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct AvailabilityReason {
    pub code: String,
    pub stage: Option<StageId>,
    pub declaration_ids: Vec<DeclId>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Availability {
    pub status: AvailabilityStatus,
    pub reasons: Vec<AvailabilityReason>,
}
impl Default for Availability {
    fn default() -> Self {
        Self {
            status: AvailabilityStatus::Complete,
            reasons: vec![],
        }
    }
}
impl Availability {
    fn add(&mut self, code: &str, stage: &StageId, ids: impl IntoIterator<Item = DeclId>) {
        let ids: BTreeSet<_> = ids.into_iter().collect();
        if ids.is_empty() {
            return;
        }
        let reason = AvailabilityReason {
            code: code.into(),
            stage: Some(stage.clone()),
            declaration_ids: ids.into_iter().collect(),
        };
        self.merge(&Self {
            status: AvailabilityStatus::Unavailable,
            reasons: vec![reason],
        });
    }

    fn merge(&mut self, other: &Self) {
        let mut reasons: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        for reason in self.reasons.iter().chain(&other.reasons) {
            reasons
                .entry((reason.code.clone(), reason.stage.clone()))
                .or_default()
                .extend(reason.declaration_ids.iter().cloned());
        }
        self.reasons = reasons
            .into_iter()
            .map(|((code, stage), ids)| AvailabilityReason {
                code,
                stage,
                declaration_ids: ids.into_iter().collect(),
            })
            .collect();
        self.status = if self.reasons.is_empty() {
            AvailabilityStatus::Complete
        } else {
            AvailabilityStatus::Unavailable
        };
    }
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AvailabilityReport {
    pub baseline_origins: Availability,
    pub origin_categories: Availability,
    pub final_raw_definitions: Availability,
    pub raw_slots: Availability,
    pub tracked_kinds: Availability,
    pub whole_program_kinds: Availability,
    pub representation_growth: Availability,
    pub stage_type_changes: Availability,
    pub stage_type_changes_by_stage: BTreeMap<StageId, Availability>,
}
fn invalid(message: &str) -> MeasurementError {
    MeasurementError::InvalidEvent(message.into())
}
fn primary_ids(inventory: &Inventory) -> BTreeSet<DeclId> {
    inventory
        .declarations
        .iter()
        .filter(|d| primary(d))
        .map(|d| d.declaration_id.clone())
        .collect()
}
fn checked_map(inventory: &Inventory, map: &DeclarationMap) -> Result<(), MeasurementError> {
    validate_inventory(inventory)?;
    let mut expected = seed_map(inventory);
    let mut actual = map.clone();
    expected.entries.sort_by(|a, b| a.id.cmp(&b.id));
    actual.entries.sort_by(|a, b| a.id.cmp(&b.id));
    if expected != actual {
        return Err(invalid("inventory/map mismatch"));
    }
    Ok(())
}
fn normalized(o: &TypeObservation) -> TypeObservation {
    let mut o = o.clone();
    o.slots.sort_by(|a, b| a.path.cmp(&b.path));
    for d in &mut o.diagnostics {
        d.ty.clear();
        d.affects.sort();
    }
    o.diagnostics
        .sort_by(|a, b| (&a.code, &a.path, &a.affects).cmp(&(&b.code, &b.path, &b.affects)));
    o
}
fn tracked_ids(
    ledger: &Ledger,
    roots: &OriginSet,
    inventory: &Inventory,
) -> Result<BTreeSet<DeclId>, MeasurementError> {
    let finals = primary_ids(inventory);
    let mut ids = BTreeSet::new();
    for root in &roots.origin_ids {
        ids.extend(ledger.descendants(root, &finals)?);
    }
    Ok(ids)
}
fn kind_availability(
    report: &mut AvailabilityReport,
    inventory: &Inventory,
    tracked: &BTreeSet<DeclId>,
) {
    let missing = primary_ids(inventory)
        .into_iter()
        .filter(|id| !inventory.observations[id].slots_complete)
        .collect::<BTreeSet<_>>();
    report.whole_program_kinds.add(
        "whole_program_slots_incomplete",
        &inventory.stage,
        missing.iter().cloned(),
    );
    report.tracked_kinds.add(
        "tracked_slots_incomplete",
        &inventory.stage,
        missing.intersection(tracked).cloned(),
    );
}

pub fn assess_availability(
    baseline: &Inventory,
    stages: &[Inventory],
    final_inventory: &Inventory,
    ledger: &Ledger,
) -> Result<AvailabilityReport, MeasurementError> {
    let roots = origin_set(baseline)?;
    if stages.len() != ledger.stages().len() {
        return Err(invalid("stage inventory coverage mismatch"));
    }
    let mut checked = Ledger::new(seed_map(baseline));
    let mut report = AvailabilityReport::default();
    report.baseline_origins.add(
        "baseline_raw_presence_unknown",
        &baseline.stage,
        roots.unknown_declaration_ids.iter().cloned(),
    );
    if !roots.exact {
        report.origin_categories = report.baseline_origins.clone();
    }
    kind_availability(
        &mut report,
        baseline,
        &roots.origin_ids.iter().cloned().collect(),
    );
    let mut previous = baseline;
    for (inventory, delta) in stages.iter().zip(ledger.stages()) {
        checked_map(inventory, &delta.map)?;
        checked.commit(delta.clone())?;
        kind_availability(
            &mut report,
            inventory,
            &tracked_ids(&checked, &roots, inventory)?,
        );
        let mut stage = Availability::default();
        for snapshot in [previous, inventory] {
            stage.add(
                "stage_endpoint_unknown",
                &inventory.stage,
                primary_ids(snapshot).into_iter().filter(|id| {
                    endpoint_state(&snapshot.observations[id]) == EndpointState::Unknown
                }),
            );
        }
        report.stage_type_changes.merge(&stage);
        report
            .stage_type_changes_by_stage
            .insert(inventory.stage.clone(), stage);
        previous = inventory;
    }
    checked_map(final_inventory, checked.current_map())?;
    if final_inventory.observations.len() != previous.observations.len()
        || final_inventory.observations.iter().any(|(id, o)| {
            previous
                .observations
                .get(id)
                .is_none_or(|p| normalized(p) != normalized(o))
        })
    {
        return Err(invalid("independent final type observation mismatch"));
    }
    if roots.exact {
        report.origin_categories.add(
            "tracked_endpoint_unknown",
            &final_inventory.stage,
            tracked_ids(&checked, &roots, final_inventory)?
                .into_iter()
                .filter(|id| {
                    endpoint_state(&final_inventory.observations[id]) == EndpointState::Unknown
                }),
        );
    }
    report.final_raw_definitions.add(
        "final_raw_presence_unknown",
        &final_inventory.stage,
        primary_ids(final_inventory)
            .into_iter()
            .filter(|id| final_inventory.observations[id].raw_presence == Presence::Unknown),
    );
    report.raw_slots.add(
        "raw_slots_incomplete",
        &final_inventory.stage,
        primary_ids(final_inventory)
            .into_iter()
            .filter(|id| !final_inventory.observations[id].raw_slots_complete),
    );
    for snapshot in [baseline, final_inventory] {
        report.representation_growth.add(
            "representation_presence_unknown",
            &snapshot.stage,
            primary_ids(snapshot)
                .into_iter()
                .filter(|id| snapshot.observations[id].data_representation == Presence::Unknown),
        );
    }
    Ok(report)
}
#[cfg(test)]
mod tests;
