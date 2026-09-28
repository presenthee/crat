//! Committed, stage-versioned declaration lineage (not assignment/data-flow edges).
use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::{
    pointer_identity::{MeasurementError, validate_map},
    pointer_inventory::{DeclId, DeclarationMap, StageId},
};
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Phase {
    Trial,
    Committed,
    Aborted,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Operation {
    Preserve,
    Replace,
    Split,
    Merge,
    Create,
    Delete,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageEvent {
    pub schema_version: u32,
    pub event_id: String,
    pub stage: StageId,
    pub phase: Phase,
    pub operation: Operation,
    pub parents: Vec<DeclId>,
    pub outputs: Vec<DeclId>,
    pub reason: String,
    pub candidate_id: Option<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StageDelta {
    pub map: DeclarationMap,
    pub events: Vec<LineageEvent>,
    pub deleted: Vec<DeclId>,
}
#[derive(Clone, Debug)]
pub struct Ledger {
    baseline: DeclarationMap,
    stages: Vec<StageDelta>,
    ancestors: BTreeMap<DeclId, BTreeSet<DeclId>>,
}
fn invalid(s: impl Into<String>) -> MeasurementError {
    MeasurementError::InvalidEvent(s.into())
}
impl Ledger {
    pub fn new(baseline: DeclarationMap) -> Self {
        let ancestors = baseline
            .entries
            .iter()
            .map(|e| (e.id.clone(), [e.id.clone()].into_iter().collect()))
            .collect();
        Self {
            baseline,
            stages: vec![],
            ancestors,
        }
    }

    pub fn current_map(&self) -> &DeclarationMap {
        self.stages.last().map_or(&self.baseline, |d| &d.map)
    }

    pub fn stages(&self) -> &[StageDelta] {
        &self.stages
    }

    pub fn checkpoint(&self) -> Self {
        self.clone()
    }

    pub fn commit(&mut self, delta: StageDelta) -> Result<(), MeasurementError> {
        validate_map(&self.baseline)?;
        validate_map(&delta.map)?;
        if delta.map.case_id != self.baseline.case_id || delta.map.profile != self.baseline.profile
        {
            return Err(invalid("lineage case/profile mismatch"));
        }
        if delta.map.stage == self.baseline.stage
            || self.stages.iter().any(|d| d.map.stage == delta.map.stage)
        {
            return Err(invalid("duplicate stage"));
        }
        let inputs: BTreeSet<_> = self.ancestors.keys().cloned().collect();
        let outputs: BTreeSet<_> = delta.map.entries.iter().map(|e| e.id.clone()).collect();
        let expected_deleted: BTreeSet<_> = inputs.difference(&outputs).cloned().collect();
        if delta.deleted.iter().cloned().collect::<BTreeSet<_>>() != expected_deleted
            || delta.deleted.len() != expected_deleted.len()
        {
            return Err(invalid("deleted IDs do not match stage disappearance"));
        }
        let historical_ids: BTreeSet<_> = self
            .baseline
            .entries
            .iter()
            .chain(self.stages.iter().flat_map(|s| s.map.entries.iter()))
            .map(|e| e.id.clone())
            .collect();
        for output in &outputs {
            if historical_ids.contains(output) && !inputs.contains(output) {
                return Err(invalid(format!("retired identity reused: {}", output.0)));
            }
        }
        let mut event_ids: BTreeSet<_> = self
            .stages
            .iter()
            .flat_map(|s| s.events.iter().map(|e| e.event_id.clone()))
            .collect();
        let mut consumed = BTreeSet::new();
        let mut ancestors = BTreeMap::new();
        for e in &delta.events {
            if e.schema_version != 1
                || e.stage != delta.map.stage
                || e.phase != Phase::Committed
                || !event_ids.insert(e.event_id.clone())
            {
                return Err(invalid(format!("invalid event envelope {}", e.event_id)));
            }
            let valid = match e.operation {
                Operation::Preserve => e.parents.len() == 1 && e.parents == e.outputs,
                Operation::Replace => e.parents.len() == 1 && e.outputs.len() == 1,
                Operation::Split => e.parents.len() == 1 && e.outputs.len() > 1,
                Operation::Merge => e.parents.len() > 1 && e.outputs.len() == 1,
                Operation::Create => e.parents.is_empty() && !e.outputs.is_empty(),
                Operation::Delete => !e.parents.is_empty() && e.outputs.is_empty(),
            };
            if !valid {
                return Err(invalid(format!("wrong arity for {}", e.event_id)));
            }
            let mut inherited = BTreeSet::new();
            for p in &e.parents {
                let Some(origins) = self.ancestors.get(p) else {
                    return Err(MeasurementError::MissingId(p.0.clone()));
                };
                if !consumed.insert(p.clone()) {
                    return Err(invalid(format!("parent claimed twice: {}", p.0)));
                }
                inherited.extend(origins.iter().cloned());
            }
            for o in &e.outputs {
                if !outputs.contains(o) {
                    return Err(MeasurementError::MissingId(o.0.clone()));
                }
                if inputs.contains(o) && !e.parents.contains(o) {
                    return Err(invalid(format!("output reuses unrelated live ID: {}", o.0)));
                }
                if ancestors.insert(o.clone(), inherited.clone()).is_some() {
                    return Err(MeasurementError::DuplicateId(o.0.clone()));
                }
            }
        }
        if consumed != inputs || ancestors.keys().cloned().collect::<BTreeSet<_>>() != outputs {
            return Err(invalid("incomplete declaration coverage"));
        }
        self.ancestors = ancestors;
        self.stages.push(delta);
        Ok(())
    }

    pub fn descendants(
        &self,
        origin: &DeclId,
        final_ids: &BTreeSet<DeclId>,
    ) -> Result<BTreeSet<DeclId>, MeasurementError> {
        if !self.baseline.entries.iter().any(|e| &e.id == origin) {
            return Err(MeasurementError::MissingId(origin.0.clone()));
        }
        let mut found = BTreeSet::new();
        for id in final_ids {
            let Some(origins) = self.ancestors.get(id) else {
                return Err(MeasurementError::MissingId(id.0.clone()));
            };
            if origins.contains(origin) {
                found.insert(id.clone());
            }
        }
        Ok(found)
    }
}
#[cfg(test)]
mod tests;
