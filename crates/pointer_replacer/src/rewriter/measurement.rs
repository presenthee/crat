//! Optional declaration observer. Rewriters record structural changes explicitly;
//! assignment uses never create lineage edges.
use std::collections::{BTreeMap, BTreeSet};

use ::utils::{
    ir::AstToHir,
    pointer_identity::{MeasurementError, reconcile_inventory, source_shape},
    pointer_inventory::{
        DeclId, DeclarationMap, MappedDeclaration, Scope, StageId, collect_bound_inventory,
        source_sites,
    },
    pointer_lineage::{Ledger, LineageEvent, Operation, Phase, StageDelta},
};
use rustc_ast::{Crate, NodeId};
use rustc_middle::ty::TyCtxt;
#[derive(Clone, Debug)]
pub struct Emission {
    pub source: String,
    pub delta: StageDelta,
}
#[derive(Clone, Debug)]
pub struct Measurement {
    ledger: Ledger,
    stage: StageId,
    phase: Phase,
    nodes: BTreeMap<NodeId, (DeclId, Scope)>,
    ignored: BTreeSet<NodeId>,
    consumed: BTreeSet<DeclId>,
    outputs: BTreeMap<NodeId, (DeclId, Scope)>,
    events: Vec<LineageEvent>,
    emissions: Vec<Emission>,
    error: Option<MeasurementError>,
    bound: bool,
}
impl Measurement {
    pub fn new(map: DeclarationMap) -> Self {
        Self {
            stage: map.stage.clone(),
            ledger: Ledger::new(map),
            phase: Phase::Committed,
            nodes: BTreeMap::new(),
            ignored: BTreeSet::new(),
            consumed: BTreeSet::new(),
            outputs: BTreeMap::new(),
            events: vec![],
            emissions: vec![],
            error: None,
            bound: false,
        }
    }

    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    pub fn checkpoint(&self) -> Self {
        self.clone()
    }

    pub fn restore(&mut self, checkpoint: Self) {
        *self = checkpoint;
    }

    pub fn start_stage(&mut self, stage: StageId, phase: Phase) {
        self.stage = stage;
        self.phase = phase;
        self.nodes.clear();
        self.ignored.clear();
        self.consumed.clear();
        self.outputs.clear();
        self.events.clear();
        self.bound = false;
    }

    pub fn id(&self, node: NodeId) -> Result<&DeclId, MeasurementError> {
        self.nodes
            .get(&node)
            .map(|(id, _)| id)
            .ok_or_else(|| MeasurementError::MissingId(format!("{:?} in {}", node, self.stage.0)))
    }

    pub fn bind(
        &mut self,
        krate: &Crate,
        mapper: &AstToHir,
        tcx: TyCtxt<'_>,
    ) -> Result<(), MeasurementError> {
        let result = self.try_bind(krate, mapper, tcx);
        if let Err(e) = &result {
            self.error = Some(e.clone());
        }
        result
    }

    fn try_bind(
        &mut self,
        krate: &Crate,
        mapper: &AstToHir,
        tcx: TyCtxt<'_>,
    ) -> Result<(), MeasurementError> {
        if let Some(e) = &self.error {
            return Err(e.clone());
        }
        if self.bound {
            return Err(MeasurementError::InvalidEvent("stage bound twice".into()));
        }
        let map = self.ledger.current_map();
        let (inv, nodes) =
            collect_bound_inventory(tcx, krate, mapper, &map.case_id, map.stage.clone());
        let inv = reconcile_inventory(inv, map)?;
        for (node, d) in nodes.into_iter().zip(inv.declarations) {
            if node == rustc_ast::DUMMY_NODE_ID
                || self
                    .nodes
                    .insert(node, (d.declaration_id, d.scope))
                    .is_some()
            {
                return Err(MeasurementError::DuplicateId(format!("AST node {node:?}")));
            }
        }
        self.ignored = source_sites(krate)
            .into_iter()
            .map(|s| s.node)
            .filter(|n| !self.nodes.contains_key(n))
            .collect();
        self.bound = true;
        Ok(())
    }

    pub fn record(
        &mut self,
        operation: Operation,
        parents: &[DeclId],
        output_nodes: &[NodeId],
        reason: &str,
    ) {
        let result = self.try_record(operation, parents, output_nodes, reason);
        if let Err(e) = result {
            self.error = Some(e);
        }
    }

    fn try_record(
        &mut self,
        operation: Operation,
        parents: &[DeclId],
        output_nodes: &[NodeId],
        reason: &str,
    ) -> Result<(), MeasurementError> {
        if let Some(e) = &self.error {
            return Err(e.clone());
        }
        if !self.bound {
            return Err(MeasurementError::InvalidEvent("record before bind".into()));
        }
        let mut scope = Scope::Application;
        for p in parents {
            let Some((_, parent_scope)) = self.nodes.values().find(|(id, _)| id == p) else {
                return Err(MeasurementError::MissingId(p.0.clone()));
            };
            scope = *parent_scope;
            if !self.consumed.insert(p.clone()) {
                return Err(MeasurementError::DuplicateId(format!("parent {}", p.0)));
            }
        }
        let event_id = format!(
            "{}:{}:{}",
            self.ledger.current_map().case_id,
            self.stage.0,
            self.events.len()
        );
        let mut outputs = vec![];
        for (i, node) in output_nodes.iter().enumerate() {
            if *node == rustc_ast::DUMMY_NODE_ID {
                return Err(MeasurementError::MissingId(
                    "output has dummy NodeId".into(),
                ));
            }
            let id = if operation == Operation::Preserve && parents.len() == 1 {
                parents[0].clone()
            } else {
                DeclId(format!("{event_id}:decl:{i}"))
            };
            if self.outputs.insert(*node, (id.clone(), scope)).is_some() {
                return Err(MeasurementError::DuplicateId(format!(
                    "output node {node:?}"
                )));
            }
            outputs.push(id);
        }
        self.events.push(LineageEvent {
            schema_version: 1,
            event_id,
            stage: self.stage.clone(),
            phase: self.phase,
            operation,
            parents: parents.to_vec(),
            outputs,
            reason: reason.into(),
            candidate_id: None,
        });
        Ok(())
    }

    /// Mark declarations introduced by generated support code explicitly.
    pub fn set_output_scope(&mut self, node: NodeId, scope: Scope) -> Result<(), MeasurementError> {
        let Some((_, value)) = self.outputs.get_mut(&node) else {
            return Err(MeasurementError::MissingId(format!("output node {node:?}")));
        };
        *value = scope;
        Ok(())
    }

    pub fn finish(&mut self, krate: &Crate, source: String) -> Result<Emission, MeasurementError> {
        let result = self.try_finish(krate, source);
        if let Err(e) = &result {
            self.error = Some(e.clone());
        }
        result
    }

    fn try_finish(&mut self, krate: &Crate, source: String) -> Result<Emission, MeasurementError> {
        if let Some(e) = &self.error {
            return Err(e.clone());
        }
        if !self.bound {
            return Err(MeasurementError::InvalidEvent("finish before bind".into()));
        }
        let mut entries = vec![];
        let mut events = self.events.clone();
        let mut seen = BTreeSet::new();
        for site in source_sites(krate) {
            if !seen.insert(site.node) {
                return Err(MeasurementError::DuplicateId(format!(
                    "output AST node {:?}",
                    site.node
                )));
            }
            if self.ignored.contains(&site.node) {
                continue;
            }
            let (id, scope) = if let Some(value) = self.outputs.get(&site.node) {
                value.clone()
            } else if let Some((id, scope)) = self.nodes.get(&site.node) {
                if self.consumed.contains(id) {
                    return Err(MeasurementError::InvalidEvent(format!(
                        "consumed declaration still present: {}",
                        id.0
                    )));
                }
                events.push(LineageEvent {
                    schema_version: 1,
                    event_id: format!(
                        "{}:{}:preserve:{}",
                        self.ledger.current_map().case_id,
                        self.stage.0,
                        events.len()
                    ),
                    stage: self.stage.clone(),
                    phase: self.phase,
                    operation: Operation::Preserve,
                    parents: vec![id.clone()],
                    outputs: vec![id.clone()],
                    reason: "unchanged source declaration".into(),
                    candidate_id: None,
                });
                (id.clone(), *scope)
            } else {
                return Err(MeasurementError::MissingId(format!(
                    "unrecorded output {:?} in {}",
                    site.node, self.stage.0
                )));
            };
            entries.push(MappedDeclaration {
                id,
                shape: source_shape(site.locator.site, &site.name),
                locator: site.locator,
                scope,
            });
        }
        if self.outputs.keys().any(|n| !seen.contains(n)) {
            return Err(MeasurementError::InvalidEvent(
                "recorded output absent from AST".into(),
            ));
        }
        let old = self.ledger.current_map();
        let final_ids: BTreeSet<_> = entries.iter().map(|e| &e.id).collect();
        let deleted = old
            .entries
            .iter()
            .filter(|e| !final_ids.contains(&e.id))
            .map(|e| e.id.clone())
            .collect();
        let map = DeclarationMap {
            schema_version: 1,
            case_id: old.case_id.clone(),
            profile: old.profile.clone(),
            stage: self.stage.clone(),
            source_hashes: Default::default(),
            entries,
        };
        let delta = StageDelta {
            map,
            events,
            deleted,
        };
        // Trials validate against a private ledger checkpoint; callers discard the
        // observer checkpoint before replay. Emitted phase still identifies trials.
        let mut validation = delta.clone();
        for e in &mut validation.events {
            e.phase = Phase::Committed;
        }
        self.ledger.commit(validation)?;
        let emission = Emission { source, delta };
        self.emissions.push(emission.clone());
        self.bound = false;
        Ok(emission)
    }

    pub fn take_emissions(&mut self) -> Result<Vec<Emission>, MeasurementError> {
        if let Some(e) = &self.error {
            return Err(e.clone());
        }
        Ok(std::mem::take(&mut self.emissions))
    }
}
#[cfg(test)]
mod tests;
