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
    next_node: u32,
    derived: BTreeMap<NodeId, (BTreeSet<NodeId>, String)>,
    local_nodes: std::collections::HashMap<rustc_hir::HirId, NodeId>,
    candidates: BTreeMap<DeclId, BTreeSet<String>>,
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
            next_node: 0,
            derived: BTreeMap::new(),
            local_nodes: Default::default(),
            candidates: Default::default(),
        }
    }

    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    pub fn phase(&self) -> Phase {
        self.phase
    }

    pub fn trial_checkpoint(&self) -> Self {
        let mut trial = self.clone();
        trial.phase = Phase::Trial;
        trial
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
        self.derived.clear();
        self.local_nodes.clear();
        self.candidates.clear();
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
        self.next_node = mapper
            .global_map
            .keys()
            .map(|n| n.as_u32())
            .max()
            .unwrap_or(0)
            .max(
                mapper
                    .local_map
                    .keys()
                    .map(|n| n.as_u32())
                    .max()
                    .unwrap_or(0),
            )
            + 1;
        {
            use rustc_ast::visit::Visitor;
            let mut bindings = LocalBindings {
                observer: self,
                mapper,
                tcx,
            };
            bindings.visit_crate(krate);
        }
        self.bound = true;
        Ok(())
    }

    pub fn local_node(&self, hir_id: rustc_hir::HirId) -> Option<NodeId> {
        self.local_nodes.get(&hir_id).copied()
    }

    /// Resolve the storage explicitly selected by a rewrite; do not chase assignments.
    pub fn storage_node(
        &self,
        expr: &rustc_ast::Expr,
        mapper: &AstToHir,
        tcx: TyCtxt<'_>,
    ) -> Option<NodeId> {
        use rustc_ast::ExprKind as E;
        if let Some(hir) = mapper.get_expr(expr.id, tcx) {
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = hir.kind
                && let rustc_hir::def::Res::Local(id) = path.res
            {
                return self.local_node(id);
            }
            if let rustc_hir::ExprKind::Field(base, _) = hir.kind {
                let types = tcx.typeck(hir.hir_id.owner);
                if let rustc_middle::ty::Adt(adt, _) = types.expr_ty(base).kind()
                    && adt.is_struct()
                {
                    let did = adt.non_enum_variant().fields[types.field_index(hir.hir_id)]
                        .did
                        .as_local()?;
                    return self
                        .nodes
                        .keys()
                        .find(|node| mapper.global_map.get(node) == Some(&did))
                        .copied();
                }
            }
        }
        match &expr.kind {
            E::Paren(e)
            | E::Cast(e, _)
            | E::AddrOf(_, _, e)
            | E::Unary(_, e)
            | E::Field(e, _)
            | E::Index(e, _, _) => self.storage_node(e, mapper, tcx),
            E::MethodCall(call) => self.storage_node(&call.receiver, mapper, tcx),
            _ => None,
        }
    }

    pub fn annotate_candidate(&mut self, node: NodeId, candidate: String) {
        match self.id(node).cloned() {
            Ok(id) => {
                self.candidates.entry(id).or_default().insert(candidate);
            }
            Err(e) => self.error = Some(e),
        }
    }

    fn candidate_for(&self, parents: &[DeclId]) -> Option<String> {
        let candidates: BTreeSet<_> = parents
            .iter()
            .filter_map(|id| self.candidates.get(id))
            .flatten()
            .collect();
        if candidates.len() == 1 {
            candidates.first().map(|s| (*s).clone())
        } else {
            None
        }
    }

    pub fn fresh_node(&mut self) -> NodeId {
        let node = NodeId::from_u32(self.next_node);
        self.next_node += 1;
        node
    }

    pub fn derive_nodes(&mut self, parent: NodeId, outputs: &[NodeId], reason: &str) {
        if let Err(e) = self.id(parent) {
            self.error = Some(e);
            return;
        }
        let entry = self
            .derived
            .entry(parent)
            .or_insert_with(|| (BTreeSet::new(), reason.into()));
        entry.0.extend(outputs.iter().copied());
    }

    pub fn generated_stmt(
        &mut self,
        stmt: &mut rustc_ast::Stmt,
        parent: Option<NodeId>,
        reason: &str,
    ) {
        use rustc_ast::mut_visit::MutVisitor;
        *stmt = Freshen { observer: self }
            .flat_map_stmt(stmt.clone())
            .pop()
            .unwrap();
        self.generated_sites(
            ::utils::pointer_inventory::source_sites_in_stmt(stmt),
            parent,
            reason,
        );
    }

    pub fn generated_expr(
        &mut self,
        expr: &mut rustc_ast::Expr,
        parent: Option<NodeId>,
        reason: &str,
    ) {
        use rustc_ast::mut_visit::MutVisitor;
        Freshen { observer: self }.visit_expr(expr);
        self.generated_sites(
            ::utils::pointer_inventory::source_sites_in_expr(expr),
            parent,
            reason,
        );
    }

    fn generated_sites(
        &mut self,
        sites: Vec<::utils::pointer_inventory::SourceSite>,
        parent: Option<NodeId>,
        reason: &str,
    ) {
        let nodes: Vec<_> = sites
            .into_iter()
            .map(|s| s.node)
            .filter(|n| {
                !self.nodes.contains_key(n)
                    && !self.outputs.contains_key(n)
                    && !self.derived.values().any(|(nodes, _)| nodes.contains(n))
            })
            .collect();
        if nodes.is_empty() {
            return;
        }
        if let Some(parent) = parent {
            self.derive_nodes(parent, &nodes, reason);
        } else {
            self.record(Operation::Create, &[], &nodes, reason);
        }
    }

    pub fn record_nodes(
        &mut self,
        operation: Operation,
        parents: &[NodeId],
        outputs: &[NodeId],
        reason: &str,
    ) {
        let ids: Result<Vec<_>, _> = parents.iter().map(|node| self.id(*node).cloned()).collect();
        match ids {
            Ok(ids) => self.record(operation, &ids, outputs, reason),
            Err(e) => self.error = Some(e),
        }
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
            candidate_id: self.candidate_for(parents),
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
        let sites = source_sites(krate);
        let present: BTreeSet<_> = sites.iter().map(|s| s.node).collect();
        for (parent, (mut outputs, reason)) in std::mem::take(&mut self.derived) {
            if present.contains(&parent) {
                outputs.insert(parent);
            }
            let operation = match outputs.len() {
                0 => Operation::Delete,
                1 if outputs.contains(&parent) => Operation::Preserve,
                1 => Operation::Replace,
                _ => Operation::Split,
            };
            self.record_nodes(
                operation,
                &[parent],
                &outputs.into_iter().collect::<Vec<_>>(),
                &reason,
            );
        }
        if let Some(e) = &self.error {
            return Err(e.clone());
        }
        let mut entries = vec![];
        let mut events = self.events.clone();
        let mut seen = BTreeSet::new();
        for site in sites {
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
                    candidate_id: self.candidate_for(std::slice::from_ref(id)),
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
struct LocalBindings<'a, 'tcx> {
    observer: &'a mut Measurement,
    mapper: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
}
impl<'ast> rustc_ast::visit::Visitor<'ast> for LocalBindings<'_, '_> {
    fn visit_param(&mut self, param: &'ast rustc_ast::Param) {
        if self.observer.nodes.contains_key(&param.ty.id)
            && let Some(p) = self.mapper.get_param(param.id, self.tcx)
        {
            p.pat.each_binding(|_, id, _, _| {
                self.observer.local_nodes.insert(id, param.ty.id);
            });
        }
        rustc_ast::visit::walk_param(self, param);
    }

    fn visit_pat(&mut self, pat: &'ast rustc_ast::Pat) {
        if self.observer.nodes.contains_key(&pat.id)
            && let Some(p) = self.mapper.get_pat(pat.id, self.tcx)
            && let rustc_hir::PatKind::Binding(_, id, _, _) = p.kind
        {
            self.observer.local_nodes.insert(id, pat.id);
        }
        rustc_ast::visit::walk_pat(self, pat);
    }
}
struct Freshen<'a> {
    observer: &'a mut Measurement,
}
impl rustc_ast::mut_visit::MutVisitor for Freshen<'_> {
    fn visit_id(&mut self, id: &mut NodeId) {
        if *id == rustc_ast::DUMMY_NODE_ID {
            *id = self.observer.fresh_node();
        }
    }
}
#[cfg(test)]
mod tests;
