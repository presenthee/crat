use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_hir::{
    self as hir,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{
    Span,
    def_id::{DefId, LocalDefId},
};

use super::*;

/// Compiler identities established by the injected-support declaration map.
/// Names alone never confer a custom pointer representation.
#[derive(Default, Clone)]
pub struct TypeRoles {
    pub cursors: HashMap<DefId, bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum DeclarationKey {
    Global(LocalDefId, Site, u32),
    Local(hir::HirId),
}

pub fn collect_inventory(tcx: TyCtxt<'_>, case_id: &str, stage: StageId) -> Inventory {
    let mut ast = crate::ast::expanded_ast(tcx);
    let mapper = crate::ast::make_ast_to_hir(&mut ast, tcx);
    let roles = injected_cursor_roles(tcx);
    let inventory =
        collect_bound_inventory_with_roles(tcx, &ast, &mapper, case_id, stage, &roles).0;
    crate::type_check(tcx);
    inventory
}

/// Standalone counting without a declaration map: recognise the injected
/// `slice_cursor` support module by its def path.
pub(super) fn injected_cursor_roles(tcx: TyCtxt<'_>) -> TypeRoles {
    let mut roles = TypeRoles::default();
    for id in tcx.hir_crate_items(()).free_items() {
        let def_id = id.owner_id.to_def_id();
        if !matches!(tcx.hir_item(id).kind, hir::ItemKind::Struct(..)) {
            continue;
        }
        match tcx.def_path_str(def_id).as_str() {
            "slice_cursor::SliceCursor" => roles.cursors.insert(def_id, false),
            "slice_cursor::SliceCursorMut" => roles.cursors.insert(def_id, true),
            _ => None,
        };
    }
    roles
}

pub(super) fn is_injected_support_owner(owner: &str) -> bool {
    owner.starts_with("slice_cursor::") || owner.starts_with("<slice_cursor::")
}

/// Reuse the rewriter's AST and mapper; never request expanded_ast after HIR queries.
pub fn collect_bound_inventory(
    tcx: TyCtxt<'_>,
    ast: &rustc_ast::Crate,
    mapper: &crate::ir::AstToHir,
    case_id: &str,
    stage: StageId,
) -> (Inventory, Vec<rustc_ast::NodeId>) {
    collect_bound_inventory_with_roles(tcx, ast, mapper, case_id, stage, &TypeRoles::default())
}

pub fn collect_bound_inventory_with_roles(
    tcx: TyCtxt<'_>,
    ast: &rustc_ast::Crate,
    mapper: &crate::ir::AstToHir,
    case_id: &str,
    stage: StageId,
    roles: &TypeRoles,
) -> (Inventory, Vec<rustc_ast::NodeId>) {
    let mut collector = Collector {
        tcx,
        roles: roles.clone(),
        inventory: Inventory {
            schema_version: MEASUREMENT_SCHEMA_VERSION,
            case_id: case_id.into(),
            profile: None,
            stage,
            source_hashes: BTreeMap::new(),
            declarations: Vec::new(),
            counting_contract: COUNTING_CONTRACT.into(),
            observations: BTreeMap::new(),
            structural_errors: Vec::new(),
        },
        keys: Vec::new(),
        bindings: HashSet::new(),
        param_bindings: HashSet::new(),
        owners: HashMap::new(),
        ordinals: HashMap::new(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut collector);
    let mut declarations: HashMap<_, _> = collector
        .keys
        .into_iter()
        .zip(collector.inventory.declarations)
        .collect();
    let sites = super::source::bound_sites(ast, mapper, tcx);
    let mut nodes = Vec::new();
    collector.inventory.declarations = Vec::new();
    let source_sites: HashMap<_, _> = super::source::source_sites(ast)
        .into_iter()
        .map(|s| (s.node, s))
        .collect();
    let mut locator_changes = BTreeMap::new();
    let mut replacements = BTreeMap::new();
    for (node, key) in sites {
        if let Some(mut d) = declarations.remove(&key) {
            let index = nodes.len();
            let Some(source_site) = source_sites.get(&node) else {
                collector.inventory.structural_errors.push(InventoryIssue {
                    locator: Some(d.locator),
                    reason: format!("missing structural source site: {node:?}"),
                });
                continue;
            };
            locator_changes.insert(d.locator.clone(), source_site.locator.clone());
            d.locator = source_site.locator.clone();
            d.name = source_site.name.clone();
            replacements.insert(d.declaration_id.clone(), DeclId(format!("{case_id}:decl:{index}")));
            nodes.push(node);
            collector.inventory.declarations.push(d);
        }
    }
    for issue in &mut collector.inventory.structural_errors {
        if let Some(locator) = issue
            .locator
            .as_ref()
            .and_then(|old| locator_changes.get(old))
        {
            issue.locator = Some(locator.clone());
        }
    }
    for (_, d) in declarations {
        collector.inventory.structural_errors.push(InventoryIssue {
            locator: Some(d.locator),
            reason: format!(
                "declaration has no source AST binding: {} {:?}",
                d.owner, d.name
            ),
        });
    }
    collector.inventory.observations.retain(|id, _| replacements.contains_key(id));
    if let Err(error) = rekey_declarations(&mut collector.inventory, &replacements) {
        collector.inventory.structural_errors.push(InventoryIssue { locator: None, reason: error.to_string() });
    }
    (collector.inventory, nodes)
}

struct Collector<'tcx> {
    roles: TypeRoles,
    tcx: TyCtxt<'tcx>,
    inventory: Inventory,
    keys: Vec<DeclarationKey>,
    bindings: HashSet<hir::HirId>,
    param_bindings: HashSet<hir::HirId>,
    owners: HashMap<LocalDefId, u32>,
    ordinals: HashMap<(LocalDefId, Site), u32>,
}

impl<'tcx> Collector<'tcx> {
    fn add(
        &mut self,
        owner: LocalDefId,
        site: Site,
        scope: Scope,
        name: Option<String>,
        ty: Ty<'tcx>,
        span: Span,
    ) {
        let owner_id = owner;
        let owner = self.tcx.def_path_str(owner.to_def_id());
        let scope = if is_injected_support_owner(&owner) { Scope::Support } else { scope };
        let next = self.owners.len() as u32;
        let owner_index = *self.owners.entry(owner_id).or_insert(next);
        let ordinal = self.ordinals.entry((owner_id, site)).or_default();
        let locator = DeclarationLocator {
            owner_path: vec![owner_index],
            site,
            ordinal: *ordinal,
            pattern_path: vec![],
        };
        self.keys
            .push(DeclarationKey::Global(owner_id, site, *ordinal));
        *ordinal += 1;
        let ty = self
            .tcx
            .try_normalize_erasing_regions(ty::TypingEnv::post_analysis(self.tcx, owner_id), ty)
            .unwrap_or(ty);
        let observed = observe_type(ty, self.tcx, &self.roles);
        let declaration_id = DeclId(format!("{}:decl:{}", self.inventory.case_id, self.inventory.declarations.len()));
        self.inventory.observations.insert(declaration_id.clone(), observed);
        let loc = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        self.inventory.declarations.push(Declaration {
            declaration_id,
            site,
            scope,
            owner,
            name,
            location: SourceLocation {
                file: loc.file.name.prefer_local().to_string(),
                line: loc.line,
                column: loc.col.0 + 1,
            },
            resolved_type: ty.to_string(),
            locator,
        });
    }

    fn signature(
        &mut self,
        id: LocalDefId,
        decl: &'tcx hir::FnDecl<'tcx>,
        body: Option<hir::BodyId>,
        scope: Scope,
    ) {
        let sig = self.tcx.fn_sig(id).instantiate_identity().skip_binder();
        for (index, ty) in sig.inputs().iter().enumerate() {
            let name = body.and_then(|b| pat_name(self.tcx.hir_body(b).params[index].pat));
            self.add(id, Site::Param, scope, name, *ty, decl.inputs[index].span);
        }
        self.add(
            id,
            Site::Return,
            scope,
            None,
            sig.output(),
            decl.output.span(),
        );
    }
}

fn pat_name(pat: &hir::Pat<'_>) -> Option<String> {
    if let hir::PatKind::Binding(_, _, name, _) = pat.kind {
        Some(name.name.to_string())
    } else {
        None
    }
}

impl<'tcx> Visitor<'tcx> for Collector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        let id = item.owner_id.def_id;
        match item.kind {
            hir::ItemKind::Fn { sig, body, .. } => {
                self.signature(id, sig.decl, Some(body), Scope::Application)
            }
            hir::ItemKind::Static(..) => self.add(
                id,
                Site::Static,
                Scope::Application,
                Some(self.tcx.item_name(id.to_def_id()).to_string()),
                self.tcx.type_of(id).instantiate_identity(),
                item.span,
            ),
            hir::ItemKind::Const(ident, ..) if ident.name.as_str() != "_" => self.add(
                id,
                Site::Const,
                Scope::Application,
                Some(self.tcx.item_name(id.to_def_id()).to_string()),
                self.tcx.type_of(id).instantiate_identity(),
                item.span,
            ),
            _ => (),
        }
        intravisit::walk_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem<'tcx>) {
        let id = item.owner_id.def_id;
        match item.kind {
            hir::ImplItemKind::Fn(sig, body) => {
                self.signature(id, sig.decl, Some(body), Scope::Application)
            }
            hir::ImplItemKind::Const(..) => self.add(
                id,
                Site::Const,
                Scope::Application,
                Some(item.ident.name.to_string()),
                self.tcx.type_of(id).instantiate_identity(),
                item.span,
            ),
            _ => (),
        }
        intravisit::walk_impl_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'tcx hir::TraitItem<'tcx>) {
        let id = item.owner_id.def_id;
        match item.kind {
            hir::TraitItemKind::Fn(sig, ref body) => self.signature(
                id,
                sig.decl,
                match body {
                    hir::TraitFn::Provided(b) => Some(*b),
                    _ => None,
                },
                Scope::Application,
            ),
            hir::TraitItemKind::Const(..) => self.add(
                id,
                Site::Const,
                Scope::Application,
                Some(item.ident.name.to_string()),
                self.tcx.type_of(id).instantiate_identity(),
                item.span,
            ),
            _ => (),
        }
        intravisit::walk_trait_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem<'tcx>) {
        let id = item.owner_id.def_id;
        match item.kind {
            hir::ForeignItemKind::Fn(sig, _, _) => {
                self.signature(id, sig.decl, None, Scope::Foreign)
            }
            hir::ForeignItemKind::Static(..) => self.add(
                id,
                Site::Static,
                Scope::Foreign,
                Some(item.ident.name.to_string()),
                self.tcx.type_of(id).instantiate_identity(),
                item.span,
            ),
            _ => (),
        }
        intravisit::walk_foreign_item(self, item);
    }

    fn visit_field_def(&mut self, field: &'tcx hir::FieldDef<'tcx>) {
        self.add(
            field.def_id,
            Site::Field,
            Scope::Application,
            Some(field.ident.name.to_string()),
            self.tcx.type_of(field.def_id).instantiate_identity(),
            field.span,
        );
        intravisit::walk_field_def(self, field);
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        for param in body.params {
            param.pat.each_binding(|_, id, _, _| {
                self.param_bindings.insert(id);
            });
        }
        intravisit::walk_body(self, body);
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, id, name, _) = pat.kind
            && pat.span.desugaring_kind().is_none()
            && !self.param_bindings.contains(&id)
            && self.bindings.insert(id)
        {
            let ty = self.tcx.typeck(id.owner).node_type(id);
            self.add(
                id.owner.def_id,
                Site::Local,
                Scope::Application,
                Some(name.name.to_string()),
                ty,
                pat.span,
            );
            *self.keys.last_mut().unwrap() = DeclarationKey::Local(id);
        }
        intravisit::walk_pat(self, pat);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(closure) = expr.kind {
            let ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(expr);
            if let ty::Closure(_, args) = ty.kind() {
                let sig = args.as_closure().sig().skip_binder();
                if let ty::Tuple(inputs) = sig.inputs()[0].kind() {
                    let body = self.tcx.hir_body(closure.body);
                    for (index, ty) in inputs.iter().enumerate() {
                        self.add(
                            closure.def_id,
                            Site::Param,
                            Scope::Application,
                            pat_name(body.params[index].pat),
                            ty,
                            body.params[index].span,
                        );
                    }
                }
                self.add(
                    closure.def_id,
                    Site::Return,
                    Scope::Application,
                    None,
                    sig.output(),
                    closure.fn_decl.output.span(),
                );
            }
        }
        intravisit::walk_expr(self, expr);
    }
}
