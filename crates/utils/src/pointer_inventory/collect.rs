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

pub fn classify_type<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Result<Vec<PointerSlot>, InventoryIssue> {
    classify_type_with_roles(ty, tcx, &TypeRoles::default())
}

/// Compiler identities established by the injected-support declaration map.
/// Names alone never confer a custom pointer representation.
#[derive(Default)]
pub struct TypeRoles {
    pub cursors: HashMap<DefId, bool>,
}

pub fn classify_type_with_roles<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    roles: &TypeRoles,
) -> Result<Vec<PointerSlot>, InventoryIssue> {
    let mut slots = Vec::new();
    walk_type(ty, tcx, roles, "root", false, &mut slots)?;
    Ok(slots)
}

fn walk_type<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    roles: &TypeRoles,
    path: &str,
    optional: bool,
    slots: &mut Vec<PointerSlot>,
) -> Result<(), InventoryIssue> {
    use PointerKind as K;
    let pointer = match *ty.kind() {
        ty::RawPtr(inner, m) => Some((if m.is_mut() { K::RawMut } else { K::RawConst }, inner)),
        ty::Ref(_, inner, m) => {
            let k = match (inner.is_slice(), optional, m.is_mut()) {
                (true, _, true) => K::SliceMut,
                (true, _, false) => K::Slice,
                (false, true, true) => K::OptRefMut,
                (false, true, false) => K::OptRef,
                (false, false, true) => K::RefMut,
                (false, false, false) => K::Ref,
            };
            Some((k, inner))
        }
        ty::Adt(def, args) if def.is_box() => {
            let inner = args.type_at(0);
            let k = match (inner.is_slice(), optional) {
                (true, true) => K::OptBoxedSlice,
                (true, false) => K::BoxedSlice,
                (false, true) => K::OptBox,
                (false, false) => K::Box,
            };
            Some((k, inner))
        }
        _ => None,
    };
    if let Some((kind, inner)) = pointer {
        slots.push(PointerSlot {
            path: path.into(),
            kind,
            optional,
        });
        return walk_type(inner, tcx, roles, &format!("{path}.pointee"), false, slots);
    }
    match *ty.kind() {
        ty::Adt(def, args) if tcx.lang_items().option_type() == Some(def.did()) => {
            walk_type(args.type_at(0), tcx, roles, path, true, slots)?
        }
        ty::Adt(def, _) if def.is_phantom_data() => (),
        ty::Adt(def, args) if roles.cursors.contains_key(&def.did()) => {
            slots.push(PointerSlot {
                path: path.into(),
                kind: if roles.cursors[&def.did()] {
                    K::SliceCursorMut
                } else {
                    K::SliceCursor
                },
                optional,
            });
            walk_type(
                args.types().next().expect("cursor element type"),
                tcx,
                roles,
                &format!("{path}.element"),
                false,
                slots,
            )?;
        }
        ty::Adt(def, args) => {
            // Local fields are inventoried at their definitions. Inspect type arguments,
            // never recursively multiply those fields at each declaration using the ADT.
            if !def.did().is_local() && !ty.is_c_void(tcx) {
                return Err(InventoryIssue {
                    locator: None,
                    reason: format!("unsupported external wrapper: {ty}"),
                });
            }
            for (i, arg) in args.types().enumerate() {
                walk_type(arg, tcx, roles, &format!("{path}.arg[{i}]"), false, slots)?;
            }
        }
        ty::Tuple(types) => {
            for (i, inner) in types.iter().enumerate() {
                walk_type(
                    inner,
                    tcx,
                    roles,
                    &format!("{path}.tuple[{i}]"),
                    false,
                    slots,
                )?;
            }
        }
        ty::Array(inner, _) | ty::Slice(inner) => {
            walk_type(inner, tcx, roles, &format!("{path}.element"), false, slots)?
        }
        ty::FnPtr(..) => slots.push(PointerSlot {
            path: path.into(),
            kind: if optional { K::OptFnPtr } else { K::FnPtr },
            optional,
        }),
        ty::Alias(..) | ty::Error(_) | ty::Infer(_) => {
            return Err(InventoryIssue {
                locator: None,
                reason: format!("unresolved type: {ty}"),
            });
        }
        _ => (),
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum DeclarationKey {
    Global(LocalDefId, Site, u32),
    Local(hir::HirId),
}

pub fn collect_inventory(tcx: TyCtxt<'_>, case_id: &str, stage: StageId) -> Inventory {
    let mut ast = crate::ast::expanded_ast(tcx);
    let mapper = crate::ast::make_ast_to_hir(&mut ast, tcx);
    collect_bound_inventory(tcx, &ast, &mapper, case_id, stage).0
}

/// Reuse the rewriter's AST and mapper; never request expanded_ast after HIR queries.
pub fn collect_bound_inventory(
    tcx: TyCtxt<'_>,
    ast: &rustc_ast::Crate,
    mapper: &crate::ir::AstToHir,
    case_id: &str,
    stage: StageId,
) -> (Inventory, Vec<rustc_ast::NodeId>) {
    let mut collector = Collector {
        tcx,
        inventory: Inventory {
            schema_version: 1,
            case_id: case_id.into(),
            profile: None,
            stage,
            source_hashes: BTreeMap::new(),
            declarations: Vec::new(),
            issues: Vec::new(),
        },
        keys: Vec::new(),
        bindings: HashSet::new(),
        param_bindings: HashSet::new(),
        owners: BTreeMap::new(),
        ordinals: BTreeMap::new(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut collector);
    crate::type_check(tcx);
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
    for (node, key) in sites {
        if let Some(mut d) = declarations.remove(&key) {
            let index = nodes.len();
            let Some(source_site) = source_sites.get(&node) else {
                collector.inventory.issues.push(InventoryIssue {
                    locator: Some(d.locator),
                    reason: format!("missing structural source site: {node:?}"),
                });
                continue;
            };
            d.locator = source_site.locator.clone();
            d.name = source_site.name.clone();
            d.declaration_id = DeclId(format!("{case_id}:decl:{index}"));
            nodes.push(node);
            collector.inventory.declarations.push(d);
        }
    }
    for (_, d) in declarations {
        collector.inventory.issues.push(InventoryIssue {
            locator: Some(d.locator),
            reason: format!(
                "declaration has no source AST binding: {} {:?}",
                d.owner, d.name
            ),
        });
    }
    (collector.inventory, nodes)
}

struct Collector<'tcx> {
    tcx: TyCtxt<'tcx>,
    inventory: Inventory,
    keys: Vec<DeclarationKey>,
    bindings: HashSet<hir::HirId>,
    param_bindings: HashSet<hir::HirId>,
    owners: BTreeMap<String, u32>,
    ordinals: BTreeMap<(String, Site), u32>,
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
        let next = self.owners.len() as u32;
        let owner_index = *self.owners.entry(owner.clone()).or_insert(next);
        let ordinal = self.ordinals.entry((owner.clone(), site)).or_default();
        let locator = DeclarationLocator {
            owner_path: vec![owner_index],
            site,
            ordinal: *ordinal,
            pattern_path: vec![],
        };
        self.keys
            .push(DeclarationKey::Global(owner_id, site, *ordinal));
        *ordinal += 1;
        let (slots, pointer_state) = match classify_type(ty, self.tcx) {
            Ok(slots) => {
                let state = if slots.iter().any(|s| s.kind.is_raw()) {
                    PointerState::Raw
                } else if slots.iter().any(|s| s.kind.is_data_pointer()) {
                    PointerState::Promoted
                } else {
                    PointerState::Nonpointer
                };
                (slots, state)
            }
            Err(mut issue) => {
                issue.locator = Some(locator.clone());
                self.inventory.issues.push(issue);
                (vec![], PointerState::Unsupported)
            }
        };
        let loc = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        self.inventory.declarations.push(Declaration {
            declaration_id: DeclId(format!(
                "{}:decl:{}",
                self.inventory.case_id,
                self.inventory.declarations.len()
            )),
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
            slots,
            pointer_state,
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
            hir::ItemKind::Const(..) => self.add(
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
