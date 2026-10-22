//! Pointer-use counting: one count per path or field expression whose type is
//! pointer-like, keyed by the root slot kind of that type.
use std::collections::{BTreeMap, HashSet};

use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    intravisit::{self, Visitor},
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use serde::Serialize;

use super::{
    collect::{TypeRoles, injected_cursor_roles, is_injected_support_owner},
    observe_type,
};

#[derive(Default, Serialize)]
pub struct UseCounts {
    /// root pointer kind -> number of use sites
    pub by_kind: BTreeMap<String, usize>,
    /// "<site>/<kind>" -> number of use sites; site is local, param, static, const or field
    pub by_site_kind: BTreeMap<String, usize>,
    /// "<owner def path>|<site>|<kind>|<field struct def path or ->" -> number of use sites
    pub by_owner: BTreeMap<String, usize>,
}

pub fn count_uses(tcx: TyCtxt<'_>) -> UseCounts {
    let mut visitor = UseVisitor {
        tcx,
        roles: injected_cursor_roles(tcx),
        counts: UseCounts::default(),
        param_bindings: HashSet::new(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    visitor.counts
}

struct UseVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    roles: TypeRoles,
    counts: UseCounts,
    param_bindings: HashSet<hir::HirId>,
}

impl<'tcx> UseVisitor<'tcx> {
    fn is_support(&self, id: hir::OwnerId) -> bool {
        is_injected_support_owner(&self.tcx.def_path_str(id.to_def_id()))
    }

    fn record(&mut self, site: &str, expr: &hir::Expr<'tcx>) {
        let typeck = self.tcx.typeck(expr.hir_id.owner);
        let ty = typeck.expr_ty(expr);
        let field_struct = match expr.kind {
            hir::ExprKind::Field(base, _) => match typeck.expr_ty_adjusted(base).peel_refs().ty_adt_def() {
                Some(adt) => self.tcx.def_path_str(adt.did()),
                None => "-".to_string(),
            },
            _ => "-".to_string(),
        };
        let owner = self.tcx.def_path_str(expr.hir_id.owner.to_def_id());
        let observed = observe_type(ty, self.tcx, &self.roles);
        let Some(root) = observed.slots.iter().find(|s| s.path == "root") else {
            return;
        };
        let kind = snake_case(&format!("{:?}", root.kind));
        *self.counts.by_kind.entry(kind.clone()).or_default() += 1;
        *self.counts.by_site_kind.entry(format!("{site}/{kind}")).or_default() += 1;
        *self
            .counts
            .by_owner
            .entry(format!("{owner}|{site}|{kind}|{field_struct}"))
            .or_default() += 1;
    }
}

impl<'tcx> Visitor<'tcx> for UseVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if !self.is_support(item.owner_id) {
            intravisit::walk_item(self, item);
        }
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem<'tcx>) {
        if !self.is_support(item.owner_id) {
            intravisit::walk_impl_item(self, item);
        }
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        for param in body.params {
            param.pat.each_binding(|_, id, _, _| {
                self.param_bindings.insert(id);
            });
        }
        intravisit::walk_body(self, body);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        let site = match expr.kind {
            hir::ExprKind::Path(hir::QPath::Resolved(None, path)) => match path.res {
                Res::Local(id) if self.param_bindings.contains(&id) => Some("param"),
                Res::Local(_) => Some("local"),
                Res::Def(DefKind::Static { .. }, _) => Some("static"),
                Res::Def(DefKind::Const | DefKind::AssocConst, _) => Some("const"),
                _ => None,
            },
            hir::ExprKind::Field(..) => Some("field"),
            _ => None,
        };
        if let Some(site) = site {
            self.record(site, expr);
        }
        intravisit::walk_expr(self, expr);
    }
}

fn snake_case(name: &str) -> String {
    let mut out = String::new();
    for (i, c) in name.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            out.push('_');
        }
        out.push(c.to_ascii_lowercase());
    }
    out
}
