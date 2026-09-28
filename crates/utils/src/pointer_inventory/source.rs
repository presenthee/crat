//! Join source declarations to typed HIR sites using compiler mappings, never spans/names.
use std::collections::HashSet;

use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};
use rustc_hir as hir;
use rustc_middle::ty::TyCtxt;

use super::{Site, collect::DeclarationKey as Key};
use crate::ir::AstToHir;

pub(super) fn bound_sites(
    ast: &ast::Crate,
    mapper: &AstToHir,
    tcx: TyCtxt<'_>,
) -> Vec<(ast::NodeId, Key)> {
    let mut visitor = BindingVisitor {
        mapper,
        tcx,
        sites: Vec::new(),
        seen: HashSet::new(),
        in_param: false,
    };
    visitor.visit_crate(ast);
    visitor.sites
}
struct BindingVisitor<'a, 'tcx> {
    mapper: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    sites: Vec<(ast::NodeId, Key)>,
    seen: HashSet<Key>,
    in_param: bool,
}
impl BindingVisitor<'_, '_> {
    fn add(&mut self, node: ast::NodeId, key: Key) {
        if self.seen.insert(key) {
            self.sites.push((node, key));
        }
    }

    fn global(&mut self, node: ast::NodeId, site: Site) {
        if let Some(id) = self.mapper.global_map.get(&node) {
            self.add(node, Key::Global(*id, site, 0));
        }
    }
}
impl<'ast> Visitor<'ast> for BindingVisitor<'_, '_> {
    fn visit_fn(&mut self, kind: visit::FnKind<'ast>, span: rustc_span::Span, node: ast::NodeId) {
        let owner = self.mapper.global_map.get(&node).copied().or_else(|| {
            if let Some(hir::Node::Expr(expr)) = self.mapper.get_local_node(node, self.tcx)
                && let hir::ExprKind::Closure(c) = expr.kind
            {
                Some(c.def_id)
            } else {
                None
            }
        });
        if let Some(owner) = owner {
            for (i, param) in kind.decl().inputs.iter().enumerate() {
                if !matches!(param.pat.kind, ast::PatKind::Missing) {
                    self.add(param.ty.id, Key::Global(owner, Site::Param, i as u32));
                }
            }
            self.add(node, Key::Global(owner, Site::Return, 0));
        }
        let _ = span;
        visit::walk_fn(self, kind);
    }

    fn visit_param(&mut self, param: &'ast ast::Param) {
        let old = self.in_param;
        self.in_param = true;
        visit::walk_param(self, param);
        self.in_param = old;
    }

    fn visit_pat(&mut self, pat: &'ast ast::Pat) {
        if !self.in_param
            && let Some(hir::Node::Pat(hpat)) = self.mapper.get_local_node(pat.id, self.tcx)
            && let hir::PatKind::Binding(_, id, _, _) = hpat.kind
        {
            self.add(pat.id, Key::Local(id));
        }
        visit::walk_pat(self, pat);
    }

    fn visit_field_def(&mut self, field: &'ast ast::FieldDef) {
        self.global(field.id, Site::Field);
        visit::walk_field_def(self, field);
    }

    fn visit_item(&mut self, item: &'ast ast::Item) {
        match item.kind {
            ast::ItemKind::Static(_) => self.global(item.id, Site::Static),
            ast::ItemKind::Const(_) => self.global(item.id, Site::Const),
            _ => (),
        }
        visit::walk_item(self, item);
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, ctxt: visit::AssocCtxt) {
        if matches!(item.kind, ast::AssocItemKind::Const(_)) {
            self.global(item.id, Site::Const);
        }
        visit::walk_assoc_item(self, item, ctxt);
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        if matches!(item.kind, ast::ForeignItemKind::Static(_)) {
            self.global(item.id, Site::Static);
        }
        visit::walk_item(self, item);
    }
}
