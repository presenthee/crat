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

/// Structural source addresses, including unresolved identifier patterns. Typed
/// collection filters non-bindings while retaining these addresses unchanged.
#[derive(Clone, Debug)]
pub struct SourceSite {
    pub node: ast::NodeId,
    pub locator: super::DeclarationLocator,
    pub name: Option<String>,
}
pub fn source_sites(ast: &ast::Crate) -> Vec<SourceSite> {
    let mut visitor = SourceVisitor {
        sites: vec![],
        in_param: false,
    };
    visitor.visit_crate(ast);
    visitor.sites
}
pub fn source_sites_in_item(item: &ast::Item) -> Vec<SourceSite> {
    let mut visitor = SourceVisitor {
        sites: vec![],
        in_param: false,
    };
    visitor.visit_item(item);
    visitor.sites
}
pub fn source_sites_in_stmt(stmt: &ast::Stmt) -> Vec<SourceSite> {
    let mut visitor = SourceVisitor {
        sites: vec![],
        in_param: false,
    };
    visitor.visit_stmt(stmt);
    visitor.sites
}
pub fn source_sites_in_expr(expr: &ast::Expr) -> Vec<SourceSite> {
    let mut visitor = SourceVisitor {
        sites: vec![],
        in_param: false,
    };
    visitor.visit_expr(expr);
    visitor.sites
}
struct SourceVisitor {
    sites: Vec<SourceSite>,
    in_param: bool,
}
impl SourceVisitor {
    fn add(&mut self, node: ast::NodeId, site: Site, name: Option<String>) {
        self.sites.push(SourceSite {
            node,
            locator: super::DeclarationLocator {
                owner_path: vec![self.sites.len() as u32],
                site,
                ordinal: 0,
                pattern_path: vec![],
            },
            name,
        });
    }
}
fn name(p: &ast::Pat) -> Option<String> {
    if let ast::PatKind::Ident(_, ident, _) = p.kind {
        Some(ident.name.to_string())
    } else {
        None
    }
}
impl<'ast> Visitor<'ast> for SourceVisitor {
    fn visit_fn(&mut self, kind: visit::FnKind<'ast>, _: rustc_span::Span, node: ast::NodeId) {
        for param in &kind.decl().inputs {
            if !matches!(param.pat.kind, ast::PatKind::Missing) {
                self.add(param.ty.id, Site::Param, name(&param.pat));
            }
        }
        self.add(node, Site::Return, None);
        visit::walk_fn(self, kind);
    }

    fn visit_param(&mut self, param: &'ast ast::Param) {
        let old = self.in_param;
        self.in_param = true;
        visit::walk_param(self, param);
        self.in_param = old;
    }

    fn visit_pat(&mut self, pat: &'ast ast::Pat) {
        if !self.in_param && matches!(pat.kind, ast::PatKind::Ident(..)) {
            self.add(pat.id, Site::Local, name(pat));
        }
        // Alternative patterns repeat one definition. The compiler-bound visitor
        // uses the canonical HirId; use the first alternative for the address.
        if let ast::PatKind::Or(patterns) = &pat.kind {
            if let Some(first) = patterns.first() {
                self.visit_pat(first);
            }
        } else {
            visit::walk_pat(self, pat);
        }
    }

    fn visit_field_def(&mut self, field: &'ast ast::FieldDef) {
        self.add(
            field.id,
            Site::Field,
            field.ident.map(|i| i.name.to_string()),
        );
        visit::walk_field_def(self, field);
    }

    fn visit_item(&mut self, item: &'ast ast::Item) {
        match &item.kind {
            ast::ItemKind::Static(s) => {
                self.add(item.id, Site::Static, Some(s.ident.name.to_string()))
            }
            ast::ItemKind::Const(c) => {
                self.add(item.id, Site::Const, Some(c.ident.name.to_string()))
            }
            _ => (),
        }
        visit::walk_item(self, item);
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, ctxt: visit::AssocCtxt) {
        if let ast::AssocItemKind::Const(c) = &item.kind {
            self.add(item.id, Site::Const, Some(c.ident.name.to_string()));
        }
        visit::walk_assoc_item(self, item, ctxt);
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        if let ast::ForeignItemKind::Static(s) = &item.kind {
            self.add(item.id, Site::Static, Some(s.ident.name.to_string()));
        }
        visit::walk_item(self, item);
    }
}
