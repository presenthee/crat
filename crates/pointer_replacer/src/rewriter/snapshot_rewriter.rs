//! Inserts immutable snapshot copies before call sites where a mutable and
//! one or more read-only raw-pointer arguments share a base. The callee then
//! reads from a fresh local array instead of the aliased object, so the later
//! borrow rewrite can promote the callee's read-only parameters out of the
//! mutable alias cluster. The inserted code is plain raw-pointer Rust; every
//! downstream sub-pass recomputes its analyses on it.
//!
//! Emission runs in two phases over the AST. `plan_sites` resolves each gated
//! candidate against MIR (call span, argument element types, the base
//! variable's debug name) and checks feasibility in the AST: the call must be
//! a whole statement, and whole-array arguments must have a recognizable
//! shape. Infeasible sites are dropped *before* callee selection, so a callee
//! is only selected when every one of its sites can actually be rewritten.
//! `apply_snapshot_isolation` then inserts the snapshot `let`s and replaces
//! the read-only arguments at the surviving sites.

use rustc_ast::{
    Block, Crate, Expr, ExprKind, Fn, Item, ItemKind, Safety, Stmt, StmtKind,
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind, VarDebugInfoContents},
    ty::{self, TyCtxt},
};
use rustc_span::{
    Span,
    def_id::{DefPathHash, LocalDefId},
};
use thin_vec::thin_vec;
use utils::ir::AstToHir;

use crate::analyses::aliasing::{CopyPlan, GatedCandidate};

/// True when `CRAT_SNAPSHOT_TRACE` asks for decision prints on stderr.
pub(crate) fn trace_enabled() -> bool {
    std::env::var("CRAT_SNAPSHOT_TRACE").is_ok_and(|v| {
        let v = v.trim();
        !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
    })
}

/// Everything the AST emission needs for one call site.
pub(crate) struct SiteRewrite {
    pub(crate) caller: LocalDefId,
    pub(crate) callee: LocalDefId,
    function: DefPathHash,
    /// The call expression's span, which identifies the AST statement.
    call_span: Span,
    runtime_len: Option<RuntimeLen>,
    copies: Vec<PlannedCopy>,
}

/// The site's shared runtime length: the call argument position holding it
/// and its source name in the caller (an unprojected parameter local).
struct RuntimeLen {
    arg_index: usize,
    source_name: String,
}

/// One read-only argument's copy, with everything resolved to strings.
enum PlannedCopy {
    /// `let snap: [elem_ty; elems] = *(<arg> as *const [elem_ty; elems]);`
    /// and the argument becomes `snap.as_ptr()`.
    Prefix {
        arg_index: usize,
        source_name: Option<String>,
        elem_ty: String,
        elems: u64,
    },
    /// `let snap: [elem_ty; len] = <base>;` — shared by every such argument
    /// of the site — and the argument's `<base>.as_ptr()`/`as_mut_ptr()`
    /// call is redirected to `snap.as_ptr()`.
    Whole {
        arg_index: usize,
        base_name: String,
        elem_ty: String,
        len: u64,
    },
    /// `let snap: Vec<elem_ty> = if <captured_len> > 0 { <read>.to_vec() }
    /// else { Vec::new() };` and the argument becomes `snap.as_ptr()`. The
    /// site's shared `runtime_len` supplies the captured length.
    Runtime {
        arg_index: usize,
        source_name: Option<String>,
        elem_ty: String,
    },
}

pub(crate) struct GeneratedSnapshot {
    pub(crate) function: DefPathHash,
    pub(crate) name: String,
    pub(crate) origin_name: Option<String>,
}

pub(crate) struct SnapshotIsolationResult {
    pub(crate) changed: bool,
    pub(crate) generated: Vec<GeneratedSnapshot>,
}

/// The source-level debug name of an unprojected local, if the body has one
/// recorded (compiler temporaries do not).
fn local_source_name(body: &rustc_middle::mir::Body<'_>, local: Local) -> Option<String> {
    body.var_debug_info.iter().find_map(|info| {
        let VarDebugInfoContents::Place(place) = &info.value else {
            return None;
        };
        (place.local == local && place.projection.is_empty()).then(|| info.name.to_string())
    })
}

/// Maximum anonymous copy hops walked by `skip_anonymous_copies` before
/// giving up, mirroring `analyses::aliasing`'s own bound.
const MAX_ANONYMOUS_COPY_DEPTH: usize = 32;

/// Walks back through anonymous (no source name) unprojected `Rvalue::Use`
/// copies — the compiler's own call-argument temporaries — to the local they
/// ultimately copy, so a call argument like `move _7` (where `_7 = copy
/// _2;`) resolves to the named parameter `_2` behind it. Mirrors
/// `analyses::aliasing::skip_anonymous_copies`, which the gate stage already
/// used to prove this call's length argument is a direct caller parameter;
/// this re-walk reaches the same local to read its debug name.
fn skip_anonymous_copies(body: &rustc_middle::mir::Body<'_>, mut local: Local) -> Local {
    let has_debug_name = |local: Local| local_source_name(body, local).is_some();
    let definitions_of = |local: Local| {
        let mut sources = vec![];
        let mut other_definitions = false;
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                match &statement.kind {
                    StatementKind::Assign(box (place, Rvalue::Use(operand)))
                        if place.as_local() == Some(local) =>
                    {
                        match operand {
                            Operand::Copy(source) | Operand::Move(source)
                                if source.projection.is_empty() =>
                            {
                                sources.push(source.local);
                            }
                            _ => other_definitions = true,
                        }
                    }
                    StatementKind::Assign(box (place, _)) if place.as_local() == Some(local) => {
                        other_definitions = true;
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator().kind
                && destination.as_local() == Some(local)
            {
                other_definitions = true;
            }
        }
        (sources, other_definitions)
    };
    for _ in 0..MAX_ANONYMOUS_COPY_DEPTH {
        if has_debug_name(local) {
            return local;
        }
        let (sources, other_definitions) = definitions_of(local);
        if other_definitions || sources.len() != 1 {
            return local;
        }
        let source = sources[0];
        if source == local {
            return local;
        }
        local = source;
    }
    local
}

fn argument_source_name(
    body: &rustc_middle::mir::Body<'_>,
    args: &[rustc_span::source_map::Spanned<Operand<'_>>],
    arg_index: usize,
) -> Option<String> {
    let (Operand::Copy(place) | Operand::Move(place)) = &args.get(arg_index)?.node else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    local_source_name(body, skip_anonymous_copies(body, place.local))
}

/// Resolves gated candidates into rewrite-ready sites and drops the ones the
/// AST cannot express: calls not in statement position, whole-array bases
/// without a debug name, and argument shapes the substitution does not
/// recognize. Returns the surviving candidates (for selection) with their
/// sites, still paired by index.
pub(crate) fn plan_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    gated: Vec<GatedCandidate>,
    krate: &Crate,
    ast_to_hir: &AstToHir,
    trace: bool,
) -> (Vec<GatedCandidate>, Vec<SiteRewrite>) {
    let skip = |candidate: &GatedCandidate, reason: &str| {
        if trace {
            eprintln!(
                "SNAPSHOT_SKIP caller={} callee={} reason={reason}",
                tcx.def_path_str(candidate.candidate.caller.to_def_id()),
                tcx.def_path_str(candidate.candidate.callee.to_def_id()),
            );
        }
    };

    // Resolve the MIR-side facts of each site.
    let mut resolved: Vec<(GatedCandidate, SiteRewrite)> = vec![];
    'candidates: for gated_candidate in gated {
        let candidate = &gated_candidate.candidate;
        let body = tcx
            .mir_drops_elaborated_and_const_checked(candidate.caller)
            .borrow();
        let terminator = body.basic_blocks[candidate.location.block].terminator();
        let call_span = terminator.source_info.span;
        let TerminatorKind::Call { args, .. } = &terminator.kind else {
            continue;
        };

        let mut copies = vec![];
        let mut runtime_len: Option<RuntimeLen> = None;
        for plan in &gated_candidate.copies {
            match *plan {
                CopyPlan::ExactPrefix { arg_index, elems } => {
                    let arg_ty = args[arg_index].node.ty(&body.local_decls, tcx);
                    let ty::TyKind::RawPtr(pointee, _) = arg_ty.kind() else {
                        continue 'candidates;
                    };
                    copies.push(PlannedCopy::Prefix {
                        arg_index,
                        source_name: argument_source_name(&body, args, arg_index),
                        elem_ty: pointee.to_string(),
                        elems,
                    });
                }
                CopyPlan::WholeArray {
                    arg_index,
                    base_local,
                    len,
                } => {
                    let Some(base_name) = local_source_name(&body, base_local) else {
                        skip(&gated_candidate, "array base has no source name");
                        continue 'candidates;
                    };
                    let ty::TyKind::Array(elem, _) = body.local_decls[base_local].ty.kind() else {
                        continue 'candidates;
                    };
                    copies.push(PlannedCopy::Whole {
                        arg_index,
                        base_name,
                        elem_ty: elem.to_string(),
                        len,
                    });
                }
                CopyPlan::RuntimePrefix {
                    arg_index,
                    len_param,
                } => {
                    let arg_ty = args[arg_index].node.ty(&body.local_decls, tcx);
                    let ty::TyKind::RawPtr(pointee, _) = arg_ty.kind() else {
                        continue 'candidates;
                    };
                    let Some(len_arg) = args.get(len_param) else {
                        continue 'candidates;
                    };
                    let (Operand::Copy(place) | Operand::Move(place)) = &len_arg.node else {
                        skip(&gated_candidate, "runtime length argument is not a place");
                        continue 'candidates;
                    };
                    if !place.projection.is_empty() {
                        skip(&gated_candidate, "runtime length argument is projected");
                        continue 'candidates;
                    }
                    let len_local = skip_anonymous_copies(&body, place.local);
                    let Some(source_name) = local_source_name(&body, len_local) else {
                        skip(&gated_candidate, "runtime length local has no source name");
                        continue 'candidates;
                    };
                    match &runtime_len {
                        Some(existing) if existing.arg_index != len_param => {
                            skip(
                                &gated_candidate,
                                "runtime copies at this site disagree on the length argument",
                            );
                            continue 'candidates;
                        }
                        Some(existing) if existing.source_name != source_name => {
                            skip(
                                &gated_candidate,
                                "runtime copies at this site disagree on the length source name",
                            );
                            continue 'candidates;
                        }
                        _ => {
                            runtime_len = Some(RuntimeLen {
                                arg_index: len_param,
                                source_name,
                            });
                        }
                    }
                    copies.push(PlannedCopy::Runtime {
                        arg_index,
                        source_name: argument_source_name(&body, args, arg_index),
                        elem_ty: pointee.to_string(),
                    });
                }
            }
        }
        drop(body);
        let site = SiteRewrite {
            caller: candidate.caller,
            callee: candidate.callee,
            function: tcx.def_path_hash(candidate.caller.to_def_id()),
            call_span,
            runtime_len,
            copies,
        };
        resolved.push((gated_candidate, site));
    }

    // Check each site against the AST: the call must be a whole statement
    // and every whole-array argument must have a recognizable shape.
    let mut by_caller: FxHashMap<LocalDefId, Vec<usize>> = FxHashMap::default();
    for (i, (_, site)) in resolved.iter().enumerate() {
        by_caller.entry(site.caller).or_default().push(i);
    }
    let mut checker = FeasibilityVisitor {
        ast_to_hir,
        sites: &resolved,
        by_caller: &by_caller,
        current: vec![],
        feasible: FxHashSet::default(),
    };
    checker.visit_crate(krate);
    let feasible = checker.feasible;

    let mut kept_candidates = vec![];
    let mut kept_sites = vec![];
    for (i, (candidate, site)) in resolved.into_iter().enumerate() {
        if feasible.contains(&i) {
            kept_candidates.push(candidate);
            kept_sites.push(site);
        } else {
            skip(
                &candidate,
                "no statement-position call with rewritable arguments",
            );
        }
    }
    (kept_candidates, kept_sites)
}

struct FeasibilityVisitor<'a> {
    ast_to_hir: &'a AstToHir,
    sites: &'a [(GatedCandidate, SiteRewrite)],
    by_caller: &'a FxHashMap<LocalDefId, Vec<usize>>,
    /// Site indices pending in the enclosing function.
    current: Vec<usize>,
    feasible: FxHashSet<usize>,
}

impl<'ast> Visitor<'ast> for FeasibilityVisitor<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        let pending = if matches!(item.kind, ItemKind::Fn(_)) {
            self.ast_to_hir
                .global_map
                .get(&item.id)
                .and_then(|def_id| self.by_caller.get(def_id))
                .cloned()
                .unwrap_or_default()
        } else {
            vec![]
        };
        let previous = std::mem::replace(&mut self.current, pending);
        visit::walk_item(self, item);
        self.current = previous;
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        if let StmtKind::Semi(expr) = &stmt.kind
            && let ExprKind::Call(_, call_args) = &expr.kind
        {
            for &i in &self.current {
                let site = &self.sites[i].1;
                if site.call_span != expr.span {
                    continue;
                }
                let copies_rewritable = site.copies.iter().all(|copy| match copy {
                    PlannedCopy::Prefix { arg_index, .. } => call_args.len() > *arg_index,
                    PlannedCopy::Whole {
                        arg_index,
                        base_name,
                        ..
                    } => call_args.get(*arg_index).is_some_and(|arg| {
                        rewrite_whole_arg(arg, base_name, "__crat_snap").is_some()
                    }),
                    PlannedCopy::Runtime { arg_index, .. } => call_args.len() > *arg_index,
                });
                let runtime_rewritable = site.runtime_len.as_ref().is_none_or(|runtime| {
                    call_args
                        .get(runtime.arg_index)
                        .is_some_and(|arg| is_plain_ident(arg, &runtime.source_name))
                        && call_args.iter().all(|arg| plain_ident_name(arg).is_some())
                });
                if copies_rewritable && runtime_rewritable {
                    self.feasible.insert(i);
                }
            }
        }
        visit::walk_stmt(self, stmt);
    }
}

/// Inserts the snapshot `let`s and replaces the read-only arguments at every
/// site. Returns whether anything changed. Under `validate`, each
/// exact-prefix snapshot is followed by a `debug_assert_eq!` re-reading the
/// original argument (whole-array copies get none: their snapshot trivially
/// equals the base it was just copied from).
pub(crate) fn apply_snapshot_isolation(
    krate: &mut Crate,
    sites: &[SiteRewrite],
    ast_to_hir: &AstToHir,
    validate: bool,
) -> SnapshotIsolationResult {
    if sites.is_empty() {
        return SnapshotIsolationResult {
            changed: false,
            generated: Vec::new(),
        };
    }
    let mut by_caller: FxHashMap<LocalDefId, Vec<&SiteRewrite>> = FxHashMap::default();
    for site in sites {
        by_caller.entry(site.caller).or_default().push(site);
    }
    let mut visitor = EmitVisitor {
        ast_to_hir,
        by_caller,
        validate,
        fn_sites: vec![],
        fn_is_unsafe: false,
        snap_counter: 0,
        changed: false,
        generated: Vec::new(),
    };
    visitor.visit_crate(krate);
    SnapshotIsolationResult {
        changed: visitor.changed,
        generated: visitor.generated,
    }
}

struct EmitVisitor<'a> {
    ast_to_hir: &'a AstToHir,
    by_caller: FxHashMap<LocalDefId, Vec<&'a SiteRewrite>>,
    validate: bool,
    /// Sites of the function currently being visited.
    fn_sites: Vec<&'a SiteRewrite>,
    fn_is_unsafe: bool,
    snap_counter: usize,
    changed: bool,
    generated: Vec<GeneratedSnapshot>,
}

impl MutVisitor for EmitVisitor<'_> {
    fn visit_item(&mut self, item: &mut Item) {
        let (sites, is_unsafe) = if let ItemKind::Fn(box Fn { ref sig, .. }) = item.kind {
            (
                self.ast_to_hir
                    .global_map
                    .get(&item.id)
                    .and_then(|def_id| self.by_caller.get(def_id))
                    .cloned()
                    .unwrap_or_default(),
                matches!(sig.header.safety, Safety::Unsafe(_)),
            )
        } else {
            (vec![], false)
        };
        let previous_sites = std::mem::replace(&mut self.fn_sites, sites);
        let previous_unsafe = std::mem::replace(&mut self.fn_is_unsafe, is_unsafe);
        let previous_counter = std::mem::replace(&mut self.snap_counter, 0);
        mut_visit::walk_item(self, item);
        self.fn_sites = previous_sites;
        self.fn_is_unsafe = previous_unsafe;
        self.snap_counter = previous_counter;
    }

    fn visit_block(&mut self, block: &mut Block) {
        mut_visit::walk_block(self, block);
        if self.fn_sites.is_empty() {
            return;
        }
        let mut i = 0;
        while i < block.stmts.len() {
            let inserts = self.rewrite_stmt(&mut block.stmts[i]);
            let n = inserts.len();
            for (k, stmt) in inserts.into_iter().enumerate() {
                block.stmts.insert(i + k, stmt);
            }
            i += n + 1;
        }
    }
}

impl EmitVisitor<'_> {
    /// Rewrites one statement's call arguments when it is a planned site and
    /// returns the snapshot statements to insert before it.
    fn rewrite_stmt(&mut self, stmt: &mut Stmt) -> Vec<Stmt> {
        let StmtKind::Semi(expr) = &mut stmt.kind else {
            return vec![];
        };
        let span = expr.span;
        let ExprKind::Call(_, call_args) = &mut expr.kind else {
            return vec![];
        };
        let sites: Vec<&SiteRewrite> = self
            .fn_sites
            .iter()
            .copied()
            .filter(|s| s.call_span == span)
            .collect();

        let mut inserts = vec![];
        for site in sites {
            // The site's runtime length, captured once before any copy reads
            // it, so a mutable call downstream of the length argument cannot
            // change what gets snapshotted.
            let runtime_capture = site.runtime_len.as_ref().map(|runtime| {
                let name = self.fresh_len_name();
                let source_name = &runtime.source_name;
                inserts.push(utils::stmt!("let {name} = {source_name};"));
                *call_args[runtime.arg_index] = utils::expr!("{name}");
                name
            });
            // Whole-array copies of one site share a single snapshot.
            let mut shared_whole: Option<String> = None;
            for copy in &site.copies {
                match copy {
                    PlannedCopy::Prefix {
                        arg_index,
                        source_name,
                        elem_ty,
                        elems,
                    } => {
                        let name = self.fresh_name();
                        let origin_name = source_name.clone().or_else(|| {
                            plain_ident_name(&call_args[*arg_index]).map(str::to_owned)
                        });
                        self.generated.push(GeneratedSnapshot {
                            function: site.function,
                            name: name.clone(),
                            origin_name,
                        });
                        let arg = pprust::expr_to_string(&call_args[*arg_index]);
                        // The element-pointer cast first: the argument may be
                        // a reference coerced to a raw pointer at the call,
                        // and a reference only casts to a pointer of its own
                        // pointee.
                        let init =
                            format!("*({arg} as *const {elem_ty} as *const [{elem_ty}; {elems}])");
                        inserts.push(utils::stmt!(
                            "let {name}: [{elem_ty}; {elems}] = {};",
                            self.in_unsafe(init)
                        ));
                        if self.validate {
                            let check = format!(
                                "std::slice::from_raw_parts({arg} as *const {elem_ty}, {elems})"
                            );
                            inserts.push(utils::stmt!(
                                "debug_assert_eq!({}, &{name}[..]);",
                                self.in_unsafe(check)
                            ));
                        }
                        *call_args[*arg_index] = utils::expr!("{name}.as_ptr()");
                        self.changed = true;
                    }
                    PlannedCopy::Whole {
                        arg_index,
                        base_name,
                        elem_ty,
                        len,
                    } => {
                        let name = match &shared_whole {
                            Some(name) => name.clone(),
                            None => {
                                let name = self.fresh_name();
                                self.generated.push(GeneratedSnapshot {
                                    function: site.function,
                                    name: name.clone(),
                                    origin_name: Some(base_name.clone()),
                                });
                                inserts.push(utils::stmt!(
                                    "let {name}: [{elem_ty}; {len}] = {base_name};"
                                ));
                                shared_whole = Some(name.clone());
                                name
                            }
                        };
                        // Feasibility already proved the shape rewritable.
                        if let Some(new_arg) =
                            rewrite_whole_arg(&call_args[*arg_index], base_name, &name)
                        {
                            *call_args[*arg_index] = new_arg;
                            self.changed = true;
                        }
                    }
                    PlannedCopy::Runtime {
                        arg_index,
                        source_name,
                        elem_ty,
                    } => {
                        let len = runtime_capture
                            .as_ref()
                            .expect("runtime copy has a site length capture");
                        let name = self.fresh_name();
                        let origin_name = source_name.clone().or_else(|| {
                            plain_ident_name(&call_args[*arg_index]).map(str::to_owned)
                        });
                        self.generated.push(GeneratedSnapshot {
                            function: site.function,
                            name: name.clone(),
                            origin_name,
                        });
                        let arg = pprust::expr_to_string(&call_args[*arg_index]);
                        let read = self.in_unsafe(format!(
                            "std::slice::from_raw_parts(({arg}) as *const {elem_ty}, {len} as usize).to_vec()"
                        ));
                        inserts.push(utils::stmt!(
                            "let {name}: Vec<{elem_ty}> = if {len} > 0 {{ {read} }} else {{ Vec::new() }};"
                        ));
                        if self.validate {
                            let check = self.in_unsafe(format!(
                                "std::slice::from_raw_parts(({arg}) as *const {elem_ty}, {len} as usize)"
                            ));
                            inserts.push(utils::stmt!(
                                "if {len} > 0 {{ debug_assert_eq!({check}, &{name}[..]); }}"
                            ));
                        }
                        *call_args[*arg_index] = utils::expr!("{name}.as_ptr()");
                        self.changed = true;
                    }
                }
            }
        }
        inserts
    }

    fn fresh_name(&mut self) -> String {
        let name = format!("__crat_snap_{}", self.snap_counter);
        self.snap_counter += 1;
        name
    }

    fn fresh_len_name(&mut self) -> String {
        let name = format!("__crat_snap_len_{}", self.snap_counter);
        self.snap_counter += 1;
        name
    }

    /// Raw-pointer reads need an unsafe context; an `unsafe fn` body already
    /// is one (`unsafe_op_in_unsafe_fn` is allow-by-default).
    fn in_unsafe(&self, code: String) -> String {
        if self.fn_is_unsafe {
            code
        } else {
            format!("unsafe {{ {code} }}")
        }
    }
}

/// Rebuilds a whole-array argument against the snapshot: the base variable's
/// `as_ptr`/`as_mut_ptr` call becomes `<snap>.as_ptr()` (the snapshot is
/// read-only), preserving any `offset` calls and casts around it. `None` for
/// any other shape.
fn rewrite_whole_arg(expr: &Expr, base_name: &str, snap_name: &str) -> Option<Expr> {
    let rebuilt = |kind: ExprKind| Expr {
        id: rustc_ast::DUMMY_NODE_ID,
        kind,
        span: expr.span,
        attrs: thin_vec![],
        tokens: None,
    };
    match &expr.kind {
        ExprKind::MethodCall(call) => {
            let method = call.seg.ident.name.as_str();
            if matches!(method, "as_ptr" | "as_mut_ptr")
                && call.args.is_empty()
                && is_plain_ident(&call.receiver, base_name)
            {
                return Some(utils::expr!("{snap_name}.as_ptr()"));
            }
            if method == "offset" && call.args.len() == 1 {
                let receiver = rewrite_whole_arg(&call.receiver, base_name, snap_name)?;
                let mut call = call.clone();
                call.receiver = P(receiver);
                return Some(rebuilt(ExprKind::MethodCall(call)));
            }
            None
        }
        ExprKind::Cast(inner, ty) => {
            let inner = rewrite_whole_arg(inner, base_name, snap_name)?;
            Some(rebuilt(ExprKind::Cast(P(inner), ty.clone())))
        }
        ExprKind::Paren(inner) => rewrite_whole_arg(inner, base_name, snap_name),
        _ => None,
    }
}

/// The identifier name of a (possibly parenthesized) plain-path expression,
/// e.g. `x` or `(x)`. `None` for any other shape.
fn plain_ident_name(expr: &Expr) -> Option<&str> {
    let mut expr = expr;
    while let ExprKind::Paren(inner) = &expr.kind {
        expr = inner;
    }
    let ExprKind::Path(None, path) = &expr.kind else {
        return None;
    };
    let [segment] = path.segments.as_slice() else {
        return None;
    };
    Some(segment.ident.name.as_str())
}

fn is_plain_ident(expr: &Expr, name: &str) -> bool {
    plain_ident_name(expr) == Some(name)
}
