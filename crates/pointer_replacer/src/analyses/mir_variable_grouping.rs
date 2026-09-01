//! Group MIR locals that correspond to the same source variable
//!
//! This module handles the mapping between MIR locals and source variables,
//! including temporaries that don't have debug info but are copies of source variables.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{Body, Local, Location, Operand, Place, Rvalue, VarDebugInfoContents, visit::Visitor},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        mir::{CallKind, TerminatorExt},
        type_qualifier::foster::{TypeQualifiers, mutability::Mutability},
    },
    utils::rustc::RustProgram,
};

/// Group MIR locals by their corresponding source variable names.
/// This includes both locals with debug info and temporaries that are copies.
pub struct SourceVarGroups {
    inner: FxHashMap<LocalDefId, FxHashMap<Local, Vec<Local>>>,
}

impl SourceVarGroups {
    pub fn new(rust_program: &RustProgram) -> Self {
        let mut inner = FxHashMap::default();
        for f in rust_program.functions.iter().copied() {
            let body = &*rust_program
                .tcx
                .mir_drops_elaborated_and_const_checked(f)
                .borrow();
            let groups = group_locals_by_source_variable(body, rust_program.tcx);
            // Store groups for function f
            inner.insert(f, groups);
        }
        Self { inner }
    }

    pub fn postprocess_promoted_mut_refs(
        &self,
        promoted_mut_refs: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    ) -> FxHashMap<LocalDefId, DenseBitSet<Local>> {
        // a Local is promoted if all locals in its source variable group are promoted
        // otherwise its promotion is removed
        let mut result = FxHashMap::default();
        for (did, promoted) in promoted_mut_refs {
            let promoted = if let Some(groups) = self.inner.get(&did) {
                let mut new_promoted = DenseBitSet::new_empty(promoted.domain_size());
                for locals in groups.values() {
                    if locals.iter().all(|local| promoted.contains(*local)) {
                        // if promoted.contains(*locals.iter().max().unwrap()) { // alternative: only promote the largest local in the group (wrong)
                        for local in locals {
                            new_promoted.insert(*local);
                        }
                    }
                }
                new_promoted
            } else {
                promoted.clone()
            };
            result.insert(did, promoted);
        }
        result
    }

    pub fn postprocess_mut_res(
        &self,
        program: &RustProgram,
        mutability_result: &TypeQualifiers<Mutability>,
    ) -> FxHashMap<LocalDefId, IndexVec<Local, bool>> {
        program
            .functions
            .iter()
            .map(|&f| {
                let mut muts = mutability_result
                    .function_body_facts(f)
                    .map(|muts| muts.iter().any(|&m| m.is_mutable()))
                    .collect::<IndexVec<_, _>>();
                if let Some(groups) = self.inner.get(&f) {
                    // if any local in the group is mutable, mark all as mutable
                    for locals in groups.values() {
                        let is_mutable = locals.iter().any(|local| muts[*local]);
                        for local in locals {
                            muts[*local] = is_mutable;
                        }
                    }
                }
                (f, muts)
            })
            .collect::<FxHashMap<_, _>>()
    }

    pub fn postprocess_offset_signs(
        &self,
        access_signs: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    ) -> FxHashMap<LocalDefId, DenseBitSet<Local>> {
        // if any local in a source variable group needs cursor, all locals in the
        // group need cursor (they alias the same source-level pointer).
        access_signs
            .into_iter()
            .map(|(did, mut cursor_locals)| {
                if let Some(groups) = self.inner.get(&did) {
                    for locals in groups.values() {
                        if locals.iter().any(|&local| cursor_locals.contains(local)) {
                            for &local in locals {
                                cursor_locals.insert(local);
                            }
                        }
                    }
                }
                (did, cursor_locals)
            })
            .filter(|(_, s)| !s.is_empty())
            .collect()
    }

    pub fn postprocess_non_null_locals(
        &self,
        non_null_locals: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    ) -> FxHashMap<LocalDefId, DenseBitSet<Local>> {
        non_null_locals
            .into_iter()
            .map(|(did, mut non_null)| {
                if let Some(groups) = self.inner.get(&did) {
                    for locals in groups.values() {
                        if !locals.iter().all(|&local| non_null.contains(local)) {
                            for &local in locals {
                                non_null.remove(local);
                            }
                        }
                    }
                }
                (did, non_null)
            })
            .filter(|(_, s)| !s.is_empty())
            .collect()
    }
}

fn group_locals_by_source_variable<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<Local, Vec<Local>> {
    // First, collect all locals that have direct debug info
    let mut src_local_to_locals: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    let mut local_to_src_local: FxHashMap<Local, Local> = FxHashMap::default();

    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value
            && let Some(local) = place.as_local()
        {
            src_local_to_locals.entry(local).or_default().push(local);
            local_to_src_local.insert(local, local);
        }
    }

    // Now find temporaries that are copies of source variables
    let rels = find_relationships(body, tcx);

    // Propagate source variable names to temporaries
    // Caveat: the order of copy_relationships should be chronological
    for (dest, src) in rels.copies {
        if dest.as_usize() == 0 {
            // skip _0 (return place)
            continue;
        }
        if let Some(src_local) = local_to_src_local.get(&src).cloned()
            && !local_to_src_local.contains_key(&dest)
            && !rels.args.contains(&dest)
        {
            src_local_to_locals.entry(src_local).or_default().push(dest);
            local_to_src_local.insert(dest, src_local);
        }
    }

    src_local_to_locals
}

#[derive(Default)]
struct Relationships {
    copies: Vec<(Local, Local)>,
    args: FxHashSet<Local>,
}

/// Find copy relationships between locals (dest = copy src or dest = move src)
fn find_relationships<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Relationships {
    struct CopyVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        rels: Relationships,
    }

    impl<'tcx> Visitor<'tcx> for CopyVisitor<'tcx> {
        fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
            if let Some(edge) =
                super::mir_local_facts::copy_edge_from_assignment(place, rvalue, location)
            {
                self.rels.copies.push((edge.destination, edge.source));
            }

            if let Rvalue::BinaryOp(_, box (l, r)) = rvalue {
                if let Some(l) = l.place()
                    && let Some(l) = l.as_local()
                {
                    self.rels.args.insert(l);
                }
                if let Some(r) = r.place()
                    && let Some(r) = r.as_local()
                {
                    self.rels.args.insert(r);
                }
            }
        }

        fn visit_terminator(
            &mut self,
            terminator: &rustc_middle::mir::Terminator<'tcx>,
            _location: Location,
        ) {
            if let Some(mir_call) = terminator.as_call(self.tcx)
                && let CallKind::RustLib(def_id) = &mir_call.func
                && super::borrow::is_borrowing_method(*def_id, self.tcx)
                && let Operand::Copy(place) | Operand::Move(place) = &mir_call.args[0].node
                && let Some(local) = place.as_local()
            {
                self.rels.args.insert(local);
            }
        }
    }

    let mut visitor = CopyVisitor {
        tcx,
        rels: Relationships::default(),
    };
    visitor.visit_body(body);
    visitor.rels
}

#[cfg(test)]
mod tests {
    use super::SourceVarGroups;
    use crate::rewriter::collect_input;

    type GroupSnapshot = Vec<(String, Vec<(usize, Vec<usize>)>)>;

    fn snapshot_source_var_groups(code: &str) -> GroupSnapshot {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_input(tcx);
            let groups = SourceVarGroups::new(&program);
            let mut snapshot = program
                .functions
                .iter()
                .map(|&function| {
                    let mut function_groups = groups.inner[&function]
                        .iter()
                        .map(|(&source, members)| {
                            (
                                source.index(),
                                members.iter().map(|member| member.index()).collect(),
                            )
                        })
                        .collect::<Vec<_>>();
                    function_groups.sort_by_key(|(source, _)| *source);
                    (
                        tcx.item_name(function.to_def_id()).to_string(),
                        function_groups,
                    )
                })
                .collect::<Vec<_>>();
            snapshot.sort_by(|left, right| left.0.cmp(&right.0));
            snapshot
        })
        .unwrap()
    }

    #[test]
    fn source_var_groups_match_pre_extraction_snapshot() {
        let actual = snapshot_source_var_groups(
            r#"
            unsafe fn copy_chain(p: *mut i32) -> *mut i32 {
                let q = p;
                let r = q;
                r
            }

            unsafe fn binary_operand(p: *mut i32, n: isize) -> *mut i32 {
                let q = p;
                let shifted = unsafe { q.offset(n + 1) };
                shifted
            }

            fn borrowing_receivers(values: &mut Vec<i32>) -> (*const i32, *mut i32) {
                let shared = values.as_ptr();
                let mutable = values.as_mut_ptr();
                (shared, mutable)
            }

            unsafe fn reassignment(
                p: *mut i32,
                other: *mut i32,
            ) -> (*mut i32, *mut i32) {
                let mut q = p;
                let before = q;
                q = other;
                let after = q;
                (before, after)
            }
            "#,
        );

        let expected = vec![
            (
                "binary_operand".to_string(),
                vec![(1, vec![1]), (2, vec![2]), (3, vec![3]), (4, vec![4])],
            ),
            (
                "borrowing_receivers".to_string(),
                vec![(1, vec![1]), (2, vec![2, 6]), (4, vec![4, 7])],
            ),
            (
                "copy_chain".to_string(),
                vec![(1, vec![1]), (2, vec![2]), (3, vec![3])],
            ),
            (
                "reassignment".to_string(),
                vec![
                    (1, vec![1]),
                    (2, vec![2, 5]),
                    (3, vec![3]),
                    (4, vec![4, 7]),
                    (6, vec![6, 8]),
                ],
            ),
        ];
        assert_eq!(actual, expected);
    }
}
