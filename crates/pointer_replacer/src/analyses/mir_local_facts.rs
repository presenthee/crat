//! Policy-free facts about whole-local MIR definitions.

use rustc_index::IndexVec;
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind,
    visit::{MutatingUseContext, PlaceContext, Visitor},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MirCopyEdge {
    pub destination: Local,
    pub source: Local,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MirLocalDefinitionKind {
    Copy(Local),
    Value,
    Unsupported,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MirLocalDefinition {
    pub location: Location,
    pub kind: MirLocalDefinitionKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MirLocalFacts {
    pub definitions: IndexVec<Local, Vec<MirLocalDefinition>>,
}

pub(crate) fn copy_edge_from_assignment(
    destination: &Place<'_>,
    rvalue: &Rvalue<'_>,
    location: Location,
) -> Option<MirCopyEdge> {
    let destination = destination.as_local()?;
    let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = rvalue else {
        return None;
    };
    Some(MirCopyEdge {
        destination,
        source: source.as_local()?,
        location,
    })
}

pub(crate) fn collect_mir_local_facts(body: &Body<'_>) -> MirLocalFacts {
    struct DefinitionCollector {
        locations: IndexVec<Local, Vec<Location>>,
    }

    impl<'tcx> Visitor<'tcx> for DefinitionCollector {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            if matches!(
                context,
                PlaceContext::MutatingUse(
                    MutatingUseContext::Call
                        | MutatingUseContext::Yield
                        | MutatingUseContext::AsmOutput
                        | MutatingUseContext::Store
                        | MutatingUseContext::Deinit
                )
            ) && let Some(local) = place.as_local()
            {
                self.locations[local].push(location);
            }
            self.super_place(place, context, location);
        }
    }

    let mut collector = DefinitionCollector {
        locations: IndexVec::from_elem_n(Vec::new(), body.local_decls.len()),
    };
    collector.visit_body(body);

    let mut definitions = IndexVec::from_elem_n(Vec::new(), body.local_decls.len());
    for (local, locations) in collector.locations.iter_enumerated() {
        for &location in locations {
            let block = &body.basic_blocks[location.block];
            let kind = if let Some(statement) = block.statements.get(location.statement_index) {
                match &statement.kind {
                    StatementKind::Assign(box (destination, rvalue))
                        if destination.as_local() == Some(local) =>
                    {
                        copy_edge_from_assignment(destination, rvalue, location)
                            .map_or(MirLocalDefinitionKind::Value, |edge| {
                                MirLocalDefinitionKind::Copy(edge.source)
                            })
                    }
                    _ => MirLocalDefinitionKind::Unsupported,
                }
            } else if location.statement_index == block.statements.len() {
                match &block.terminator().kind {
                    TerminatorKind::Call { destination, .. }
                        if destination.as_local() == Some(local) =>
                    {
                        MirLocalDefinitionKind::Value
                    }
                    _ => MirLocalDefinitionKind::Unsupported,
                }
            } else {
                MirLocalDefinitionKind::Unsupported
            };
            definitions[local].push(MirLocalDefinition { location, kind });
        }
        definitions[local].sort_by_key(|definition| {
            (
                definition.location.block.index(),
                definition.location.statement_index,
            )
        });
        definitions[local].dedup();
    }

    MirLocalFacts { definitions }
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::{Body, Local, VarDebugInfoContents};

    use super::{MirLocalDefinitionKind, collect_mir_local_facts};
    use crate::rewriter::collect_input;

    fn local_named(body: &Body<'_>, name: &str) -> Local {
        body.var_debug_info
            .iter()
            .find_map(|info| {
                let VarDebugInfoContents::Place(place) = &info.value else {
                    return None;
                };
                (info.name.as_str() == name)
                    .then(|| place.as_local())
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing MIR local named {name}"))
    }

    #[test]
    fn facts_record_copy_and_call_destinations() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            unsafe fn consume(_: *mut i32) {}

            unsafe fn f(p: *mut i32) {
                let q: *mut i32 = p;
                unsafe { consume(q.offset(1)) };
            }
            "#,
            |tcx| {
                let program = collect_input(tcx);
                let function = program
                    .functions
                    .iter()
                    .copied()
                    .find(|&function| tcx.item_name(function.to_def_id()).as_str() == "f")
                    .expect("missing function f");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let p = local_named(&body, "p");
                let q = local_named(&body, "q");
                let facts = collect_mir_local_facts(&body);

                assert!(facts.definitions[q].iter().any(|definition| {
                    matches!(
                        definition.kind,
                        MirLocalDefinitionKind::Copy(source) if source == p
                    )
                }));

                assert!(facts.definitions.iter().flatten().any(|definition| {
                    let block = &body.basic_blocks[definition.location.block];
                    definition.location.statement_index == block.statements.len()
                        && matches!(definition.kind, MirLocalDefinitionKind::Value)
                }));
            },
        )
        .unwrap();
    }
}
