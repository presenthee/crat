use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{Body, Location, START_BLOCK};

use super::{
    AccessEffect, AccessFootprint, AccessUnknownReason, AtomicLoopEffect, FunctionAccessSummary,
    HazardOrder, Invalidation, ParamScope, PotentialHazard, extractor::LocationEffect,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct AccessState {
    prior_writes: FxHashSet<AccessFootprint>,
    hazards: FxHashSet<PotentialHazard>,
    invalidations: FxHashSet<Invalidation>,
}

pub(crate) fn solve_body(
    body: &Body<'_>,
    effects: &FxHashMap<Location, LocationEffect>,
    atomic_loops: &[AtomicLoopEffect],
) -> FunctionAccessSummary {
    let atomic_loops: FxHashMap<_, _> = atomic_loops
        .iter()
        .map(|atomic| (atomic.recognized.id.header, atomic))
        .collect();

    let mut entries = FxHashMap::default();
    entries.insert(START_BLOCK, AccessState::default());
    let mut worklist = VecDeque::from([START_BLOCK]);
    let mut reads = FxHashSet::default();
    let mut writes = FxHashSet::default();
    let mut hazards = FxHashSet::default();
    let mut invalidations = FxHashSet::default();
    let mut contains_repetition = reachable_cfg_has_cycle(body);

    while let Some(block) = worklist.pop_front() {
        let mut state = entries[&block].clone();
        if let Some(atomic) = atomic_loops.get(&block) {
            apply_effect(
                &mut state,
                &atomic.effect,
                &mut reads,
                &mut writes,
                &mut hazards,
                &mut invalidations,
            );
            contains_repetition = true;
            let [exit] = atomic.recognized.exits[..] else {
                unreachable!("certified loops have one normal exit");
            };
            enqueue_state(exit.to, &state, &mut entries, &mut worklist);
            continue;
        }
        let block_data = &body.basic_blocks[block];
        for statement_index in 0..=block_data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            let Some(location_effect) = effects.get(&location) else {
                continue;
            };
            match location_effect {
                LocationEffect::Effect(effect) => {
                    apply_effect(
                        &mut state,
                        effect,
                        &mut reads,
                        &mut writes,
                        &mut hazards,
                        &mut invalidations,
                    );
                    contains_repetition |= effect.contains_repetition;
                }
                LocationEffect::Call(_) => {
                    let invalidation = Invalidation {
                        scope: ParamScope::All,
                        reason: AccessUnknownReason::UnsupportedCall,
                        location,
                        call_chain: vec![],
                    };
                    state.invalidations.insert(invalidation.clone());
                    invalidations.insert(invalidation);
                }
            }
        }

        for successor in block_data.terminator().successors() {
            enqueue_state(successor, &state, &mut entries, &mut worklist);
        }
    }

    let mut effect = AccessEffect {
        reads: reads.into_iter().collect(),
        writes: writes.into_iter().collect(),
        hazards: hazards.into_iter().collect(),
        invalidations: invalidations.into_iter().collect(),
        contains_repetition,
    };
    effect.normalize();
    FunctionAccessSummary { effect }
}

fn reachable_cfg_has_cycle(body: &Body<'_>) -> bool {
    let successors = body
        .basic_blocks
        .iter()
        .map(|block| {
            block
                .terminator()
                .successors()
                .map(|successor| successor.index())
                .collect()
        })
        .collect::<Vec<Vec<_>>>();

    reachable_graph_has_cycle(&successors, START_BLOCK.index())
}

pub(crate) fn reachable_graph_has_cycle(successors: &[Vec<usize>], start: usize) -> bool {
    const UNVISITED: u8 = 0;
    const ACTIVE: u8 = 1;
    const FINISHED: u8 = 2;

    let mut colors = vec![UNVISITED; successors.len()];
    colors[start] = ACTIVE;
    let mut stack = vec![(start, 0)];

    while let Some((node, next_edge)) = stack.last_mut() {
        if let Some(&successor) = successors[*node].get(*next_edge) {
            *next_edge += 1;
            match colors[successor] {
                UNVISITED => {
                    colors[successor] = ACTIVE;
                    stack.push((successor, 0));
                }
                ACTIVE => return true,
                FINISHED => {}
                _ => unreachable!(),
            }
        } else {
            colors[*node] = FINISHED;
            stack.pop();
        }
    }

    false
}

fn enqueue_state(
    block: rustc_middle::mir::BasicBlock,
    state: &AccessState,
    entries: &mut FxHashMap<rustc_middle::mir::BasicBlock, AccessState>,
    worklist: &mut VecDeque<rustc_middle::mir::BasicBlock>,
) {
    match entries.entry(block) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(state.clone());
            worklist.push_back(block);
        }
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            if join_state(entry.get_mut(), state) {
                worklist.push_back(block);
            }
        }
    }
}

fn apply_effect(
    state: &mut AccessState,
    effect: &AccessEffect,
    summary_reads: &mut FxHashSet<AccessFootprint>,
    summary_writes: &mut FxHashSet<AccessFootprint>,
    summary_hazards: &mut FxHashSet<PotentialHazard>,
    summary_invalidations: &mut FxHashSet<Invalidation>,
) {
    summary_reads.extend(effect.reads.iter().cloned());
    summary_writes.extend(effect.writes.iter().cloned());
    state.hazards.extend(effect.hazards.iter().cloned());
    state
        .hazards
        .extend(state.prior_writes.iter().flat_map(|write| {
            effect.reads.iter().map(|read| PotentialHazard {
                write: write.clone(),
                read: read.clone(),
                order: HazardOrder::Sequential,
            })
        }));
    state.prior_writes.extend(effect.writes.iter().cloned());
    state
        .invalidations
        .extend(effect.invalidations.iter().cloned());

    summary_hazards.extend(state.hazards.iter().cloned());
    summary_invalidations.extend(state.invalidations.iter().cloned());
}

fn join_state(target: &mut AccessState, incoming: &AccessState) -> bool {
    let old_sizes = (
        target.prior_writes.len(),
        target.hazards.len(),
        target.invalidations.len(),
    );
    target
        .prior_writes
        .extend(incoming.prior_writes.iter().cloned());
    target.hazards.extend(incoming.hazards.iter().cloned());
    target
        .invalidations
        .extend(incoming.invalidations.iter().cloned());
    old_sizes
        != (
            target.prior_writes.len(),
            target.hazards.len(),
            target.invalidations.len(),
        )
}
