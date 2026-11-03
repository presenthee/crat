//! Structural recognition of simple counted MIR loops.

use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        BasicBlock, BasicBlockData, BinOp, Body, Local, Operand, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::TyCtxt,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoopId {
    pub function: LocalDefId,
    pub header: BasicBlock,
}

// `LocalDefId` intentionally has no rustc-provided ordering. Loop IDs only
// live within one compiler session, where its local index is sufficient.
impl Ord for LoopId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.function
            .local_def_index
            .cmp(&other.function.local_def_index)
            .then_with(|| self.header.cmp(&other.header))
    }
}

impl PartialOrd for LoopId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug)]
pub struct LoopRegion {
    pub blocks: FxHashSet<BasicBlock>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoopExit {
    pub from: BasicBlock,
    pub to: BasicBlock,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InductionModel {
    pub local: Local,
    pub init_block: BasicBlock,
}

#[derive(Clone, Debug)]
pub struct RecognizedLoop {
    pub id: LoopId,
    pub region: LoopRegion,
    #[allow(dead_code)]
    pub entry: BasicBlock,
    pub exits: Vec<LoopExit>,
    pub induction: InductionModel,
    pub ordered_blocks: Vec<BasicBlock>,
}

pub fn recognize_loops(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Vec<RecognizedLoop> {
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
    recognize_body(&body, def_id)
}

fn recognize_body(body: &Body<'_>, def_id: LocalDefId) -> Vec<RecognizedLoop> {
    let dominators = body.basic_blocks.dominators();
    let dominates = |dominator, node| dominators.dominates(dominator, node);
    let successors = Successors::new(body);

    // Cleanup targets are kept separate from normal CFG edges. In
    // particular, a call's unwind edge is not a normal exit from a loop.
    debug_assert!(
        successors
            .cleanup
            .iter()
            .flatten()
            .all(|&bb| body.basic_blocks[bb].is_cleanup)
    );

    let mut candidates = vec![];
    for (latch, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        for &header in &successors.normal[latch.index()] {
            if dominators.dominates(header, latch)
                && let Some(region) =
                    natural_region(header, latch, &successors.predecessors, &dominates)
            {
                candidates.push(Candidate {
                    header,
                    latch,
                    region,
                });
            }
        }
    }

    candidates
        .iter()
        .enumerate()
        .filter(|(index, candidate)| {
            // Overlapping natural regions are nested loops or alternate
            // latches for one loop. V1 recognizes neither loop in that case.
            !candidates.iter().enumerate().any(|(other_index, other)| {
                index != &other_index && !candidate.region.is_disjoint(&other.region)
            })
        })
        .filter_map(|(_, candidate)| {
            recognize_candidate(body, def_id, candidate, &successors, &dominates)
        })
        .collect()
}

struct Successors {
    normal: Vec<Vec<BasicBlock>>,
    cleanup: Vec<Vec<BasicBlock>>,
    predecessors: Vec<Vec<BasicBlock>>,
}

impl Successors {
    fn new(body: &Body<'_>) -> Self {
        let mut normal = vec![vec![]; body.basic_blocks.len()];
        let mut cleanup = vec![vec![]; body.basic_blocks.len()];
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for target in data.terminator().successors() {
                if body.basic_blocks[target].is_cleanup {
                    cleanup[bb.index()].push(target);
                } else {
                    normal[bb.index()].push(target);
                }
            }
        }

        let mut predecessors = vec![vec![]; body.basic_blocks.len()];
        for (from, targets) in normal.iter().enumerate() {
            let from = BasicBlock::from_usize(from);
            for &to in targets {
                predecessors[to.index()].push(from);
            }
        }

        Self {
            normal,
            cleanup,
            predecessors,
        }
    }
}

struct Candidate {
    header: BasicBlock,
    latch: BasicBlock,
    region: FxHashSet<BasicBlock>,
}

fn natural_region(
    header: BasicBlock,
    latch: BasicBlock,
    predecessors: &[Vec<BasicBlock>],
    dominates: &impl Fn(BasicBlock, BasicBlock) -> bool,
) -> Option<FxHashSet<BasicBlock>> {
    let mut region = FxHashSet::default();
    region.insert(header);
    let mut worklist = vec![latch];
    while let Some(bb) = worklist.pop() {
        if !dominates(header, bb) {
            return None;
        }
        if !region.insert(bb) {
            continue;
        }
        worklist.extend(
            predecessors[bb.index()]
                .iter()
                .copied()
                .filter(|&pred| dominates(header, pred)),
        );
    }
    Some(region)
}

fn recognize_candidate(
    body: &Body<'_>,
    def_id: LocalDefId,
    candidate: &Candidate,
    successors: &Successors,
    dominates: &impl Fn(BasicBlock, BasicBlock) -> bool,
) -> Option<RecognizedLoop> {
    let header = candidate.header;
    let header_data = &body.basic_blocks[header];
    let TerminatorKind::SwitchInt { discr, targets } = &header_data.terminator().kind else {
        return None;
    };
    let value_targets: Vec<_> = targets.iter().collect();
    let [(0, exit_target)] = value_targets[..] else {
        return None;
    };
    let entry = targets.otherwise();
    if entry == exit_target
        || !candidate.region.contains(&entry)
        || candidate.region.contains(&exit_target)
    {
        return None;
    }
    let induction = comparison_induction(header_data, discr)?;

    let mut outside_predecessors = FxHashSet::default();
    for (from, targets) in successors.normal.iter().enumerate() {
        let from = BasicBlock::from_usize(from);
        if candidate.region.contains(&from) {
            continue;
        }
        for &to in targets {
            if candidate.region.contains(&to) {
                if to != header {
                    return None;
                }
                outside_predecessors.insert(from);
            }
        }
    }
    if outside_predecessors.len() != 1 {
        return None;
    }

    let exits: Vec<_> = candidate
        .region
        .iter()
        .flat_map(|&from| {
            successors.normal[from.index()]
                .iter()
                .copied()
                .filter(move |to| !candidate.region.contains(to))
                .map(move |to| LoopExit { from, to })
        })
        .collect();
    let [exit] = exits[..] else {
        return None;
    };
    if exit.from != header || exit.to != exit_target {
        return None;
    }

    let ordered_blocks = ordered_block_chain(body, candidate, entry, successors)?;
    let induction = induction_model(body, induction, &candidate.region, header, dominates)?;

    Some(RecognizedLoop {
        id: LoopId {
            function: def_id,
            header,
        },
        region: LoopRegion {
            blocks: candidate.region.clone(),
        },
        entry,
        exits,
        induction,
        ordered_blocks,
    })
}

fn comparison_induction(data: &BasicBlockData<'_>, discr: &Operand<'_>) -> Option<Local> {
    let mut condition = discr.place()?.as_local()?;
    let mut before = data.statements.len();
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(condition) {
            return None;
        }
        let (statement_index, rvalue) = assignment_before(data, condition, before)?;
        match rvalue {
            Rvalue::Use(operand) => {
                condition = operand.place()?.as_local()?;
                before = statement_index;
            }
            Rvalue::BinaryOp(BinOp::Lt, operands) => {
                let lhs = operands.0.place()?.as_local()?;
                return Some(resolve_local_copy(data, lhs, statement_index));
            }
            _ => return None,
        }
    }
}

fn assignment_before<'a, 'tcx>(
    data: &'a BasicBlockData<'tcx>,
    local: Local,
    before: usize,
) -> Option<(usize, &'a Rvalue<'tcx>)> {
    data.statements[..before]
        .iter()
        .enumerate()
        .rev()
        .find_map(|(index, statement)| {
            let StatementKind::Assign(box (place, rvalue)) = &statement.kind else {
                return None;
            };
            (place.as_local() == Some(local)).then_some((index, rvalue))
        })
}

fn resolve_local_copy(data: &BasicBlockData<'_>, mut local: Local, mut before: usize) -> Local {
    let mut seen = FxHashSet::default();
    while seen.insert(local) {
        let Some((statement_index, Rvalue::Use(operand))) = assignment_before(data, local, before)
        else {
            break;
        };
        let Some(next) = operand.place().and_then(|place| place.as_local()) else {
            break;
        };
        local = next;
        before = statement_index;
    }
    local
}

fn ordered_block_chain(
    body: &Body<'_>,
    candidate: &Candidate,
    entry: BasicBlock,
    successors: &Successors,
) -> Option<Vec<BasicBlock>> {
    let mut ordered = vec![candidate.header];
    let mut seen: FxHashSet<_> = [candidate.header].into_iter().collect();
    let mut current = entry;
    loop {
        if !candidate.region.contains(&current) || !seen.insert(current) {
            return None;
        }
        ordered.push(current);
        let target = match &body.basic_blocks[current].terminator().kind {
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::Call {
                target: Some(target),
                ..
            } => *target,
            _ => return None,
        };
        if successors.normal[current.index()].as_slice() != [target] {
            return None;
        }
        if current == candidate.latch {
            if target != candidate.header {
                return None;
            }
            break;
        }
        current = target;
    }
    (seen == candidate.region).then_some(ordered)
}

#[derive(Clone, Copy)]
enum DefinitionSite {
    Statement(BasicBlock, usize),
    Call(BasicBlock),
}

impl DefinitionSite {
    fn block(self) -> BasicBlock {
        match self {
            Self::Statement(block, _) | Self::Call(block) => block,
        }
    }
}

fn induction_model(
    body: &Body<'_>,
    local: Local,
    region: &FxHashSet<BasicBlock>,
    header: BasicBlock,
    dominates: &impl Fn(BasicBlock, BasicBlock) -> bool,
) -> Option<InductionModel> {
    let sites = definition_sites(body, local);
    let (inside, outside): (Vec<_>, Vec<_>) = sites
        .into_iter()
        .partition(|site| region.contains(&site.block()));
    let [DefinitionSite::Statement(step_block, step_index)] = inside[..] else {
        return None;
    };
    if step_block == header
        || !is_unit_step(
            &body.basic_blocks[step_block].statements[step_index].kind,
            local,
        )
        || outside.is_empty()
        || outside.iter().any(|site| !dominates(site.block(), header))
    {
        return None;
    }

    let init_block =
        outside
            .into_iter()
            .map(DefinitionSite::block)
            .reduce(|current, candidate| {
                if dominates(current, candidate) {
                    candidate
                } else {
                    current
                }
            })?;
    Some(InductionModel { local, init_block })
}

fn definition_sites(body: &Body<'_>, local: Local) -> Vec<DefinitionSite> {
    let mut sites = vec![];
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, _)) = &statement.kind
                && place.as_local() == Some(local)
            {
                sites.push(DefinitionSite::Statement(bb, index));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && destination.as_local() == Some(local)
        {
            sites.push(DefinitionSite::Call(bb));
        }
    }
    sites
}

fn is_unit_step(kind: &StatementKind<'_>, local: Local) -> bool {
    let StatementKind::Assign(box (place, Rvalue::BinaryOp(BinOp::Add, operands))) = kind else {
        return false;
    };
    place.as_local() == Some(local)
        && operands.0.place().and_then(|place| place.as_local()) == Some(local)
        && is_const_one(&operands.1)
}

fn is_const_one(operand: &Operand<'_>) -> bool {
    let Operand::Constant(constant) = operand else {
        return false;
    };
    constant
        .const_
        .try_to_scalar()
        .and_then(|scalar| scalar.try_to_scalar_int().ok())
        .is_some_and(|integer| integer.to_bits_unchecked() == 1)
}

#[cfg(test)]
mod tests;
