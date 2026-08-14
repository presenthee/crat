use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{Local, Location};

use crate::analyses::pointer_flow::slots::{SlotIdx, SlotTable};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PfgNode {
    Slot(SlotIdx),
    Base(BaseId),
    CallReturn(Location),
    CastResult(Location),
}

impl PfgNode {
    pub(crate) fn as_slot(&self) -> Option<SlotIdx> {
        if let PfgNode::Slot(slot) = self {
            Some(*slot)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BaseId {
    Param {
        local: Local,
        slot: SlotIdx,
    },
    LocalArray {
        local: Local,
    },
    LocalVec {
        local: Local,
    },
    LocalScalar {
        local: Local,
    },
    RawBorrow {
        target: Option<SlotIdx>,
        location: Location,
    },
    HeapAlloc {
        location: Location,
    },
    OpaqueReturn {
        location: Location,
    },
    IntToPtr {
        location: Location,
    },
    Unknown {
        location: Location,
        reason: UnknownReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UnknownReason {
    NullLike,
    ConstantPointer,
    UnsupportedProjection,
    UnsupportedMemoryLoad,
    UnsupportedCall,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Offset {
    Const(i64),
    Unknown,
}

impl Offset {
    pub fn compose(self, edge: Self) -> Self {
        match (self, edge) {
            (Self::Const(offset), Self::Const(edge_offset)) => offset
                .checked_add(edge_offset)
                .map_or(Self::Unknown, Self::Const),
            _ => Self::Unknown,
        }
    }

    pub fn join(self, other: Self) -> Self {
        if self == other { self } else { Self::Unknown }
    }

    pub fn as_const(self) -> Option<i64> {
        match self {
            Self::Const(offset) => Some(offset),
            Self::Unknown => None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct PointerFlowGraph {
    pub nodes: FxHashSet<PfgNode>,
    pub edges: FxHashMap<PfgNode, FxHashSet<(PfgNode, Offset)>>,
    pub bases: FxHashSet<BaseId>,
}

#[derive(Clone, Debug, Default)]
pub struct ProvenanceResult {
    pub reachable_bases: FxHashMap<PfgNode, FxHashSet<BaseId>>,
    pub base_offsets: FxHashMap<(PfgNode, BaseId), Offset>,
}

impl PointerFlowGraph {
    pub(crate) fn add_node(&mut self, node: PfgNode) {
        self.nodes.insert(node);
    }

    pub(crate) fn add_base(&mut self, base: BaseId) {
        self.bases.insert(base.clone());
        self.add_node(PfgNode::Base(base));
    }

    pub(crate) fn add_edge(&mut self, src: PfgNode, dst: PfgNode) {
        self.add_edge_with_offset(src, dst, Offset::Const(0));
    }

    pub(crate) fn add_edge_with_offset(&mut self, src: PfgNode, dst: PfgNode, offset: Offset) {
        self.nodes.insert(src.clone());
        self.nodes.insert(dst.clone());
        self.edges.entry(src).or_default().insert((dst, offset));
    }

    pub(crate) fn add_base_edge(&mut self, base: BaseId, dst: PfgNode) {
        self.add_base(base.clone());
        self.add_edge(PfgNode::Base(base), dst);
    }

    pub(crate) fn add_bidirectional_edge(&mut self, a: PfgNode, b: PfgNode) {
        self.add_edge(a.clone(), b.clone());
        self.add_edge(b, a);
    }
}

impl ProvenanceResult {
    pub fn offset_from_base(&self, node: &PfgNode, base: &BaseId) -> Option<Offset> {
        self.base_offsets
            .get(&(node.clone(), base.clone()))
            .copied()
    }

    pub fn unique_base(&self, node: &PfgNode) -> Option<BaseId> {
        let bases = self.reachable_bases.get(node)?;
        if bases.len() == 1 {
            bases.iter().next().cloned()
        } else {
            None
        }
    }

    /// Like `unique_base`, but treats `Unknown(NullLike)` entries as transparent.
    /// Used in `select_rewrite_groups` to include variables that are null-initialized
    /// before being assigned from a real base (e.g. `prev = null_mut(); prev = raw;`).
    pub fn unique_non_null_base(&self, node: &PfgNode) -> Option<BaseId> {
        let bases = self.reachable_bases.get(node)?;
        let mut iter = bases.iter().filter(|b| {
            !matches!(
                b,
                BaseId::Unknown {
                    reason: UnknownReason::NullLike,
                    ..
                }
            )
        });
        let unique = iter.next()?.clone();
        iter.next().is_none().then_some(unique)
    }

    pub fn unique_non_null_base_at_const_offset(&self, node: &PfgNode) -> Option<(BaseId, i64)> {
        let base = self.unique_non_null_base(node)?;
        let offset = self.offset_from_base(node, &base)?.as_const()?;
        Some((base, offset))
    }
}

/// Returns `(base_local, slot_offset_within_local)` for `DirectlyRewriteable` bases.
/// Returns `None` for `RawBorrow { target: None }` (no trackable local).
pub(crate) fn base_local_of_base(base: &BaseId, slot_table: &SlotTable) -> Option<(Local, usize)> {
    match base {
        BaseId::Param { local, slot } => {
            let offset = slot - slot_table.local_slots(*local).start;
            Some((*local, offset))
        }
        BaseId::LocalArray { local } | BaseId::LocalScalar { local } => Some((*local, 0)),
        BaseId::RawBorrow {
            target: Some(slot), ..
        } => {
            let root = slot_table.slot_infos[*slot].root;
            let offset = slot - slot_table.local_slots(root).start;
            Some((root, offset))
        }
        BaseId::RawBorrow { target: None, .. } => None,
        _ => None,
    }
}

pub(crate) fn solve_reachable_bases(graph: &PointerFlowGraph) -> ProvenanceResult {
    let mut base_offsets: FxHashMap<(PfgNode, BaseId), Offset> = FxHashMap::default();
    let mut worklist = VecDeque::new();

    for base in &graph.bases {
        let node = PfgNode::Base(base.clone());
        base_offsets.insert((node.clone(), base.clone()), Offset::Const(0));
        worklist.push_back((node, base.clone()));
    }

    while let Some((src, base)) = worklist.pop_front() {
        let Some(src_offset) = base_offsets.get(&(src.clone(), base.clone())).copied() else {
            continue;
        };
        let Some(dsts) = graph.edges.get(&src) else {
            continue;
        };
        for (dst, edge_offset) in dsts {
            let candidate = src_offset.compose(*edge_offset);
            let key = (dst.clone(), base.clone());
            match base_offsets.entry(key) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(candidate);
                    worklist.push_back((dst.clone(), base.clone()));
                }
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let joined = entry.get().join(candidate);
                    if *entry.get() != joined {
                        entry.insert(joined);
                        worklist.push_back((dst.clone(), base.clone()));
                    }
                }
            }
        }
    }

    let mut reachable_bases: FxHashMap<PfgNode, FxHashSet<BaseId>> = FxHashMap::default();
    for (node, base) in base_offsets.keys() {
        reachable_bases
            .entry(node.clone())
            .or_default()
            .insert(base.clone());
    }

    ProvenanceResult {
        reachable_bases,
        base_offsets,
    }
}

#[cfg(test)]
mod offset_tests {
    use rustc_middle::mir::Local;

    use super::{BaseId, Offset, PfgNode, PointerFlowGraph, solve_reachable_bases};

    fn local_scalar(local: usize) -> BaseId {
        BaseId::LocalScalar {
            local: Local::from_usize(local),
        }
    }

    #[test]
    fn offset_compose_adds_signed_constants() {
        assert_eq!(
            Offset::Const(-4).compose(Offset::Const(10)),
            Offset::Const(6)
        );
    }

    #[test]
    fn offset_compose_overflow_is_unknown() {
        assert_eq!(
            Offset::Const(i64::MAX).compose(Offset::Const(1)),
            Offset::Unknown
        );
    }

    #[test]
    fn offset_join_keeps_equal_and_widens_unequal() {
        assert_eq!(Offset::Const(4).join(Offset::Const(4)), Offset::Const(4));
        assert_eq!(Offset::Const(4).join(Offset::Const(8)), Offset::Unknown);
    }

    #[test]
    fn identity_edges_preserve_zero_offset() {
        let base = local_scalar(1);
        let dst = PfgNode::Slot(0);
        let mut graph = PointerFlowGraph::default();
        graph.add_base_edge(base.clone(), dst.clone());

        let result = solve_reachable_bases(&graph);
        let reachable_bases = result
            .reachable_bases
            .get(&dst)
            .cloned()
            .unwrap_or_default();

        assert!(reachable_bases.contains(&base));
        assert_eq!(result.offset_from_base(&dst, &base), Some(Offset::Const(0)));
        assert_eq!(
            result.unique_non_null_base_at_const_offset(&dst),
            Some((base, 0))
        );
    }

    #[test]
    fn unequal_path_offsets_join_to_unknown_without_losing_base() {
        let base = local_scalar(1);
        let src = PfgNode::Base(base.clone());
        let dst = PfgNode::Slot(0);
        let mut graph = PointerFlowGraph::default();
        graph.add_base(base.clone());
        graph.add_edge_with_offset(src.clone(), dst.clone(), Offset::Const(4));
        graph.add_edge_with_offset(src, dst.clone(), Offset::Const(8));

        let result = solve_reachable_bases(&graph);
        let reachable_bases = result
            .reachable_bases
            .get(&dst)
            .cloned()
            .unwrap_or_default();
        let base_offsets = result.base_offsets.clone();

        assert!(reachable_bases.contains(&base));
        assert_eq!(
            base_offsets.get(&(dst.clone(), base.clone())),
            Some(&Offset::Unknown)
        );
        assert_eq!(result.offset_from_base(&dst, &base), Some(Offset::Unknown));
    }

    #[test]
    fn cursor_cycle_converges_to_unknown() {
        let base = local_scalar(1);
        let src = PfgNode::Base(base.clone());
        let cursor = PfgNode::Slot(0);
        let mut graph = PointerFlowGraph::default();
        graph.add_base(base.clone());
        graph.add_edge(src, cursor.clone());
        graph.add_edge_with_offset(cursor.clone(), cursor.clone(), Offset::Const(1));

        let result = solve_reachable_bases(&graph);
        let reachable_bases = result
            .reachable_bases
            .get(&cursor)
            .cloned()
            .unwrap_or_default();
        let base_offsets = result.base_offsets.clone();

        assert!(reachable_bases.contains(&base));
        assert_eq!(
            base_offsets.get(&(cursor.clone(), base.clone())),
            Some(&Offset::Unknown)
        );
        assert_eq!(
            result.offset_from_base(&cursor, &base),
            Some(Offset::Unknown)
        );
    }
}
