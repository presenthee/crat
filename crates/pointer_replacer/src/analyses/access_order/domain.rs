use std::hash::{Hash, Hasher};

use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Location;

use crate::analyses::{loop_recognizer::LoopId, pointer_flow::graph::BaseId};

pub type ParamIdx = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AccessKind {
    Read,
    Write,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub enum AccessOrigin {
    Parameter(SymbolicAddress),
    ProvenDisjoint(BaseId),
    MayAliasParameters,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OffsetExpr {
    Const(i64),
    LoopAffine {
        loop_id: LoopId,
        stride_bytes: i64,
        constant_bytes: i64,
    },
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolicAddress {
    pub origin: ParamIdx,
    pub offset: OffsetExpr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CallFrame {
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub location: Location,
}

/// Byte width of an access. `Linear` means `scale * param + offset` where
/// `param` is an integer parameter of the summarized function; the invariant
/// `scale >= 1` holds (a zero scale is normalized to `Const`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WidthExpr {
    Const(u64),
    Linear {
        param: ParamIdx,
        scale: u64,
        offset: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub struct AccessEvent {
    pub kind: AccessKind,
    pub origins: Vec<AccessOrigin>,
    pub width: Option<WidthExpr>,
    pub location: Location,
    pub call_chain: Vec<CallFrame>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AccessFootprint {
    pub address: SymbolicAddress,
    pub width: WidthExpr,
    pub location: Location,
    pub call_chain: Vec<CallFrame>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HazardOrder {
    Sequential,
    SameIteration(LoopId),
    LaterIteration(LoopId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PotentialHazard {
    pub write: AccessFootprint,
    pub read: AccessFootprint,
    pub order: HazardOrder,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamScope {
    Known(FxHashSet<ParamIdx>),
    All,
}

impl Hash for ParamScope {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Known(scope) => {
                0_u8.hash(state);
                let mut params: Vec<_> = scope.iter().copied().collect();
                params.sort_unstable();
                params.hash(state);
            }
            Self::All => 1_u8.hash(state),
        }
    }
}

impl ParamScope {
    pub fn intersects(&self, params: &[ParamIdx]) -> bool {
        match self {
            Self::Known(scope) => params.iter().any(|param| scope.contains(param)),
            Self::All => true,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AccessUnknownReason {
    UnresolvedOrigin,
    UnknownOffset,
    UnknownWidth,
    UnsupportedStatement,
    UnsupportedTerminator,
    UnsupportedCall,
    ForeignCall,
    IndirectCall,
    InlineAssembly,
    RecursiveCall,
    IncompleteCallee,
    #[allow(dead_code)]
    RejectedNestedRepetition,
    IncompatibleHazardOrder,
    SolverUnknown,
    UnresolvedSymbolicWidth,
    SummaryBudgetExceeded,
}

/// Upper bound on the number of footprints, hazards, and invalidations a
/// single effect or function summary may hold before the analysis degrades it
/// to one conservative all-parameter invalidation. Substituted callee
/// summaries multiply through call sites, so unbounded composition can exhaust
/// memory on large translated programs.
pub(crate) const ACCESS_SUMMARY_BUDGET: usize = 10_000;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Invalidation {
    pub scope: ParamScope,
    pub reason: AccessUnknownReason,
    pub location: Location,
    pub call_chain: Vec<CallFrame>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AccessEffect {
    pub reads: Vec<AccessFootprint>,
    pub writes: Vec<AccessFootprint>,
    pub hazards: Vec<PotentialHazard>,
    pub invalidations: Vec<Invalidation>,
    pub contains_repetition: bool,
}

impl AccessEffect {
    pub fn empty() -> Self {
        Self {
            reads: vec![],
            writes: vec![],
            hazards: vec![],
            invalidations: vec![],
            contains_repetition: false,
        }
    }

    #[allow(dead_code)]
    pub fn read(read: AccessFootprint) -> Self {
        Self {
            reads: vec![read],
            ..Self::empty()
        }
    }

    #[allow(dead_code)]
    pub fn write(write: AccessFootprint) -> Self {
        Self {
            writes: vec![write],
            ..Self::empty()
        }
    }

    pub fn normalize(&mut self) {
        deduplicate(&mut self.reads);
        deduplicate(&mut self.writes);
        deduplicate(&mut self.hazards);
        deduplicate(&mut self.invalidations);
    }

    pub(crate) fn element_count(&self) -> usize {
        self.reads.len() + self.writes.len() + self.hazards.len() + self.invalidations.len()
    }

    pub fn then(self, next: AccessEffect) -> AccessEffect {
        let mut hazards = self.hazards;
        hazards.extend(next.hazards);
        hazards.extend(self.writes.iter().flat_map(|write| {
            next.reads.iter().map(|read| PotentialHazard {
                write: write.clone(),
                read: read.clone(),
                order: HazardOrder::Sequential,
            })
        }));

        let mut effect = Self {
            reads: self.reads,
            writes: self.writes,
            hazards,
            invalidations: self.invalidations,
            contains_repetition: self.contains_repetition || next.contains_repetition,
        };
        effect.reads.extend(next.reads);
        effect.writes.extend(next.writes);
        effect.invalidations.extend(next.invalidations);
        effect.normalize();
        effect
    }
}

impl Default for AccessEffect {
    fn default() -> Self {
        Self::empty()
    }
}

fn deduplicate<T: Clone + Eq + Hash>(values: &mut Vec<T>) {
    let mut seen = FxHashSet::default();
    values.retain(|value| seen.insert(value.clone()));
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SubstitutedAddress {
    pub base: BaseId,
    pub offset: OffsetExpr,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HazardWitness {
    pub write_location: Location,
    pub read_location: Location,
    pub write_address: SubstitutedAddress,
    pub read_address: SubstitutedAddress,
    pub write_call_chain: Vec<CallFrame>,
    pub read_call_chain: Vec<CallFrame>,
    pub order: HazardOrder,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WriteWitness {
    pub location: Location,
    pub address: SubstitutedAddress,
    pub call_chain: Vec<CallFrame>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AccessOrderVerdict {
    Proven,
    MayReadAfterWrite { witness: HazardWitness },
    Unknown { reasons: Vec<AccessUnknownReason> },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum WriteVerdict {
    NeverWritten,
    MayBeWritten { witness: WriteWitness },
    Unknown { reasons: Vec<AccessUnknownReason> },
}
