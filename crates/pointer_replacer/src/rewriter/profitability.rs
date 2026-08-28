#[cfg(test)]
mod tests {
    use super::*;

    fn m(raw: usize, unsafe_ops: usize, deref: usize) -> CandidateMeasurement {
        CandidateMeasurement {
            baseline: ProfitabilityMetrics {
                raw_materializations: 10,
                unsafe_operations: 10,
                dereferences: 10,
            },
            trial: ProfitabilityMetrics {
                raw_materializations: 10 - raw,
                unsafe_operations: 10 - unsafe_ops,
                dereferences: 10 - deref,
            },
            unknown_promotions: 0,
        }
    }

    #[test]
    fn raw_is_deciding_metric() {
        assert!(matches!(
            decide(m(1, 0, 0)),
            ProfitabilityDecision::Accept {
                deciding_metric: ProfitabilityMetric::RawMaterializations,
                ..
            }
        ));
    }
    #[test]
    fn raw_decrease_wins_over_unsafe_increase() {
        let mut measurement = m(1, 0, 0);
        measurement.trial.unsafe_operations += 4;
        assert!(matches!(
            decide(measurement),
            ProfitabilityDecision::Accept {
                deciding_metric: ProfitabilityMetric::RawMaterializations,
                ..
            }
        ));
    }
    #[test]
    fn unsafe_is_deciding_metric_after_raw_tie() {
        assert!(matches!(
            decide(m(0, 1, 0)),
            ProfitabilityDecision::Accept {
                deciding_metric: ProfitabilityMetric::UnsafeOperations,
                ..
            }
        ));
    }
    #[test]
    fn unsafe_decrease_wins_over_dereference_increase() {
        let mut measurement = m(0, 1, 0);
        measurement.trial.dereferences += 4;
        assert!(matches!(
            decide(measurement),
            ProfitabilityDecision::Accept {
                deciding_metric: ProfitabilityMetric::UnsafeOperations,
                ..
            }
        ));
    }
    #[test]
    fn dereference_is_deciding_metric_after_prior_ties() {
        assert!(matches!(
            decide(m(0, 0, 1)),
            ProfitabilityDecision::Accept {
                deciding_metric: ProfitabilityMetric::Dereferences,
                ..
            }
        ));
    }
    #[test]
    fn increases_at_each_metric_are_rejected() {
        for (raw, unsafe_ops, deref, reason) in [
            (
                1usize,
                0usize,
                0usize,
                RejectionReason::MoreRawMaterializations,
            ),
            (0, 1, 0, RejectionReason::MoreUnsafeOperations),
            (0, 0, 1, RejectionReason::MoreDereferences),
        ] {
            let mut measurement = m(0, 0, 0);
            measurement.trial.raw_materializations += raw * 2;
            measurement.trial.unsafe_operations += unsafe_ops * 2;
            measurement.trial.dereferences += deref * 2;
            assert!(
                matches!(decide(measurement), ProfitabilityDecision::Reject { reason: r, .. } if r == reason)
            );
        }
    }

    #[test]
    fn metric_deltas_are_signed() {
        let deltas = metric_deltas(
            ProfitabilityMetrics {
                raw_materializations: 0,
                unsafe_operations: 2,
                dereferences: 4,
            },
            ProfitabilityMetrics {
                raw_materializations: 1,
                unsafe_operations: 1,
                dereferences: 3,
            },
        );
        assert_eq!(deltas.raw_materializations, 1);
        assert_eq!(deltas.unsafe_operations, -1);
        assert_eq!(deltas.dereferences, -1);
    }
    #[test]
    fn neutral_and_unknown_are_rejected() {
        assert!(matches!(
            decide(m(0, 0, 0)),
            ProfitabilityDecision::Reject {
                reason: RejectionReason::Neutral,
                ..
            }
        ));
        let mut measurement = m(1, 1, 1);
        measurement.unknown_promotions = 1;
        assert!(matches!(
            decide(measurement),
            ProfitabilityDecision::Reject {
                reason: RejectionReason::UnknownAttribution,
                ..
            }
        ));
    }

    #[test]
    fn source_keys_distinguish_shadowed_bindings() {
        assert_ne!(SourceBindingKey::new("p", 0), SourceBindingKey::new("p", 1));
    }

    #[test]
    fn array_members_are_canonicalized_in_order() {
        let id = CandidateId::array_local(
            DefPathHash::default(),
            SourceBindingKey::new("base", 0),
            vec![SourceBindingKey::new("z", 1), SourceBindingKey::new("a", 0)],
        );
        assert_eq!(
            id.members(),
            Some(&[SourceBindingKey::new("a", 0), SourceBindingKey::new("z", 1)][..])
        );
    }

    #[test]
    fn duplicate_array_members_remain_observable() {
        let id = CandidateId::array_local(
            DefPathHash::default(),
            SourceBindingKey::new("base", 0),
            vec![
                SourceBindingKey::new("member", 0),
                SourceBindingKey::new("member", 0),
            ],
        );
        assert!(id.has_duplicate_members());
        assert_eq!(id.members().unwrap().len(), 2);
    }

    #[test]
    fn duplicate_lineage_is_ambiguous_and_not_returned_as_unique() {
        let mut catalog = LineageCatalog::default();
        let function = DefPathHash::default();
        let parent = CandidateId::epoch(function, SourceBindingKey::new("scratch", 0));
        catalog.insert(function, "scratch__epoch_0", parent.clone(), 0);
        catalog.insert(function, "scratch__epoch_0", parent, 1);
        assert!(catalog.lookup(function, "scratch__epoch_0").is_none());
        assert_eq!(
            catalog
                .lookup_all(function, "scratch__epoch_0")
                .unwrap()
                .len(),
            2
        );
    }
}
use std::collections::HashMap;

use rustc_span::def_id::DefPathHash;

use super::decision::PtrKind;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ProfitabilityMetrics {
    pub raw_materializations: usize,
    pub unsafe_operations: usize,
    pub dereferences: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ProfitabilityMetricDeltas {
    pub raw_materializations: i128,
    pub unsafe_operations: i128,
    pub dereferences: i128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ProfitabilityMetric {
    RawMaterializations,
    UnsafeOperations,
    Dereferences,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct CandidateMeasurement {
    pub baseline: ProfitabilityMetrics,
    pub trial: ProfitabilityMetrics,
    pub unknown_promotions: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CandidateId {
    Epoch {
        function: DefPathHash,
        binding: SourceBindingKey,
    },
    ArrayLocal {
        function: DefPathHash,
        base: SourceBindingKey,
        members: Vec<SourceBindingKey>,
    },
}

impl CandidateId {
    pub fn epoch(function: DefPathHash, binding: SourceBindingKey) -> Self {
        Self::Epoch { function, binding }
    }

    pub fn array_local(
        function: DefPathHash,
        base: SourceBindingKey,
        mut members: Vec<SourceBindingKey>,
    ) -> Self {
        members.sort();
        Self::ArrayLocal {
            function,
            base,
            members,
        }
    }

    pub fn members(&self) -> Option<&[SourceBindingKey]> {
        match self {
            Self::ArrayLocal { members, .. } => Some(members),
            Self::Epoch { .. } => None,
        }
    }

    /// Duplicate members indicate ambiguous attribution and must fail closed.
    pub fn has_duplicate_members(&self) -> bool {
        self.members()
            .is_some_and(|members| members.windows(2).any(|pair| pair[0] == pair[1]))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SourceBindingKey {
    pub name: String,
    pub occurrence: usize,
}

impl SourceBindingKey {
    pub fn new(name: impl Into<String>, occurrence: usize) -> Self {
        Self {
            name: name.into(),
            occurrence,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ArtifactId {
    pub candidate: CandidateId,
    pub ordinal: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ArtifactFootprint {
    pub id: ArtifactId,
    /// Stable source identity retained across trial compiler sessions.
    pub source_name: Option<String>,
    /// Display-form source span; compiler spans themselves must not escape a session.
    pub source_span: Option<String>,
    pub ownership: ArtifactOwnership,
    pub fate: ArtifactFate,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ArtifactOwnership {
    Baseline,
    Trial,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ArtifactFate {
    Eliminated,
    RemainsRaw,
    Promoted(PtrKind),
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProfitabilityDecision {
    Accept {
        measurement: CandidateMeasurement,
        deciding_metric: ProfitabilityMetric,
    },
    Reject {
        measurement: CandidateMeasurement,
        reason: RejectionReason,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum RejectionReason {
    MoreRawMaterializations,
    MoreUnsafeOperations,
    MoreDereferences,
    Neutral,
    UnknownAttribution,
}

pub fn metric_deltas(
    baseline: ProfitabilityMetrics,
    trial: ProfitabilityMetrics,
) -> ProfitabilityMetricDeltas {
    fn delta(trial: usize, baseline: usize) -> i128 {
        let trial = i128::try_from(trial).expect("usize must fit in i128");
        let baseline = i128::try_from(baseline).expect("usize must fit in i128");
        trial - baseline
    }
    ProfitabilityMetricDeltas {
        raw_materializations: delta(trial.raw_materializations, baseline.raw_materializations),
        unsafe_operations: delta(trial.unsafe_operations, baseline.unsafe_operations),
        dereferences: delta(trial.dereferences, baseline.dereferences),
    }
}

pub fn decide(measurement: CandidateMeasurement) -> ProfitabilityDecision {
    if measurement.unknown_promotions != 0 {
        return ProfitabilityDecision::Reject {
            measurement,
            reason: RejectionReason::UnknownAttribution,
        };
    }
    let deltas = metric_deltas(measurement.baseline.clone(), measurement.trial.clone());
    if deltas.raw_materializations != 0 {
        return result(
            measurement,
            deltas.raw_materializations < 0,
            ProfitabilityMetric::RawMaterializations,
            RejectionReason::MoreRawMaterializations,
        );
    }
    if deltas.unsafe_operations != 0 {
        return result(
            measurement,
            deltas.unsafe_operations < 0,
            ProfitabilityMetric::UnsafeOperations,
            RejectionReason::MoreUnsafeOperations,
        );
    }
    if deltas.dereferences != 0 {
        return result(
            measurement,
            deltas.dereferences < 0,
            ProfitabilityMetric::Dereferences,
            RejectionReason::MoreDereferences,
        );
    }
    ProfitabilityDecision::Reject {
        measurement,
        reason: RejectionReason::Neutral,
    }
}

fn result(
    measurement: CandidateMeasurement,
    accepted: bool,
    metric: ProfitabilityMetric,
    reason: RejectionReason,
) -> ProfitabilityDecision {
    if accepted {
        ProfitabilityDecision::Accept {
            measurement,
            deciding_metric: metric,
        }
    } else {
        ProfitabilityDecision::Reject {
            measurement,
            reason,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct LineageCatalog {
    entries: HashMap<(DefPathHash, String), Vec<(CandidateId, usize)>>,
    unknown: std::collections::HashSet<(DefPathHash, String)>,
}

impl LineageCatalog {
    pub fn insert(
        &mut self,
        function: DefPathHash,
        generated_binding: impl Into<String>,
        parent: CandidateId,
        epoch_ordinal: usize,
    ) {
        self.entries
            .entry((function, generated_binding.into()))
            .or_default()
            .push((parent, epoch_ordinal));
    }

    pub fn lookup(
        &self,
        function: DefPathHash,
        generated_binding: &str,
    ) -> Option<(&CandidateId, usize)> {
        let entries = self
            .entries
            .get(&(function, generated_binding.to_owned()))?;
        (entries.len() == 1).then(|| (&entries[0].0, entries[0].1))
    }

    /// Returns all entries, including duplicates, for conservative callers.
    pub fn lookup_all(
        &self,
        function: DefPathHash,
        generated_binding: &str,
    ) -> Option<&[(CandidateId, usize)]> {
        self.entries
            .get(&(function, generated_binding.to_owned()))
            .map(Vec::as_slice)
    }

    /// Marks a generated binding whose parent could not be attributed.
    pub fn mark_unknown(&mut self, function: DefPathHash, generated_binding: impl Into<String>) {
        self.unknown.insert((function, generated_binding.into()));
    }

    pub fn is_unknown(&self, function: DefPathHash, generated_binding: &str) -> bool {
        self.unknown
            .contains(&(function, generated_binding.to_owned()))
    }
}
