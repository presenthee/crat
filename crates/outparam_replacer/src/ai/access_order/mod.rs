use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

/// Per-callee ordering facts about its pointer parameters. Argument indices are
/// 0-based positions in the callee's parameter list.
#[derive(Debug, Default, Clone)]
pub struct AccessOrderSummary {
    /// The callee has an access the analysis could not attribute to a parameter,
    /// so no ordering claim about it can be trusted.
    pub unanalyzable: bool,
    /// `(reader, writer)` means a read through parameter `reader` may run after a
    /// write through parameter `writer`.
    pub read_after_write: FxHashSet<(usize, usize)>,
}

impl AccessOrderSummary {
    /// True when no read through any `imm` parameter may observe a write through
    /// any `mut_` parameter.
    pub fn reads_precede_writes(&self, mut_: &[usize], imm: &[usize]) -> bool {
        !self.unanalyzable
            && !imm.iter().any(|i| {
                mut_.iter()
                    .any(|m| self.read_after_write.contains(&(*i, *m)))
            })
    }
}

/// Run the interpreter fresh with parameter access-order tracking enabled and
/// return a summary per local function.
pub fn analyze_access_order(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, AccessOrderSummary> {
    let config = crate::Config {
        track_access_order: true,
        max_loop_head_states: usize::MAX,
        ..Default::default()
    };
    crate::ai::analysis::analyze(&config, false, tcx).2
}

#[cfg(test)]
mod tests;
