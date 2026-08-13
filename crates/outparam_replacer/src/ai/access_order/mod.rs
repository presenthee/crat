use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

/// Precomputed access-order effect of one recognized loop. Producer-side
/// contract (soundness-critical): every read or write through a function
/// parameter at any location in `blocks` is accounted for in `reads`,
/// `writes`, and `internal_pairs`. A summary may only be constructed when
/// this holds; the interpreter trusts it without re-checking.
#[derive(Debug, Clone)]
pub struct LoopSummary {
    /// Blocks belonging to the loop (header, body, latch).
    pub blocks: FxHashSet<BasicBlock>,
    /// 0-based parameter indices read through inside the loop.
    pub reads: FxHashSet<usize>,
    /// 0-based parameter indices written through inside the loop.
    pub writes: FxHashSet<usize>,
    /// `(reader, writer)` pairs for which the loop itself may perform a
    /// same-location read-after-write, assuming reader and writer alias the
    /// same base (matching `read_after_write` pair semantics).
    pub internal_pairs: FxHashSet<(usize, usize)>,
}

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
    /// Parameters that may be written through on some path, including paths that
    /// do not reach an exit. Argument indices are 0-based.
    pub may_write_params: FxHashSet<usize>,
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

    /// True when no listed parameter may be written through in the callee.
    pub fn params_never_written(&self, params: &[usize]) -> bool {
        !self.unanalyzable && !params.iter().any(|p| self.may_write_params.contains(p))
    }
}

/// Run the interpreter fresh with parameter access-order tracking enabled and
/// return a summary per local function.
pub fn analyze_access_order<'tcx>(
    tcx: TyCtxt<'tcx>,
    loop_summaries: &FxHashMap<LocalDefId, Vec<LoopSummary>>,
) -> FxHashMap<LocalDefId, AccessOrderSummary> {
    let config = crate::Config {
        track_access_order: true,
        max_loop_head_states: usize::MAX,
        ..Default::default()
    };
    crate::ai::analysis::analyze(&config, false, loop_summaries, tcx).2
}

#[cfg(test)]
mod tests;
