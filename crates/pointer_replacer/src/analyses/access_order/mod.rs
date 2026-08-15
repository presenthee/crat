mod domain;
pub(crate) mod extractor;
mod loop_effect;
mod query;
pub(crate) mod solver;
mod summary;

pub use domain::*;
pub(crate) use loop_effect::AtomicLoopEffect;
#[allow(unused_imports)]
pub use query::{ActualAddress, CallSiteAccess, QueryError};
pub use summary::{AccessOrderAnalysis, FunctionAccessSummary};

#[cfg(test)]
mod tests;
