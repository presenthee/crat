//! Typed declaration inventory for pointer effectiveness measurements.
mod collect;
mod model;
mod source;
pub use collect::{
    TypeRoles, classify_type, classify_type_with_roles, collect_bound_inventory, collect_inventory,
};
pub use model::*;
pub use source::{SourceSite, source_sites};
#[cfg(test)]
mod tests;
