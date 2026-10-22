//! Typed declaration inventory for pointer effectiveness measurements.
mod collect;
mod model;
mod observation;
mod source;
pub use collect::{TypeRoles, collect_bound_inventory, collect_bound_inventory_with_roles, collect_inventory};
mod uses;
pub use uses::{UseCounts, count_uses};
mod validation;
pub use validation::{validate_inventory, rekey_declarations};
pub use model::*;
pub use observation::{endpoint_state, observe_type, validate_observation};
pub use source::{
    SourceSite, source_sites, source_sites_in_expr, source_sites_in_item, source_sites_in_stmt,
};
#[cfg(test)]
mod tests;
