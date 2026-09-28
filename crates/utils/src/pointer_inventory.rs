//! Typed declaration inventory for pointer effectiveness measurements.
mod collect;
mod model;
mod source;
pub use collect::{
    TypeRoles, classify_type, classify_type_with_roles, collect_bound_inventory,
    collect_bound_inventory_with_roles, collect_inventory,
};
pub use model::*;
pub use source::{
    SourceSite, source_sites, source_sites_in_expr, source_sites_in_item, source_sites_in_stmt,
};
#[cfg(test)]
mod tests;
