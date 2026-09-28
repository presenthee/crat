//! Typed declaration inventory for pointer effectiveness measurements.
mod collect;
mod model;
pub use collect::{TypeRoles, classify_type, classify_type_with_roles, collect_inventory};
pub use model::*;
#[cfg(test)]
mod tests;
