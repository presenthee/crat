use std::collections::{BTreeMap, BTreeSet};
use crate::pointer_identity::MeasurementError;
use super::*;

pub fn validate_inventory(inventory: &Inventory) -> Result<(), MeasurementError> {
    if inventory.schema_version != MEASUREMENT_SCHEMA_VERSION || inventory.counting_contract != COUNTING_CONTRACT || !inventory.structural_errors.is_empty() {
        return Err(MeasurementError::UnsupportedInventory("invalid inventory envelope or structural errors".into()));
    }
    let mut ids = BTreeSet::new();
    let mut locators = BTreeSet::new();
    for d in &inventory.declarations {
        if !ids.insert(d.declaration_id.clone()) { return Err(MeasurementError::DuplicateId(d.declaration_id.0.clone())); }
        if d.site != d.locator.site || !locators.insert(&d.locator) { return Err(MeasurementError::AmbiguousLocator(format!("{:?}",d.locator))); }
    }
    if inventory.observations.keys().cloned().collect::<BTreeSet<_>>() != ids { return Err(MeasurementError::MissingId("observation coverage".into())); }
    for o in inventory.observations.values() { validate_observation(o)?; }
    Ok(())
}

pub fn rekey_declarations(inventory: &mut Inventory, replacements: &BTreeMap<DeclId, DeclId>) -> Result<(), MeasurementError> {
    validate_inventory(inventory)?;
    if replacements.keys().collect::<BTreeSet<_>>() != inventory.observations.keys().collect() { return Err(MeasurementError::MissingId("rekey must cover all declarations".into())); }
    if replacements.values().collect::<BTreeSet<_>>().len() != replacements.len() { return Err(MeasurementError::DuplicateId("duplicate rekey destination".into())); }
    let observations = std::mem::take(&mut inventory.observations);
    inventory.observations = observations.into_iter().map(|(id,o)| (replacements[&id].clone(),o)).collect();
    for d in &mut inventory.declarations { d.declaration_id = replacements[&d.declaration_id].clone(); }
    Ok(())
}
