//! Compiler inventory; emitted JSON is handled by the CLI, diagnostics by rustc.
use rustc_middle::ty::TyCtxt;
use utils::{
    pointer_identity::{MeasurementError, reconcile},
    pointer_inventory::{DeclarationMap, Inventory, SourceHashes, StageId, collect_inventory},
};

pub fn find_pointers(
    tcx: TyCtxt<'_>,
    map: Option<&DeclarationMap>,
    hashes: &SourceHashes,
) -> Result<Inventory, MeasurementError> {
    if let Some(map) = map {
        return reconcile(tcx, map, hashes);
    }
    let mut inventory = collect_inventory(tcx, "crate", StageId("input".into()));
    utils::pointer_inventory::validate_inventory(&inventory)?;
    inventory.source_hashes = hashes.clone();
    Ok(inventory)
}
