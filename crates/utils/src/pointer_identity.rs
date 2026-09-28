//! Verified, stage-local declaration identities. A map describes exactly one source version.
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    path::{Component, Path, PathBuf},
};

use rustc_middle::ty::TyCtxt;
use sha2::{Digest, Sha256};

use crate::pointer_inventory::{self, *};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MeasurementError {
    HashMismatch(String),
    AmbiguousLocator(String),
    MissingId(String),
    DuplicateId(String),
    UnsupportedInventory(String),
    InvalidEvent(String),
    Io(String),
}
impl fmt::Display for MeasurementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for MeasurementError {}
impl From<std::io::Error> for MeasurementError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e.to_string())
    }
}

/// Shape is checked only within an emitted source version. Renames/type changes
/// require an explicitly updated output map; they are never guessed here.
pub fn declaration_shape(d: &Declaration) -> String {
    source_shape(d.site, &d.name)
}
pub fn source_shape(site: Site, name: &Option<String>) -> String {
    format!("{site:?}|{name:?}")
}
pub fn seed_map(inventory: &Inventory) -> DeclarationMap {
    DeclarationMap {
        schema_version: 1,
        case_id: inventory.case_id.clone(),
        profile: inventory.profile.clone(),
        stage: inventory.stage.clone(),
        source_hashes: inventory.source_hashes.clone(),
        entries: inventory
            .declarations
            .iter()
            .map(|d| MappedDeclaration {
                id: d.declaration_id.clone(),
                locator: d.locator.clone(),
                scope: d.scope,
                shape: declaration_shape(d),
            })
            .collect(),
    }
}

pub fn validate_map(map: &DeclarationMap) -> Result<(), MeasurementError> {
    if map.schema_version != 1 {
        return Err(MeasurementError::InvalidEvent(format!(
            "unsupported map schema {}",
            map.schema_version
        )));
    }
    let mut ids = BTreeSet::new();
    let mut locators = BTreeSet::new();
    for entry in &map.entries {
        if !ids.insert(&entry.id) {
            return Err(MeasurementError::DuplicateId(entry.id.0.clone()));
        }
        if !locators.insert(&entry.locator) {
            return Err(MeasurementError::AmbiguousLocator(format!(
                "{}: {:?}",
                map.stage.0, entry.locator
            )));
        }
    }
    Ok(())
}

pub fn hash_sources(root: &Path, paths: &[PathBuf]) -> Result<SourceHashes, MeasurementError> {
    let root = root.canonicalize()?;
    let mut hashes = SourceHashes::new();
    for path in paths {
        if path.as_os_str().is_empty()
            || path
                .components()
                .any(|c| !matches!(c, Component::Normal(_)))
        {
            return Err(MeasurementError::Io(format!(
                "source path must be relative and normalized: {}",
                path.display()
            )));
        }
        let key = path
            .to_str()
            .ok_or_else(|| MeasurementError::Io("non-UTF8 source path".into()))?
            .to_owned();
        if hashes.contains_key(&key) {
            return Err(MeasurementError::Io(format!(
                "duplicate source path: {key}"
            )));
        }
        let full = root.join(path).canonicalize()?;
        if !full.starts_with(&root) {
            return Err(MeasurementError::Io(format!(
                "source path escapes root: {key}"
            )));
        }
        hashes.insert(key, format!("{:x}", Sha256::digest(fs::read(full)?)));
    }
    Ok(hashes)
}

pub fn reconcile(
    tcx: TyCtxt<'_>,
    map: &DeclarationMap,
    actual_hashes: &SourceHashes,
) -> Result<Inventory, MeasurementError> {
    validate_map(map)?;
    if &map.source_hashes != actual_hashes {
        return Err(MeasurementError::HashMismatch(format!(
            "{} source hashes differ",
            map.stage.0
        )));
    }
    let mut ast = crate::ast::expanded_ast(tcx);
    let mapper = crate::ast::make_ast_to_hir(&mut ast, tcx);
    let roles = mapped_type_roles(&ast, &mapper, tcx, map);
    let (inventory, _) = pointer_inventory::collect_bound_inventory_with_roles(
        tcx,
        &ast,
        &mapper,
        &map.case_id,
        map.stage.clone(),
        &roles,
    );
    crate::type_check(tcx);
    reconcile_inventory(inventory, map)
}

/// A cursor role requires both an explicit support declaration map and the
/// compiler identity of its owning struct. User types with that name do not qualify.
pub fn mapped_type_roles(
    ast: &rustc_ast::Crate,
    mapper: &crate::ir::AstToHir,
    tcx: TyCtxt<'_>,
    map: &DeclarationMap,
) -> TypeRoles {
    let support: BTreeSet<_> = map
        .entries
        .iter()
        .filter(|e| e.scope == Scope::Support)
        .map(|e| &e.locator)
        .collect();
    let mut roles = TypeRoles::default();
    for site in source_sites(ast) {
        if site.locator.site != Site::Field || !support.contains(&site.locator) {
            continue;
        }
        let Some(field) = mapper.global_map.get(&site.node) else {
            continue;
        };
        let owner = tcx.parent(field.to_def_id());
        if tcx.def_kind(owner) != rustc_hir::def::DefKind::Struct {
            continue;
        }
        match tcx.item_name(owner).as_str() {
            "SliceCursor" => {
                roles.cursors.insert(owner, false);
            }
            "SliceCursorMut" => {
                roles.cursors.insert(owner, true);
            }
            _ => (),
        }
    }
    roles
}

pub fn reconcile_inventory(
    mut inventory: Inventory,
    map: &DeclarationMap,
) -> Result<Inventory, MeasurementError> {
    validate_map(map)?;
    if !inventory.issues.is_empty() {
        return Err(MeasurementError::UnsupportedInventory(format!(
            "{}: {:?}",
            map.stage.0, inventory.issues
        )));
    }
    let mut entries: BTreeMap<_, _> = map.entries.iter().map(|e| (&e.locator, e)).collect();
    for d in &mut inventory.declarations {
        let entry = entries.remove(&d.locator).ok_or_else(|| {
            MeasurementError::MissingId(format!("{}: {:?}", map.stage.0, d.locator))
        })?;
        if entry.shape != declaration_shape(d) {
            return Err(MeasurementError::AmbiguousLocator(format!(
                "{}: {:?}: expected {}, found {}",
                map.stage.0,
                d.locator,
                entry.shape,
                declaration_shape(d)
            )));
        }
        d.declaration_id = entry.id.clone();
        d.scope = entry.scope;
    }
    if let Some(entry) = entries.values().next() {
        return Err(MeasurementError::MissingId(format!(
            "{}: absent output {}",
            map.stage.0, entry.id.0
        )));
    }
    inventory.source_hashes = map.source_hashes.clone();
    inventory.profile = map.profile.clone();
    Ok(inventory)
}

#[cfg(test)]
mod tests;
