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
        schema_version: MEASUREMENT_SCHEMA_VERSION,
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
    if map.schema_version != MEASUREMENT_SCHEMA_VERSION {
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
    validate_inventory(&inventory)?;
    let mut replacements = BTreeMap::new();
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
        replacements.insert(d.declaration_id.clone(), entry.id.clone());
        d.scope = entry.scope;
    }
    if let Some(entry) = entries.values().next() {
        return Err(MeasurementError::MissingId(format!(
            "{}: absent output {}",
            map.stage.0, entry.id.0
        )));
    }
    rekey_declarations(&mut inventory, &replacements)?;
    inventory.source_hashes = map.source_hashes.clone();
    inventory.profile = map.profile.clone();
    Ok(inventory)
}

#[cfg(test)]
mod tests;

/// Exact compiler inputs for a crate snapshot, excluding configuration overlays,
/// build caches and measurement output. Never follow an escaping symlink.
pub fn crate_source_paths(root: &Path) -> Result<Vec<PathBuf>, MeasurementError> {
    fn walk(root: &Path, dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), MeasurementError> {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if matches!(
                name.as_ref(),
                "aws-translate"
                    | "bundles"
                    | "target"
                    | ".git"
                    | ".superpowers"
            ) {
                continue;
            }
            let path = entry.path();
            let canonical = path.canonicalize()?;
            if !canonical.starts_with(root)
                || canonical
                    .components()
                    .any(|c| matches!(c.as_os_str().to_str(), Some("aws-translate" | "bundles")))
            {
                return Err(MeasurementError::Io(format!(
                    "source escapes crate: {}",
                    path.display()
                )));
            }
            if path.is_dir() {
                if entry.file_type()?.is_symlink() {
                    return Err(MeasurementError::Io(
                        "symlinked source directory is unsupported".into(),
                    ));
                }
                walk(root, &path, files)?;
            } else if path.extension().is_some_and(|ext| ext == "rs")
                || matches!(
                    name.as_ref(),
                    "Cargo.toml" | "Cargo.lock" | "rust-toolchain" | "rust-toolchain.toml"
                )
                || path.strip_prefix(root).ok() == Some(Path::new(".cargo/config.toml"))
            {
                files.push(path.strip_prefix(root).unwrap().to_owned());
            }
        }
        Ok(())
    }
    if root
        .components()
        .any(|c| matches!(c.as_os_str().to_str(), Some("aws-translate" | "bundles")))
    {
        return Err(MeasurementError::Io("prohibited input tree".into()));
    }
    let root = root.canonicalize()?;
    let mut files = Vec::new();
    walk(&root, &root, &mut files)?;
    files.sort();
    Ok(files)
}

pub fn crate_hashes(root: &Path) -> Result<SourceHashes, MeasurementError> {
    hash_sources(root, &crate_source_paths(root)?)
}

pub fn relative_locations(inventory: &mut Inventory, root: &Path) -> Result<(), MeasurementError> {
    let root = root.canonicalize()?;
    for declaration in &mut inventory.declarations {
        let file = Path::new(&declaration.location.file);
        // Declarations spanning outside the crate (macro-expanded std code) keep
        // their absolute path so the counting scripts can filter them.
        if let Ok(rel) = file.strip_prefix(&root) {
            declaration.location.file = rel.to_string_lossy().into_owned();
        }
    }
    Ok(())
}
