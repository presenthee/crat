use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct DeclId(pub String);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct StageId(pub String);
pub type SourceHashes = BTreeMap<String, String>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Site {
    Local,
    Param,
    Return,
    Field,
    Static,
    Const,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Scope {
    Application,
    Foreign,
    Support,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PointerState {
    Raw,
    Promoted,
    Nonpointer,
    Unsupported,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PointerKind {
    RawConst,
    RawMut,
    Ref,
    RefMut,
    OptRef,
    OptRefMut,
    Box,
    OptBox,
    BoxedSlice,
    OptBoxedSlice,
    Slice,
    SliceMut,
    SliceCursor,
    SliceCursorMut,
    FnPtr,
    OptFnPtr,
}
impl PointerKind {
    pub fn is_raw(self) -> bool {
        matches!(self, Self::RawConst | Self::RawMut)
    }

    pub fn is_data_pointer(self) -> bool {
        !matches!(self, Self::FnPtr | Self::OptFnPtr)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PointerSlot {
    pub path: String,
    pub kind: PointerKind,
    pub optional: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceLocation {
    pub file: String,
    pub line: usize,
    pub column: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DeclarationLocator {
    pub owner_path: Vec<u32>,
    pub site: Site,
    pub ordinal: u32,
    pub pattern_path: Vec<u32>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Declaration {
    pub declaration_id: DeclId,
    pub site: Site,
    pub scope: Scope,
    pub owner: String,
    pub name: Option<String>,
    pub location: SourceLocation,
    pub resolved_type: String,
    pub locator: DeclarationLocator,
    pub slots: Vec<PointerSlot>,
    pub pointer_state: PointerState,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InventoryIssue {
    pub locator: Option<DeclarationLocator>,
    pub reason: String,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inventory {
    pub schema_version: u32,
    pub case_id: String,
    pub profile: Option<String>,
    pub stage: StageId,
    pub source_hashes: SourceHashes,
    pub declarations: Vec<Declaration>,
    pub issues: Vec<InventoryIssue>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MappedDeclaration {
    pub id: DeclId,
    pub locator: DeclarationLocator,
    pub scope: Scope,
    pub shape: String,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclarationMap {
    pub schema_version: u32,
    pub case_id: String,
    pub profile: Option<String>,
    pub stage: StageId,
    pub source_hashes: SourceHashes,
    pub entries: Vec<MappedDeclaration>,
}
