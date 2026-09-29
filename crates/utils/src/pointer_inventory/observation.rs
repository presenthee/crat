use std::collections::BTreeSet;

use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::{
    Symbol,
    def_id::{CRATE_DEF_INDEX, DefId},
};

use super::*;
use crate::pointer_identity::MeasurementError;

pub fn endpoint_state(o: &TypeObservation) -> EndpointState {
    match (o.raw_presence, o.data_representation) {
        (Presence::Present, _) => EndpointState::Raw,
        (Presence::Absent, Presence::Present) => EndpointState::Promoted,
        (Presence::Absent, Presence::Absent) => EndpointState::Nonpointer,
        _ => EndpointState::Unknown,
    }
}

pub fn validate_observation(o: &TypeObservation) -> Result<(), MeasurementError> {
    let invalid = || MeasurementError::UnsupportedInventory("inconsistent type observation".into());
    let raw = o.slots.iter().any(|s| s.kind.is_raw());
    let data = o.slots.iter().any(|s| s.kind.is_data_pointer());
    if o.slots
        .iter()
        .map(|s| &s.path)
        .collect::<BTreeSet<_>>()
        .len()
        != o.slots.len()
        || (raw && o.raw_presence != Presence::Present)
        || (data && o.data_representation != Presence::Present)
        || (o.raw_presence == Presence::Present && o.data_representation != Presence::Present)
        || (o.data_representation == Presence::Absent && o.raw_presence != Presence::Absent)
        || (o.raw_presence == Presence::Absent && !o.raw_slots_complete)
        || (o.slots_complete && !o.raw_slots_complete)
        || (o.raw_slots_complete
            && o.raw_presence
                != if raw {
                    Presence::Present
                } else {
                    Presence::Absent
                })
        || (o.slots_complete
            && o.data_representation
                != if data {
                    Presence::Present
                } else {
                    Presence::Absent
                })
    {
        return Err(invalid());
    }
    let unresolved: BTreeSet<_> = [
        (
            o.raw_presence == Presence::Unknown,
            ObservationFact::RawPresence,
        ),
        (
            o.data_representation == Presence::Unknown,
            ObservationFact::DataRepresentation,
        ),
        (!o.slots_complete, ObservationFact::Slots),
        (!o.raw_slots_complete, ObservationFact::RawSlots),
    ]
    .into_iter()
    .filter_map(|(yes, fact)| yes.then_some(fact))
    .collect();
    let mut explained = BTreeSet::new();
    for d in &o.diagnostics {
        let affects: BTreeSet<_> = d.affects.iter().copied().collect();
        if d.code.is_empty()
            || d.path.is_empty()
            || affects.is_empty()
            || affects.len() != d.affects.len()
            || !affects.is_subset(&unresolved)
        {
            return Err(invalid());
        }
        explained.extend(affects);
    }
    if explained != unresolved {
        return Err(invalid());
    }
    Ok(())
}

// Resolve definitions through canonical standard-library modules, never through
// displayed type names or a user type with the same short name.
fn standard_def(tcx: TyCtxt<'_>, krate: &str, path: &[&str]) -> Option<DefId> {
    let krate = tcx
        .crates(())
        .iter()
        .find(|&&k| tcx.crate_name(k).as_str() == krate)?;
    let mut did = DefId {
        krate: *krate,
        index: CRATE_DEF_INDEX,
    };
    for component in path {
        did = tcx
            .module_children(did)
            .iter()
            .find(|child| child.ident.name.as_str() == *component)?
            .res
            .opt_def_id()?;
    }
    Some(did)
}

pub fn observe_type<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, roles: &TypeRoles) -> TypeObservation {
    let mut slots = Vec::new();
    let mut diagnostics = Vec::new();
    walk_type(ty, tcx, roles, "root", false, &mut slots, &mut diagnostics);
    let unknown = !diagnostics.is_empty();
    let raw_presence = if slots.iter().any(|s| s.kind.is_raw()) {
        Presence::Present
    } else if unknown {
        Presence::Unknown
    } else {
        Presence::Absent
    };
    let data_representation = if slots.iter().any(|s| s.kind.is_data_pointer()) {
        Presence::Present
    } else if unknown {
        Presence::Unknown
    } else {
        Presence::Absent
    };
    for d in &mut diagnostics {
        d.affects = [
            (
                raw_presence == Presence::Unknown,
                ObservationFact::RawPresence,
            ),
            (
                data_representation == Presence::Unknown,
                ObservationFact::DataRepresentation,
            ),
            (true, ObservationFact::Slots),
            (true, ObservationFact::RawSlots),
        ]
        .into_iter()
        .filter_map(|(yes, fact)| yes.then_some(fact))
        .collect();
    }
    TypeObservation {
        raw_presence,
        data_representation,
        slots,
        slots_complete: !unknown,
        raw_slots_complete: !unknown,
        diagnostics,
    }
}

fn walk_type<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    roles: &TypeRoles,
    path: &str,
    optional: bool,
    slots: &mut Vec<PointerSlot>,
    diagnostics: &mut Vec<TypeDiagnostic>,
) {
    use PointerKind as K;
    let unknown = |diagnostics: &mut Vec<TypeDiagnostic>, code: &str| {
        diagnostics.push(TypeDiagnostic {
            code: code.into(),
            path: path.into(),
            ty: ty.to_string(),
            affects: vec![],
        });
    };
    let pointer = match *ty.kind() {
        ty::RawPtr(inner, m) => Some((if m.is_mut() { K::RawMut } else { K::RawConst }, inner)),
        ty::Ref(_, inner, m) => Some((
            match (inner.is_slice(), optional, m.is_mut()) {
                (true, _, true) => K::SliceMut,
                (true, _, false) => K::Slice,
                (false, true, true) => K::OptRefMut,
                (false, true, false) => K::OptRef,
                (false, false, true) => K::RefMut,
                (false, false, false) => K::Ref,
            },
            inner,
        )),
        ty::Adt(def, args) if def.is_box() => {
            if args.types().nth(1).is_some_and(|a| !matches!(a.kind(), ty::Adt(d, _) if Some(d.did()) == standard_def(tcx,"alloc", &["alloc","Global"]))) {
                unknown(diagnostics, "unsupported_allocator"); return;
            }
            let inner = args.type_at(0);
            Some((
                match (inner.is_slice(), optional) {
                    (true, true) => K::OptBoxedSlice,
                    (true, false) => K::BoxedSlice,
                    (false, true) => K::OptBox,
                    (false, false) => K::Box,
                },
                inner,
            ))
        }
        _ => None,
    };
    if let Some((kind, inner)) = pointer {
        slots.push(PointerSlot {
            path: path.into(),
            kind,
            optional,
        });
        walk_type(
            inner,
            tcx,
            roles,
            &format!("{path}.pointee"),
            false,
            slots,
            diagnostics,
        );
        return;
    }
    match *ty.kind() {
        ty::Adt(def, args) if tcx.lang_items().option_type() == Some(def.did()) => {
            walk_type(args.type_at(0), tcx, roles, path, true, slots, diagnostics)
        }
        ty::Adt(def, _) if def.is_phantom_data() => (),
        ty::Adt(def, args) if roles.cursors.contains_key(&def.did()) => {
            slots.push(PointerSlot {
                path: path.into(),
                kind: if roles.cursors[&def.did()] {
                    K::SliceCursorMut
                } else {
                    K::SliceCursor
                },
                optional,
            });
            if let Some(inner) = args.types().next() {
                walk_type(
                    inner,
                    tcx,
                    roles,
                    &format!("{path}.element"),
                    false,
                    slots,
                    diagnostics,
                );
            } else {
                unknown(diagnostics, "missing_cursor_element");
            }
        }
        ty::Adt(def, args) if tcx.get_diagnostic_item(Symbol::intern("Vec")) == Some(def.did()) => {
            if args.types().nth(1).is_none_or(|a| !matches!(a.kind(), ty::Adt(d,_) if Some(d.did()) == standard_def(tcx,"alloc", &["alloc","Global"]))) {
                unknown(diagnostics,"unsupported_allocator"); return;
            }
            slots.push(PointerSlot {
                path: path.into(),
                kind: K::Vec,
                optional,
            });
            walk_type(
                args.type_at(0),
                tcx,
                roles,
                &format!("{path}.element"),
                false,
                slots,
                diagnostics,
            );
        }
        ty::Adt(def, _) if Some(def.did()) == standard_def(tcx, "alloc", &["string", "String"]) => {
            slots.push(PointerSlot {
                path: path.into(),
                kind: K::String,
                optional,
            })
        }
        ty::Adt(def, _) if Some(def.did()) == standard_def(tcx, "core", &["cmp", "Ordering"]) => (),
        ty::Adt(def, args)
            if tcx.get_diagnostic_item(Symbol::intern("Result")) == Some(def.did()) =>
        {
            walk_type(
                args.type_at(0),
                tcx,
                roles,
                &format!("{path}.ok"),
                false,
                slots,
                diagnostics,
            );
            walk_type(
                args.type_at(1),
                tcx,
                roles,
                &format!("{path}.err"),
                false,
                slots,
                diagnostics,
            );
        }
        ty::Adt(def, args) => {
            let lang = tcx.lang_items();
            let is_range = [
                lang.range_struct(),
                lang.range_from_struct(),
                lang.range_to_struct(),
                lang.range_full_struct(),
                lang.range_inclusive_struct(),
                lang.range_to_inclusive_struct(),
            ]
            .into_iter()
            .flatten()
            .any(|d| d == def.did());
            if !def.did().is_local() && !ty.is_c_void(tcx) && !is_range {
                unknown(diagnostics, "unsupported_external_type");
                return;
            }
            for (i, inner) in args.types().enumerate() {
                walk_type(
                    inner,
                    tcx,
                    roles,
                    &format!("{path}.arg[{i}]"),
                    false,
                    slots,
                    diagnostics,
                );
            }
        }
        ty::Tuple(types) => {
            for (i, inner) in types.iter().enumerate() {
                walk_type(
                    inner,
                    tcx,
                    roles,
                    &format!("{path}.tuple[{i}]"),
                    false,
                    slots,
                    diagnostics,
                );
            }
        }
        ty::Array(inner, _) | ty::Slice(inner) => walk_type(
            inner,
            tcx,
            roles,
            &format!("{path}.element"),
            false,
            slots,
            diagnostics,
        ),
        ty::FnPtr(..) => slots.push(PointerSlot {
            path: path.into(),
            kind: if optional { K::OptFnPtr } else { K::FnPtr },
            optional,
        }),
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_)
        | ty::Str
        | ty::Never
        | ty::FnDef(..)
        | ty::Closure(..) => (),
        _ => unknown(diagnostics, "unresolved_type"),
    }
}

#[cfg(test)]
mod tests;
