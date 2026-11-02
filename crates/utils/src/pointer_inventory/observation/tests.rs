use super::*;

fn observations(code: &str) -> Vec<TypeObservation> {
    crate::compilation::run_compiler_on_str(code, |tcx| {
        let did = tcx
            .hir_body_owners()
            .find(|&did| tcx.item_name(did.to_def_id()).as_str() == "f")
            .unwrap();
        tcx.fn_sig(did)
            .instantiate_identity()
            .skip_binder()
            .inputs()
            .iter()
            .map(|&ty| observe_type(ty, tcx, &TypeRoles::default()))
            .collect()
    })
    .unwrap()
}

#[test]
fn partial_rawness_retains_outer_slot() {
    let obs = observations(
        "fn f(a: *mut std::ptr::NonNull<u8>, b: std::ptr::NonNull<u8>, c: &mut *const u8) {}",
    );
    assert_eq!(obs[0].raw_presence, Presence::Present);
    assert_eq!(obs[0].data_representation, Presence::Present);
    assert_eq!(endpoint_state(&obs[0]), EndpointState::Raw);
    assert_eq!(obs[0].slots[0].kind, PointerKind::RawMut);
    assert!(!obs[0].raw_slots_complete);
    assert_eq!(
        obs[0].diagnostics[0].affects,
        [ObservationFact::Slots, ObservationFact::RawSlots]
    );
    assert_eq!(endpoint_state(&obs[1]), EndpointState::Unknown);
    assert_eq!(endpoint_state(&obs[2]), EndpointState::Raw);
    for o in &obs {
        validate_observation(o).unwrap();
    }
}

#[test]
fn presence_composition_does_not_invent_absence() {
    let obs = observations(
        "fn f<T>(a: T, b: (i32, T), c: (*mut u8, T), d: Option<Option<&T>>, e: [*const u8; 20]) {}",
    );
    assert_eq!(obs[0].raw_presence, Presence::Unknown);
    assert_eq!(obs[1].raw_presence, Presence::Unknown);
    assert_eq!(obs[2].raw_presence, Presence::Present);
    assert_eq!(obs[3].raw_presence, Presence::Unknown);
    assert_eq!(obs[3].data_representation, Presence::Present);
    assert_eq!(obs[4].slots.len(), 1);
    for o in &obs {
        validate_observation(o).unwrap();
    }
}

#[test]
fn standard_container_payloads() {
    let obs = observations(
        "fn f(a: Result<i32,bool>, b: std::cmp::Ordering, c: Result<*mut u8,bool>, d: Vec<i32>, e: String, f: Option<Vec<i32>>, g: Vec<*mut i32>) {}",
    );
    assert_eq!(
        obs.iter().map(endpoint_state).collect::<Vec<_>>(),
        [
            EndpointState::Nonpointer,
            EndpointState::Nonpointer,
            EndpointState::Raw,
            EndpointState::Promoted,
            EndpointState::Promoted,
            EndpointState::Promoted,
            EndpointState::Raw
        ]
    );
    assert_eq!(obs[3].slots[0].kind, PointerKind::Vec);
    assert_eq!(obs[4].slots[0].kind, PointerKind::String);
    assert!(obs[5].slots[0].optional);
    assert_eq!(obs[6].slots[1].path, "root.element");
    assert_eq!(obs[2].slots[0].path, "root.ok");
    for o in &obs {
        validate_observation(o).unwrap();
    }
}

#[test]
fn standard_identity_and_allocator_are_required() {
    let obs = observations(
        "#![feature(allocator_api)] struct Vec; struct String; struct Ordering; fn f(a: Vec, b: String, c: Ordering, d: std::vec::Vec<u8, std::alloc::System>) {}",
    );
    for o in &obs[..3] {
        assert_eq!(endpoint_state(o), EndpointState::Nonpointer);
        assert!(o.slots.is_empty());
    }
    assert_eq!(endpoint_state(&obs[3]), EndpointState::Unknown);
    assert!(!obs[3].slots_complete);
}

#[test]
fn observation_consistency_rejects_contradictions() {
    let mut o = observations("fn f(p: *mut u8) {}").remove(0);
    o.raw_presence = Presence::Absent;
    assert!(validate_observation(&o).is_err());
    let mut o = observations("fn f(p: std::ptr::NonNull<u8>) {}").remove(0);
    o.diagnostics.clear();
    assert!(validate_observation(&o).is_err());
    let o = TypeObservation {
        raw_presence: Presence::Absent,
        data_representation: Presence::Unknown,
        slots: vec![],
        slots_complete: false,
        raw_slots_complete: true,
        diagnostics: vec![TypeDiagnostic {
            code: "nonraw_detail".into(),
            path: "root".into(),
            ty: "opaque nonraw".into(),
            affects: vec![ObservationFact::DataRepresentation, ObservationFact::Slots],
        }],
    };
    validate_observation(&o).unwrap();
    assert_eq!(endpoint_state(&o), EndpointState::Unknown);
}

#[test]
fn supported_nonstorage_and_alias_projections() {
    let obs = observations(
        "type P = *mut u8; fn f(a: P, b: fn(*mut u8)->*mut u8, c: std::marker::PhantomData<*mut u8>, d: std::ops::Range<i32>, e: *const std::ffi::c_void) {}",
    );
    assert_eq!(
        obs.iter().map(endpoint_state).collect::<Vec<_>>(),
        [
            EndpointState::Raw,
            EndpointState::Nonpointer,
            EndpointState::Nonpointer,
            EndpointState::Nonpointer,
            EndpointState::Raw
        ]
    );
    assert_eq!(obs[1].slots.len(), 1);
    assert!(obs[2].slots.is_empty());
}

#[test]
fn foreign_types_are_terminal_leaves() {
    let obs = observations(
        r#"
        #![feature(extern_types)]
        unsafe extern "C" { type Opaque; }
        fn f(a: *mut Opaque, b: Option<&mut Opaque>, c: &mut &mut Opaque,
             d: &mut *mut Opaque, e: *const *mut Opaque,
             f: Option<*mut Opaque>, g: [*const Opaque; 4]) {}
    "#,
    );
    use PointerKind::{OptRefMut, RawConst, RawMut, RefMut};
    let expected = [
        vec![("root", RawMut, false)],
        vec![("root", OptRefMut, true)],
        vec![("root", RefMut, false), ("root.pointee", RefMut, false)],
        vec![("root", RefMut, false), ("root.pointee", RawMut, false)],
        vec![("root", RawConst, false), ("root.pointee", RawMut, false)],
        vec![("root", RawMut, true)],
        vec![("root.element", RawConst, false)],
    ];
    assert_eq!(obs.len(), expected.len());
    for (i, (o, slots)) in obs.iter().zip(expected).enumerate() {
        assert_eq!(
            o.slots
                .iter()
                .map(|s| (s.path.as_str(), s.kind, s.optional))
                .collect::<Vec<_>>(),
            slots
        );
        let promoted = i == 1 || i == 2;
        assert_eq!(
            o.raw_presence,
            if promoted {
                Presence::Absent
            } else {
                Presence::Present
            }
        );
        assert_eq!(o.data_representation, Presence::Present);
        assert!(o.slots_complete && o.raw_slots_complete, "{i}: {o:?}");
        assert!(o.diagnostics.is_empty(), "{i}: {o:?}");
        assert_eq!(
            endpoint_state(o),
            if promoted {
                EndpointState::Promoted
            } else {
                EndpointState::Raw
            }
        );
        validate_observation(o).unwrap();
    }
}

#[test]
fn foreign_type_aliases_preserve_observations() {
    let obs = observations(
        r#"
        #![feature(extern_types)]
        unsafe extern "C" { type Opaque; type UnrelatedName; }
        type Raw = *mut Opaque;
        type Borrow<'a> = Option<&'a mut Opaque>;
        fn f(a: *mut Opaque, b: Raw, c: *mut UnrelatedName,
             d: Option<&mut Opaque>, e: Borrow<'_>, f: Option<&mut UnrelatedName>) {}
    "#,
    );
    assert_eq!(obs[0], obs[1]);
    assert_eq!(obs[0], obs[2]);
    assert_eq!(obs[3], obs[4]);
    assert_eq!(obs[3], obs[5]);
    for o in &obs {
        assert!(o.slots_complete && o.raw_slots_complete);
        assert!(o.diagnostics.is_empty());
        validate_observation(o).unwrap();
    }
}

#[test]
fn foreign_leaf_does_not_mask_other_unknowns() {
    let obs = observations(
        r#"
        #![feature(extern_types)]
        unsafe extern "C" { type Opaque; }
        fn f<T>(a: (&Opaque, T), b: &T, c: std::ptr::NonNull<u8>,
                d: *mut std::ptr::NonNull<u8>) {}
    "#,
    );
    for o in &obs[..3] {
        assert_eq!(o.raw_presence, Presence::Unknown);
    }
    for o in &obs[..2] {
        assert_eq!(o.data_representation, Presence::Present);
        assert_eq!(o.slots.len(), 1);
        assert_eq!(o.slots[0].kind, PointerKind::Ref);
    }
    assert_eq!(obs[3].raw_presence, Presence::Present);
    assert_eq!(obs[3].slots[0].kind, PointerKind::RawMut);
    for o in &obs {
        assert!(!o.slots_complete && !o.raw_slots_complete);
        assert!(!o.diagnostics.is_empty());
        validate_observation(o).unwrap();
    }
}
