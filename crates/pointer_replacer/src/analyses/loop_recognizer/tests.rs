use rustc_hash::FxHashSet;
use rustc_hir::{ItemKind, def_id::LocalDefId};
use rustc_middle::{mir::TerminatorKind, ty::TyCtxt};

use super::{RecognizedLoop, recognize_body, recognize_loops};

fn find_fn(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if let ItemKind::Fn { ident, .. } = item.kind
            && ident.name.as_str() == name
        {
            return item.owner_id.def_id;
        }
    }
    panic!("no function named {name}");
}

fn run(code: &str, fn_name: &str) -> (LocalDefId, Vec<RecognizedLoop>) {
    let fn_name = fn_name.to_string();
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        let def_id = find_fn(tcx, &fn_name);
        (def_id, recognize_loops(tcx, def_id))
    })
    .unwrap()
}

#[test]
fn recognizes_natural_unit_stride_loop() {
    let (def_id, loops) = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc += 1; i += 1; }
            acc
        }
        "#,
        "f",
    );

    let [recognized] = &loops[..] else {
        panic!("expected exactly one loop, got {loops:#?}");
    };
    assert_eq!(recognized.id.function, def_id);
    assert_eq!(recognized.id.header, recognized.ordered_blocks[0]);
    assert!(recognized.region.blocks.contains(&recognized.id.header));
    assert!(
        !recognized
            .region
            .blocks
            .contains(&recognized.induction.init_block)
    );
}

#[test]
fn records_single_normal_exit_and_ordered_blocks() {
    // `Guard` gives the body call a cleanup edge. That unwind edge is not a
    // second normal loop exit.
    let (_, loops) = run(
        r#"
        pub struct Guard;
        impl Drop for Guard { fn drop(&mut self) {} }
        #[inline(never)]
        pub fn bump(x: i32) -> i32 { x + 1 }
        pub unsafe fn f(len: i32) -> i32 {
            let _guard = Guard;
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc = bump(acc); i += 1; }
            acc
        }
        "#,
        "f",
    );

    let [recognized] = &loops[..] else {
        panic!("expected exactly one loop, got {loops:#?}");
    };
    let [exit] = recognized.exits[..] else {
        panic!("expected one normal exit, got {:#?}", recognized.exits);
    };
    assert_eq!(exit.from, recognized.id.header);
    assert!(recognized.region.blocks.contains(&exit.from));
    assert!(!recognized.region.blocks.contains(&exit.to));
    assert_eq!(recognized.entry, recognized.ordered_blocks[1]);
    assert_eq!(recognized.ordered_blocks[0], recognized.id.header);
    let ordered: FxHashSet<_> = recognized.ordered_blocks.iter().copied().collect();
    assert_eq!(ordered.len(), recognized.ordered_blocks.len());
    assert_eq!(ordered, recognized.region.blocks);
}

#[test]
fn rejects_branch_in_body() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len {
                if i & 1 == 0 { acc += 1; } else { acc += 2; }
                i += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_early_exit() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32, stop: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len {
                if i == stop { return acc; }
                acc += 1;
                i += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_non_unit_step() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc += 1; i += 2; }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_double_increment() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len { acc += 1; i += 1; i += 1; }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_increment_in_header() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while {
                let go = i < len;
                i += 1;
                go
            } {
                acc += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_copy_defined_after_comparison_use() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            let mut previous = i;
            while {
                let go = previous < len;
                previous = i;
                go
            } {
                acc += 1;
                i += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_nested_loop() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(rows: i32, cols: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < rows {
                let mut j = 0;
                while j < cols { acc += 1; j += 1; }
                i += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn rejects_multiple_entries() {
    let loops = ::utils::compilation::run_compiler_on_str(
        r#"
        pub unsafe fn f(len: i32, flag: bool) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            if flag { acc += 1; }
            while i < len { acc += 1; i += 1; }
            acc
        }
        "#,
        |tcx| {
            let def_id = find_fn(tcx, "f");
            let original = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
            let recognized = recognize_body(&original, def_id);
            let [recognized] = &recognized[..] else {
                panic!("source loop should be recognizable before mutation");
            };
            let header = recognized.id.header;

            // This pinned MIR inserts a join preheader after the source-level
            // flag branch, so the unmodified header has only one outside
            // predecessor. Rewire one flag arm directly to the header while
            // leaving the other arm through that preheader.
            let mut body = (*original).clone();
            let branch = body
                .basic_blocks
                .iter_enumerated()
                .find_map(|(bb, data)| {
                    (bb != header
                        && matches!(data.terminator().kind, TerminatorKind::SwitchInt { .. }))
                    .then_some(bb)
                })
                .expect("pre-loop flag branch");
            let TerminatorKind::SwitchInt { targets, .. } =
                &body.basic_blocks[branch].terminator().kind
            else {
                unreachable!();
            };
            let arm = targets.all_targets()[0];
            let TerminatorKind::Goto { target } =
                &mut body.basic_blocks_mut()[arm].terminator_mut().kind
            else {
                panic!("flag branch arm should end at the join preheader");
            };
            *target = header;
            recognize_body(&body, def_id)
        },
    )
    .unwrap();
    assert!(loops.is_empty());
}

#[test]
fn rejects_multiple_exits() {
    let (_, loops) = run(
        r#"
        pub unsafe fn f(len: i32, first: i32, second: i32) -> i32 {
            let mut acc = 0;
            let mut i = 0;
            while i < len {
                if i == first { break; }
                if i == second { return acc; }
                acc += 1;
                i += 1;
            }
            acc
        }
        "#,
        "f",
    );
    assert!(loops.is_empty());
}

#[test]
fn recognition_does_not_inspect_pointer_origins() {
    // The loaded pointer has an origin that the old access-aware summarizer
    // refuses. Structural recognition must ignore that question entirely.
    let (_, loops) = run(
        r#"
        pub unsafe fn f(table: *mut *mut i32, len: i32) {
            let mut i = 0;
            while i < len {
                let p = *table.offset(i as isize);
                *p = i;
                i += 1;
            }
        }
        "#,
        "f",
    );
    assert_eq!(loops.len(), 1);
}
