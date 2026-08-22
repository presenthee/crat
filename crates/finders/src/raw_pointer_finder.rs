use rustc_ast::{
    Ty, TyKind,
    visit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;

pub fn count_raw_pointers(tcx: TyCtxt<'_>) -> usize {
    let mut finder = RawPointerFinder::default();
    utils::ast::foreach_crate(
        |krate| {
            finder.visit_crate(&krate);
        },
        tcx,
    );
    finder.count
}

pub fn find_raw_pointers(tcx: TyCtxt<'_>) {
    println!("{}", count_raw_pointers(tcx));
}

#[derive(Default)]
struct RawPointerFinder {
    count: usize,
}

impl Visitor<'_> for RawPointerFinder {
    fn visit_ty(&mut self, ty: &Ty) {
        if matches!(ty.kind, TyKind::Ptr(_)) {
            self.count += 1;
        }
        visit::walk_ty(self, ty);
    }
}

#[cfg(test)]
mod tests {
    use utils::compilation;

    use super::*;

    #[test]
    fn counts_nested_raw_pointer_types() {
        compilation::run_compiler_on_str(
            r#"
struct S {
    pointer: *mut i32,
}

fn f(_: *const *mut u8) -> Option<unsafe extern "C" fn(*const u8) -> *mut u8> {
    None
}
"#,
            |tcx| assert_eq!(count_raw_pointers(tcx), 5),
        )
        .unwrap();
    }
}
