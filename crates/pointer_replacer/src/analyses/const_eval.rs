//! Backward const-evaluation of MIR operand def chains, shared by the
//! read-extent and access-order analyses. Debug MIR (as produced by
//! `mir_drops_elaborated_and_const_checked`) routes checked arithmetic
//! through `*WithOverflow` tuples and never const-propagates, so constant
//! offsets and counts must be recovered by walking single-definition chains
//! backward from the operand.

use rustc_hash::FxHashMap;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Operand, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};

/// Constant scalar arguments known at the querying call site, keyed by 0-based
/// parameter index. Values are raw bits, truncated to the parameter's width.
pub type Ctx = std::collections::BTreeMap<usize, u128>;

/// Depth bound for backward const-evaluation of operand def chains.
pub const MAX_EVAL_DEPTH: usize = 32;

#[derive(Clone, Copy)]
pub enum DefSite {
    Stmt(BasicBlock, usize),
    Call(BasicBlock),
}

/// Single direct definitions per local; multiply-defined locals map to `None`.
pub fn collect_defs(body: &Body<'_>) -> FxHashMap<Local, Option<DefSite>> {
    let mut defs: FxHashMap<Local, Option<DefSite>> = FxHashMap::default();
    let record = |local: Local, site: DefSite, defs: &mut FxHashMap<Local, Option<DefSite>>| {
        defs.entry(local)
            .and_modify(|e| *e = None)
            .or_insert(Some(site));
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (i, stmt) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, _)) = &stmt.kind
                && place.projection.is_empty()
            {
                record(place.local, DefSite::Stmt(bb, i), &mut defs);
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && destination.projection.is_empty()
        {
            record(destination.local, DefSite::Call(bb), &mut defs);
        }
    }
    defs
}

/// A constant scalar with its MIR type; `bits` are truncated to the type's
/// width.
#[derive(Clone, Copy)]
pub struct ScalarVal<'tcx> {
    pub bits: u128,
    pub ty: Ty<'tcx>,
}

pub struct EvalCx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'a Body<'tcx>,
    pub defs: &'a FxHashMap<Local, Option<DefSite>>,
    pub ctx: &'a Ctx,
    pub typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> EvalCx<'_, 'tcx> {
    pub fn int_size(&self, ty: Ty<'tcx>) -> Option<rustc_abi::Size> {
        if !matches!(
            ty.kind(),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Bool | ty::TyKind::Char
        ) {
            return None;
        }
        Some(
            self.tcx
                .layout_of(self.typing_env.as_query_input(ty))
                .ok()?
                .size,
        )
    }

    pub fn operand(&self, op: &Operand<'tcx>, depth: usize) -> Option<ScalarVal<'tcx>> {
        if depth == 0 {
            return None;
        }
        match op {
            Operand::Constant(c) => {
                let (int, ty) = if let Some(scalar) = c.const_.try_to_scalar()
                    && let Ok(int) = scalar.try_to_scalar_int()
                {
                    (int, c.const_.ty())
                } else if let rustc_middle::mir::Const::Unevaluated(uv, ty) = c.const_
                    && uv.promoted.is_none()
                    && let Ok(v) = self.tcx.const_eval_poly(uv.def)
                    && let rustc_middle::mir::ConstValue::Scalar(scalar) = v
                    && let Ok(int) = scalar.try_to_scalar_int()
                {
                    (int, ty)
                } else {
                    return None;
                };
                Some(ScalarVal {
                    bits: int.to_bits(int.size()),
                    ty,
                })
            }
            Operand::Copy(place) | Operand::Move(place) => {
                // Debug MIR routes checked arithmetic through `*WithOverflow`
                // tuples: field 0 is the wrapped value, field 1 the overflow
                // flag.
                if let [ProjectionElem::Field(field, field_ty)] = place.projection[..] {
                    return self.overflow_tuple_field(
                        place.local,
                        field.as_usize(),
                        field_ty,
                        depth - 1,
                    );
                }
                if !place.projection.is_empty() {
                    return None;
                }
                self.local(place.local, depth - 1)
            }
        }
    }

    fn local(&self, local: Local, depth: usize) -> Option<ScalarVal<'tcx>> {
        let index = local.as_usize();
        let ty = self.body.local_decls[local].ty;
        // A parameter's value comes from the context alone. Its implicit
        // entry definition means an explicit assignment, even a single one,
        // does not dominate earlier uses, so following the definition (as
        // done for ordinary locals below) would evaluate the wrong value.
        if index >= 1 && index <= self.body.arg_count {
            if self.defs.contains_key(&local) {
                return None;
            }
            let bits = *self.ctx.get(&(index - 1))?;
            let size = self.int_size(ty)?;
            return Some(ScalarVal {
                bits: size.truncate(bits),
                ty,
            });
        }
        match self.defs.get(&local).copied()?? {
            DefSite::Stmt(bb, i) => {
                let StatementKind::Assign(box (place, rvalue)) =
                    &self.body.basic_blocks[bb].statements[i].kind
                else {
                    return None;
                };
                if place.local != local {
                    return None;
                }
                self.rvalue(rvalue, ty, depth)
            }
            DefSite::Call(bb) => self.call_result(bb, ty, depth),
        }
    }

    /// Field `field` of a local whose single definition is an
    /// overflow-checked binary operation.
    fn overflow_tuple_field(
        &self,
        local: Local,
        field: usize,
        field_ty: Ty<'tcx>,
        depth: usize,
    ) -> Option<ScalarVal<'tcx>> {
        if depth == 0 {
            return None;
        }
        let Some(Some(DefSite::Stmt(bb, i))) = self.defs.get(&local).copied() else {
            return None;
        };
        let StatementKind::Assign(box (_, Rvalue::BinaryOp(op, box (a, b)))) =
            &self.body.basic_blocks[bb].statements[i].kind
        else {
            return None;
        };
        let plain = match op {
            BinOp::AddWithOverflow => BinOp::Add,
            BinOp::SubWithOverflow => BinOp::Sub,
            BinOp::MulWithOverflow => BinOp::Mul,
            _ => return None,
        };
        let l = self.operand(a, depth - 1)?;
        let r = self.operand(b, depth - 1)?;
        match field {
            0 => self.binary(plain, l, r, field_ty),
            1 => {
                let size = self.int_size(l.ty)?;
                let wrapped = self.binary(plain, l, r, l.ty)?;
                let extend = |bits: u128| {
                    if l.ty.is_signed() {
                        size.sign_extend(bits)
                    } else {
                        bits as i128
                    }
                };
                let exact = match plain {
                    BinOp::Add => extend(l.bits).checked_add(extend(r.bits))?,
                    BinOp::Sub => extend(l.bits).checked_sub(extend(r.bits))?,
                    _ => extend(l.bits).checked_mul(extend(r.bits))?,
                };
                Some(ScalarVal {
                    bits: (extend(wrapped.bits) != exact) as u128,
                    ty: self.tcx.types.bool,
                })
            }
            _ => None,
        }
    }

    pub fn rvalue(
        &self,
        rvalue: &Rvalue<'tcx>,
        ty: Ty<'tcx>,
        depth: usize,
    ) -> Option<ScalarVal<'tcx>> {
        match rvalue {
            Rvalue::Use(op) => self.operand(op, depth),
            Rvalue::Cast(CastKind::IntToInt, op, to_ty) => {
                let v = self.operand(op, depth)?;
                let from_size = self.int_size(v.ty)?;
                let to_size = self.int_size(*to_ty)?;
                let extended = if v.ty.is_signed() {
                    from_size.sign_extend(v.bits) as u128
                } else {
                    v.bits
                };
                Some(ScalarVal {
                    bits: to_size.truncate(extended),
                    ty: *to_ty,
                })
            }
            Rvalue::BinaryOp(op, box (a, b)) => {
                let l = self.operand(a, depth)?;
                let r = self.operand(b, depth)?;
                self.binary(*op, l, r, ty)
            }
            _ => None,
        }
    }

    fn binary(
        &self,
        op: BinOp,
        l: ScalarVal<'tcx>,
        r: ScalarVal<'tcx>,
        result_ty: Ty<'tcx>,
    ) -> Option<ScalarVal<'tcx>> {
        let size = self.int_size(l.ty)?;
        let signed = l.ty.is_signed();
        let (ls, rs) = (size.sign_extend(l.bits), size.sign_extend(r.bits));
        let arith = |v: u128| ScalarVal {
            bits: size.truncate(v),
            ty: result_ty,
        };
        let cmp = |c: bool| ScalarVal {
            bits: c as u128,
            ty: self.tcx.types.bool,
        };
        Some(match op {
            BinOp::Add => arith(l.bits.wrapping_add(r.bits)),
            BinOp::Sub => arith(l.bits.wrapping_sub(r.bits)),
            BinOp::Mul => arith(l.bits.wrapping_mul(r.bits)),
            BinOp::BitAnd => arith(l.bits & r.bits),
            BinOp::BitOr => arith(l.bits | r.bits),
            BinOp::BitXor => arith(l.bits ^ r.bits),
            BinOp::Eq => cmp(l.bits == r.bits),
            BinOp::Ne => cmp(l.bits != r.bits),
            BinOp::Lt if signed => cmp(ls < rs),
            BinOp::Le if signed => cmp(ls <= rs),
            BinOp::Gt if signed => cmp(ls > rs),
            BinOp::Ge if signed => cmp(ls >= rs),
            BinOp::Lt => cmp(l.bits < r.bits),
            BinOp::Le => cmp(l.bits <= r.bits),
            BinOp::Gt => cmp(l.bits > r.bits),
            BinOp::Ge => cmp(l.bits >= r.bits),
            _ => return None,
        })
    }

    /// Results of the curated pure calls: wrapping arithmetic and `size_of`.
    fn call_result(&self, bb: BasicBlock, ty: Ty<'tcx>, depth: usize) -> Option<ScalarVal<'tcx>> {
        let TerminatorKind::Call { func, args, .. } = &self.body.basic_blocks[bb].terminator().kind
        else {
            return None;
        };
        let ty::TyKind::FnDef(callee, generic_args) = func.constant()?.ty().kind() else {
            return None;
        };
        let name = self.tcx.item_name(*callee);
        match name.as_str() {
            "wrapping_add" | "wrapping_sub" | "wrapping_mul" if args.len() == 2 => {
                let l = self.operand(&args[0].node, depth)?;
                let r = self.operand(&args[1].node, depth)?;
                let op = match name.as_str() {
                    "wrapping_add" => BinOp::Add,
                    "wrapping_sub" => BinOp::Sub,
                    _ => BinOp::Mul,
                };
                self.binary(op, l, r, ty)
            }
            "size_of" if args.is_empty() => {
                let size = self
                    .tcx
                    .layout_of(self.typing_env.as_query_input(generic_args.type_at(0)))
                    .ok()?
                    .size;
                Some(ScalarVal {
                    bits: size.bytes() as u128,
                    ty,
                })
            }
            _ => None,
        }
    }
}
