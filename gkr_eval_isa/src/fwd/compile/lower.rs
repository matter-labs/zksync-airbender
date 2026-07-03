//! Schedule-driven virtual lowering for the Stage-3 forward-program generator (T3a).
//!
//! This is the schedule-driven forward-compile path (post-T3b the ONLY one; the old
//! residency-coupled `arith.rs` emission engine was deleted in the flip). It walks a
//! persisted `LayerSchedule` and lowers each atom root's expression into a stream of
//! RICH virtual instructions (`VInstr`, mirroring ISA `Instr`) whose operands are
//! symbolic `ValueId`s rather than cells. `compile_layer` (in `mod.rs`) then projects
//! the stream onto `place::VirtualInstr`, runs the Task-1 lifetime-overlap allocator,
//! and materializes the rich stream to concrete ISA `Instr`.
//!
//! Value/admit model (T3a: value-correct, traffic deferred to Task 5):
//!   - Track `defined: HashSet<ExprId>` mirroring the schedule's residency SETS
//!     (`resident_before`/`resident_after`); an `ExprId` is *defined-resident* once we
//!     have physically evicted its value into a cell (`Mov DstFromAcc Cell(v)`).
//!   - Serve an operand as `VirtualOp::Value(v)` ONLY when `v` is truly defined-resident
//!     (value-safe). A source / resolution leaf resolves to its backing / `Special`.
//!     Any other compound is RECOMPUTED by descending its cone (pure, value-safe) — we
//!     never read a stale cell, so value correctness is robust to reorder/drift.
//!   - Residency is realized from the schedule's SETS (not the `Demand` event kinds):
//!     at every step we top up `defined` to the step's residents and drop the rest.
//!     This is the "recompute wherever Resident/Reload cannot be safely realized"
//!     fallback the T3a brief permits; the `DemandKind`-exact traffic replay is Task 5.
//!   - Cache (materialize-only) roots are committed to their `CacheOutput` sink when
//!     their shared `ExprId` is produced/recomputed, and exposed as `root_outputs` so
//!     the Task-5 cache-value gate is non-vacuous.
//!
//! Arithmetic (fold splitting, FMA fusion, field-homogeneous grouping, `-1`/`0`
//! strength reduction, over-arity chunking) is a faithful re-implementation of
//! `arith.rs`'s PURE structure, reusing its pure helpers verbatim
//! (`child_operand_field`, `classify_additive_child`, `split_reduction`,
//! `field_from_u8`/`sign_from_u8`, `is_*` predicates). Only operand delivery differs.

use std::collections::{HashMap, HashSet};

use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, LayerSchedule, ReadPlace, RootId, SourceKind,
};

use super::super::context::{DagForwardContext, ForwardAction};
use super::super::isa::{LdcSub, MovDir, OperandField, OperandLine, Sign, Special, MAX_ARITY};
use super::analyze::{analyze_layer, materialize_descriptors};
use super::arith::{
    child_operand_field, classify_additive_child, field_from_u8, is_constant_one,
    is_neg_one_factor, is_zero_expr, sign_from_u8, AdditiveChild,
};
use super::place::{ValueId, VInstrKind, VirtualInstr, VirtualOp};
use super::schedule::split_reduction;
use super::schedule_residency::MaterializeMap;
use crate::fwd::compile::CompileError;

/// BabyBear field −1 (= P−1), the canonical additive-inverse-of-1 representative.
const BABYBEAR_NEG_ONE: u32 = 0x78000001 - 1;

/// Fresh internal `ValueId`s are minted from this base so they never collide with real
/// layer `ExprId`s (`0..layer.exprs.len()`), which `lower_layer_virtual` asserts.
const INTERNAL_BASE: u32 = 1 << 30;

// ─────────────────────────────────────────────────────────────────────────────────
// Rich virtual instruction (mirrors ISA `Instr`, isa.rs:56-62) with symbolic operands.
// ─────────────────────────────────────────────────────────────────────────────────

/// A virtual destination: a symbolic cell (`ValueId`) or a committed materialize write.
#[derive(Clone, Copy, Debug)]
pub(crate) enum VDst {
    Cell(ValueId),
    GlobalMaterialize { slot: u8, col: u16 },
}

/// A rich virtual instruction. Operands are `VirtualOp` (Task 1) — symbolic `Value`s
/// resolved to `Smem` cells by placement, plus the residency-free backing/ldc/special
/// operands. `defines` names the `ValueId` a `Mov DstFromAcc Cell(v)` produces (`None`
/// for folds and materialize writes). `is_dram_read` is Task-5 traffic metadata.
#[derive(Clone, Debug)]
pub(crate) enum VInstr {
    Add { field: OperandField, sign: Sign, reads: Vec<VirtualOp>, defines: Option<ValueId>, is_dram_read: bool },
    Mul { field: OperandField, reads: Vec<VirtualOp>, defines: Option<ValueId>, is_dram_read: bool },
    Fma { field_lhs: OperandField, field_rhs: OperandField, sign: Sign, pairs: Vec<(VirtualOp, VirtualOp)>, defines: Option<ValueId>, is_dram_read: bool },
    Mov { dir: MovDir, field: OperandField, dst: Option<VDst>, src: Option<VirtualOp>, defines: Option<ValueId>, is_dram_read: bool },
}

impl VInstr {
    pub(crate) fn defines(&self) -> Option<ValueId> {
        match self {
            VInstr::Add { defines, .. }
            | VInstr::Mul { defines, .. }
            | VInstr::Fma { defines, .. }
            | VInstr::Mov { defines, .. } => *defines,
        }
    }

    pub(crate) fn is_dram_read(&self) -> bool {
        match self {
            VInstr::Add { is_dram_read, .. }
            | VInstr::Mul { is_dram_read, .. }
            | VInstr::Fma { is_dram_read, .. }
            | VInstr::Mov { is_dram_read, .. } => *is_dram_read,
        }
    }

    /// Representative operand field (Fma reports `field_lhs`). Used for `widths` and the
    /// placement projection; the interpreter ignores the field bit for value.
    pub(crate) fn field(&self) -> OperandField {
        match self {
            VInstr::Add { field, .. } | VInstr::Mul { field, .. } | VInstr::Mov { field, .. } => {
                *field
            }
            VInstr::Fma { field_lhs, .. } => *field_lhs,
        }
    }

    /// The `VInstrKind` tag (for the placement projection).
    fn kind(&self) -> VInstrKind {
        match self {
            VInstr::Add { .. } => VInstrKind::Add,
            VInstr::Mul { .. } => VInstrKind::Mul,
            VInstr::Fma { .. } => VInstrKind::Fma,
            VInstr::Mov { .. } => VInstrKind::Mov,
        }
    }

    /// The `sign` (Fma/Add carry it; Mul/Mov are `Plus`).
    fn sign(&self) -> Sign {
        match self {
            VInstr::Add { sign, .. } | VInstr::Fma { sign, .. } => *sign,
            _ => Sign::Plus,
        }
    }

    /// Project onto the Task-1 placement input. Placement only inspects `defines` +
    /// `VirtualOp::Value` reads for liveness; the other fields are carried for shape.
    pub(crate) fn to_place(&self) -> VirtualInstr {
        let reads: Vec<VirtualOp> = match self {
            VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => reads.clone(),
            VInstr::Fma { pairs, .. } => {
                let mut r = Vec::with_capacity(pairs.len() * 2);
                for (l, rr) in pairs {
                    r.push(l.clone());
                    r.push(rr.clone());
                }
                r
            }
            VInstr::Mov { src, .. } => src.iter().cloned().collect(),
        };
        VirtualInstr {
            op: self.kind(),
            field: self.field(),
            defines: self.defines(),
            reads,
            sign: self.sign(),
            is_dram_read: self.is_dram_read(),
        }
    }
}

/// Where an atom root's value lands, before cell placement.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)] // `Cell` is a reserved interface variant (smem-resident roots; unused in T3a).
pub(crate) enum VirtualRootOutput {
    /// Materialized to a backing `(slot, col)` — Compute (and Cache) roots.
    Global { slot: u8, col: u16 },
    /// A `CopyAlias` root's stable-storage source operand (zero program lanes).
    Alias(OperandLine),
    /// A root that stays smem-resident in a cell (unused in T3a; reserved).
    Cell(ValueId),
}

// ─────────────────────────────────────────────────────────────────────────────────
// The schedule-walking virtual lowerer.
// ─────────────────────────────────────────────────────────────────────────────────

struct VirtualLower<'a> {
    ctx: &'a mut DagForwardContext,
    /// Owned clone of `ctx.cross_layer_fields` so `child_operand_field` can borrow it
    /// immutably while `ctx` is mutated (interning backings/consts/challenges).
    cross: HashMap<ReadPlace, cs::gkr_compiler::dag_ir::FieldKind>,
    out: Vec<VInstr>,
    step_of_instr: Vec<usize>,
    cur_step: usize,
    /// Real `ExprId`s currently defined-resident (physically in a cell). Never internal.
    defined: HashSet<ExprId>,
    widths: HashMap<ValueId, OperandField>,
    next_internal: u32,
    /// Compute roots by their shared `ExprId`: `(RootId, slot, col, sink field)`.
    expr_to_compute: HashMap<ExprId, Vec<(RootId, u8, u16, OperandField)>>,
    exposed: HashSet<RootId>,
    root_outputs: Vec<(RootId, VirtualRootOutput)>,
    /// Interned resolution-leaf descriptors (`ExprId → ctx.specials` index).
    desc_by_expr: HashMap<ExprId, u16>,
}

impl<'a> VirtualLower<'a> {
    fn emit(&mut self, vi: VInstr) {
        self.out.push(vi);
        self.step_of_instr.push(self.cur_step);
    }

    fn fresh_internal(&mut self) -> ValueId {
        let id = ExprId(self.next_internal);
        self.next_internal += 1;
        id
    }

    // ── operand seeding / evict primitives ────────────────────────────────────────

    fn emit_init_field(&mut self, op: VirtualOp, field: OperandField) {
        let is_dram = is_dram_op(&op);
        self.emit(VInstr::Mov {
            dir: MovDir::AccFromSrc,
            field,
            dst: None,
            src: Some(op),
            defines: None,
            is_dram_read: is_dram,
        });
    }

    fn emit_init(&mut self, op: VirtualOp) {
        self.emit_init_field(op, OperandField::Base);
    }

    fn emit_unary_negate(&mut self) {
        self.emit(VInstr::Mul {
            field: OperandField::Base,
            reads: vec![VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 }],
            defines: None,
            is_dram_read: false,
        });
    }

    /// `Mov DstFromAcc Cell(v)` — define `v` into a cell (the residency/temp evict).
    fn emit_evict_to_cell(&mut self, v: ValueId, field: OperandField) {
        self.emit(VInstr::Mov {
            dir: MovDir::DstFromAcc,
            field,
            dst: Some(VDst::Cell(v)),
            src: None,
            defines: Some(v),
            is_dram_read: false,
        });
    }

    fn push_fold(&mut self, field: OperandField, ops: Vec<VirtualOp>, is_add: bool, sign: Sign) {
        let is_dram = ops.iter().any(is_dram_op);
        if is_add {
            self.emit(VInstr::Add { field, sign, reads: ops, defines: None, is_dram_read: is_dram });
        } else {
            self.emit(VInstr::Mul { field, reads: ops, defines: None, is_dram_read: is_dram });
        }
    }

    fn push_fma_chunked(
        &mut self,
        field_lhs: OperandField,
        field_rhs: OperandField,
        sign: Sign,
        pairs: Vec<(VirtualOp, VirtualOp)>,
    ) {
        for chunk in pairs.chunks(MAX_ARITY) {
            let is_dram = chunk.iter().any(|(l, r)| is_dram_op(l) || is_dram_op(r));
            self.emit(VInstr::Fma {
                field_lhs,
                field_rhs,
                sign,
                pairs: chunk.to_vec(),
                defines: None,
                is_dram_read: is_dram,
            });
        }
    }

    // ── source resolution (residency-free; mirrors arith::source_to_operand arms) ──

    fn source_to_vop(
        &mut self,
        layer: &DagLayer,
        expr_id: ExprId,
    ) -> Result<VirtualOp, CompileError> {
        if layer.resolutions.contains_key(&expr_id) {
            let desc = *self.desc_by_expr.get(&expr_id).ok_or_else(|| {
                CompileError::FieldMismatch(format!(
                    "resolution leaf {} not interned by materialize_descriptors",
                    expr_id.0
                ))
            })?;
            return Ok(VirtualOp::Special { desc });
        }
        let Expr::Source(src_id) = &layer.exprs[expr_id.0 as usize] else {
            return Err(CompileError::FieldMismatch(format!(
                "source_to_vop on non-source expr {}",
                expr_id.0
            )));
        };
        match &layer.sources[src_id.0 as usize].kind {
            SourceKind::Read { place } => {
                let (slot, col) = self.ctx.backings.read_slot_col(place)?;
                Ok(VirtualOp::Global { slot, col })
            }
            SourceKind::VirtualSetup { kind } => {
                let (slot, col) = self.ctx.backings.virtual_setup_slot(kind)?;
                Ok(VirtualOp::Global { slot, col })
            }
            SourceKind::Constant { value } => match *value {
                1 => Ok(VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::One as u16 }),
                v if v == BABYBEAR_NEG_ONE => {
                    Ok(VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 })
                }
                v => {
                    let idx = self.ctx.consts.intern(v);
                    Ok(VirtualOp::Ldc { sub: LdcSub::Const, idx })
                }
            },
            SourceKind::Challenge { reference } => {
                let (sub, idx) = self.ctx.challenges.intern(reference);
                Ok(VirtualOp::Ldc { sub, idx })
            }
            SourceKind::LookupValue { .. } => Err(CompileError::UncoveredLookupLeaf(expr_id.0)),
        }
    }

    // ── operand lowering: serve resident, else source, else recompute ─────────────

    fn lower_operand_virtual(
        &mut self,
        layer: &DagLayer,
        expr_id: ExprId,
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<VirtualOp, CompileError> {
        // 1. Truly defined-resident → serve from its cell (value-safe).
        if self.defined.contains(&expr_id) {
            return Ok(VirtualOp::Value(expr_id));
        }
        // 2. A source or resolution-pruned leaf resolves to one operand line.
        if layer.resolutions.contains_key(&expr_id)
            || matches!(&layer.exprs[expr_id.0 as usize], Expr::Source(_))
        {
            return self.source_to_vop(layer, expr_id);
        }
        // 3. Compound: recompute the cone into the acc, then evict to a cell. If this
        //    value is a scheduled resident (admitted this step) we define it under its
        //    own ExprId so later uses serve it; otherwise a fresh internal temp.
        let field = child_operand_field(layer, expr_id, expected, &self.cross);
        self.compile_expr_virtual(layer, expr_id, field, resident_target)?;
        self.materialize_if_root(expr_id, true);
        if resident_target.contains(&expr_id) {
            self.widths.insert(expr_id, field);
            self.emit_evict_to_cell(expr_id, field);
            self.defined.insert(expr_id);
            Ok(VirtualOp::Value(expr_id))
        } else {
            let t = self.fresh_internal();
            self.widths.insert(t, field);
            self.emit_evict_to_cell(t, field);
            Ok(VirtualOp::Value(t))
        }
    }

    // ── expression lowering into the accumulator (mirrors arith::compile_expr) ────

    fn compile_expr_virtual(
        &mut self,
        layer: &DagLayer,
        expr_id: ExprId,
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<(), CompileError> {
        if layer.resolutions.contains_key(&expr_id) {
            let desc = *self.desc_by_expr.get(&expr_id).ok_or_else(|| {
                CompileError::FieldMismatch(format!(
                    "resolution leaf {} not interned by materialize_descriptors",
                    expr_id.0
                ))
            })?;
            let field = child_operand_field(layer, expr_id, expected, &self.cross);
            self.emit_init_field(VirtualOp::Special { desc }, field);
            return Ok(());
        }
        match &layer.exprs[expr_id.0 as usize] {
            Expr::Source(_) => {
                let field = child_operand_field(layer, expr_id, expected, &self.cross);
                let op = self.source_to_vop(layer, expr_id)?;
                self.emit_init_field(op, field);
                Ok(())
            }
            Expr::Add(children) => {
                let ch = children.clone();
                self.compile_add_virtual(layer, ch, expected, resident_target)
            }
            Expr::Mul(children) => {
                let ch = children.clone();
                self.compile_mul_virtual(layer, ch, expected, resident_target)
            }
        }
    }

    fn compile_add_virtual(
        &mut self,
        layer: &DagLayer,
        children: Vec<ExprId>,
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<(), CompileError> {
        let children: Vec<ExprId> =
            children.into_iter().filter(|&c| !is_zero_expr(layer, c)).collect();
        if children.is_empty() {
            // Sum of only zeros = 0 (value-safe identity; degenerate roots don't occur).
            self.emit_init_field(
                VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::Zero as u16 },
                OperandField::Base,
            );
            return Ok(());
        }
        if self.try_compile_fma_virtual(layer, &children, expected, resident_target)?.is_some() {
            return Ok(());
        }
        self.compile_reduction_virtual(layer, &children, true, false, expected, resident_target)
    }

    fn compile_mul_virtual(
        &mut self,
        layer: &DagLayer,
        children: Vec<ExprId>,
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<(), CompileError> {
        // A product with any zero factor is 0 (annihilator). Short-circuit so a
        // `Constant{0}` factor never reaches source resolution (which forbids 0).
        if children.iter().any(|&c| is_zero_expr(layer, c)) {
            self.emit_init_field(
                VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::Zero as u16 },
                OperandField::Base,
            );
            return Ok(());
        }
        let factors: Vec<ExprId> =
            children.into_iter().filter(|&c| !is_constant_one(layer, c)).collect();
        if factors.is_empty() {
            // Product of only `1`s = 1.
            self.emit_init_field(
                VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::One as u16 },
                OperandField::Base,
            );
            return Ok(());
        }
        let mut neg_one_count = 0usize;
        let mut surviving: Vec<ExprId> = Vec::with_capacity(factors.len());
        for &f in &factors {
            if is_neg_one_factor(layer, f) {
                neg_one_count += 1;
            } else {
                surviving.push(f);
            }
        }
        let negate = neg_one_count % 2 == 1;
        if surviving.is_empty() {
            // Product of only `-1`s = ±1 (never in real circuits): value-safe identity.
            self.emit_init_field(
                VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::One as u16 },
                OperandField::Base,
            );
            if negate {
                self.emit_unary_negate();
            }
            return Ok(());
        }
        self.compile_reduction_virtual(layer, &surviving, false, negate, expected, resident_target)
    }

    /// Field-homogeneous reduction (mirrors arith::compile_reduction).
    fn compile_reduction_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        is_add: bool,
        negate: bool,
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<(), CompileError> {
        debug_assert!(!children.is_empty());
        // Pre-materialize every child to an operand BEFORE seeding the acc (a compound
        // child clobbers the acc during its own lowering).
        let mut ops: Vec<(OperandField, VirtualOp, Sign)> = Vec::with_capacity(children.len());
        for &c in children {
            let (to_lower, sign) = if is_add {
                match classify_additive_child(layer, c) {
                    AdditiveChild::Product { .. } => (c, Sign::Plus),
                    AdditiveChild::Addend { sign, id } => (id, sign),
                }
            } else {
                (c, Sign::Plus)
            };
            let field = child_operand_field(layer, to_lower, expected, &self.cross);
            let op = self.lower_operand_virtual(layer, to_lower, expected, resident_target)?;
            ops.push((field, op, sign));
        }

        // Seed selection: a Plus Base term, else any Plus term, else a Base term.
        let init_idx = ops
            .iter()
            .position(|(f, _, s)| *f == OperandField::Base && *s == Sign::Plus)
            .or_else(|| ops.iter().position(|(_, _, s)| *s == Sign::Plus))
            .or_else(|| ops.iter().position(|(f, _, _)| *f == OperandField::Base))
            .unwrap_or(0);
        self.emit_init_field(ops[init_idx].1.clone(), ops[init_idx].0);
        if ops[init_idx].2 == Sign::Minus {
            self.emit_unary_negate();
        }

        if ops.len() == 1 {
            if negate {
                self.emit_unary_negate();
            }
            return Ok(());
        }

        let mut base_plus: Vec<VirtualOp> = Vec::new();
        let mut base_minus: Vec<VirtualOp> = Vec::new();
        let mut ext_plus: Vec<VirtualOp> = Vec::new();
        let mut ext_minus: Vec<VirtualOp> = Vec::new();
        for (i, (field, op, sign)) in ops.iter().enumerate() {
            if i == init_idx {
                continue;
            }
            match (field, sign) {
                (OperandField::Base, Sign::Plus) => base_plus.push(op.clone()),
                (OperandField::Base, Sign::Minus) => base_minus.push(op.clone()),
                (OperandField::Ext, Sign::Plus) => ext_plus.push(op.clone()),
                (OperandField::Ext, Sign::Minus) => ext_minus.push(op.clone()),
            }
        }
        let seed_is_base = ops[init_idx].0 == OperandField::Base;

        for (field, sign, group) in [
            (OperandField::Base, Sign::Plus, base_plus),
            (OperandField::Base, Sign::Minus, base_minus),
        ] {
            if group.is_empty() {
                continue;
            }
            self.emit_reduction_group_virtual(field, group, is_add, sign)?;
        }
        if negate && seed_is_base {
            self.emit_unary_negate();
        }
        for (field, sign, group) in [
            (OperandField::Ext, Sign::Plus, ext_plus),
            (OperandField::Ext, Sign::Minus, ext_minus),
        ] {
            if group.is_empty() {
                continue;
            }
            self.emit_reduction_group_virtual(field, group, is_add, sign)?;
        }
        if negate && !seed_is_base {
            self.emit_unary_negate();
        }
        Ok(())
    }

    /// One field-homogeneous group, split via `split_reduction` past `MAX_ARITY`
    /// (mirrors arith::emit_reduction_group). Split partials evict to fresh internal
    /// cells and fold back in.
    fn emit_reduction_group_virtual(
        &mut self,
        field: OperandField,
        ops: Vec<VirtualOp>,
        is_add: bool,
        sign: Sign,
    ) -> Result<(), CompileError> {
        if ops.len() <= MAX_ARITY {
            self.push_fold(field, ops, is_add, sign);
            return Ok(());
        }
        if is_add && sign == Sign::Minus {
            return Err(CompileError::FieldMismatch(
                "over-MAX_ARITY Sign::Minus ADD group is unsupported (evict-split is not sign-trivial)"
                    .into(),
            ));
        }
        let sizes = split_reduction(ops.len());
        let mut idx = 0usize;
        let mut chunks = sizes.into_iter();
        let first = chunks.next().expect("split_reduction yields >=1 chunk for arity>0");
        self.push_fold(field, ops[idx..idx + first].to_vec(), is_add, Sign::Plus);
        idx += first;
        for size in chunks {
            let t = self.fresh_internal();
            self.widths.insert(t, field);
            self.emit_evict_to_cell(t, field);
            let chunk = &ops[idx..idx + size];
            idx += size;
            self.emit_init(chunk[0].clone());
            if chunk.len() > 1 {
                self.push_fold(field, chunk[1..].to_vec(), is_add, Sign::Plus);
            }
            self.push_fold(field, vec![VirtualOp::Value(t)], is_add, Sign::Plus);
        }
        Ok(())
    }

    /// Lower an Add whose children include ≥1 binary product to `init/ADD + FMA`
    /// (mirrors arith::try_compile_fma). `Ok(None)` when there is no product child.
    fn try_compile_fma_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<Option<()>, CompileError> {
        let mut products: Vec<(Sign, ExprId, ExprId)> = Vec::with_capacity(children.len());
        let mut addends: Vec<(Sign, ExprId)> = Vec::new();
        for &c in children {
            match classify_additive_child(layer, c) {
                AdditiveChild::Product { sign, lhs, rhs } => products.push((sign, lhs, rhs)),
                AdditiveChild::Addend { sign, id } => addends.push((sign, id)),
            }
        }
        if products.is_empty() {
            return Ok(None);
        }

        let mut addend_ops: Vec<(OperandField, VirtualOp, Sign)> =
            Vec::with_capacity(addends.len());
        for &(sign, c) in &addends {
            let f = child_operand_field(layer, c, expected, &self.cross);
            let op = self.lower_operand_virtual(layer, c, expected, resident_target)?;
            addend_ops.push((f, op, sign));
        }
        let mut lo: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)> =
            Vec::with_capacity(products.len());
        for &(sign, lhs, rhs) in &products {
            let lf = child_operand_field(layer, lhs, expected, &self.cross);
            let rf = child_operand_field(layer, rhs, expected, &self.cross);
            let lhs_op = self.lower_operand_virtual(layer, lhs, expected, resident_target)?;
            let rhs_op = self.lower_operand_virtual(layer, rhs, expected, resident_target)?;
            lo.push((sign, lf, lhs_op, rf, rhs_op));
        }

        // Seed the accumulator; `fma_lo` is the product set still to fold as FMA.
        let fma_lo: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)> =
            if !addend_ops.is_empty() {
                let seed = addend_ops
                    .iter()
                    .position(|(f, _, s)| *f == OperandField::Base && *s == Sign::Plus)
                    .or_else(|| addend_ops.iter().position(|(_, _, s)| *s == Sign::Plus))
                    .or_else(|| addend_ops.iter().position(|(f, _, _)| *f == OperandField::Base))
                    .unwrap_or(0);
                self.emit_init_field(addend_ops[seed].1.clone(), addend_ops[seed].0);
                if addend_ops[seed].2 == Sign::Minus {
                    self.emit_unary_negate();
                }
                let mut base_plus: Vec<VirtualOp> = Vec::new();
                let mut base_minus: Vec<VirtualOp> = Vec::new();
                let mut ext_plus: Vec<VirtualOp> = Vec::new();
                let mut ext_minus: Vec<VirtualOp> = Vec::new();
                for (i, (f, op, s)) in addend_ops.iter().enumerate() {
                    if i == seed {
                        continue;
                    }
                    match (f, s) {
                        (OperandField::Base, Sign::Plus) => base_plus.push(op.clone()),
                        (OperandField::Base, Sign::Minus) => base_minus.push(op.clone()),
                        (OperandField::Ext, Sign::Plus) => ext_plus.push(op.clone()),
                        (OperandField::Ext, Sign::Minus) => ext_minus.push(op.clone()),
                    }
                }
                for (f, s, group) in [
                    (OperandField::Base, Sign::Plus, base_plus),
                    (OperandField::Base, Sign::Minus, base_minus),
                    (OperandField::Ext, Sign::Plus, ext_plus),
                    (OperandField::Ext, Sign::Minus, ext_minus),
                ] {
                    if group.is_empty() {
                        continue;
                    }
                    self.emit_reduction_group_virtual(f, group, true, s)?;
                }
                lo
            } else {
                let seed = lo.iter().position(|(s, ..)| *s == Sign::Plus).unwrap_or(0);
                let (seed_sign, lf0, lhs0_op, rf0, rhs0_op) = lo[seed].clone();
                self.emit_init_field(lhs0_op, lf0);
                self.emit(VInstr::Mul {
                    field: rf0,
                    reads: vec![rhs0_op.clone()],
                    defines: None,
                    is_dram_read: is_dram_op(&rhs0_op),
                });
                if seed_sign == Sign::Minus {
                    self.emit_unary_negate();
                }
                if lo.len() == 1 {
                    return Ok(Some(()));
                }
                let mut rest = lo;
                rest.remove(seed);
                rest
            };

        use std::collections::BTreeMap;
        let mut groups: BTreeMap<(u8, u8, u8), Vec<(VirtualOp, VirtualOp)>> = BTreeMap::new();
        for (sign, lf, lhs_op, rf, rhs_op) in fma_lo {
            let ((cf_l, cf_r), (op_l, op_r)) = canonical_fma_pair_v(lf, rf, lhs_op, rhs_op);
            groups
                .entry((cf_l as u8, cf_r as u8, sign as u8))
                .or_default()
                .push((op_l, op_r));
        }
        for ((lf, rf, sign), gpairs) in groups {
            self.push_fma_chunked(field_from_u8(lf), field_from_u8(rf), sign_from_u8(sign), gpairs);
        }
        Ok(Some(()))
    }

    // ── materialize obligations (Compute/Cache roots) ────────────────────────────

    /// Emit the committed write(s) for every Compute root whose expr is `expr_id`, and
    /// expose each as a `root_output`. `from_acc` reads the accumulator (value just
    /// computed); otherwise the value is read from its resident cell.
    fn materialize_if_root(&mut self, expr_id: ExprId, from_acc: bool) {
        let Some(roots) = self.expr_to_compute.get(&expr_id).cloned() else { return };
        for (rid, slot, col, field) in roots {
            if self.exposed.contains(&rid) {
                continue;
            }
            if from_acc {
                self.emit(VInstr::Mov {
                    dir: MovDir::DstFromAcc,
                    field,
                    dst: Some(VDst::GlobalMaterialize { slot, col }),
                    src: None,
                    defines: None,
                    is_dram_read: false,
                });
            } else {
                self.emit(VInstr::Mov {
                    dir: MovDir::DstFromSrc,
                    field,
                    dst: Some(VDst::GlobalMaterialize { slot, col }),
                    src: Some(VirtualOp::Value(expr_id)),
                    defines: None,
                    is_dram_read: false,
                });
            }
            self.root_outputs.push((rid, VirtualRootOutput::Global { slot, col }));
            self.exposed.insert(rid);
        }
    }
}

/// True if `op` is a real backing (DRAM) read. Over-counts VirtualSetup-backed reads as
/// DRAM (cosmetic — `is_dram_read` is Task-5 metadata, unused by placement/interp).
fn is_dram_op(op: &VirtualOp) -> bool {
    matches!(op, VirtualOp::Global { .. })
}

/// Canonicalize a commutative FMA pair so mixed products are `(Base, Ext)` (H5).
fn canonical_fma_pair_v(
    lf: OperandField,
    rf: OperandField,
    lhs: VirtualOp,
    rhs: VirtualOp,
) -> ((OperandField, OperandField), (VirtualOp, VirtualOp)) {
    match (lf, rf) {
        (OperandField::Ext, OperandField::Base) => {
            ((OperandField::Base, OperandField::Ext), (rhs, lhs))
        }
        _ => ((lf, rf), (lhs, rhs)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// The Phase-1 driver.
// ─────────────────────────────────────────────────────────────────────────────────

/// Walk `schedule.order`, lowering each atom root's expression to a rich `VInstr`
/// stream with symbolic operands + realizing the schedule's residency SETS.
///
/// Returns `(instrs, step_of_instr, root_outputs, resident_realized)`. The 4th element
/// (H5) is the EXPLICIT per-step residency boundary snapshots — this extends the T3a
/// brief's 3-tuple so the realized residency is recorded during the walk rather than
/// reconstructed from `cell_of`. `this_layer` (the artifact layer index) is likewise a
/// small extension: it is required to resolve `Export` materialize sinks.
pub(crate) fn lower_layer_virtual(
    layer: &DagLayer,
    schedule: &LayerSchedule,
    ctx: &mut DagForwardContext,
    _mat: &MaterializeMap,
    this_layer: usize,
) -> Result<
    (
        Vec<VInstr>,
        Vec<usize>,
        Vec<(RootId, VirtualRootOutput)>,
        Vec<(Vec<ExprId>, Vec<ExprId>)>,
    ),
    CompileError,
> {
    // Intern reached resolution descriptors ONCE (ctx.specials); the interned map feeds
    // Special operand resolution during lowering (never re-resolved per use).
    let graph = analyze_layer(layer, ctx);
    let desc_by_expr = materialize_descriptors(&graph.descriptors, layer, ctx);
    let cross = ctx.cross_layer_fields.clone();

    // Internal ValueIds live in a disjoint HIGH range (assert real ExprIds stay below).
    assert!(
        (layer.exprs.len() as u64) < INTERNAL_BASE as u64,
        "layer has {} exprs; internal ValueId base {INTERNAL_BASE} would collide",
        layer.exprs.len()
    );

    // Compute roots by shared ExprId: intern each sink's backing once.
    let mut expr_to_compute: HashMap<ExprId, Vec<(RootId, u8, u16, OperandField)>> = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        let rid = RootId(idx as u32);
        let Some(sink) = root.materialize.as_ref() else { continue };
        if matches!(ctx.actions.get(&rid), Some(ForwardAction::Compute)) {
            let (key, col) = super::sink_to_backing(sink, this_layer);
            let slot = ctx.backings.intern(key)?;
            let field = super::operand_field_of(sink);
            expr_to_compute.entry(root.expr).or_default().push((rid, slot, col, field));
        }
    }

    let mut st = VirtualLower {
        ctx,
        cross,
        out: Vec::new(),
        step_of_instr: Vec::new(),
        cur_step: 0,
        defined: HashSet::new(),
        widths: HashMap::new(),
        next_internal: INTERNAL_BASE,
        expr_to_compute,
        exposed: HashSet::new(),
        root_outputs: Vec::new(),
        desc_by_expr,
    };

    let mut resident_realized: Vec<(Vec<ExprId>, Vec<ExprId>)> =
        Vec::with_capacity(schedule.order.len());

    for (p, &rid) in schedule.order.iter().enumerate() {
        st.cur_step = p;
        let step = &schedule.steps[p];
        let rb: HashSet<ExprId> = step.resident_before.iter().copied().collect();
        let ra: HashSet<ExprId> = step.resident_after.iter().copied().collect();

        // Drop values the schedule no longer keeps resident entering this step (implicit
        // cone-fit drops + explicit evicts, realized as a set difference). This bounds
        // the served/held set to the schedule's residency so cell pressure tracks the
        // (validated ≤ budget) plan — we never serve a value whose cell may be reused.
        st.defined.retain(|v| rb.contains(v));
        let before = sorted_real(&st.defined);

        // Process the ordered atom root. Shared sub-values that the schedule keeps
        // resident (`resident_target = ra`) are defined LAZILY the first time a cone
        // computes them (in `lower_operand_virtual`) and served thereafter — so the
        // in-cone residents shield their subtrees (keeping the transient peak small,
        // matching the optimizer's `cone_peak`) without an eager whole-set top-up that
        // would over-hold `resident_before ∪ resident_after`.
        let action = st.ctx.actions.get(&rid).cloned();
        match action {
            Some(ForwardAction::Compute) => {
                if !st.exposed.contains(&rid) {
                    let expr = layer.roots[rid.0 as usize].expr;
                    let sink = layer.roots[rid.0 as usize]
                        .materialize
                        .as_ref()
                        .expect("Compute root has a materialize sink");
                    let expected = super::operand_field_of(sink);
                    if st.defined.contains(&expr) {
                        st.materialize_if_root(expr, false);
                    } else {
                        st.compile_expr_virtual(layer, expr, expected, &ra)?;
                        st.materialize_if_root(expr, true);
                        if ra.contains(&expr) && !st.defined.contains(&expr) {
                            let field = child_operand_field(layer, expr, expected, &st.cross);
                            st.widths.insert(expr, field);
                            st.emit_evict_to_cell(expr, field);
                            st.defined.insert(expr);
                        }
                    }
                }
            }
            Some(ForwardAction::CopyAlias { src_addr, .. }) => {
                if !st.exposed.contains(&rid) {
                    let place = super::copy_src_read_place(src_addr).ok_or_else(|| {
                        CompileError::FieldMismatch(format!(
                            "CopyAlias src_addr {src_addr:?} is not a backing read (RootId {})",
                            rid.0
                        ))
                    })?;
                    let (slot, col) = st.ctx.backings.read_slot_col(&place)?;
                    st.root_outputs
                        .push((rid, VirtualRootOutput::Alias(OperandLine::Global { slot, col })));
                    st.exposed.insert(rid);
                }
            }
            Some(ForwardAction::SkipScratchPrefill) => { /* emits nothing; not exposed */ }
            None => return Err(CompileError::OutputUnresolved(rid)),
        }

        // Snapshot the realized residency leaving this step (real ExprIds only).
        let after = sorted_real(&st.defined);
        resident_realized.push((before, after));
    }

    // Final sweep: expose any Compute root (typically cross-layer-only Cache roots) not
    // reached by the ordered walk, so the Task-5 cache-value gate is non-vacuous.
    st.cur_step = schedule.order.len().saturating_sub(1);
    let mut pending: Vec<ExprId> = st
        .expr_to_compute
        .iter()
        .filter(|(_, roots)| roots.iter().any(|(rid, ..)| !st.exposed.contains(rid)))
        .map(|(&e, _)| e)
        .collect();
    pending.sort_by_key(|e| e.0);
    let empty: HashSet<ExprId> = HashSet::new();
    for expr in pending {
        if st.defined.contains(&expr) {
            st.materialize_if_root(expr, false);
        } else {
            let field = child_operand_field(layer, expr, OperandField::Base, &st.cross);
            st.compile_expr_virtual(layer, expr, field, &empty)?;
            st.materialize_if_root(expr, true);
        }
    }

    Ok((st.out, st.step_of_instr, st.root_outputs, resident_realized))
}

/// Sorted real (non-internal) `ExprId`s of a defined-resident set.
fn sorted_real(defined: &HashSet<ExprId>) -> Vec<ExprId> {
    let mut v: Vec<ExprId> = defined.iter().copied().filter(|e| e.0 < INTERNAL_BASE).collect();
    v.sort_by_key(|e| e.0);
    v
}
