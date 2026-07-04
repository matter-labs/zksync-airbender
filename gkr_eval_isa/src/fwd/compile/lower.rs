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

use std::collections::{BTreeMap, HashMap, HashSet};

use cs::gkr_compiler::dag_ir::{
    DagLayer, DemandKind, Expr, ExprId, LayerSchedule, ReadPlace, ReplayEvent, RootId, SinkInfo,
    SinkKind, SourceKind,
};

use super::super::context::{DagForwardContext, ForwardAction};
use super::super::isa::{LdcSub, MovDir, OperandField, OperandLine, Sign, Special, MAX_ARITY};
use super::analyze::{analyze_layer, materialize_descriptors};
use super::arith::{
    child_operand_field, classify_additive_child, field_from_u8, is_constant_one,
    is_neg_one_factor, is_zero_expr, sign_from_u8, AdditiveChild,
};
use super::decisions::OccurrenceStreams;
use super::place::{ValueId, VInstrKind, VirtualInstr, VirtualOp};
use super::schedule::split_reduction;
use super::schedule_residency::MaterializeMap;
use super::MaterializePolicy;
use crate::fwd::compile::CompileError;

/// Width (in cells) of a value's residency footprint under `MaterializePolicy::Decisions`
/// (Task 3): `Base` = 1, `Ext` = 4 — mirrors `place::width_of`/the traffic-tally convention
/// used elsewhere in this crate (`mod.rs::tally_operand`).
fn resident_width(field: OperandField) -> usize {
    match field {
        OperandField::Base => 1,
        OperandField::Ext => 4,
    }
}

/// Task 3: `MaterializePolicy::Decisions` residency state — present only under that
/// policy (`None` for `LegacyRecompute`/`Materialize`). `resident` is the width-weighted
/// resident set, a `BTreeMap` (per the brief's determinism requirement: eviction-candidate
/// enumeration must not depend on hash-iteration order). `VirtualLower::defined` mirrors
/// `resident`'s keys — `defined` stays the single policy-agnostic "is this value's cell
/// servable" source of truth read everywhere else in this file; `resident` is Decisions'
/// own bookkeeping for width/priority-driven admission and eviction.
struct DecisionsState {
    streams: OccurrenceStreams,
    resident: BTreeMap<ExprId, OperandField>,
    budget: usize,
}

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
    /// Emission policy. `LegacyRecompute` = the lazy realize-from-sets + recompute path
    /// (default, unchanged); `Materialize` = the event-local cache-produce vs fuse path.
    policy: MaterializePolicy,
    /// `ExprId`s that appear as a direct child of some `Add` in this layer (layer-global).
    add_child_exprs: HashSet<ExprId>,
    /// Cache-root expr ids (`materialize: Some(Cache{..})`): NEVER fusable (layer-global).
    cache_root_exprs: HashSet<ExprId>,
    /// Values `Admit`ed in the step being replayed (authoritative; NOT `resident_after`).
    admitted_this_step: HashSet<ExprId>,
    /// Values with a `Recompute` `Demand` in the step being replayed.
    recompute_this_step: HashSet<ExprId>,
    /// Task 3 (`Decisions` only): residency state driven by `SiteDecisions`/
    /// `OccurrenceStreams`. `None` under `LegacyRecompute`/`Materialize`.
    decisions: Option<DecisionsState>,
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

    // ── Task 3: `Decisions`-policy residency (admission / eviction) ────────────────

    /// Consume one occurrence off `v`'s demand stream (`Decisions` only; a no-op under
    /// `LegacyRecompute`/`Materialize`). MUST be called exactly once per demand site the
    /// lowering visits for `v` — every `lower_operand_virtual` call and every root's own
    /// top-level output demand (the driver loop) — so `effective_priority` keeps reading
    /// the CURRENT stream front. Call this BEFORE any hit/miss branching on `v`.
    fn serve_occurrence(&mut self, v: ExprId) {
        if let Some(ds) = &mut self.decisions {
            ds.streams.serve(v);
        }
    }

    /// Attempt to admit a just-produced value `v` (occupying `field`'s width) into the
    /// `Decisions` resident set. Only meaningful under `MaterializePolicy::Decisions`
    /// (returns `false` otherwise). On success, `v` is inserted into both `resident` and
    /// `defined` (and any evicted victims are removed from both) — the caller still needs
    /// to emit the physical evict-to-cell instruction.
    ///
    /// Precondition: `v`'s CURRENT occurrence has already been `serve_occurrence`d, so
    /// `effective_priority(v)` reflects `v`'s NEXT (future) occurrence — the one admission
    /// is deciding whether to preserve residency for (brief: "≥1 remaining occurrence").
    ///
    /// Capacity (brief): width-weighted vs `budget`, headroom 0. If admitting `v` requires
    /// eviction, victims are the min-effective-priority residents (`total_cmp`, `ExprId`
    /// tie-break; a dead/`None`-priority resident sorts as -infinity, evicted first). If
    /// even the weakest resident's priority is >= the admitting occurrence's priority (or
    /// there isn't enough to evict), admission is SKIPPED — no partial eviction.
    fn try_admit(&mut self, v: ExprId, field: OperandField) -> bool {
        let Some(ds) = &mut self.decisions else { return false };
        let Some(admitting_priority) = ds.streams.effective_priority(v) else {
            return false; // no remaining occurrence: not worth caching
        };
        let need = resident_width(field);
        let used: usize = ds.resident.values().copied().map(resident_width).sum();
        if used + need <= ds.budget {
            ds.resident.insert(v, field);
            self.defined.insert(v);
            return true;
        }

        // Over budget: rank eviction candidates ascending by (effective priority, ExprId).
        let mut candidates: Vec<(f64, ExprId, OperandField)> = ds
            .resident
            .iter()
            .map(|(&id, &f)| {
                let p = ds.streams.effective_priority(id).unwrap_or(f64::NEG_INFINITY);
                (p, id, f)
            })
            .collect();
        candidates.sort_by(|a, b| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1)));

        let mut freed = 0usize;
        let mut to_evict: Vec<ExprId> = Vec::new();
        for (priority, id, f) in candidates {
            if used + need <= ds.budget + freed {
                break;
            }
            if priority >= admitting_priority {
                return false; // weakest remaining victim is at least as valuable: skip
            }
            freed += resident_width(f);
            to_evict.push(id);
        }
        if used + need > ds.budget + freed {
            return false; // ran out of candidates without freeing enough
        }
        for id in to_evict {
            ds.resident.remove(&id);
            self.defined.remove(&id);
        }
        ds.resident.insert(v, field);
        self.defined.insert(v);
        true
    }

    /// Finalize a just-produced value (its true value is now in the acc): decide whether
    /// it becomes resident (readable later as `Value(expr_id)`) or a one-off fresh temp,
    /// then evict it out of the acc into a cell. Returns the operand naming whichever cell
    /// it landed in.
    ///
    /// - `LegacyRecompute`/`Materialize`: static membership in `resident_target` (the
    ///   schedule's realized `resident_after` set; unchanged Task-1 behavior).
    /// - `Decisions`: `try_admit` (Task 3) — `resident_target` is ignored (always empty
    ///   under `Decisions`, since only the schedule-driven policies populate it).
    fn finalize_produced(
        &mut self,
        expr_id: ExprId,
        field: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> VirtualOp {
        let admitted = if matches!(self.policy, MaterializePolicy::Decisions { .. }) {
            self.try_admit(expr_id, field)
        } else {
            resident_target.contains(&expr_id)
        };
        if admitted {
            self.widths.insert(expr_id, field);
            self.emit_evict_to_cell(expr_id, field);
            self.defined.insert(expr_id); // idempotent under `Decisions` (try_admit already did this)
            VirtualOp::Value(expr_id)
        } else {
            let t = self.fresh_internal();
            self.widths.insert(t, field);
            self.emit_evict_to_cell(t, field);
            VirtualOp::Value(t)
        }
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
        // Task 3 (`Decisions` only, no-op otherwise): this call IS a demand site — one
        // occurrence off `expr_id`'s stream, consumed before any hit/miss branching so
        // `effective_priority` reflects the NEXT occurrence for any admission decision
        // taken below (`try_admit`'s precondition).
        self.serve_occurrence(expr_id);

        // 1. Truly defined-resident → serve from its cell (value-safe).
        if self.defined.contains(&expr_id) {
            return Ok(VirtualOp::Value(expr_id));
        }
        // 2. A source or resolution-pruned leaf resolves to one operand line. Under
        //    `Decisions`, a leaf can ALSO be admitted into residency (Task 3: caching
        //    isn't limited to compound recomputes — brief's `read_leaf_cacheable`) so a
        //    repeatedly-read DRAM/const/etc. leaf can be served from a cell later.
        if layer.resolutions.contains_key(&expr_id)
            || matches!(&layer.exprs[expr_id.0 as usize], Expr::Source(_))
        {
            let op = self.source_to_vop(layer, expr_id)?;
            if matches!(self.policy, MaterializePolicy::Decisions { .. }) {
                let field = child_operand_field(layer, expr_id, expected, &self.cross);
                if self.try_admit(expr_id, field) {
                    self.emit_init_field(op, field);
                    self.widths.insert(expr_id, field);
                    self.emit_evict_to_cell(expr_id, field);
                    self.defined.insert(expr_id);
                    return Ok(VirtualOp::Value(expr_id));
                }
            }
            return Ok(op);
        }
        // 3. Compound: recompute the cone into the acc, then finalize residency (Task 1
        //    schedule-driven `resident_target`, or Task 3 `Decisions` admission).
        let field = child_operand_field(layer, expr_id, expected, &self.cross);
        self.compile_expr_virtual(layer, expr_id, field, resident_target)?;
        self.materialize_if_root(expr_id, true);
        Ok(self.finalize_produced(expr_id, field, resident_target))
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
        // `Decisions` (Task 3) deliberately does NOT take the `compile_add_materialize`
        // branch: it reuses this SAME virtual/FMA-partition path as `LegacyRecompute` so
        // its admit/evict decisions replay in lock-step with `OccurrenceStreams::build`'s
        // demand order (which mirrors ONLY this path — see `decisions.rs`'s module doc).
        // Routing `Decisions` through `compile_add_materialize` instead would visit an
        // `Add`'s children in a DIFFERENT order (original encounter order, not
        // addends-before-products), silently misaligning `serve_occurrence` calls against
        // the precomputed streams and rotting the scorer's effective priorities.
        if matches!(self.policy, MaterializePolicy::Materialize) {
            return self.compile_add_materialize(layer, &children, expected, resident_target);
        }
        if self.try_compile_fma_virtual(layer, &children, expected, resident_target)?.is_some() {
            return Ok(());
        }
        self.compile_reduction_virtual(layer, &children, true, false, expected, resident_target)
    }

    /// A FUSABLE product (Global Constraint 2): a `Mul` that is a direct child of an
    /// `Add` in this layer and is NOT a cache root. Cache-root `Mul`s flow through the
    /// existing materialize/`Resident`/`Reload` path unchanged; only fusable products
    /// participate in the event-local cache-produce-vs-fuse decision.
    fn is_fusable_product(&self, layer: &DagLayer, p: ExprId) -> bool {
        matches!(layer.exprs[p.0 as usize], Expr::Mul(_))
            && self.add_child_exprs.contains(&p)
            && !self.cache_root_exprs.contains(&p)
    }

    /// Event-local per-step decision (Global Constraint 1): a fusable product `p` whose
    /// current step has BOTH a `Recompute` `Demand` for `p` and an `Admit{p}` event is
    /// CACHE-PRODUCED (`Mul`→cell). A `Recompute` without a same-step `Admit` fuses; a
    /// `Resident` read is served from `p`'s already-defined cell (the `defined` check).
    fn cache_produce_now(&self, p: ExprId) -> bool {
        self.admitted_this_step.contains(&p) && self.recompute_this_step.contains(&p)
    }

    /// Materialize-policy `Add` lowering (Global Constraints 1–5): split the fusable
    /// `Mul`-in-`Add` children by their event-local decision. CACHE-PRODUCE products are
    /// emitted FIRST as real `Mul`→cell (`defines = p`, TRUE signed value); already-cached
    /// (`Resident`/defined) fusable products are read as `Value(p)` addends (the cell holds
    /// the signed value, so their contribution sign is `Plus`); remaining fusable products
    /// FUSE (`Fma`) exactly as the legacy path. Non-fusable (cache-root) binary products
    /// keep the legacy fuse resolution. Then plain addends fold in, then the fused `Fma`s.
    fn compile_add_materialize(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        expected: OperandField,
        resident_target: &HashSet<ExprId>,
    ) -> Result<(), CompileError> {
        // Cache-produce products: (sign, p, p-field, lhs-field, lhs-op, rhs-field, rhs-op).
        let mut cache_produce: Vec<(
            Sign,
            ExprId,
            OperandField,
            OperandField,
            VirtualOp,
            OperandField,
            VirtualOp,
        )> = Vec::new();
        // Fused products: (sign, lhs-field, lhs-op, rhs-field, rhs-op).
        let mut fused: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)> = Vec::new();
        // Plain addends + resident-read fusable products: (field, op, sign).
        let mut addend_ops: Vec<(OperandField, VirtualOp, Sign)> = Vec::new();

        // Lower every operand up front (a compound child clobbers the acc during its own
        // lowering, so all operand deliveries must precede the acc-based emission below).
        for &c in children {
            match classify_additive_child(layer, c) {
                AdditiveChild::Product { sign, lhs, rhs } => {
                    let fusable = self.is_fusable_product(layer, c);
                    if fusable && self.defined.contains(&c) {
                        // Already cached (this step's `Resident`, or an earlier cache-produce):
                        // the cell holds `p`'s TRUE signed value, so add it with sign `Plus`.
                        let f = child_operand_field(layer, c, expected, &self.cross);
                        let op = self.lower_operand_virtual(layer, c, expected, resident_target)?;
                        addend_ops.push((f, op, Sign::Plus));
                    } else if fusable && self.cache_produce_now(c) {
                        let pf = child_operand_field(layer, c, expected, &self.cross);
                        let lf = child_operand_field(layer, lhs, expected, &self.cross);
                        let rf = child_operand_field(layer, rhs, expected, &self.cross);
                        let lhs_op =
                            self.lower_operand_virtual(layer, lhs, expected, resident_target)?;
                        let rhs_op =
                            self.lower_operand_virtual(layer, rhs, expected, resident_target)?;
                        cache_produce.push((sign, c, pf, lf, lhs_op, rf, rhs_op));
                    } else {
                        // Fuse: a fusable product without a cache-produce decision, or a
                        // cache-root binary product (kept on the legacy fuse resolution).
                        let lf = child_operand_field(layer, lhs, expected, &self.cross);
                        let rf = child_operand_field(layer, rhs, expected, &self.cross);
                        let lhs_op =
                            self.lower_operand_virtual(layer, lhs, expected, resident_target)?;
                        let rhs_op =
                            self.lower_operand_virtual(layer, rhs, expected, resident_target)?;
                        fused.push((sign, lf, lhs_op, rf, rhs_op));
                    }
                }
                AdditiveChild::Addend { sign, id } => {
                    let f = child_operand_field(layer, id, expected, &self.cross);
                    let op = self.lower_operand_virtual(layer, id, expected, resident_target)?;
                    addend_ops.push((f, op, sign));
                }
            }
        }

        // ── Seed the accumulator: CACHE-PRODUCE products FIRST (empty-acc, Constraint 4). ──
        let mut acc_field = OperandField::Base;
        let mut seeded = false;
        for (i, (sign, p, pf, lf, lhs_op, rf, rhs_op)) in cache_produce.iter().enumerate() {
            if i > 0 {
                // Offload the live partial to a fresh temp, produce this product, add back.
                // The temp holds the PREVIOUS accumulator, so it must be evicted AND folded
                // back at the accumulator's OWN field (`acc_field`) — NOT this product's
                // field (`*pf`), which can differ (e.g. base×base vs a product with an Ext
                // factor). `acc_field` is still the pre-product field here (it is only
                // widened at the end of the iteration, after this fold).
                let partial_field = acc_field;
                let t = self.fresh_internal();
                self.widths.insert(t, partial_field);
                self.emit_evict_to_cell(t, partial_field);
                self.produce_product_into_acc(*sign, *lf, lhs_op, *rf, rhs_op);
                self.widths.insert(*p, *pf);
                self.emit_evict_to_cell(*p, *pf);
                self.defined.insert(*p);
                self.push_fold(partial_field, vec![VirtualOp::Value(t)], true, Sign::Plus);
            } else {
                self.produce_product_into_acc(*sign, *lf, lhs_op, *rf, rhs_op);
                self.widths.insert(*p, *pf);
                self.emit_evict_to_cell(*p, *pf);
                self.defined.insert(*p);
                seeded = true;
            }
            if *pf == OperandField::Ext {
                acc_field = OperandField::Ext;
            }
        }

        // If no cache-produce seeded the acc, seed from an addend, else from a fused product.
        let mut seed_addend: Option<usize> = None;
        if !seeded {
            if !addend_ops.is_empty() {
                seed_addend = Some(self.seed_from_addends(&addend_ops));
            } else if !fused.is_empty() {
                let s = fused.iter().position(|(sg, ..)| *sg == Sign::Plus).unwrap_or(0);
                let (ssign, lf0, lhs0, rf0, rhs0) = fused.remove(s);
                self.produce_product_into_acc(ssign, lf0, &lhs0, rf0, &rhs0);
            } else {
                // Degenerate (all children filtered to zero): value-safe 0.
                self.emit_init_field(
                    VirtualOp::Ldc { sub: LdcSub::Special, idx: Special::Zero as u16 },
                    OperandField::Base,
                );
            }
        }

        // Fold the (non-seed) addends into the acc, then the remaining FUSED products.
        self.fold_addends_into_acc(&addend_ops, seed_addend)?;
        self.emit_fma_products(fused);
        Ok(())
    }

    /// Pick + emit the accumulator seed among `addend_ops` (a Base-Plus term, else any
    /// Plus, else any Base, else the first), applying a `Minus` seed as a unary negate.
    /// Returns the chosen seed index. Precondition: `addend_ops` is non-empty. Shared by
    /// `try_compile_fma_virtual` and `compile_add_materialize` (one seed heuristic).
    fn seed_from_addends(&mut self, addend_ops: &[(OperandField, VirtualOp, Sign)]) -> usize {
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
        seed
    }

    /// Fold `addend_ops` (skipping the already-seeded `skip` index, if any) into the acc,
    /// grouped by (field, sign) so each homogeneous group is one ADD (MAX_ARITY-split).
    /// Shared by `try_compile_fma_virtual` and `compile_add_materialize`.
    fn fold_addends_into_acc(
        &mut self,
        addend_ops: &[(OperandField, VirtualOp, Sign)],
        skip: Option<usize>,
    ) -> Result<(), CompileError> {
        let mut base_plus: Vec<VirtualOp> = Vec::new();
        let mut base_minus: Vec<VirtualOp> = Vec::new();
        let mut ext_plus: Vec<VirtualOp> = Vec::new();
        let mut ext_minus: Vec<VirtualOp> = Vec::new();
        for (i, (f, op, s)) in addend_ops.iter().enumerate() {
            if Some(i) == skip {
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
        Ok(())
    }

    /// Fold binary products into the acc as FMA pairs, canonicalized (H5) and grouped by
    /// (field_lhs, field_rhs, sign) so commutative same-shape pairs share one chunked FMA.
    /// Shared by `try_compile_fma_virtual` and `compile_add_materialize`.
    fn emit_fma_products(
        &mut self,
        products: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)>,
    ) {
        use std::collections::BTreeMap;
        let mut groups: BTreeMap<(u8, u8, u8), Vec<(VirtualOp, VirtualOp)>> = BTreeMap::new();
        for (sign, lf, lhs_op, rf, rhs_op) in products {
            let ((cf_l, cf_r), (op_l, op_r)) = canonical_fma_pair_v(lf, rf, lhs_op, rhs_op);
            groups.entry((cf_l as u8, cf_r as u8, sign as u8)).or_default().push((op_l, op_r));
        }
        for ((lf, rf, sign), gpairs) in groups {
            self.push_fma_chunked(field_from_u8(lf), field_from_u8(rf), sign_from_u8(sign), gpairs);
        }
    }

    /// Compute `lhs*rhs` into the (empty) accumulator, applying a leading `-1` as a
    /// unary negate so the acc holds the product's TRUE signed value (Constraints 3/4).
    fn produce_product_into_acc(
        &mut self,
        sign: Sign,
        lf: OperandField,
        lhs_op: &VirtualOp,
        rf: OperandField,
        rhs_op: &VirtualOp,
    ) {
        self.emit_init_field(lhs_op.clone(), lf);
        self.emit(VInstr::Mul {
            field: rf,
            reads: vec![rhs_op.clone()],
            defines: None,
            is_dram_read: is_dram_op(rhs_op),
        });
        if sign == Sign::Minus {
            self.emit_unary_negate();
        }
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
                let seed = self.seed_from_addends(&addend_ops);
                self.fold_addends_into_acc(&addend_ops, Some(seed))?;
                lo
            } else {
                let seed = lo.iter().position(|(s, ..)| *s == Sign::Plus).unwrap_or(0);
                let (seed_sign, lf0, lhs0_op, rf0, rhs0_op) = lo[seed].clone();
                self.produce_product_into_acc(seed_sign, lf0, &lhs0_op, rf0, &rhs0_op);
                if lo.len() == 1 {
                    return Ok(Some(()));
                }
                let mut rest = lo;
                rest.remove(seed);
                rest
            };

        self.emit_fma_products(fma_lo);
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
    policy: MaterializePolicy,
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

    // Layer-global fusability inputs (Global Constraint 2): the set of exprs that appear
    // as a direct child of some `Add`, and the set of cache-root exprs (never fusable).
    let mut add_child_exprs: HashSet<ExprId> = HashSet::new();
    for e in &layer.exprs {
        if let Expr::Add(children) = e {
            add_child_exprs.extend(children.iter().copied());
        }
    }
    let mut cache_root_exprs: HashSet<ExprId> = HashSet::new();
    for root in &layer.roots {
        if let Some(SinkInfo { kind: SinkKind::Cache { .. }, .. }) = &root.materialize {
            cache_root_exprs.insert(root.expr);
        }
    }

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

    // Task 3: under `Decisions`, precompute the demand-order occurrence streams ONCE
    // (mirrors the emitter's actual `Add`/`Mul` virtual-lowering traversal — see
    // `decisions.rs`'s module doc) before `policy` is moved into `st` below.
    let decisions_state = match &policy {
        MaterializePolicy::Decisions { decisions, budget } => Some(DecisionsState {
            streams: OccurrenceStreams::build(layer, &schedule.order, decisions),
            resident: BTreeMap::new(),
            budget: *budget,
        }),
        MaterializePolicy::LegacyRecompute | MaterializePolicy::Materialize => None,
    };

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
        policy,
        add_child_exprs,
        cache_root_exprs,
        admitted_this_step: HashSet::new(),
        recompute_this_step: HashSet::new(),
        decisions: decisions_state,
    };

    let mut resident_realized: Vec<(Vec<ExprId>, Vec<ExprId>)> =
        Vec::with_capacity(schedule.order.len());

    for (p, &rid) in schedule.order.iter().enumerate() {
        st.cur_step = p;

        // Step-boundary residency inputs. ONLY the `Materialize` arm reads the schedule's
        // `StepPlan` residency sets and events (the arm — and the reads — go away in a
        // later task). `LegacyRecompute` is BLIND to `schedule.steps`: empty-rb semantics
        // unconditionally, i.e. `st.defined` is cleared at every step boundary (pure
        // per-step recompute).
        let mut rb: HashSet<ExprId> = HashSet::new();
        let mut ra: HashSet<ExprId> = HashSet::new();

        // Under `Materialize`, derive the event-local decision inputs for this step from
        // its `Admit`/`Demand` events (authoritative — NOT `resident_after`, Constraint 1).
        // `LegacyRecompute` leaves these empty, so `compile_add_materialize` never fires.
        if matches!(st.policy, MaterializePolicy::Materialize) {
            let step = &schedule.steps[p];
            rb = step.resident_before.iter().copied().collect();
            ra = step.resident_after.iter().copied().collect();
            let mut admitted: HashSet<ExprId> = HashSet::new();
            let mut recompute: HashSet<ExprId> = HashSet::new();
            for ev in &step.events {
                match ev {
                    ReplayEvent::Admit { value } => {
                        admitted.insert(*value);
                    }
                    ReplayEvent::Demand { value, kind, .. } => match kind {
                        DemandKind::Recompute => {
                            recompute.insert(*value);
                        }
                        DemandKind::Reload => {
                            // Constraint 5: a fusable (`Intermediate`) product is never
                            // reloaded — reloadability is a cache-root-only property.
                            debug_assert!(
                                !st.is_fusable_product(layer, *value),
                                "Reload demand targets fusable Intermediate product {}",
                                value.0
                            );
                        }
                        DemandKind::Resident => {}
                    },
                    ReplayEvent::Evict { .. } => {}
                }
            }
            st.admitted_this_step = admitted;
            st.recompute_this_step = recompute;
        }

        // Drop values the schedule no longer keeps resident entering this step (implicit
        // cone-fit drops + explicit evicts, realized as a set difference). This bounds
        // the served/held set to the schedule's residency so cell pressure tracks the
        // (validated ≤ budget) plan — we never serve a value whose cell may be reused.
        // Task 3: `Decisions` residency is NOT schedule-step-scoped — it persists across
        // root/step boundaries under its OWN admission/eviction bookkeeping (`try_admit`),
        // so it is exempt from this per-step clear (`rb` is meaningless under `Decisions`,
        // which never populates it).
        if !matches!(st.policy, MaterializePolicy::Decisions { .. }) {
            st.defined.retain(|v| rb.contains(v));
        }
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
                    // Task 3: a root's own output is itself a demand site (mirrors
                    // `decisions.rs::build`'s `SiteConsumer::RootOutput` push) — served
                    // exactly once here, hit or miss, before branching on residency.
                    if matches!(st.policy, MaterializePolicy::Decisions { .. }) {
                        st.serve_occurrence(expr);
                    }
                    if st.defined.contains(&expr) {
                        st.materialize_if_root(expr, false);
                    } else {
                        st.compile_expr_virtual(layer, expr, expected, &ra)?;
                        st.materialize_if_root(expr, true);
                        let field = child_operand_field(layer, expr, expected, &st.cross);
                        let admit = if matches!(st.policy, MaterializePolicy::Decisions { .. }) {
                            st.try_admit(expr, field)
                        } else {
                            ra.contains(&expr) && !st.defined.contains(&expr)
                        };
                        if admit {
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
