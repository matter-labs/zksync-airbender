//! Schedule-driven lowering to virtual forward-VM instructions.
//!
//! Resident values are addressed symbolically until placement assigns cells.
//! Nonresident compounds are recomputed from their cones; sources and resolved
//! leaves read their backing directly. Cache roots are materialized when their
//! shared expression is produced.

use std::collections::{HashMap, HashSet};

use gkr_eval_ir::{DagLayer, Expr, ExprId, ReadPlace, RootId, SourceKind};

use crate::forward::artifact::ForwardLayerArtifact;
use crate::forward::BABYBEAR_NEG_ONE;

use super::super::context::DagForwardContext;
use super::super::isa::{LdcSub, MovDir, OperandField, Sign, Special, MAX_ARITY};
use super::arith::{
    child_operand_field, classify_additive_child, is_constant_one, is_neg_one_factor, is_zero_expr,
    AdditiveChild,
};
use super::decisions::{OccurrenceStreams, SiteDecisions};
use super::place::{ValueId, VirtualOp};
use crate::forward::compile::CompileError;

fn bucket_ops(ops: &[(OperandField, VirtualOp, Sign)], skip: usize) -> [Vec<VirtualOp>; 4] {
    let mut groups = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
    for (index, (field, op, sign)) in ops.iter().enumerate() {
        if index == skip {
            continue;
        }
        let group = match (field, sign) {
            (OperandField::Base, Sign::Plus) => 0,
            (OperandField::Base, Sign::Minus) => 1,
            (OperandField::Ext, Sign::Plus) => 2,
            (OperandField::Ext, Sign::Minus) => 3,
        };
        groups[group].push(*op);
    }
    groups
}

/// State for decision-driven admission and eviction.
struct DecisionsState {
    streams: OccurrenceStreams,
    resident: HashMap<ExprId, OperandField>,
    budget: usize,
    /// Lanes claimed by residents and pending temporaries.
    live_width: usize,
    /// Temporaries awaiting their single consuming read.
    pending_temps: HashSet<ValueId>,
    /// Deferred reads that prevent eviction of their resident value.
    pending_reads: HashMap<ValueId, usize>,
    /// Current value identity for re-admitted expressions.
    generation: HashMap<ExprId, ValueId>,
}

#[derive(Clone, Copy)]
struct Materialization {
    root: RootId,
    slot: u8,
    col: u16,
    field: OperandField,
    cache_only: bool,
}

#[derive(Clone, Copy)]
enum MaterializationSource {
    Accumulator,
    Operand(VirtualOp),
}

/// A virtual destination: a symbolic cell (`ValueId`) or a committed materialize write.
#[derive(Clone, Copy, Debug)]
pub(crate) enum VDst {
    Cell(ValueId),
    GlobalMaterialize { slot: u8, col: u16 },
}

/// A virtual instruction with symbolic resident values and direct source operands.
#[derive(Debug)]
pub(crate) enum VInstr {
    Add {
        field: OperandField,
        sign: Sign,
        reads: Vec<VirtualOp>,
    },
    Mul {
        field: OperandField,
        reads: Vec<VirtualOp>,
    },
    Fma {
        field_lhs: OperandField,
        field_rhs: OperandField,
        sign: Sign,
        pairs: Vec<(VirtualOp, VirtualOp)>,
    },
    Mov {
        dir: MovDir,
        field: OperandField,
        dst: Option<VDst>,
        src: Option<VirtualOp>,
    },
}

impl VInstr {
    pub(crate) fn defines(&self) -> Option<ValueId> {
        match self {
            VInstr::Mov {
                dir: MovDir::DstFromAcc | MovDir::DstFromSrc,
                dst: Some(VDst::Cell(value)),
                ..
            } => Some(*value),
            _ => None,
        }
    }

    pub(crate) fn for_each_read(&self, mut f: impl FnMut(&VirtualOp)) {
        match self {
            VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => reads.iter().for_each(f),
            VInstr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    f(lhs);
                    f(rhs);
                }
            }
            VInstr::Mov { src, .. } => {
                if let Some(src) = src {
                    f(src);
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// The schedule-walking virtual lowerer.
// ─────────────────────────────────────────────────────────────────────────────────

struct VirtualLower<'a> {
    ctx: &'a mut DagForwardContext,
    cross: &'a HashMap<ReadPlace, gkr_eval_ir::FieldKind>,
    out: Vec<VInstr>,
    widths: HashMap<ValueId, OperandField>,
    next_internal: u32,
    materializations: HashMap<ExprId, Vec<Materialization>>,
    exposed: Vec<bool>,
    decisions: DecisionsState,
}

impl<'a> VirtualLower<'a> {
    fn emit(&mut self, vi: VInstr) {
        // Demand-driven eviction (Decisions only): this instruction's `reads` is the
        // exact set `place::compute_live_ranges` will scan too — release any pending
        // temp the instant its one-and-only consuming read appears here, so the
        // tracker's live_width tracks the SAME instant `plan_placement` will treat as
        // that temp's `last_use`.
        let ds = &mut self.decisions;
        if !ds.pending_temps.is_empty() || !ds.pending_reads.is_empty() {
            vi.for_each_read(|op| {
                if let VirtualOp::Value(id) = op {
                    if let Some(cnt) = ds.pending_reads.get_mut(id) {
                        *cnt -= 1;
                        if *cnt == 0 {
                            ds.pending_reads.remove(id);
                        }
                    }
                    if ds.pending_temps.remove(id) {
                        let width = self
                            .widths
                            .get(id)
                            .expect("pending temp must have a recorded width")
                            .lanes();
                        ds.live_width -= width;
                    }
                }
            });
        }
        self.out.push(vi);
    }

    /// Register a `VirtualOp::Value(id)` about to be returned to a caller that will
    /// consume it LATER (not inline) — increments `pending_reads[id]` so
    /// `evict_to_fit` won't pick `id` as an eviction victim while this reference is
    /// still outstanding (see `pending_reads`'s doc). The single choke point for
    /// every `Value`-producing exit of `lower_operand_virtual`/`finalize_produced`.
    fn defer_read(&mut self, id: ValueId) -> VirtualOp {
        *self.decisions.pending_reads.entry(id).or_insert(0) += 1;
        VirtualOp::Value(id)
    }

    fn fresh_internal(&mut self) -> ValueId {
        let id = ExprId(self.next_internal);
        self.next_internal += 1;
        id
    }

    // ── operand seeding / evict primitives ────────────────────────────────────────

    fn emit_init_field(&mut self, op: VirtualOp, field: OperandField) {
        self.emit(VInstr::Mov {
            dir: MovDir::AccFromSrc,
            field,
            dst: None,
            src: Some(op),
        });
    }

    /// Pure accumulator negation, encoded as a zero-arity `Mul`.
    fn emit_unary_negate(&mut self) {
        self.emit(VInstr::Mul {
            field: OperandField::Base,
            reads: vec![],
        });
    }

    /// `Mov DstFromAcc Cell(v)` — define `v` into a cell (the residency/temp evict).
    fn emit_evict_to_cell(&mut self, v: ValueId, field: OperandField) {
        self.emit(VInstr::Mov {
            dir: MovDir::DstFromAcc,
            field,
            dst: Some(VDst::Cell(v)),
            src: None,
        });
    }

    // ── Decision-driven residency ────────────────────────────────────────────────

    /// Consume one occurrence from `v`'s demand stream before hit/miss handling.
    fn serve_occurrence(&mut self, v: ExprId) {
        self.decisions.streams.serve(v);
    }

    fn try_admit(&mut self, v: ExprId, field: OperandField) -> Option<ValueId> {
        let admitting_priority = self.decisions.streams.effective_priority(v)?;
        let need = field.lanes();
        if !self.evict_to_fit(need, Some(admitting_priority)) {
            return None;
        }
        let evicted_before = self.decisions.generation.contains_key(&v);
        let gen_id = if evicted_before {
            self.fresh_internal()
        } else {
            v
        };
        let ds = &mut self.decisions;
        ds.resident.insert(v, field);
        ds.generation.insert(v, gen_id);
        ds.live_width += need;
        Some(gen_id)
    }

    /// Current serving value for a resident expression.
    fn current_value_id(&self, real: ExprId) -> ValueId {
        if let Some(g) = self.decisions.generation.get(&real).copied() {
            return g;
        }
        real
    }

    /// Free `need` lanes by evicting the lowest-priority eligible residents.
    /// Admissions do not evict an equally valuable resident; mandatory
    /// temporaries ignore that priority cutoff.
    fn evict_to_fit(&mut self, need: usize, admitting_priority: Option<f64>) -> bool {
        let ds = &self.decisions;
        if ds.live_width + need <= ds.budget {
            return true;
        }
        // Exclude any resident with an outstanding deferred-consumption reference
        // (`pending_reads` > 0): a sibling child already resolved a `Value(id)` read
        // for it that is still queued for a LATER emission (see `pending_reads`'s
        // doc). Evicting it now would free width the tracker would then hand out to
        // something else, while `plan_placement` still holds `id` live through that
        // later read — a genuine underestimate. Skipping it here costs nothing but a
        // possibly-suboptimal victim choice; it is never a correctness gap. The
        // pending-reads lookup is keyed by the CURRENT generation id (`generation`),
        // not the real `ExprId`, since that is what `defer_read` incremented against.
        let mut candidates: Vec<(f64, ExprId, OperandField)> = ds
            .resident
            .iter()
            .filter(|&(&id, _)| {
                let gen_id = ds.generation.get(&id).copied().unwrap_or(id);
                ds.pending_reads.get(&gen_id).copied().unwrap_or(0) == 0
            })
            .map(|(&id, &f)| {
                let p = ds
                    .streams
                    .effective_priority(id)
                    .unwrap_or(f64::NEG_INFINITY);
                (p, id, f)
            })
            .collect();
        candidates.sort_by(|a, b| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1)));

        let budget = ds.budget;
        let live_width = ds.live_width;
        let mut freed = 0usize;
        let mut to_evict: Vec<(ExprId, OperandField)> = Vec::new();
        for (priority, id, f) in candidates {
            if live_width - freed + need <= budget {
                break;
            }
            if let Some(admitting_priority) = admitting_priority {
                if priority >= admitting_priority {
                    return false; // weakest remaining victim is at least as valuable: skip
                }
            }
            freed += f.lanes();
            to_evict.push((id, f));
        }
        if live_width - freed + need > budget {
            return false; // ran out of candidates without freeing enough
        }
        let ds = &mut self.decisions;
        for (id, f) in to_evict {
            ds.resident.remove(&id);
            ds.live_width -= f.lanes();
        }
        true
    }

    /// Allocate a required expression temporary, evicting residents until it fits.
    fn alloc_temp_evicting(&mut self, field: OperandField) -> Result<ValueId, CompileError> {
        let need = field.lanes();
        if !self.evict_to_fit(need, None) {
            return Err(CompileError::BudgetBelowFloor {
                floor: self.decisions.live_width + need,
                budget: self.decisions.budget,
            });
        }
        let t = self.fresh_internal();
        self.widths.insert(t, field);
        self.decisions.live_width += field.lanes();
        self.decisions.pending_temps.insert(t);
        self.emit_evict_to_cell(t, field);
        Ok(t)
    }

    /// Store a produced value in a resident cell or one-use temporary.
    fn finalize_produced(
        &mut self,
        expr_id: ExprId,
        field: OperandField,
    ) -> Result<VirtualOp, CompileError> {
        let admitted = self.try_admit(expr_id, field);
        if let Some(gen_id) = admitted {
            self.widths.insert(gen_id, field);
            self.emit_evict_to_cell(gen_id, field);
            Ok(self.defer_read(gen_id))
        } else {
            let t = self.alloc_temp_evicting(field)?;
            Ok(self.defer_read(t))
        }
    }

    fn push_fold(&mut self, field: OperandField, ops: Vec<VirtualOp>, is_add: bool, sign: Sign) {
        if is_add {
            self.emit(VInstr::Add {
                field,
                sign,
                reads: ops,
            });
        } else {
            self.emit(VInstr::Mul { field, reads: ops });
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
            self.emit(VInstr::Fma {
                field_lhs,
                field_rhs,
                sign,
                pairs: chunk.to_vec(),
            });
        }
    }

    fn intern_virtual_setup(&mut self, kind: gkr_eval_ir::VirtualSetupKind) -> u16 {
        self.ctx
            .specials
            .intern(super::super::source::SpecialStrategy::VirtualSetup { kind })
    }

    fn intern_top_bits(&mut self, reference: gkr_eval_ir::InitsAndTeardownsTopBitsRef) -> u16 {
        self.ctx
            .specials
            .intern(super::super::source::SpecialStrategy::InitsAndTeardownsTopBits { reference })
    }

    fn intern_resolution(&mut self, layer: &DagLayer, expr_id: ExprId) -> u16 {
        let strategy = layer
            .resolutions
            .get(&expr_id)
            .expect("resolution must exist");
        self.ctx
            .specials
            .intern(super::super::source::lower_resolution(strategy))
    }

    fn operand_field(&self, layer: &DagLayer, id: ExprId) -> OperandField {
        child_operand_field(layer, id, self.cross)
    }

    // ── source resolution (residency-free; mirrors arith::source_to_operand arms) ──

    fn source_to_vop(
        &mut self,
        layer: &DagLayer,
        expr_id: ExprId,
    ) -> Result<VirtualOp, CompileError> {
        if layer.resolutions.contains_key(&expr_id) {
            let desc = self.intern_resolution(layer, expr_id);
            return Ok(VirtualOp::Special { desc });
        }
        let Expr::Source(src_id) = &layer.exprs[expr_id.0 as usize] else {
            unreachable!("source_to_vop requires a source or resolution")
        };
        match &layer.sources[src_id.0 as usize] {
            SourceKind::Read { place } => {
                let field = super::read_place_operand_field(place, self.cross);
                let (slot, col) = self.ctx.backings.read_slot_col(place, field)?;
                Ok(VirtualOp::Global { slot, col })
            }
            SourceKind::VirtualSetup { kind } => {
                let desc = self.intern_virtual_setup(*kind);
                Ok(VirtualOp::Special { desc })
            }
            SourceKind::InitsAndTeardownsTopBits { reference } => {
                let desc = self.intern_top_bits(*reference);
                Ok(VirtualOp::Special { desc })
            }
            SourceKind::Constant { value } => match *value {
                0 => Ok(VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::Zero as u16,
                }),
                1 => Ok(VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::One as u16,
                }),
                v if v == BABYBEAR_NEG_ONE => Ok(VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::NegOne as u16,
                }),
                v => {
                    let idx = self.ctx.consts.intern(v);
                    Ok(VirtualOp::Ldc {
                        sub: LdcSub::Const,
                        idx,
                    })
                }
            },
            SourceKind::Challenge { reference } => {
                let (sub, idx) = self
                    .ctx
                    .derived_e4
                    .intern(reference)
                    .ok_or(CompileError::UnsupportedChallenge(*reference))?;
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
    ) -> Result<VirtualOp, CompileError> {
        // Advance this value's demand stream before making admission decisions.
        self.serve_occurrence(expr_id);

        // 1. Serve resident values from their current generation.
        if self.decisions.resident.contains_key(&expr_id) {
            let gen_id = self.current_value_id(expr_id);
            return Ok(self.defer_read(gen_id));
        }
        // 2. Resolve a source or pruned leaf, optionally admitting it.
        if layer.resolutions.contains_key(&expr_id)
            || matches!(&layer.exprs[expr_id.0 as usize], Expr::Source(_))
        {
            let op = self.source_to_vop(layer, expr_id)?;
            let field = self.operand_field(layer, expr_id);
            if let Some(gen_id) = self.try_admit(expr_id, field) {
                self.emit_init_field(op, field);
                self.materialize(expr_id, MaterializationSource::Accumulator, true);
                self.widths.insert(gen_id, field);
                self.emit_evict_to_cell(gen_id, field);
                return Ok(self.defer_read(gen_id));
            }
            self.materialize(expr_id, MaterializationSource::Operand(op), true);
            return Ok(op);
        }
        // 3. Recompute a compound expression, then decide residency.
        let field = self.operand_field(layer, expr_id);
        self.compile_expr_virtual(layer, expr_id, field)?;
        self.materialize(expr_id, MaterializationSource::Accumulator, false);
        self.finalize_produced(expr_id, field)
    }

    // ── expression lowering into the accumulator (mirrors arith::compile_expr) ────

    fn compile_expr_virtual(
        &mut self,
        layer: &DagLayer,
        expr_id: ExprId,
        expected: OperandField,
    ) -> Result<(), CompileError> {
        if layer.resolutions.contains_key(&expr_id) {
            let desc = self.intern_resolution(layer, expr_id);
            let field = self.operand_field(layer, expr_id);
            self.emit_init_field(VirtualOp::Special { desc }, field);
            self.materialize(expr_id, MaterializationSource::Accumulator, true);
            return Ok(());
        }
        match &layer.exprs[expr_id.0 as usize] {
            Expr::Source(_) => {
                let field = self.operand_field(layer, expr_id);
                let op = self.source_to_vop(layer, expr_id)?;
                self.emit_init_field(op, field);
                self.materialize(expr_id, MaterializationSource::Accumulator, true);
                Ok(())
            }
            Expr::Add(children) => self.compile_add_virtual(layer, children, expected),
            Expr::Mul(children) => self.compile_mul_virtual(layer, children, expected),
        }
    }

    fn compile_add_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        expected: OperandField,
    ) -> Result<(), CompileError> {
        if children.is_empty() {
            self.emit_init_field(
                VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::Zero as u16,
                },
                expected,
            );
            return Ok(());
        }
        if self.try_compile_fma_virtual(layer, children)? {
            return Ok(());
        }
        self.compile_reduction_virtual(layer, children, true, false)
    }

    /// Pick + emit the accumulator seed among `addend_ops` (a Base-Plus term, else any
    /// Plus, else any Base, else the first), applying a `Minus` seed as a unary negate.
    /// Returns the chosen seed index. Precondition: `addend_ops` is non-empty.
    fn seed_from_addends(&mut self, addend_ops: &[(OperandField, VirtualOp, Sign)]) -> usize {
        let seed = addend_ops
            .iter()
            .position(|(f, _, s)| *f == OperandField::Base && *s == Sign::Plus)
            .or_else(|| addend_ops.iter().position(|(_, _, s)| *s == Sign::Plus))
            .or_else(|| {
                addend_ops
                    .iter()
                    .position(|(f, _, _)| *f == OperandField::Base)
            })
            .unwrap_or(0);
        self.emit_init_field(addend_ops[seed].1, addend_ops[seed].0);
        if addend_ops[seed].2 == Sign::Minus {
            self.emit_unary_negate();
        }
        seed
    }

    fn fold_addends_into_acc(
        &mut self,
        addend_ops: &[(OperandField, VirtualOp, Sign)],
        skip: usize,
    ) -> Result<(), CompileError> {
        let [base_plus, base_minus, ext_plus, ext_minus] = bucket_ops(addend_ops, skip);
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

    /// Fold binary products grouped by operand fields and sign.
    fn emit_fma_products(
        &mut self,
        products: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)>,
    ) {
        use std::collections::BTreeMap;
        let mut groups: BTreeMap<(OperandField, OperandField, Sign), Vec<(VirtualOp, VirtualOp)>> =
            BTreeMap::new();
        for (sign, lf, lhs_op, rf, rhs_op) in products {
            let ((cf_l, cf_r), (op_l, op_r)) = canonical_fma_pair_v(lf, rf, lhs_op, rhs_op);
            groups
                .entry((cf_l, cf_r, sign))
                .or_default()
                .push((op_l, op_r));
        }
        for ((lf, rf, sign), gpairs) in groups {
            self.push_fma_chunked(lf, rf, sign, gpairs);
        }
    }

    /// Compute `lhs*rhs` into the (empty) accumulator, applying a leading `-1` as a
    /// unary negate so the accumulator holds the signed product.
    fn produce_product_into_acc(
        &mut self,
        sign: Sign,
        lf: OperandField,
        lhs_op: &VirtualOp,
        rf: OperandField,
        rhs_op: &VirtualOp,
    ) {
        self.emit_init_field(*lhs_op, lf);
        self.emit(VInstr::Mul {
            field: rf,
            reads: vec![*rhs_op],
        });
        if sign == Sign::Minus {
            self.emit_unary_negate();
        }
    }

    fn compile_mul_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        expected: OperandField,
    ) -> Result<(), CompileError> {
        // A zero factor annihilates the product.
        if children.iter().any(|&c| is_zero_expr(layer, c)) {
            self.emit_init_field(
                VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::Zero as u16,
                },
                expected,
            );
            return Ok(());
        }
        let factors: Vec<ExprId> = children
            .iter()
            .copied()
            .filter(|&c| !is_constant_one(layer, c))
            .collect();
        if factors.is_empty() {
            // Product of only `1`s = 1.
            self.emit_init_field(
                VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::One as u16,
                },
                expected,
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
            // Product of only `-1`s = ±1.
            self.emit_init_field(
                VirtualOp::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::One as u16,
                },
                expected,
            );
            if negate {
                self.emit_unary_negate();
            }
            return Ok(());
        }
        self.compile_reduction_virtual(layer, &surviving, false, negate)
    }

    /// Field-homogeneous reduction.
    fn compile_reduction_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        is_add: bool,
        negate: bool,
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
            let field = self.operand_field(layer, to_lower);
            let op = self.lower_operand_virtual(layer, to_lower)?;
            ops.push((field, op, sign));
        }

        let init_idx = self.seed_from_addends(&ops);

        if ops.len() == 1 {
            if negate {
                self.emit_unary_negate();
            }
            return Ok(());
        }

        let [base_plus, base_minus, ext_plus, ext_minus] = bucket_ops(&ops, init_idx);
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

    /// Emit one field-homogeneous group, spilling partial reductions when needed.
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
        let mut chunks = ops.chunks(MAX_ARITY);
        let first = chunks.next().expect("ops is non-empty");
        self.push_fold(field, first.to_vec(), is_add, Sign::Plus);
        for chunk in chunks {
            let t = self.alloc_temp_evicting(field)?;
            self.emit_init_field(chunk[0], field);
            if chunk.len() > 1 {
                self.push_fold(field, chunk[1..].to_vec(), is_add, Sign::Plus);
            }
            self.push_fold(field, vec![VirtualOp::Value(t)], is_add, Sign::Plus);
        }
        Ok(())
    }

    /// Lower an add containing at least one binary product.
    fn try_compile_fma_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
    ) -> Result<bool, CompileError> {
        let mut products: Vec<(Sign, ExprId, ExprId)> = Vec::with_capacity(children.len());
        let mut addends: Vec<(Sign, ExprId)> = Vec::new();
        for &c in children {
            match classify_additive_child(layer, c) {
                AdditiveChild::Product { sign, lhs, rhs } => products.push((sign, lhs, rhs)),
                AdditiveChild::Addend { sign, id } => addends.push((sign, id)),
            }
        }
        if products.is_empty() {
            return Ok(false);
        }
        let mut addend_ops: Vec<(OperandField, VirtualOp, Sign)> =
            Vec::with_capacity(addends.len());
        for &(sign, c) in &addends {
            let f = self.operand_field(layer, c);
            let op = self.lower_operand_virtual(layer, c)?;
            addend_ops.push((f, op, sign));
        }
        let mut lo: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)> =
            Vec::with_capacity(products.len());
        for &(sign, lhs, rhs) in &products {
            let lf = self.operand_field(layer, lhs);
            let rf = self.operand_field(layer, rhs);
            let lhs_op = self.lower_operand_virtual(layer, lhs)?;
            let rhs_op = self.lower_operand_virtual(layer, rhs)?;
            lo.push((sign, lf, lhs_op, rf, rhs_op));
        }

        // Seed the accumulator; `fma_lo` is the product set still to fold as FMA.
        let fma_lo: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)> =
            if !addend_ops.is_empty() {
                let seed = self.seed_from_addends(&addend_ops);
                self.fold_addends_into_acc(&addend_ops, seed)?;
                lo
            } else {
                let seed = lo.iter().position(|(s, ..)| *s == Sign::Plus).unwrap_or(0);
                let (seed_sign, lf0, lhs0_op, rf0, rhs0_op) = lo[seed];
                self.produce_product_into_acc(seed_sign, lf0, &lhs0_op, rf0, &rhs0_op);
                if lo.len() == 1 {
                    return Ok(true);
                }
                let mut rest = lo;
                rest.remove(seed);
                rest
            };

        self.emit_fma_products(fma_lo);
        Ok(true)
    }

    fn materialize(&mut self, expr_id: ExprId, source: MaterializationSource, cache_only: bool) {
        let Some(targets) = self.materializations.get(&expr_id).cloned() else {
            return;
        };
        for target in targets {
            if (cache_only && !target.cache_only) || self.exposed[target.root.0 as usize] {
                continue;
            }
            let (dir, src) = match &source {
                MaterializationSource::Accumulator => (MovDir::DstFromAcc, None),
                MaterializationSource::Operand(op) => (MovDir::DstFromSrc, Some(*op)),
            };
            self.emit(VInstr::Mov {
                dir,
                field: target.field,
                dst: Some(VDst::GlobalMaterialize {
                    slot: target.slot,
                    col: target.col,
                }),
                src,
            });
            self.exposed[target.root.0 as usize] = true;
        }
    }
}

/// Canonicalize a commutative FMA pair so mixed products are `(Base, Ext)`.
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

/// Lower scheduled roots to symbolic instructions.
pub(crate) fn lower_layer_virtual(
    layer: &DagLayer,
    schedule: &ForwardLayerArtifact,
    ctx: &mut DagForwardContext,
    cross: &HashMap<ReadPlace, gkr_eval_ir::FieldKind>,
    compute_roots: &std::collections::BTreeSet<RootId>,
    decisions: &SiteDecisions,
    budget: usize,
) -> Result<(Vec<VInstr>, HashMap<ValueId, OperandField>), CompileError> {
    // Cache-only roots are handled by the final sweep below.
    let atom_order = schedule.atom_order(layer);

    let mut materializations: HashMap<ExprId, Vec<Materialization>> = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        let rid = RootId(idx as u32);
        let Some(sink) = root.materialize.as_ref() else {
            continue;
        };
        if compute_roots.contains(&rid) {
            let (key, offset) = super::sink_to_backing(sink);
            // Dense per-slot renumbering via the SAME authority as reads, so the
            // GlobalMaterialize write and any later read of this value agree.
            let (slot, col) = ctx.backings.slot_col(key, offset)?;
            let field = super::operand_field_of(sink);
            materializations
                .entry(root.expr)
                .or_default()
                .push(Materialization {
                    root: rid,
                    slot,
                    col,
                    field,
                    cache_only: root.claim.is_none(),
                });
        }
    }

    let decisions_state = DecisionsState {
        streams: OccurrenceStreams::build(layer, &atom_order, compute_roots, decisions),
        resident: HashMap::new(),
        budget,
        live_width: 0,
        pending_temps: HashSet::new(),
        pending_reads: HashMap::new(),
        generation: HashMap::new(),
    };

    let mut st = VirtualLower {
        ctx,
        cross,
        out: Vec::new(),
        widths: HashMap::new(),
        next_internal: u32::try_from(layer.exprs.len()).expect("expression count fits u32"),
        materializations,
        exposed: vec![false; layer.roots.len()],
        decisions: decisions_state,
    };

    for &rid in &atom_order {
        if compute_roots.contains(&rid) && !st.exposed[rid.0 as usize] {
            let expr = layer.roots[rid.0 as usize].expr;
            let sink = layer.roots[rid.0 as usize]
                .materialize
                .as_ref()
                .expect("Compute root has a materialize sink");
            let expected = super::operand_field_of(sink);
            // A root output is one demand occurrence.
            st.serve_occurrence(expr);
            if st.decisions.resident.contains_key(&expr) {
                let value = VirtualOp::Value(st.current_value_id(expr));
                st.materialize(expr, MaterializationSource::Operand(value), false);
            } else {
                st.compile_expr_virtual(layer, expr, expected)?;
                st.materialize(expr, MaterializationSource::Accumulator, false);
                let field = st.operand_field(layer, expr);
                if let Some(gen_id) = st.try_admit(expr, field) {
                    st.widths.insert(gen_id, field);
                    st.emit_evict_to_cell(gen_id, field);
                }
            }
        }
    }

    // Expose compute roots not reached by the scheduled atom walk.
    let mut pending: Vec<ExprId> = st
        .materializations
        .iter()
        .filter(|(_, targets)| {
            targets
                .iter()
                .any(|target| !st.exposed[target.root.0 as usize])
        })
        .map(|(&e, _)| e)
        .collect();
    pending.sort_by_key(|e| e.0);
    for expr in pending {
        if st.decisions.resident.contains_key(&expr) {
            let value = VirtualOp::Value(st.current_value_id(expr));
            st.materialize(expr, MaterializationSource::Operand(value), false);
        } else {
            let field = st.operand_field(layer, expr);
            st.compile_expr_virtual(layer, expr, field)?;
            st.materialize(expr, MaterializationSource::Accumulator, false);
        }
    }

    Ok((st.out, st.widths))
}

// ─────────────────────────────────────────────────────────────────────────────────
