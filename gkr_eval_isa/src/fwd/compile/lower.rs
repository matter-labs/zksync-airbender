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
//! Value/admit model:
//!   - Track `defined: HashSet<ExprId>` — an `ExprId` is *defined-resident* once we have
//!     physically evicted its value into a cell (`Mov DstFromAcc Cell(v)`).
//!   - Serve an operand as `VirtualOp::Value(v)` ONLY when `v` is truly defined-resident
//!     (value-safe). A source / resolution leaf resolves to its backing / `Special`.
//!     Any other compound is RECOMPUTED by descending its cone (pure, value-safe) — we
//!     never read a stale cell, so value correctness is robust to reorder/drift.
//!   - `decisions: None` never admits into `defined` (every insert site is
//!     decisions-gated), so every step is pure recompute; schema v2 (Task 4) has no
//!     persisted per-step residency to realize from. `Some(&SiteDecisions)` (Task 3)
//!     instead owns residency across the whole layer via
//!     `SiteDecisions`/`OccurrenceStreams`-driven admit/evict (`try_admit`).
//!   - Cache (materialize-only) roots are committed to their `CacheOutput` sink when
//!     their shared `ExprId` is produced/recomputed, and exposed as `root_outputs` so
//!     the cache-value gate is non-vacuous.
//!
//! Arithmetic (fold splitting, FMA fusion, field-homogeneous grouping, `-1`/`0`
//! strength reduction, over-arity chunking) is a faithful re-implementation of
//! `arith.rs`'s PURE structure, reusing its pure helpers verbatim
//! (`child_operand_field`, `classify_additive_child`, `split_reduction`,
//! `field_from_u8`/`sign_from_u8`, `is_*` predicates). Only operand delivery differs.

use std::collections::{BTreeMap, HashMap, HashSet};

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
use super::decisions::{OccurrenceStreams, SiteDecisions};
use super::place::{ValueId, VInstrKind, VirtualInstr, VirtualOp};
use super::schedule::split_reduction;
use crate::fwd::compile::CompileError;

/// Width (in cells) of a value's residency footprint under the `Decisions` residency
/// policy (Task 3): `Base` = 1, `Ext` = 4 — mirrors `place::width_of`/the traffic-tally
/// convention used elsewhere in this crate (`mod.rs::tally_operand`).
fn resident_width(field: OperandField) -> usize {
    match field {
        OperandField::Base => 1,
        OperandField::Ext => 4,
    }
}

/// Task 3: `Decisions` residency state — present only when `VirtualLower::decisions`
/// is `Some`. `resident` is the width-weighted
/// resident set, a `BTreeMap` (per the brief's determinism requirement: eviction-candidate
/// enumeration must not depend on hash-iteration order). `VirtualLower::defined` mirrors
/// `resident`'s keys — `defined` stays the single policy-agnostic "is this value's cell
/// servable" source of truth read everywhere else in this file; `resident` is Decisions'
/// own bookkeeping for width/priority-driven admission and eviction.
struct DecisionsState {
    streams: OccurrenceStreams,
    resident: BTreeMap<ExprId, OperandField>,
    budget: usize,
    /// Authoritative running count of width-weighted cells currently claimed by
    /// EITHER a resident (`resident`'s values) OR an in-flight expression temp
    /// (`pending_temps`). This is the demand-driven eviction tracker (replaces the
    /// deleted static `resident_cap_for_order` pre-reservation): incremented at
    /// every `emit_evict_to_cell` (real ExprId admission or fresh internal temp),
    /// decremented when a temp's single consuming read is emitted (see
    /// `VirtualLower::emit`'s pending-temp release scan) or when a resident is
    /// force-evicted (`evict_to_fit`). Dead residents (occurrence stream
    /// exhausted) are NOT proactively released — they sort first
    /// (`f64::NEG_INFINITY` effective priority) whenever eviction next runs, which
    /// is a safe (conservative, never-underestimating) simplification: holding a
    /// dead resident a little longer than strictly necessary can only make the
    /// tracker MORE conservative relative to `plan_placement`'s independent
    /// liveness model, never less.
    live_width: usize,
    /// Fresh-internal temp `ValueId`s that have been evicted to a cell
    /// (`emit_evict_to_cell`) but not yet consumed by their one-and-only reading
    /// instruction. Every temp minted by `alloc_temp_evicting` is read exactly
    /// once (by construction of this emitter's fold/reduction call sites), so
    /// membership here is release-once: `VirtualLower::emit`'s reads-scan removes
    /// an entry (and its width from `live_width`) the instant it sees that temp
    /// read as a `VirtualOp::Value` operand — the SAME instruction
    /// `place::compute_live_ranges` will record as that value's `last_use`, so
    /// this tracker's per-temp interval exactly matches `plan_placement`'s.
    pending_temps: std::collections::HashSet<ValueId>,
    /// Outstanding deferred-consumption count for EVERY `VirtualOp::Value(id)`
    /// `lower_operand_virtual`/`finalize_produced` has returned to a caller but that
    /// caller has not yet emitted a consuming read for (`defer_read` increments;
    /// `VirtualLower::emit`'s reads-scan decrements, dropping the entry at 0).
    /// Tracked for BOTH temps and residents, but consulted only for residents:
    /// `evict_to_fit` must never pick a resident with a nonzero count as an
    /// eviction victim. Without this, a resident already resolved into a sibling
    /// child's pending operand slot (e.g. `compile_reduction_virtual`'s
    /// "pre-materialize every child" loop — child A resolves to a resident HIT,
    /// child B's compound lowering then triggers admission-or-temp eviction
    /// pressure) could be evicted while child A's fold instruction reading it is
    /// still queued for LATER emission: `plan_placement` will still see that value
    /// live through its real (later) `last_use` instruction regardless of this
    /// emitter's bookkeeping, so freeing its width immediately on eviction would
    /// be a genuine underestimate relative to `plan_placement` — exactly the
    /// invariant this whole tracker must not violate.
    pending_reads: std::collections::HashMap<ValueId, usize>,
    /// Real `ExprId`s ever evicted (admission-time or temp-pressure-forced) during
    /// this layer compile. No longer a re-admission ban (Task 8c lifted that
    /// restriction — see `generation`): it is consulted ONLY to decide whether the
    /// NEXT admission of this `ExprId` needs a fresh generation identity (it has a
    /// prior `defines` instruction already emitted) or can reuse the real `ExprId`
    /// as its own cell identity (this is its first-ever admission).
    evicted_ever: HashSet<ExprId>,
    /// Task 8c: `ExprId → current serving `ValueId`` indirection. A real `ExprId`'s
    /// FIRST admission serves as itself (`generation[v] == v`, the common case, kept
    /// out of this map implicitly — absence means "= v"). Every RE-admission (after
    /// an eviction recorded in `evicted_ever`) mints a fresh internal `ValueId`
    /// (`fresh_internal`, same disjoint-from-real-ExprId range fresh temps use) and
    /// records it here — so each generation gets its OWN `defines` instruction and
    /// its OWN short `[def, last_use]` interval under `plan_placement`'s
    /// `compute_live_ranges`, instead of one value acquiring a second `defines` that
    /// would collapse two disjoint generations into a single (possibly wider than
    /// tracked) span — the exact underestimate risk the deleted `never_readmit` ban
    /// existed to rule out structurally. Every resident-serving read (`defined`-hit
    /// in `lower_operand_virtual`, and `materialize_if_root`'s from-cell path) must
    /// go through `current_value_id` to read the CURRENT generation, not the real
    /// `ExprId`, once a value has ever been re-admitted.
    generation: HashMap<ExprId, ValueId>,
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
    /// Cache/materialize-only roots (`materialize.is_some() && claim.is_none()`) by expr.
    /// Eager F3 materialization targets ONLY these (never claim-bearing output roots,
    /// which are atoms materialized at their scheduled position by the root-driver).
    expr_to_cache_root: HashMap<ExprId, Vec<(RootId, u8, u16, OperandField)>>,
    exposed: HashSet<RootId>,
    root_outputs: Vec<(RootId, VirtualRootOutput)>,
    /// Interned resolution-leaf descriptors (`ExprId → ctx.specials` index).
    desc_by_expr: HashMap<ExprId, u16>,
    /// VirtualSetup kind → interned `ctx.specials` index (dedup: ≤4 entries/layer).
    /// All `VirtualSetup { kind }` sources of the same kind evaluate to the same
    /// `virtual_setup(kind, row)`, so one descriptor per kind is value-correct.
    virtual_setup_descs: HashMap<cs::gkr_compiler::dag_ir::VirtualSetupKind, u16>,
    /// Task 3 residency state driven by `SiteDecisions`/`OccurrenceStreams`. `Some` =
    /// the emitter-owned residency policy; `None` = the uncached per-step-recompute
    /// path (still the default for callers that pass no decisions). This is now the
    /// ONLY mode carrier — no separate policy field.
    decisions: Option<DecisionsState>,
}

impl<'a> VirtualLower<'a> {
    fn emit(&mut self, vi: VInstr) {
        // Demand-driven eviction (Decisions only): this instruction's `reads` is the
        // exact set `place::compute_live_ranges` will scan too — release any pending
        // temp the instant its one-and-only consuming read appears here, so the
        // tracker's live_width tracks the SAME instant `plan_placement` will treat as
        // that temp's `last_use`.
        if let Some(ds) = &mut self.decisions {
            if !ds.pending_temps.is_empty() || !ds.pending_reads.is_empty() {
                let place_instr = vi.to_place();
                for op in &place_instr.reads {
                    if let VirtualOp::Value(id) = op {
                        // Drain one outstanding deferred-consumption slot (see
                        // `pending_reads`'s doc) — gates eviction candidacy, independent
                        // of the temp-width release below.
                        if let Some(cnt) = ds.pending_reads.get_mut(id) {
                            *cnt -= 1;
                            if *cnt == 0 {
                                ds.pending_reads.remove(id);
                            }
                        }
                        if ds.pending_temps.remove(id) {
                            let width = resident_width(
                                *self.widths.get(id).expect("pending temp must have a recorded width"),
                            );
                            ds.live_width = ds.live_width.saturating_sub(width);
                        }
                    }
                }
            }
        }
        self.out.push(vi);
        self.step_of_instr.push(self.cur_step);
    }

    /// Register a `VirtualOp::Value(id)` about to be returned to a caller that will
    /// consume it LATER (not inline) — increments `pending_reads[id]` so
    /// `evict_to_fit` won't pick `id` as an eviction victim while this reference is
    /// still outstanding (see `pending_reads`'s doc). The single choke point for
    /// every `Value`-producing exit of `lower_operand_virtual`/`finalize_produced`.
    fn defer_read(&mut self, id: ValueId) -> VirtualOp {
        if let Some(ds) = &mut self.decisions {
            *ds.pending_reads.entry(id).or_insert(0) += 1;
        }
        VirtualOp::Value(id)
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

    /// Consume one occurrence off `v`'s demand stream (`Some`-decisions only; a no-op
    /// under `decisions: None`). MUST be called exactly once per demand site the
    /// lowering visits for `v` — every `lower_operand_virtual` call and every root's own
    /// top-level output demand (the driver loop) — so `effective_priority` keeps reading
    /// the CURRENT stream front. Call this BEFORE any hit/miss branching on `v`.
    fn serve_occurrence(&mut self, v: ExprId) {
        if let Some(ds) = &mut self.decisions {
            ds.streams.serve(v);
        }
    }

    /// Attempt to admit a just-produced value `v` (occupying `field`'s width) into the
    /// `Decisions` resident set. Only meaningful when `self.decisions` is `Some`
    /// (returns `None` otherwise). On success, `v` is inserted into both `resident` and
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
    ///
    /// Task 8c: on success, returns `Some(id)` naming the `ValueId` the caller must
    /// physically evict-to-cell (`emit_evict_to_cell(id, field)`) and read thereafter
    /// — `v` itself on `v`'s first-ever admission, or a FRESH internal generation id
    /// if `v` was evicted at some earlier point in this layer compile (see
    /// `generation`'s doc). The bookkeeping side effects (`resident`/`generation`/
    /// `live_width`/`defined`) are all applied here; emitting the physical
    /// evict-to-cell instruction stays the caller's job since callers differ on
    /// whether the acc already holds `v`'s value at this point (a leaf must
    /// `emit_init_field` first) or already does (a just-recomputed compound/root).
    fn try_admit(&mut self, v: ExprId, field: OperandField) -> Option<ValueId> {
        // RR-invariant: admit into residency ONLY values the genome scores — cs's site
        // domain (cacheable ∧ fan-out ≥ 2). Non-domain values (challenges, constants,
        // virtual-setup / lookup leaves, and fan-out-1 values) carry zero DRAM traffic,
        // so caching them cannot save a read — it only squats a residency slot that could
        // hold a genuine DRAM value. This `try_admit` is the SINGLE admission choke (leaf
        // path lower.rs:~684, compound/root via `finalize_produced`), so gating here makes
        // "every evictable value is genome-backed" hold by construction. Checked before
        // `effective_priority`/`evict_to_fit` so a refused value has no side effects.
        if !self.decisions.as_ref()?.streams.is_admittable(v) {
            return None;
        }
        let admitting_priority = self.decisions.as_ref()?.streams.effective_priority(v)?;
        let need = resident_width(field);
        if !self.evict_to_fit(need, Some(admitting_priority)) {
            return None;
        }
        let evicted_before =
            self.decisions.as_ref().expect("checked Some above").evicted_ever.contains(&v);
        let gen_id = if evicted_before { self.fresh_internal() } else { v };
        let ds = self.decisions.as_mut().expect("checked Some above");
        ds.resident.insert(v, field);
        ds.generation.insert(v, gen_id);
        ds.live_width += need;
        self.defined.insert(v);
        Some(gen_id)
    }

    /// Task 8c: the `ValueId` currently serving real `ExprId` `real` — `real` itself
    /// unless it has ever been re-admitted after an eviction, in which case it is the
    /// fresh generation id `try_admit` minted (see `generation`'s doc). Every read of
    /// a `defined`-resident real `ExprId` MUST go through this (not use `real`
    /// directly), so it lands on the physical cell the CURRENT generation's
    /// `defines` instruction produced.
    fn current_value_id(&self, real: ExprId) -> ValueId {
        self.decisions.as_ref().and_then(|ds| ds.generation.get(&real).copied()).unwrap_or(real)
    }

    /// Demand-driven eviction (replaces the deleted static `resident_cap_for_order`
    /// pre-reservation): free at least `need` width-weighted cells by evicting
    /// lowest-effective-priority residents (ascending `(effective priority, ExprId)`,
    /// `total_cmp`; a dead/no-remaining-occurrence resident's priority reads as
    /// `f64::NEG_INFINITY`, so it is always evicted before any live one).
    ///
    /// - `admitting_priority = Some(p)` (an ADMISSION deciding whether `v` is worth
    ///   caching): all-or-nothing, no partial eviction — if the weakest remaining
    ///   victim's priority is already `>= p`, the eviction (and thus the admission)
    ///   is skipped; `false` means "don't admit", not "infeasible".
    /// - `admitting_priority = None` (a MANDATORY expression-temp allocation: the
    ///   compile cannot proceed without this cell, caching value is irrelevant):
    ///   forced, priority-unconditional eviction — evict lowest-priority residents
    ///   regardless of their value until `need` fits or the resident set is
    ///   exhausted. `false` here means genuine infeasibility.
    ///
    /// Every evicted `ExprId` is recorded in `evicted_ever` (see its doc) so its NEXT
    /// admission, if any, mints a fresh generation id instead of reusing `id`.
    fn evict_to_fit(&mut self, need: usize, admitting_priority: Option<f64>) -> bool {
        let Some(ds) = &self.decisions else { return false };
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
                let p = ds.streams.effective_priority(id).unwrap_or(f64::NEG_INFINITY);
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
            freed += resident_width(f);
            to_evict.push((id, f));
        }
        if live_width - freed + need > budget {
            return false; // ran out of candidates without freeing enough
        }
        let ds = self.decisions.as_mut().expect("checked Some above");
        for (id, f) in to_evict {
            ds.resident.remove(&id);
            self.defined.remove(&id);
            ds.live_width -= resident_width(f);
            ds.evicted_ever.insert(id);
        }
        true
    }

    /// Allocate a fresh internal expression-temp's cell under demand-driven eviction
    /// pressure: force-evict residents (`evict_to_fit(.., None)`, mandatory —
    /// temps are structurally required for the compile to proceed, unlike an
    /// admission which can simply decline) until `field`'s width fits, then mint the
    /// temp, register it as pending (single-use release, see `pending_temps`'s doc),
    /// and physically evict it to a cell. `decisions: None` (`self.decisions.is_none()`)
    /// skips all tracking — its only feasibility gate is `plan_placement`.
    fn alloc_temp_evicting(&mut self, field: OperandField) -> Result<ValueId, CompileError> {
        if self.decisions.is_some() {
            let need = resident_width(field);
            if !self.evict_to_fit(need, None) {
                let ds = self.decisions.as_ref().expect("checked Some above");
                return Err(CompileError::BudgetBelowFloor {
                    floor: ds.live_width + need,
                    budget: ds.budget,
                });
            }
        }
        let t = self.fresh_internal();
        self.widths.insert(t, field);
        if let Some(ds) = &mut self.decisions {
            ds.live_width += resident_width(field);
            ds.pending_temps.insert(t);
        }
        self.emit_evict_to_cell(t, field);
        Ok(t)
    }

    /// Finalize a just-produced value (its true value is now in the acc): decide whether
    /// it becomes resident (readable later as `Value(expr_id)`) or a one-off fresh temp,
    /// then evict it out of the acc into a cell. Returns the operand naming whichever cell
    /// it landed in.
    ///
    /// - `decisions = None`: never resident — schema v2 has no persisted per-step
    ///   residency, so this is pure per-step recompute (unchanged Task-1 behavior).
    /// - `decisions = Some(..)`: `try_admit` (Task 3) decides.
    fn finalize_produced(
        &mut self,
        expr_id: ExprId,
        field: OperandField,
    ) -> Result<VirtualOp, CompileError> {
        let admitted = if self.decisions.is_some() { self.try_admit(expr_id, field) } else { None };
        if let Some(gen_id) = admitted {
            self.widths.insert(gen_id, field);
            self.emit_evict_to_cell(gen_id, field);
            self.defined.insert(expr_id); // idempotent under `Decisions` (try_admit already did this)
            Ok(self.defer_read(gen_id))
        } else {
            let t = self.alloc_temp_evicting(field)?;
            Ok(self.defer_read(t))
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

    /// Intern a `VirtualSetup { kind }` source as a computed `Special` descriptor,
    /// deduped by kind. `origin_expr` is the VirtualSetup source expr (the fold oracle
    /// re-resolves it via the same `virtual_setup` resolver, so the peek↔fold parity
    /// gate stays live and catches a kind/origin mispairing).
    fn intern_virtual_setup(
        &mut self,
        kind: cs::gkr_compiler::dag_ir::VirtualSetupKind,
        origin_expr: ExprId,
    ) -> u16 {
        if let Some(&d) = self.virtual_setup_descs.get(&kind) {
            return d;
        }
        let desc = self.ctx.specials.push(super::super::source::SpecialDescriptor {
            strategy: super::super::source::SpecialStrategy::VirtualSetup { kind: kind.clone() },
            origin_expr,
        });
        self.virtual_setup_descs.insert(kind, desc);
        desc
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
                let desc = self.intern_virtual_setup(kind.clone(), expr_id);
                Ok(VirtualOp::Special { desc })
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
    ) -> Result<VirtualOp, CompileError> {
        // Task 3 (`Decisions` only, no-op otherwise): this call IS a demand site — one
        // occurrence off `expr_id`'s stream, consumed before any hit/miss branching so
        // `effective_priority` reflects the NEXT occurrence for any admission decision
        // taken below (`try_admit`'s precondition).
        self.serve_occurrence(expr_id);

        // 1. Truly defined-resident → serve from its CURRENT generation's cell
        //    (Task 8c: `expr_id` itself unless it was re-admitted after an eviction).
        if self.defined.contains(&expr_id) {
            let gen_id = self.current_value_id(expr_id);
            return Ok(self.defer_read(gen_id));
        }
        // 2. A source or resolution-pruned leaf resolves to one operand line. Under
        //    `Decisions`, a leaf can ALSO be admitted into residency (Task 3: caching
        //    isn't limited to compound recomputes — brief's `read_leaf_cacheable`) so a
        //    repeatedly-read DRAM/const/etc. leaf can be served from a cell later.
        if layer.resolutions.contains_key(&expr_id)
            || matches!(&layer.exprs[expr_id.0 as usize], Expr::Source(_))
        {
            let op = self.source_to_vop(layer, expr_id)?;
            if self.decisions.is_some() {
                let field = child_operand_field(layer, expr_id, expected, &self.cross);
                if let Some(gen_id) = self.try_admit(expr_id, field) {
                    // HIGH-1: eager cache write from the SOURCE (F1-clean). Writing from acc
                    // here would wedge a `DstFromAcc(cache)` between the leaf load and the
                    // cell eviction (both read acc), which F1 cannot fuse; sourcing the
                    // cache write directly keeps the `init;evict` pair F1-fusible.
                    self.materialize_cache_root_from_src(expr_id, &op);
                    self.emit_init_field(op, field);
                    self.widths.insert(gen_id, field);
                    self.emit_evict_to_cell(gen_id, field);
                    self.defined.insert(expr_id);
                    return Ok(self.defer_read(gen_id));
                }
            }
            self.materialize_cache_root_from_src(expr_id, &op); // F3: eager cache write from source
            return Ok(op);
        }
        // 3. Compound: recompute the cone into the acc, then finalize residency (Task 3
        //    `Decisions` admission; a no-op when `decisions` is `None`).
        let field = child_operand_field(layer, expr_id, expected, &self.cross);
        self.compile_expr_virtual(layer, expr_id, field)?;
        self.materialize_if_root(expr_id, true);
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
            let desc = *self.desc_by_expr.get(&expr_id).ok_or_else(|| {
                CompileError::FieldMismatch(format!(
                    "resolution leaf {} not interned by materialize_descriptors",
                    expr_id.0
                ))
            })?;
            let field = child_operand_field(layer, expr_id, expected, &self.cross);
            self.emit_init_field(VirtualOp::Special { desc }, field);
            self.materialize_cache_root_from_acc(expr_id); // F3: eager cache write from acc
            return Ok(());
        }
        match &layer.exprs[expr_id.0 as usize] {
            Expr::Source(_) => {
                let field = child_operand_field(layer, expr_id, expected, &self.cross);
                let op = self.source_to_vop(layer, expr_id)?;
                self.emit_init_field(op, field);
                self.materialize_cache_root_from_acc(expr_id); // F3: eager cache write from acc
                Ok(())
            }
            Expr::Add(children) => {
                let ch = children.clone();
                self.compile_add_virtual(layer, ch, expected)
            }
            Expr::Mul(children) => {
                let ch = children.clone();
                self.compile_mul_virtual(layer, ch, expected)
            }
        }
    }

    fn compile_add_virtual(
        &mut self,
        layer: &DagLayer,
        children: Vec<ExprId>,
        expected: OperandField,
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
        if self.try_compile_fma_virtual(layer, &children, expected)?.is_some() {
            return Ok(());
        }
        self.compile_reduction_virtual(layer, &children, true, false, expected)
    }

    /// Pick + emit the accumulator seed among `addend_ops` (a Base-Plus term, else any
    /// Plus, else any Base, else the first), applying a `Minus` seed as a unary negate.
    /// Returns the chosen seed index. Precondition: `addend_ops` is non-empty. Shared by
    /// `try_compile_fma_virtual` (one seed heuristic).
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
    /// Used by `try_compile_fma_virtual`.
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
    /// Used by `try_compile_fma_virtual`.
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
        self.compile_reduction_virtual(layer, &surviving, false, negate, expected)
    }

    /// Field-homogeneous reduction (mirrors arith::compile_reduction).
    fn compile_reduction_virtual(
        &mut self,
        layer: &DagLayer,
        children: &[ExprId],
        is_add: bool,
        negate: bool,
        expected: OperandField,
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
            let op = self.lower_operand_virtual(layer, to_lower, expected)?;
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
            let t = self.alloc_temp_evicting(field)?;
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
            let op = self.lower_operand_virtual(layer, c, expected)?;
            addend_ops.push((f, op, sign));
        }
        let mut lo: Vec<(Sign, OperandField, VirtualOp, OperandField, VirtualOp)> =
            Vec::with_capacity(products.len());
        for &(sign, lhs, rhs) in &products {
            let lf = child_operand_field(layer, lhs, expected, &self.cross);
            let rf = child_operand_field(layer, rhs, expected, &self.cross);
            let lhs_op = self.lower_operand_virtual(layer, lhs, expected)?;
            let rhs_op = self.lower_operand_virtual(layer, rhs, expected)?;
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
    ///
    /// Root/cache-sink transparency under Task 8c (verified, not assumed): this
    /// function's OWN bookkeeping (`expr_to_compute` keyed by the real `ExprId`,
    /// `root_outputs`/`exposed` keyed by `RootId`) never touches `generation` — a
    /// root's external identity (which `RootId` it is, which `(slot, col)` it
    /// materializes to) is exactly what it was before this task. The only thing
    /// generation indirection changes is WHICH PHYSICAL CELL the `from_acc = false`
    /// branch reads from: a root's expr CAN be evicted-then-re-admitted before the
    /// driver reaches the root's own turn (it's an ordinary `ExprId`, read like any
    /// other value by whatever else in the layer references it), so the read must go
    /// through `current_value_id` the same as every other resident-serving read.
    /// This is safe because roots are produced (written to their backing) exactly
    /// once regardless: `exposed` gates re-entry into this function entirely, so a
    /// LATER re-admission of the same `ExprId` (after this root's write already
    /// happened) can never trigger a second materialize write here.
    fn materialize_if_root(&mut self, expr_id: ExprId, from_acc: bool) {
        let Some(roots) = self.expr_to_compute.get(&expr_id).cloned() else { return };
        let src_id = self.current_value_id(expr_id);
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
                    src: Some(VirtualOp::Value(src_id)),
                    defines: None,
                    is_dram_read: false,
                });
            }
            self.root_outputs.push((rid, VirtualRootOutput::Global { slot, col }));
            self.exposed.insert(rid);
        }
    }

    /// Eager F3: materialize every UNexposed cache root sharing `expr_id` FROM THE ACC
    /// (the value is currently live in acc). Mirrors `materialize_if_root`'s `exposed`
    /// dedup + `root_outputs` push, but reads `expr_to_cache_root` (cache-only).
    fn materialize_cache_root_from_acc(&mut self, expr_id: ExprId) {
        let Some(roots) = self.expr_to_cache_root.get(&expr_id).cloned() else { return };
        for (rid, slot, col, field) in roots {
            if self.exposed.contains(&rid) {
                continue;
            }
            self.emit(VInstr::Mov {
                dir: MovDir::DstFromAcc,
                field,
                dst: Some(VDst::GlobalMaterialize { slot, col }),
                src: None,
                defines: None,
                is_dram_read: false,
            });
            self.root_outputs.push((rid, VirtualRootOutput::Global { slot, col }));
            self.exposed.insert(rid);
        }
    }

    /// Eager F3: materialize every UNexposed cache root sharing `expr_id` FROM THE SOURCE
    /// operand `op` (the value is NOT in acc — a non-admitted leaf; going through acc
    /// would clobber it and add a MOV). Emits `DstFromSrc(GlobalMaterialize, op)`.
    fn materialize_cache_root_from_src(&mut self, expr_id: ExprId, op: &VirtualOp) {
        let Some(roots) = self.expr_to_cache_root.get(&expr_id).cloned() else { return };
        for (rid, slot, col, field) in roots {
            if self.exposed.contains(&rid) {
                continue;
            }
            self.emit(VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field,
                dst: Some(VDst::GlobalMaterialize { slot, col }),
                src: Some(op.clone()),
                defines: None,
                is_dram_read: false,
            });
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

/// Walk `schedule.atom_order()`, lowering each atom root's expression to a rich `VInstr`
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
    this_layer: usize,
    decisions: Option<&SiteDecisions>,
    budget: usize,
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

    // Flat atom execution order (Phase 1: `schedule.units` → flattened atom roots).
    // `cache_roots` are deliberately NOT part of this stream — they never enter the
    // occurrence/priority streams; materialize-only roots are handled by the final
    // sweep below.
    let atom_order = schedule.atom_order();

    // Internal ValueIds live in a disjoint HIGH range (assert real ExprIds stay below).
    assert!(
        (layer.exprs.len() as u64) < INTERNAL_BASE as u64,
        "layer has {} exprs; internal ValueId base {INTERNAL_BASE} would collide",
        layer.exprs.len()
    );

    // Compute roots by shared ExprId: intern each sink's backing once.
    let mut expr_to_compute: HashMap<ExprId, Vec<(RootId, u8, u16, OperandField)>> = HashMap::new();
    // F3: cache/materialize-only roots (`claim.is_none()`) — the eager-materialize targets.
    // NEVER claim-bearing output roots (they are atoms served at their scheduled position).
    let mut expr_to_cache_root: HashMap<ExprId, Vec<(RootId, u8, u16, OperandField)>> =
        HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        let rid = RootId(idx as u32);
        let Some(sink) = root.materialize.as_ref() else { continue };
        if matches!(ctx.actions.get(&rid), Some(ForwardAction::Compute)) {
            let (key, col) = super::sink_to_backing(sink, this_layer);
            let slot = ctx.backings.intern(key)?;
            let field = super::operand_field_of(sink);
            expr_to_compute.entry(root.expr).or_default().push((rid, slot, col, field));
            if root.claim.is_none() {
                expr_to_cache_root.entry(root.expr).or_default().push((rid, slot, col, field));
            }
        }
    }

    // Task 3: under `Decisions`, precompute the demand-order occurrence streams ONCE
    // (mirrors the emitter's actual `Add`/`Mul` virtual-lowering traversal — see
    // `decisions.rs`'s module doc).
    let decisions_state = decisions.map(|d| DecisionsState {
        streams: OccurrenceStreams::build(layer, &atom_order, &ctx.actions, d),
        resident: BTreeMap::new(),
        budget,
        live_width: 0,
        pending_temps: std::collections::HashSet::new(),
        pending_reads: std::collections::HashMap::new(),
        evicted_ever: HashSet::new(),
        generation: HashMap::new(),
    });

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
        expr_to_cache_root,
        exposed: HashSet::new(),
        root_outputs: Vec::new(),
        desc_by_expr,
        virtual_setup_descs: HashMap::new(),
        decisions: decisions_state,
    };

    let mut resident_realized: Vec<(Vec<ExprId>, Vec<ExprId>)> =
        Vec::with_capacity(atom_order.len());

    for (p, &rid) in atom_order.iter().enumerate() {
        st.cur_step = p;

        // Step-boundary residency. Schema v2 (Task 4) has no persisted per-step residency
        // at all (`LayerSchedule` carries `order` + `sites`, not a step replay). Under
        // `decisions = None` nothing is ever admitted into `st.defined` (every insert
        // site is decisions-gated), so it is empty at every step boundary — pure
        // per-step recompute, no clear needed. `Some`-decisions residency is NOT
        // schedule-step-scoped — it persists across root/step boundaries under its
        // OWN admission/eviction bookkeeping (`try_admit`).
        let before = sorted_real(&st.defined);

        // Process the ordered atom root. Under `decisions = None` every value not
        // already resident is defined LAZILY (recompute) the first time a cone computes
        // it and served thereafter.
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
                    if st.decisions.is_some() {
                        st.serve_occurrence(expr);
                    }
                    if st.defined.contains(&expr) {
                        st.materialize_if_root(expr, false);
                    } else {
                        st.compile_expr_virtual(layer, expr, expected)?;
                        st.materialize_if_root(expr, true);
                        let field = child_operand_field(layer, expr, expected, &st.cross);
                        let admit =
                            if st.decisions.is_some() { st.try_admit(expr, field) } else { None };
                        if let Some(gen_id) = admit {
                            st.widths.insert(gen_id, field);
                            st.emit_evict_to_cell(gen_id, field);
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
    st.cur_step = atom_order.len().saturating_sub(1);
    let mut pending: Vec<ExprId> = st
        .expr_to_compute
        .iter()
        .filter(|(_, roots)| roots.iter().any(|(rid, ..)| !st.exposed.contains(rid)))
        .map(|(&e, _)| e)
        .collect();
    pending.sort_by_key(|e| e.0);
    for expr in pending {
        if st.defined.contains(&expr) {
            st.materialize_if_root(expr, false);
        } else {
            let field = child_operand_field(layer, expr, OperandField::Base, &st.cross);
            st.compile_expr_virtual(layer, expr, field)?;
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

#[cfg(test)]
mod tests {
    use crate::fwd::compile::compile_circuit;
    use crate::fwd::isa::{Instr, OperandLine};
    use crate::fwd::source::SpecialStrategy;
    use cs::gkr_compiler::dag_ir::{lower_dag, validate, CircuitSchedule};
    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::base::BabyBearField;
    use std::path::PathBuf;

    fn compiled_circuit_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
    }
    fn load_fixture(name: &str) -> Option<GKRCircuitArtifact<BabyBearField>> {
        let bytes = std::fs::read(compiled_circuit_dir().join(format!("{name}.json"))).ok()?;
        serde_json::from_slice(&bytes).ok()
    }
    fn load_schedule(stem: &str) -> Option<CircuitSchedule> {
        let bytes =
            std::fs::read(compiled_circuit_dir().join(format!("{stem}_schedule_b16_gkr.json"))).ok()?;
        serde_json::from_slice(&bytes).ok()
    }

    /// Step 2 (Task 1, TDD): a `SourceKind::VirtualSetup` read lowers to a computed
    /// `Special` strategy, NOT a `Global` DRAM backing. add_sub L0 reads VirtualSetup
    /// columns, so its compiled program must carry an `OperandLine::Special { desc }`
    /// whose descriptor strategy is `SpecialStrategy::VirtualSetup`. Before the
    /// representation swap the same source lowered to `OperandLine::Global` (no such
    /// Special descriptor exists), so this test fails RED until the lowering lands.
    #[test]
    fn virtual_setup_lowers_to_special_strategy() {
        let Some(artifact) = load_fixture("add_sub_lui_auipc_mop_layout_gkr") else {
            eprintln!("add_sub fixture not found — skipping VirtualSetup-lowering gate");
            return;
        };
        let dag = lower_dag(&artifact).expect("lower_dag");
        validate(&dag).expect("validate");
        let Some(sched) = load_schedule("add_sub_lui_auipc_mop") else {
            eprintln!("add_sub schedule not found — skipping VirtualSetup-lowering gate");
            return;
        };
        let compiled = compile_circuit(&dag, &sched, &artifact).expect("compile_circuit");
        let l0 = &compiled.layers[0];

        // Find a `Special` operand whose descriptor is a VirtualSetup strategy.
        let mut found = false;
        {
            let mut check = |op: &OperandLine| {
                if let OperandLine::Special { desc } = op {
                    if matches!(
                        l0.ctx.specials.get(*desc).map(|d| &d.strategy),
                        Some(SpecialStrategy::VirtualSetup { .. })
                    ) {
                        found = true;
                    }
                }
            };
            for instr in &l0.program.instrs {
                match instr {
                    Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                        operands.iter().for_each(&mut check)
                    }
                    Instr::Fma { pairs, .. } => {
                        pairs.iter().for_each(|(l, r)| {
                            check(l);
                            check(r);
                        })
                    }
                    Instr::Mov { src: Some(op), .. } => check(op),
                    Instr::Mov { src: None, .. } => {}
                }
            }
        }
        assert!(
            found,
            "add_sub L0 must emit a Special operand backed by a SpecialStrategy::VirtualSetup \
             descriptor (VirtualSetup is a computed Special, not a Global DRAM backing)"
        );
    }
}
