//! Bwd compile driver (Task 5, spec §3): compile a [`DistilledLayer`] to a
//! backward-VM program.
//!
//! Legacy whole-root compilation ends with the distilled root's value in the
//! accumulator. Fragment compilation instead computes each fragment independently
//! and ends it with a semantic batch-accumulation sink. Neither mode emits
//! `DstLine::GlobalMaterialize` (the bwd lowering runs with empty materialize
//! maps). Bindings are NOT a compile input: the program is round- and
//! policy-invariant, `bind()` only produces per-run
//! [`super::distill::BwdBindings`].
//!
//! Spine accumulation: `ArenaBuilder::add` flattens + sorts, so the distilled
//! alpha spine is one WIDE `Add`. Lowering it through the shared reduction
//! machinery would pre-materialize every term into a concurrent Ext temp
//! (never b16-feasible for a whole-layer root), so the driver accumulates
//! term-by-term — spill partial, compute term, fold spill back — bounding the
//! spine's own state to ONE Ext cell (`lower_bwd_root_virtual`). The
//! occurrence replay ([`OccurrenceStreams::build_bwd_root`]) mirrors exactly
//! this decomposition over [`spine_terms`].
//!
//! Descriptor namespace rule: `OperandLine::Special { desc }` in a bwd program
//! indexes ONLY [`BwdSpecialTable`] — fwd's `SpecialTable`/peek validators/fwd
//! stats tally are never applied to bwd programs, hence the local
//! [`tally_bwd_program`] and the [`BwdTrafficStats`] extension (a `FoldSource`
//! use encodes as a Special and would be invisible to `dram_traffic`).

use std::collections::BTreeMap;

use gkr_eval_ir::{Expr, ExprId};

use crate::bwd::batch::unpack_batch_dst;
use crate::fwd::binding::{bind_final_sources, BackingTable, SourceMarkerMode, SourceWindowTable};
use crate::fwd::compile::decisions::OccurrenceStreams;
use crate::fwd::compile::{
    compile_bwd_fragments_program, compile_bwd_program, compile_bwd_program_peak, PlanInput,
    SiteDecisions,
};
use crate::fwd::context::DagForwardContext;
use crate::fwd::error::CompileError;
use crate::fwd::isa::{DstLine, Instr, LdcSub, OperandField, OperandLine, Program};
use crate::fwd::source::{ConstBank, DerivedE4Banks};
use crate::fwd::stats::{CompileStats, OP_ADD, OP_FMA, OP_MOV, OP_MUL};

use super::distill::{distilled_site_domain, DistilledLayer};
use super::plan::{plan_entries_fnv, BwdOccurrencePlan};
use super::source::{BwdSpecial, BwdSpecialTable};
use super::trace::{
    freeze_demand_with, live_profile, plan_epoch, plan_epoch_fragment, BwdCompileTrace,
    DirectTopCorrection, FrozenDemand,
};

// ── BwdTrafficStats ───────────────────────────────────────────────────────────

/// Search-facing traffic extension (REV2, moved from Task 12): `CompileStats.
/// dram_traffic` counts `Global` operands only, so FoldSources (encoded as
/// `Special`) would be invisible to the Task-8 objective. `fold_traffic` is the
/// ROLE-NEUTRAL tally at 4 cells (Ext width) per use — exact per-role/depth
/// byte costs stay in Task 12's census model.
///
/// `fold_traffic` counts 4 cells per READ-ORIGIN fold use ONLY: a VS-origin
/// fold (`origin.is_vs()`) uses the O(k) multilinear closed form — compute-only,
/// zero DRAM — so it contributes to `fold_uses` but adds NO `fold_traffic`.
/// Invariant: `fold_traffic == 4 * (fold_uses - vs_fold_uses)`, where
/// `vs_fold_uses` is the VS-origin subset of `fold_uses`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BwdTrafficStats {
    /// Width-weighted `Global` (real DRAM backing) operand traffic, in cells —
    /// mirrors `CompileStats::dram_traffic` (R0-regime Reads and cross-layer reads).
    pub global: usize,
    /// `Special { desc }` operand uses whose desc is a `BwdSpecial::FoldSource`
    /// — BOTH Read-origin and VS-origin uses count here.
    pub fold_uses: usize,
    /// Role-neutral fold operand traffic: `4 * (fold_uses - vs_fold_uses)`
    /// (Ext width per READ-origin use only — VS-origin uses add no traffic).
    pub fold_traffic: usize,
    /// Base-field fragment products accumulated into the E4 batch.
    pub batch_fma_base: usize,
    /// Extension-field fragment products accumulated into the E4 batch.
    pub batch_fma_ext: usize,
}

// ── BwdCompiledLayer ──────────────────────────────────────────────────────────

/// A compiled backward layer: the round/policy-invariant program + the tables
/// its operands index. `budget` is in bf lanes (buckets = `budget / 4`).
#[derive(Clone, Debug)]
pub struct BwdCompiledLayer {
    pub program: Program,
    /// Logical `c_init` descriptor for the independent fragment batch.
    pub acc_init_desc: Option<u16>,
    /// The BWD descriptor namespace `Special` operands index (never fwd's).
    pub specials: BwdSpecialTable,
    /// Backing slots for R0-regime `Global` reads.
    pub backings: BackingTable,
    pub source_windows: SourceWindowTable,
    pub consts: ConstBank,
    pub derived_e4: DerivedE4Banks,
    /// Smem budget in bf lanes; v2 ext buckets = `budget / 4`.
    pub budget: usize,
    pub stats: CompileStats,
    pub stats_ext: BwdTrafficStats,
}

fn bind_bwd_sources(
    program: &mut Program,
    ctx: &mut DagForwardContext,
) -> Result<(), CompileError> {
    ctx.source_windows = bind_final_sources(program, &ctx.backings, SourceMarkerMode::Backward)?;
    Ok(())
}

// ── spine terms ───────────────────────────────────────────────────────────────

/// The driver's term decomposition of the distilled root: the top-level
/// children of the (flattened, sorted — `ArenaBuilder` canonicalization) alpha
/// spine `Add`, or the root expr itself when it is not an `Add` (single-unit
/// layers / leaf roots). Accumulation over any decomposition is value-identical
/// by Add commutativity; the replay twin mirrors exactly this decomposition, so
/// both the driver and [`OccurrenceStreams::build_bwd_root`] MUST consume this
/// same function's output.
pub fn spine_terms(d: &DistilledLayer) -> Vec<ExprId> {
    let root_expr = d.layer.roots[d.root.0 as usize].expr;
    match &d.layer.exprs[root_expr.0 as usize] {
        Expr::Add(children) if !children.is_empty() => children.clone(),
        _ => vec![root_expr],
    }
}

// ── compile driver ────────────────────────────────────────────────────────────

/// Compile a distilled layer at `budget` (bf lanes). `decisions` carries the
/// per-site residency genes keyed to DISTILLED `ExprId`s (`None` = uncached
/// per-demand recompute). Bindings are deliberately NOT an input — see the
/// module doc (round/policy invariance).
///
/// Legacy-first compile driver (SP1). The baseline is the pre-materialize
/// lowering (`stream_reductions = false`, byte-identical to before this task);
/// only when it reports [`CompileError::BudgetBelowFloor`] do we retry with the
/// one-Ext-cell reduction streaming engaged. Feasibility with streaming ⊇ legacy
/// and streamed programs are value-identical to legacy on both the uncached and
/// searched paths, so this fallback never changes a value or shrinks feasibility.
pub fn compile_distilled(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<BwdCompiledLayer, CompileError> {
    match compile_distilled_streamed(d, budget, decisions, false) {
        Err(CompileError::BudgetBelowFloor { .. }) => {
            compile_distilled_streamed(d, budget, decisions, true)
        }
        other => other,
    }
}

/// The legacy pre-materialize lowering ONLY (`stream_reductions = false`) — the
/// SP1 baseline, exposed for the parity tests that must observe the un-streamed
/// floor (a `BudgetBelowFloor` that streaming would otherwise mask).
pub fn compile_distilled_legacy_only(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<BwdCompiledLayer, CompileError> {
    compile_distilled_streamed(d, budget, decisions, false)
}

/// Fill-then-trim compile at a fixed `stream_reductions` (same semantics as fwd
/// `compile_layer` at the same budget): lower with eviction effectively disabled
/// (FILL), let `plan_placement` at the real `budget` be the feasibility oracle,
/// and on overflow binary-search the largest lowering budget whose placement fits
/// (`lower_budget == budget` is the guaranteed baseline). `pub` for the SP1 parity
/// tests, which pin the streamed vs legacy variants against each other.
pub fn compile_distilled_streamed(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<BwdCompiledLayer, CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_at(d, budget, lb, decisions, stream_reductions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Lower at `lower_budget` (eviction dial), place at `place_budget` (real cell
/// budget) — the bwd sibling of fwd's `compile_layer_at`.
fn compile_distilled_at(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<BwdCompiledLayer, CompileError> {
    let layer = &d.layer;
    let root_expr = layer.roots[d.root.0 as usize].expr;
    let terms = spine_terms(d);

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    // The bwd occurrence/demand replay, over the SAME term decomposition the
    // driver executes, gated by the DISTILLED site domain.
    let streams = decisions.map(|dec| {
        OccurrenceStreams::build_bwd_root(
            layer,
            d.root,
            root_expr,
            &terms,
            dec,
            &distilled_site_domain(d),
        )
    });

    let (mut program, max_live_cells, _trace) = compile_bwd_program(
        layer,
        root_expr,
        &terms,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        streams,
        place_budget,
        lower_budget,
        stream_reductions,
        None, // trace
        None, // plan (gene / uncached path)
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    // The bwd lowering runs the fwd resolution hook with empty materialize maps
    // and CLEARED resolutions, so it must never intern a fwd SpecialDescriptor:
    // bwd Special operands index `d.specials` (the BWD table), a disjoint
    // namespace. A non-empty fwd table here means a resolution fence leaked into
    // the fwd descriptor namespace.
    assert!(
        ctx.specials.is_empty(),
        "bwd compile leaked into the fwd descriptor namespace"
    );

    let (mut stats, stats_ext) = tally_bwd_program(&program, &d.specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok(BwdCompiledLayer {
        program,
        acc_init_desc: None,
        specials: d.specials.clone(),
        backings: ctx.backings,
        source_windows: ctx.source_windows,
        consts: ctx.consts,
        derived_e4: ctx.derived_e4,
        budget: place_budget,
        stats,
        stats_ext,
    })
}

// ── Task 1 (CS-M0) traced compile driver (observation-only) ────────────────────

/// Traced sibling of [`compile_distilled`]: compile `d` at `budget` on the SAME
/// legacy-first-then-streamed fallback, AND return the [`BwdCompileTrace`] observed
/// during the WINNING compile (the one whose program is returned). The returned
/// `BwdCompiledLayer` is byte-identical to `compile_distilled`'s output for the same
/// inputs — the trace only records what the lowering did; it never changes a value,
/// an instruction, or feasibility (fwd/untraced parity is gated).
pub fn compile_distilled_traced(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    match compile_distilled_streamed_traced(d, budget, decisions, false) {
        Err(CompileError::BudgetBelowFloor { .. }) => {
            compile_distilled_streamed_traced(d, budget, decisions, true)
        }
        other => other,
    }
}

/// Traced sibling of [`compile_distilled_streamed`] — the same fill-then-trim
/// feasibility search, keeping the trace of the WINNING lowering budget (the `at`
/// call that becomes `best`). The search decisions depend only on placement, never on
/// the trace, so this picks the identical `lower_budget` as the untraced search.
fn compile_distilled_streamed_traced(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_at_traced(d, budget, lb, decisions, stream_reductions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Traced sibling of [`compile_distilled_at`] — seeds a [`BwdCompileTrace`] with the
/// plan epoch / budget / mode, threads it through `compile_bwd_program` (which fills
/// its `events`), then fills the per-instruction `free[t] = place_budget -
/// live_profile[t]` (saturating) spare-lane envelope from the materialized program.
fn compile_distilled_at_traced(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    let layer = &d.layer;
    let root_expr = layer.roots[d.root.0 as usize].expr;
    let terms = spine_terms(d);

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    let streams = decisions.map(|dec| {
        OccurrenceStreams::build_bwd_root(
            layer,
            d.root,
            root_expr,
            &terms,
            dec,
            &distilled_site_domain(d),
        )
    });

    let seed = BwdCompileTrace {
        epoch: plan_epoch(d, place_budget, stream_reductions),
        budget: place_budget,
        stream_reductions,
        events: Vec::new(),
        free: Vec::new(),
    };

    let (mut program, max_live_cells, trace) = compile_bwd_program(
        layer,
        root_expr,
        &terms,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        streams,
        place_budget,
        lower_budget,
        stream_reductions,
        Some(seed),
        None, // plan (gene / uncached traced path)
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    assert!(
        ctx.specials.is_empty(),
        "bwd compile leaked into the fwd descriptor namespace"
    );

    let mut trace = trace.expect("a Some-seeded traced compile returns its trace");
    // free[t] = budget - live lanes at t (saturating): the spare-lane envelope a later
    // occurrence planner can reclaim. `live_profile` is length == program.instrs.len().
    trace.free = live_profile(&program)
        .into_iter()
        .map(|occ| place_budget.saturating_sub(occ))
        .collect();

    let (mut stats, stats_ext) = tally_bwd_program(&program, &d.specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok((
        BwdCompiledLayer {
            program,
            acc_init_desc: None,
            specials: d.specials.clone(),
            backings: ctx.backings,
            source_windows: ctx.source_windows,
            consts: ctx.consts,
            derived_e4: ctx.derived_e4,
            budget: place_budget,
            stats,
            stats_ext,
        },
        trace,
    ))
}

// ── Task 4 (CS-M0) plan-driven compile driver ──────────────────────────────────

/// Plan-driven backward compile (spec §4/§5, CS-M3 Stage 2). Replay `plan` against `d` via
/// the fill-then-trim realizer [`compile_distilled_at_planned`]: lower with eviction
/// effectively disabled and let `plan_placement` at the real `budget` be the 2-D feasibility
/// oracle (`lower_budget == budget` is the guaranteed baseline). The WINNING lowering's trace
/// is returned as the next round's planner input, with `stream_reductions` pinned FROM the
/// plan and tracing ON. The plan's per-occurrence `Retain`/`Bypass` actions drive residency;
/// capacity is re-checked live at each event (evict only EXPIRED residents, else `Refuse`;
/// never preempt a live retention); the fingerprint matcher fails closed to a Bypass-tail on
/// the first divergence and records it once.
///
/// HARD ERRORS (panics — a wrong/corrupted plan must never replay silently, spec §4):
/// the plan's `epoch` must equal `plan_epoch(d, budget, plan.stream_reductions)` and its
/// `entries_fnv` must equal a re-hash of `plan.entries` ([`plan_entries_fnv`]).
///
/// [`CompileError::BudgetBelowFloor`] propagates as `Err` — the engine's fallback is
/// Task 9; this driver never masks it with a legacy retry (unlike `compile_distilled`).
pub fn compile_distilled_planned(
    d: &DistilledLayer,
    budget: usize,
    plan: &BwdOccurrencePlan,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    let expected_epoch = plan_epoch(d, budget, plan.stream_reductions);
    assert_eq!(
        plan.epoch, expected_epoch,
        "plan epoch mismatch: plan carries {} but (layer, budget {budget}, stream_reductions \
         {}) hashes to {expected_epoch} — wrong or stale plan",
        plan.epoch, plan.stream_reductions,
    );
    let expected_fnv = plan_entries_fnv(&plan.entries);
    assert_eq!(
        plan.entries_fnv,
        expected_fnv,
        "plan entries_fnv mismatch: plan carries {} but its {} entries re-hash to \
         {expected_fnv} — corrupted plan",
        plan.entries_fnv,
        plan.entries.len(),
    );
    compile_distilled_at_planned(d, budget, plan)
}

/// The fill-then-trim realizer for the plan-driven compile (spec §4/§5, CS-M3 Stage 2) —
/// the bwd sibling of the GA driver's [`compile_distilled_streamed`] fill-then-trim. Lower
/// with eviction effectively disabled (`lower_budget = FILL`) so every planned `Retain`
/// lands, let `plan_placement` at the real `budget` (== `place_budget`) be the 2-D
/// feasibility oracle, and on placement overflow (`BudgetBelowFloor`) binary-search the
/// largest `lower_budget` that place-fits. `lower_budget == budget` is the guaranteed
/// baseline (`lo` seed) — never worse than the pre-Stage-2 single lowering. The winning
/// `(layer, trace)` is threaded out (the trace of the WINNING `lower_budget`, kept keyed on
/// `place_budget` throughout so the plan's `place_budget` epoch rides it regardless of which
/// `lower_budget` won). Non-`BudgetBelowFloor` errors propagate unchanged.
fn compile_distilled_at_planned(
    d: &DistilledLayer,
    budget: usize,
    plan: &BwdOccurrencePlan,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_at_planned_lb(d, budget, lb, plan);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// The single plan-driven lowering at an explicit `lower_budget` (the eviction dial),
/// placing at `place_budget` (the real cell budget) — the inner of the fill-then-trim
/// wrapper [`compile_distilled_at_planned`], and the plan sibling of `compile_distilled_at`
/// (gene channel OFF, plan channel ON, trace ON). The trace's epoch / budget / `free`
/// envelope stay keyed on `place_budget` (NEVER `lower_budget`), so the winning trace
/// carries the plan's `place_budget` epoch — consistent with the `compile_distilled_planned`
/// epoch assert and the downstream `freeze_demand` re-key — regardless of which
/// `lower_budget` won the search. `pub` for the fill-then-trim monotonicity test, which
/// drives the `lower_budget == budget` baseline directly.
pub fn compile_distilled_at_planned_lb(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    plan: &BwdOccurrencePlan,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    let layer = &d.layer;
    let root_expr = layer.roots[d.root.0 as usize].expr;
    let terms = spine_terms(d);
    let stream_reductions = plan.stream_reductions;

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    // The distilled site-domain value set — only these serves drive the matcher
    // (mirrors `OccurrenceStreams::admittable`; same set `freeze_demand` filters on).
    let domain: std::collections::BTreeSet<ExprId> = distilled_site_domain(d)
        .into_iter()
        .map(|s| s.value)
        .collect();

    let seed = BwdCompileTrace {
        epoch: plan_epoch(d, place_budget, stream_reductions),
        budget: place_budget,
        stream_reductions,
        events: Vec::new(),
        free: Vec::new(),
    };

    let (mut program, max_live_cells, trace) = compile_bwd_program(
        layer,
        root_expr,
        &terms,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        None,         // gene channel OFF — plan mode is exclusive
        place_budget, // place_budget: the real cell budget (2-D placement oracle)
        lower_budget, // lower_budget: the eviction dial (FILL disables eviction)
        stream_reductions,
        Some(seed),
        Some(PlanInput { plan, domain }),
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    assert!(
        ctx.specials.is_empty(),
        "bwd compile leaked into the fwd descriptor namespace"
    );

    let mut trace = trace.expect("a Some-seeded planned compile returns its trace");
    trace.free = live_profile(&program)
        .into_iter()
        .map(|occ| place_budget.saturating_sub(occ))
        .collect();

    let (mut stats, stats_ext) = tally_bwd_program(&program, &d.specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok((
        BwdCompiledLayer {
            program,
            acc_init_desc: None,
            specials: d.specials.clone(),
            backings: ctx.backings,
            source_windows: ctx.source_windows,
            consts: ctx.consts,
            derived_e4: ctx.derived_e4,
            budget: place_budget,
            stats,
            stats_ext,
        },
        trace,
    ))
}

// ── CS-M5a Task 5: fragment-mode (full-decomposition) compile driver ──────────

/// Build the compile-local CLONED [`BwdSpecialTable`] for a fragment compile (Task 3
/// ownership): clone `d.specials`, then intern an `AccInit` descriptor iff `c_init` is
/// non-empty and a `Coefficient{fragment}` descriptor for each fragment whose recipe is
/// NON-TRIVIAL. Returns `(specials, coeff_descs, acc_init_desc)`, where `coeff_descs[i]`
/// is `Some(desc)` iff fragment `i`'s recipe is non-trivial (so the lowering encodes it
/// in that fragment's sink). ONLY descriptors referenced by a sink or by logical
/// `acc_init_desc` metadata are interned — a `Coefficient` for a trivial recipe, or an
/// `AccInit` for an empty `c_init`, would be an orphan the value gate rejects.
/// The interned descs land BEYOND `d.specials.len()` (the distilled table never holds a
/// `Coefficient`/`AccInit`), so `bind`'s per-run `states` stay dense over `d.specials`.
pub(crate) fn fragment_descs(
    d: &DistilledLayer,
) -> (BwdSpecialTable, Vec<Option<u16>>, Option<u16>) {
    let mut specials = d.specials.clone();
    let acc_init_desc = if d.fragments.c_init.terms.is_empty() {
        None
    } else {
        Some(specials.intern(BwdSpecial::AccInit))
    };
    let coeff_descs = d
        .fragments
        .fragments
        .iter()
        .enumerate()
        .map(|(i, f)| {
            if f.recipe.is_trivial() {
                None
            } else {
                Some(specials.intern(BwdSpecial::Coefficient { fragment: i as u32 }))
            }
        })
        .collect();
    (specials, coeff_descs, acc_init_desc)
}

/// Fragment-mode sibling of [`compile_distilled`] (Task 5, spec §3): compile the
/// FULL-DECOMPOSITION view of `d` — each fragment is computed independently and its sink
/// contributes `recipe_i · value(fragment_i)` to an E4 batch initialized from logical
/// `c_init` metadata — instead of the spine-accumulation term loop. `order` permutes the
/// schedule positions (`order[pos] = frag_idx`, identity when `None`); the batch reduction
/// is a field sum, so any order yields a bit-identical result. There is no `decisions`
/// parameter: the gene channel is TERM-ONLY in M5a, so this path is uncached (here) or
/// plan-driven ([`compile_distilled_fragments_planned`]). Same
/// legacy-first-then-streamed feasibility fallback as `compile_distilled`.
pub fn compile_distilled_fragments(
    d: &DistilledLayer,
    budget: usize,
    order: Option<&[usize]>,
) -> Result<BwdCompiledLayer, CompileError> {
    match compile_distilled_fragments_streamed(d, budget, order, false) {
        Err(CompileError::BudgetBelowFloor { .. }) => {
            compile_distilled_fragments_streamed(d, budget, order, true)
        }
        other => other,
    }
}

/// Fragment sibling of [`compile_distilled_streamed`] — the same fill-then-trim feasibility
/// search at a fixed `stream_reductions` (`lower_budget == budget` is the guaranteed
/// baseline; `plan_placement` at the real `budget` is the oracle).
fn compile_distilled_fragments_streamed(
    d: &DistilledLayer,
    budget: usize,
    order: Option<&[usize]>,
    stream_reductions: bool,
) -> Result<BwdCompiledLayer, CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_fragments_at(d, budget, lb, order, stream_reductions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Fragment sibling of [`compile_distilled_at`]: lower at `lower_budget`, place at
/// `place_budget`, tally against the CLONED (Coefficient/AccInit-extended) specials.
fn compile_distilled_fragments_at(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    order: Option<&[usize]>,
    stream_reductions: bool,
) -> Result<BwdCompiledLayer, CompileError> {
    let layer = &d.layer;
    let (specials, coeff_descs, acc_init_desc) = fragment_descs(d);

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    let (mut program, max_live_cells, _trace) = compile_bwd_fragments_program(
        layer,
        &d.fragments,
        order,
        &coeff_descs,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        place_budget,
        lower_budget,
        stream_reductions,
        None, // trace
        None, // plan (uncached path)
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    // Same namespace fence as the term path: the bwd hook + cleared resolutions must never
    // intern a fwd SpecialDescriptor; Coefficient/AccInit live in the CLONED bwd table only.
    assert!(
        ctx.specials.is_empty(),
        "bwd fragment compile leaked into the fwd descriptor namespace"
    );

    let (mut stats, stats_ext) = tally_bwd_program(&program, &specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok(BwdCompiledLayer {
        program,
        acc_init_desc,
        specials,
        backings: ctx.backings,
        source_windows: ctx.source_windows,
        consts: ctx.consts,
        derived_e4: ctx.derived_e4,
        budget: place_budget,
        stats,
        stats_ext,
    })
}

/// Traced fragment sibling of [`compile_distilled_traced`] (observation-only): same
/// legacy-first-then-streamed fallback, returning the [`BwdCompileTrace`] of the WINNING
/// compile. No freeze: the fragment-trace variant (`DirectTopCorrection`) lands in Task 6.
pub fn compile_distilled_fragments_traced(
    d: &DistilledLayer,
    budget: usize,
    order: Option<&[usize]>,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    match compile_distilled_fragments_streamed_traced(d, budget, order, false) {
        Err(CompileError::BudgetBelowFloor { .. }) => {
            compile_distilled_fragments_streamed_traced(d, budget, order, true)
        }
        other => other,
    }
}

/// Traced fragment sibling of [`compile_distilled_streamed`] — same fill-then-trim, keeping
/// the trace of the WINNING lowering budget.
fn compile_distilled_fragments_streamed_traced(
    d: &DistilledLayer,
    budget: usize,
    order: Option<&[usize]>,
    stream_reductions: bool,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    const FILL: usize = 1 << 20;
    let at =
        |lb: usize| compile_distilled_fragments_at_traced(d, budget, lb, order, stream_reductions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Traced fragment sibling of [`compile_distilled_at_traced`] — seeds a trace, threads it
/// through `compile_bwd_fragments_program`, then fills the per-instruction `free` envelope.
fn compile_distilled_fragments_at_traced(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    order: Option<&[usize]>,
    stream_reductions: bool,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    let layer = &d.layer;
    let (specials, coeff_descs, acc_init_desc) = fragment_descs(d);

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    let seed = BwdCompileTrace {
        epoch: plan_epoch_fragment(d, place_budget, stream_reductions),
        budget: place_budget,
        stream_reductions,
        events: Vec::new(),
        free: Vec::new(),
    };

    let (mut program, max_live_cells, trace) = compile_bwd_fragments_program(
        layer,
        &d.fragments,
        order,
        &coeff_descs,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        place_budget,
        lower_budget,
        stream_reductions,
        Some(seed),
        None, // plan (uncached traced path)
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    assert!(
        ctx.specials.is_empty(),
        "bwd fragment compile leaked into the fwd descriptor namespace"
    );

    let mut trace = trace.expect("a Some-seeded traced compile returns its trace");
    trace.free = live_profile(&program)
        .into_iter()
        .map(|occ| place_budget.saturating_sub(occ))
        .collect();

    let (mut stats, stats_ext) = tally_bwd_program(&program, &specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok((
        BwdCompiledLayer {
            program,
            acc_init_desc,
            specials,
            backings: ctx.backings,
            source_windows: ctx.source_windows,
            consts: ctx.consts,
            derived_e4: ctx.derived_e4,
            budget: place_budget,
            stats,
            stats_ext,
        },
        trace,
    ))
}

/// Plan-driven fragment sibling of [`compile_distilled_planned`] (spec §4/§5): replay
/// `plan` against the fragment decomposition of `d`. Same hard epoch / `entries_fnv`
/// asserts (a wrong or corrupted plan must never replay silently) and the same
/// fill-then-trim realizer, `stream_reductions` pinned FROM the plan and tracing ON. No
/// freeze here (Task 6). `order` permutes the schedule positions like the uncached entry.
pub fn compile_distilled_fragments_planned(
    d: &DistilledLayer,
    budget: usize,
    plan: &BwdOccurrencePlan,
    order: Option<&[usize]>,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    let expected_epoch = plan_epoch_fragment(d, budget, plan.stream_reductions);
    assert_eq!(
        plan.epoch, expected_epoch,
        "plan epoch mismatch: plan carries {} but (layer, budget {budget}, stream_reductions \
         {}) hashes to {expected_epoch} — wrong or stale plan",
        plan.epoch, plan.stream_reductions,
    );
    let expected_fnv = plan_entries_fnv(&plan.entries);
    assert_eq!(
        plan.entries_fnv,
        expected_fnv,
        "plan entries_fnv mismatch: plan carries {} but its {} entries re-hash to \
         {expected_fnv} — corrupted plan",
        plan.entries_fnv,
        plan.entries.len(),
    );
    compile_distilled_fragments_at_planned(d, budget, plan, order)
}

/// Fill-then-trim realizer for the plan-driven fragment compile — the fragment sibling of
/// [`compile_distilled_at_planned`].
fn compile_distilled_fragments_at_planned(
    d: &DistilledLayer,
    budget: usize,
    plan: &BwdOccurrencePlan,
    order: Option<&[usize]>,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_fragments_at_planned_lb(d, budget, lb, plan, order);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// The single plan-driven fragment lowering at an explicit `lower_budget` — the fragment
/// sibling of [`compile_distilled_at_planned_lb`] (gene channel OFF by construction, plan
/// channel ON, trace ON). The trace's epoch / `free` envelope stay keyed on `place_budget`.
fn compile_distilled_fragments_at_planned_lb(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    plan: &BwdOccurrencePlan,
    order: Option<&[usize]>,
) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
    let layer = &d.layer;
    let (specials, coeff_descs, acc_init_desc) = fragment_descs(d);
    let stream_reductions = plan.stream_reductions;

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    let domain: std::collections::BTreeSet<ExprId> = distilled_site_domain(d)
        .into_iter()
        .map(|s| s.value)
        .collect();

    let seed = BwdCompileTrace {
        epoch: plan_epoch_fragment(d, place_budget, stream_reductions),
        budget: place_budget,
        stream_reductions,
        events: Vec::new(),
        free: Vec::new(),
    };

    let (mut program, max_live_cells, trace) = compile_bwd_fragments_program(
        layer,
        &d.fragments,
        order,
        &coeff_descs,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        place_budget,
        lower_budget,
        stream_reductions,
        Some(seed),
        Some(PlanInput { plan, domain }),
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    assert!(
        ctx.specials.is_empty(),
        "bwd fragment compile leaked into the fwd descriptor namespace"
    );

    let mut trace = trace.expect("a Some-seeded planned compile returns its trace");
    trace.free = live_profile(&program)
        .into_iter()
        .map(|occ| place_budget.saturating_sub(occ))
        .collect();

    let (mut stats, stats_ext) = tally_bwd_program(&program, &specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok((
        BwdCompiledLayer {
            program,
            acc_init_desc,
            specials,
            backings: ctx.backings,
            source_windows: ctx.source_windows,
            consts: ctx.consts,
            derived_e4: ctx.derived_e4,
            budget: place_budget,
            stats,
            stats_ext,
        },
        trace,
    ))
}

// ── CS-M5a Task 6: compile-backend parameterization ───────────────────────────

/// The compile-driver abstraction the freeze + pricing stack is parameterized over
/// (CS-M5a Task 6). A backend bundles the three driver-specific operations the priced
/// pipeline needs — an uncached traced compile ([`Self::traced`]), a plan-driven replay
/// ([`Self::planned`]), and the freeze of a compiled trace into a [`FrozenDemand`]
/// ([`Self::freeze`], which selects the driver's [`DirectTopCorrection`]) — so the same
/// pricing code drives either the spine-accumulation ([`TermBackend`]) or the
/// full-decomposition ([`FragmentBackend`]) lowering. The term path routes through the
/// existing byte-identical entries.
pub trait BwdCompileBackend {
    fn planned(
        &self,
        d: &DistilledLayer,
        budget: usize,
        plan: &BwdOccurrencePlan,
    ) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError>;
    fn traced(
        &self,
        d: &DistilledLayer,
        budget: usize,
    ) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError>;
    fn freeze(
        &self,
        d: &DistilledLayer,
        c: &BwdCompiledLayer,
        t: &BwdCompileTrace,
    ) -> Option<FrozenDemand>;
}

/// The spine-accumulation (TERM) backend: delegates to the existing
/// [`compile_distilled_traced`] (uncached, `decisions: None`) / [`compile_distilled_planned`]
/// entries and freezes with the [`DirectTopCorrection::Term`] correction — byte-identical
/// to the pre-Task-6 pipeline.
pub struct TermBackend;

impl BwdCompileBackend for TermBackend {
    fn planned(
        &self,
        d: &DistilledLayer,
        budget: usize,
        plan: &BwdOccurrencePlan,
    ) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
        compile_distilled_planned(d, budget, plan)
    }
    fn traced(
        &self,
        d: &DistilledLayer,
        budget: usize,
    ) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
        compile_distilled_traced(d, budget, None)
    }
    fn freeze(
        &self,
        d: &DistilledLayer,
        c: &BwdCompiledLayer,
        t: &BwdCompileTrace,
    ) -> Option<FrozenDemand> {
        freeze_demand_with(
            d,
            t,
            &c.program,
            &c.specials,
            &c.backings,
            &c.source_windows,
            DirectTopCorrection::Term,
        )
    }
}

/// The full-decomposition (FRAGMENT) backend: delegates to
/// [`compile_distilled_fragments_traced`] / [`compile_distilled_fragments_planned`] at the
/// carried schedule `order` and freezes with [`DirectTopCorrection::None`] (Task 5.2 serves
/// every top atom, so there is no unserved direct-top gather to re-credit).
pub struct FragmentBackend {
    pub order: Vec<usize>,
}

impl BwdCompileBackend for FragmentBackend {
    fn planned(
        &self,
        d: &DistilledLayer,
        budget: usize,
        plan: &BwdOccurrencePlan,
    ) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
        compile_distilled_fragments_planned(d, budget, plan, Some(&self.order))
    }
    fn traced(
        &self,
        d: &DistilledLayer,
        budget: usize,
    ) -> Result<(BwdCompiledLayer, BwdCompileTrace), CompileError> {
        compile_distilled_fragments_traced(d, budget, Some(&self.order))
    }
    fn freeze(
        &self,
        d: &DistilledLayer,
        c: &BwdCompiledLayer,
        t: &BwdCompileTrace,
    ) -> Option<FrozenDemand> {
        freeze_demand_with(
            d,
            t,
            &c.program,
            &c.specials,
            &c.backings,
            &c.source_windows,
            DirectTopCorrection::None,
        )
    }
}

// ── Task 6 (LIGHT) peak-composition diagnostic seam ───────────────────────────

/// Diagnostic sibling of [`compile_distilled`]: compile `d` at `budget` (streamed on the
/// same legacy-first-then-streamed fallback as `compile_distilled`) and ALSO return the
/// PEAK instruction index and the peak-live `(ExprId, width)` set — the values occupying the
/// placement peak that `max_live_cells` measures. Additive: `compile_distilled` and the
/// production `compile_distilled_streamed`/`compile_distilled_at` paths are untouched; this
/// mirrors their control flow through the peak-instrumented `compile_bwd_program_peak`.
/// The returned `BwdCompiledLayer` is value-identical to `compile_distilled`'s for the same
/// inputs; `sum(width for (_, width) in live) == layer.stats.max_live_cells` by construction.
pub fn compile_distilled_peak(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<(BwdCompiledLayer, usize, Vec<(ExprId, usize)>), CompileError> {
    match compile_distilled_streamed_peak(d, budget, decisions, false) {
        Err(CompileError::BudgetBelowFloor { .. }) => {
            compile_distilled_streamed_peak(d, budget, decisions, true)
        }
        other => other,
    }
}

/// Peak-instrumented sibling of [`compile_distilled_streamed`] — same fill-then-trim
/// feasibility search, threading the winning compile's peak readout through `best`.
fn compile_distilled_streamed_peak(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<(BwdCompiledLayer, usize, Vec<(ExprId, usize)>), CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_at_peak(d, budget, lb, decisions, stream_reductions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Peak-instrumented sibling of [`compile_distilled_at`] — lower at `lower_budget`, place
/// at `place_budget` via `compile_bwd_program_peak`, returning the compiled layer plus its
/// peak instruction index and peak-live `(ExprId, width)` set.
fn compile_distilled_at_peak(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<(BwdCompiledLayer, usize, Vec<(ExprId, usize)>), CompileError> {
    let layer = &d.layer;
    let root_expr = layer.roots[d.root.0 as usize].expr;
    let terms = spine_terms(d);

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    let streams = decisions.map(|dec| {
        OccurrenceStreams::build_bwd_root(
            layer,
            d.root,
            root_expr,
            &terms,
            dec,
            &distilled_site_domain(d),
        )
    });

    let (mut program, max_live_cells, peak_instr, peak_live) = compile_bwd_program_peak(
        layer,
        root_expr,
        &terms,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        streams,
        place_budget,
        lower_budget,
        stream_reductions,
    )?;
    bind_bwd_sources(&mut program, &mut ctx)?;

    assert!(
        ctx.specials.is_empty(),
        "bwd compile leaked into the fwd descriptor namespace"
    );

    let (mut stats, stats_ext) = tally_bwd_program(&program, &d.specials, &ctx.source_windows);
    stats.max_live_cells = max_live_cells;

    Ok((
        BwdCompiledLayer {
            program,
            acc_init_desc: None,
            specials: d.specials.clone(),
            backings: ctx.backings,
            source_windows: ctx.source_windows,
            consts: ctx.consts,
            derived_e4: ctx.derived_e4,
            budget: place_budget,
            stats,
            stats_ext,
        },
        peak_instr,
        peak_live,
    ))
}

// ── stats tally (bwd descriptor namespace) ────────────────────────────────────

/// Cell width of an operand under `field` (Ext = 4, Base = 1) — the same
/// convention as fwd's `tally_operand` width weighting.
fn width_of(field: OperandField) -> usize {
    match field {
        OperandField::Base => 1,
        OperandField::Ext => 4,
    }
}

/// Tally the concrete bwd program. Mirrors fwd's per-operand accounting, except
/// `Special { desc }` resolves against the BWD table: a `VirtualSetup` desc is
/// resolver-computed (0 traffic, uncounted, like fwd's VirtualSetup strategy); a
/// Read-origin `FoldSource` desc is a real fold-side gather — counted in
/// `special_reads` AND in the search-facing `BwdTrafficStats` (4 cells/use,
/// role-neutral). A VS-origin `FoldSource` uses the O(k) multilinear closed form
/// (Task 7): compute-only, zero DRAM, so it adds `fold_uses` but no `fold_traffic`.
pub(crate) fn tally_bwd_program(
    program: &Program,
    specials: &BwdSpecialTable,
    source_windows: &SourceWindowTable,
) -> (CompileStats, BwdTrafficStats) {
    let mut stats = CompileStats::default();
    let mut ext = BwdTrafficStats::default();
    stats.program_lanes = program.instrs.len();
    let mut tally = |op: &OperandLine,
                     field: OperandField,
                     stats: &mut CompileStats,
                     ext: &mut BwdTrafficStats| {
        match op {
            OperandLine::LogicalGlobal { .. } => {
                stats.dram_reads += 1;
                let w = width_of(field);
                stats.dram_traffic += w;
                ext.global += w;
            }
            OperandLine::LogicalFold { desc, .. } => {
                tally_fold_source(*desc, specials, stats, ext);
            }
            OperandLine::Source { window, column, .. } => {
                if let Some(desc) = source_windows.fold_desc(*window, *column) {
                    tally_fold_source(desc, specials, stats, ext);
                } else {
                    stats.dram_reads += 1;
                    let w = width_of(field);
                    stats.dram_traffic += w;
                    ext.global += w;
                }
            }
            OperandLine::Smem { .. } => stats.cell_reads += 1,
            OperandLine::Ldc {
                sub: LdcSub::Special,
                ..
            } => {} // inline literal
            OperandLine::Ldc { .. } => stats.ldc_reads += 1,
            OperandLine::Special { desc } => match specials.get(*desc) {
                Some(BwdSpecial::VirtualSetup { .. }) => {} // resolver-computed, 0 traffic
                Some(BwdSpecial::FoldSource { origin }) => {
                    stats.special_reads += 1;
                    ext.fold_uses += 1;
                    // A Read-origin fold gathers the FOLDED VALUE (always Ext, 4
                    // cells) per use — role-neutral, NOT the origin's own field
                    // width (Task 3's origin-width split lives only in cost.rs).
                    // A VS-origin fold uses the O(k) multilinear closed form
                    // (Task 7): compute-only, zero DRAM, so it is NOT tallied
                    // into the search-facing fold traffic (fold_uses is still
                    // counted — it is a real Special operand occurrence).
                    if !origin.is_vs() {
                        ext.fold_traffic += 4;
                    }
                }
                // Legacy source-form Coefficient/AccInit descriptors are scalar-pure
                // recipe values the interp evaluates locally from consts/derived_e4 —
                // no DRAM, no fold buffer. New fragment programs reference them through
                // logical batch metadata and encoded sinks instead, so they do not enter
                // this operand tally.
                Some(BwdSpecial::Coefficient { .. }) | Some(BwdSpecial::AccInit) => {
                    stats.ldc_reads += 1;
                }
                // A dense bwd table has a desc for every index a Special operand
                // can name; None means the program referenced an out-of-range desc.
                None => debug_assert!(false, "bwd Special operand names an unknown desc {desc}"),
            },
        }
    };
    for instr in &program.instrs {
        match instr {
            Instr::Mov {
                dir,
                dst,
                src,
                field,
                ..
            } => {
                stats.op_counts[OP_MOV] += 1;
                if let Some(op) = src {
                    tally(op, *field, &mut stats, &mut ext);
                }
                if matches!(
                    dir,
                    crate::fwd::isa::MovDir::DstFromAcc | crate::fwd::isa::MovDir::DstFromSrc
                ) && matches!(dst, Some(DstLine::Smem { .. }))
                {
                    stats.cell_stores += 1;
                }
                if *dir == crate::fwd::isa::MovDir::DstFromAcc
                    && dst
                        .as_ref()
                        .is_some_and(|dst| unpack_batch_dst(dst).is_some())
                {
                    match field {
                        OperandField::Base => ext.batch_fma_base += 1,
                        OperandField::Ext => ext.batch_fma_ext += 1,
                    }
                }
            }
            Instr::Add {
                field, operands, ..
            } => {
                stats.op_counts[OP_ADD] += 1;
                for op in operands {
                    tally(op, *field, &mut stats, &mut ext);
                }
            }
            Instr::Mul {
                field, operands, ..
            } => {
                stats.op_counts[OP_MUL] += 1;
                for op in operands {
                    tally(op, *field, &mut stats, &mut ext);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                stats.op_counts[OP_FMA] += 1;
                for (l, r) in pairs {
                    tally(l, *field_lhs, &mut stats, &mut ext);
                    tally(r, *field_rhs, &mut stats, &mut ext);
                }
            }
        }
    }
    // Fold-side gather descriptor count (the bwd sibling of fwd's peek-only
    // `special_gathers`): VirtualSetup descs are resolver-computed, excluded.
    stats.special_gathers = (0..specials.len() as u16)
        .filter(|&i| matches!(specials.get(i), Some(BwdSpecial::FoldSource { .. })))
        .count();
    (stats, ext)
}

fn tally_fold_source(
    desc: u16,
    specials: &BwdSpecialTable,
    stats: &mut CompileStats,
    ext: &mut BwdTrafficStats,
) {
    stats.special_reads += 1;
    ext.fold_uses += 1;
    if matches!(
        specials.get(desc),
        Some(BwdSpecial::FoldSource { origin }) if !origin.is_vs()
    ) {
        ext.fold_traffic += 4;
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::batch::{unpack_batch_dst, BATCH_COEFFICIENT_ONE};
    use crate::bwd::distill::{bind, distill};
    use crate::bwd::source::MaterializationPolicy;
    use crate::fwd::encode::encode;
    use crate::fwd::isa::MovDir;
    use gkr_eval_ir::{
        BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo, DagLayer, ReadPlace,
        Root, RootGroup, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };
    use std::collections::{BTreeMap, HashMap};

    // ── layer-building helpers (claim-only roots — bwd shape) ────────────────

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column },
            },
        }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    fn layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
        let batching = BatchingOrder {
            roots: roots
                .iter()
                .enumerate()
                .filter(|(_, r)| r.claim.is_some())
                .map(|(i, _)| gkr_eval_ir::RootId(i as u32))
                .collect(),
        };
        DagLayer {
            sources,
            exprs,
            roots,
            batching,
            resolutions: BTreeMap::new(),
        }
    }

    /// All-sites decisions at priority 1.0 over the DISTILLED domain.
    fn all_sites(d: &DistilledLayer) -> SiteDecisions {
        SiteDecisions::new(distilled_site_domain(d).into_iter().map(|k| (k, 1.0)))
    }

    // ── terminal-acc invariant helpers ────────────────────────────────────────

    /// Spec §3: (i) `GlobalMaterialize` appears nowhere; (ii) the LAST instruction
    /// leaves the value in acc — an arith op (acc-folding) or `Mov AccFromSrc`.
    fn assert_result_in_acc(p: &Program) {
        assert!(!p.instrs.is_empty(), "bwd program must not be empty");
        for i in &p.instrs {
            if let Instr::Mov {
                dst: Some(DstLine::GlobalMaterialize { .. }),
                ..
            } = i
            {
                panic!("bwd program must never emit GlobalMaterialize: {i:?}");
            }
        }
        match p.instrs.last().unwrap() {
            Instr::Add { .. } | Instr::Mul { .. } | Instr::Fma { .. } => {}
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                ..
            } => {}
            other => panic!("terminal instruction must leave the root value in acc: {other:?}"),
        }
    }

    fn for_each_operand(p: &Program, mut f: impl FnMut(&OperandLine)) {
        for instr in &p.instrs {
            match instr {
                Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                    operands.iter().for_each(&mut f)
                }
                Instr::Fma { pairs, .. } => pairs.iter().for_each(|(l, r)| {
                    f(l);
                    f(r);
                }),
                Instr::Mov { src: Some(op), .. } => f(op),
                Instr::Mov { src: None, .. } => {}
            }
        }
    }

    fn count_desc_uses(p: &Program, desc: u16) -> usize {
        let mut n = 0;
        for_each_operand(p, |op| {
            if matches!(op, OperandLine::Special { desc: d } if *d == desc) {
                n += 1;
            }
        });
        n
    }

    fn count_smem_reads(p: &Program) -> usize {
        let mut n = 0;
        for_each_operand(p, |op| {
            if matches!(op, OperandLine::Smem { .. }) {
                n += 1;
            }
        });
        n
    }

    #[test]
    fn fragment_compiler_emits_one_independent_sink_per_fragment() {
        let l = layer(
            vec![read_src(0), read_src(1)],
            vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1))],
            vec![claim_only_root(ExprId(0), 0), claim_only_root(ExprId(1), 1)],
        );
        let d = distill(&l, crate::BwdRegime::R0, &HashMap::new(), None);
        assert_eq!(d.fragments.fragments.len(), 2);
        let (_, coefficient_descs, acc_init_desc) = fragment_descs(&d);
        let c = compile_distilled_fragments(&d, 16, None).unwrap();

        assert_eq!(c.acc_init_desc, acc_init_desc);
        let sinks = c
            .program
            .instrs
            .iter()
            .filter_map(|instr| match instr {
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field,
                    dst: Some(dst),
                    src: None,
                } => unpack_batch_dst(dst).map(|desc| (*field, desc)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            sinks,
            coefficient_descs
                .iter()
                .map(|desc| (OperandField::Base, desc.unwrap_or(BATCH_COEFFICIENT_ONE)))
                .collect::<Vec<_>>()
        );
        assert_eq!(c.stats_ext.batch_fma_base, 2);
        assert_eq!(c.stats_ext.batch_fma_ext, 0);
        for_each_operand(&c.program, |operand| {
            assert!(!matches!(
                operand,
                OperandLine::Special { desc }
                    if coefficient_descs.contains(&Some(*desc))
                        || Some(*desc) == acc_init_desc
            ));
        });
    }

    // ── Coefficient / AccInit tally (Task 3) ──────────────────────────────────

    /// Reads of Coefficient/AccInit descriptors tally as `ldc_reads` and
    /// contribute ZERO to every DRAM / fold traffic class (they are locally
    /// evaluated scalar-pure recipe values, not fold-side gathers).
    #[test]
    fn coefficient_and_acc_init_reads_tally_as_ldc_zero_traffic() {
        let mut specials = BwdSpecialTable::default();
        let acc = specials.intern(BwdSpecial::AccInit);
        let coeff = specials.intern(BwdSpecial::Coefficient { fragment: 0 });

        // Mov Acc<-AccInit ; Mul × [Coefficient{0}, Coefficient{0}] : 3 reads.
        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Ext,
                    dst: None,
                    src: Some(OperandLine::Special { desc: acc }),
                },
                Instr::Mul {
                    field: OperandField::Ext,
                    promote: false,
                    negate_acc: false,
                    operands: vec![
                        OperandLine::Special { desc: coeff },
                        OperandLine::Special { desc: coeff },
                    ],
                },
            ],
        };

        let (stats, ext) = tally_bwd_program(&program, &specials, &SourceWindowTable::default());

        assert_eq!(
            stats.ldc_reads, 3,
            "1 AccInit + 2 Coefficient reads count as ldc_reads"
        );
        assert_eq!(stats.dram_reads, 0);
        assert_eq!(stats.dram_traffic, 0);
        assert_eq!(
            stats.special_reads, 0,
            "coeff/acc-init are not fold-side special gathers"
        );
        assert_eq!(stats.special_gathers, 0);
        assert_eq!(stats.cell_reads, 0);
        assert_eq!(
            ext,
            BwdTrafficStats::default(),
            "zero global / fold_uses / fold_traffic for coeff/acc-init"
        );
    }

    // ── (a)+(c): bare Read-leaf root — R0 Global / Ext FoldSource ─────────────

    #[test]
    fn terminal_bare_read_leaf_root() {
        // Single claim-only root whose cone is a bare Read leaf.
        let l = layer(
            vec![read_src(0)],
            vec![Expr::Source(SourceId(0))],
            vec![claim_only_root(ExprId(0), 0)],
        );
        // (a) R0: the leaf is a final plain source read.
        let d = distill(&l, crate::BwdRegime::R0, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("R0 compile");
        assert_result_in_acc(&c.program);
        assert_eq!(
            c.program.instrs.len(),
            1,
            "source-only root is one Mov AccFromSrc"
        );
        assert!(
            matches!(
                &c.program.instrs[0],
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    src: Some(OperandLine::Source {
                        first_access: true,
                        ..
                    }),
                    ..
                }
            ),
            "R0 bare Read root must be Mov AccFromSrc <- first Source, got {:?}",
            c.program.instrs[0]
        );
        assert_eq!(c.stats_ext.fold_uses, 0);
        assert!(c.stats_ext.global > 0);

        // (c) Ext: this legacy compiler represents the leaf as a FoldSource
        // Special in the BWD namespace. The shared eval-plan compiler moves
        // read-origin folds onto final Source lanes instead.
        let d = distill(&l, crate::BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("Ext compile");
        assert_result_in_acc(&c.program);
        assert_eq!(c.program.instrs.len(), 1);
        let Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Ext,
            src: Some(OperandLine::Special { desc }),
            ..
        } = &c.program.instrs[0]
        else {
            panic!(
                "Ext bare Read root must be Mov{{Ext}} AccFromSrc <- Special, got {:?}",
                c.program.instrs[0]
            );
        };
        assert!(
            matches!(c.specials.get(*desc), Some(BwdSpecial::FoldSource { .. })),
            "the desc must be a FoldSource in the BWD table"
        );
        assert_eq!(
            c.stats_ext,
            BwdTrafficStats {
                global: 0,
                fold_uses: 1,
                fold_traffic: 4,
                batch_fma_base: 0,
                batch_fma_ext: 0,
            }
        );
    }

    // ── (b): bare Challenge root ──────────────────────────────────────────────

    #[test]
    fn terminal_bare_challenge_root() {
        let l = layer(
            vec![SourceInfo {
                kind: SourceKind::Challenge {
                    reference: ChallengeRef {
                        key: ChallengeKey::ClaimBatching,
                        power: ChallengePower::One,
                    },
                },
            }],
            vec![Expr::Source(SourceId(0))],
            vec![claim_only_root(ExprId(0), 0)],
        );
        for regime in [crate::BwdRegime::R0, crate::BwdRegime::Ext] {
            let d = distill(&l, regime, &HashMap::new(), None);
            let c = compile_distilled(&d, 16, None).expect("compile");
            assert_result_in_acc(&c.program);
            assert!(
                matches!(
                    &c.program.instrs[0],
                    Instr::Mov {
                        dir: MovDir::AccFromSrc,
                        src: Some(OperandLine::Ldc { .. }),
                        ..
                    }
                ),
                "challenge root must load from an Ldc bank, got {:?}",
                c.program.instrs[0]
            );
        }
    }

    // ── (d): compound root ────────────────────────────────────────────────────

    #[test]
    fn terminal_compound_root() {
        // root = w0*w1 + w2 (one claim root, so the spine IS the cone).
        let l = layer(
            vec![read_src(0), read_src(1), read_src(2)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = w2
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 3 = w0*w1
                Expr::Add(vec![ExprId(3), ExprId(2)]), // 4 = root
            ],
            vec![claim_only_root(ExprId(4), 0)],
        );
        for regime in [crate::BwdRegime::R0, crate::BwdRegime::Ext] {
            let d = distill(&l, regime, &HashMap::new(), None);
            let c = compile_distilled(&d, 16, None).expect("compile");
            assert_result_in_acc(&c.program);
            assert!(
                matches!(
                    c.program.instrs.last().unwrap(),
                    Instr::Add { .. } | Instr::Mul { .. } | Instr::Fma { .. }
                ),
                "compound root must terminate in an acc-folding arith op"
            );
            assert!(c.stats.program_lanes > 1);
        }
    }

    // ── (e): admissions under pressure — admitted-then-evicted, tight budget ──

    #[test]
    fn terminal_under_admission_and_eviction_pressure() {
        // Shared Ext compound c1 = w0 + w1 used by three claim roots; Ext regime
        // at b8 (2 ext buckets): the spill temp + an admitted c1 fill the file, so
        // subsequent mandatory temps force-evict the resident — the compile must
        // still terminate with the root value in acc and fit max_live_cells <= 8.
        let l = layer(
            vec![read_src(0), read_src(1), read_src(2), read_src(3)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = w2
                Expr::Source(SourceId(3)),             // 3 = w3
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 4 = c1 (shared)
                Expr::Mul(vec![ExprId(4), ExprId(2)]), // 5 = c1*w2
                Expr::Mul(vec![ExprId(4), ExprId(3)]), // 6 = c1*w3
                Expr::Add(vec![ExprId(4), ExprId(2)]), // 7 = c1+w2
            ],
            vec![
                claim_only_root(ExprId(5), 0),
                claim_only_root(ExprId(6), 1),
                claim_only_root(ExprId(7), 2),
            ],
        );
        let d = distill(&l, crate::BwdRegime::Ext, &HashMap::new(), None);
        let decisions = all_sites(&d);
        let c = compile_distilled(&d, 8, Some(&decisions)).expect("b8 compile under pressure");
        assert_result_in_acc(&c.program);
        assert!(
            c.stats.max_live_cells <= 8,
            "placement must fit b8, got {}",
            c.stats.max_live_cells
        );
        assert!(
            c.stats.cell_reads > 0,
            "spill/residency traffic expected under pressure"
        );
        assert!(c.stats.cell_stores > 0);
    }

    // ── replay/serve + admission alignment (rewritten LookupValue + FoldSource) ──

    /// Canonical: q = w0 + w1; lv = LookupValue{query = q}; root = lv*lv + w2.
    /// Distilled (Ext): the lv leaf is REWRITTEN to q (fan-out 2 site) and the
    /// Read leaves become FoldSources.
    fn lookup_fold_layer() -> DagLayer {
        layer(
            vec![
                read_src(0),
                read_src(1),
                SourceInfo {
                    kind: SourceKind::LookupValue {
                        kind: gkr_eval_ir::LookupValueKind::GenericColumn { column: 0 },
                        set_index: 0,
                        query: ExprId(2),
                    },
                },
                read_src(2),
            ],
            vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = q (the query)
                Expr::Source(SourceId(2)),             // 3 = lv
                Expr::Source(SourceId(3)),             // 4 = w2
                Expr::Mul(vec![ExprId(3), ExprId(3)]), // 5 = lv*lv
                Expr::Add(vec![ExprId(5), ExprId(4)]), // 6 = root
            ],
            vec![claim_only_root(ExprId(6), 0)],
        )
    }

    /// Locate distilled leaf ExprIds by their Read column, and q as the Add of
    /// the two w0/w1 leaves.
    fn find_distilled_ids(d: &DistilledLayer) -> (ExprId, ExprId, ExprId, ExprId) {
        let mut w = BTreeMap::new(); // column -> leaf ExprId
        for (i, e) in d.layer.exprs.iter().enumerate() {
            if let Expr::Source(sid) = e {
                if let SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column },
                } = &d.layer.sources[sid.0 as usize].kind
                {
                    w.insert(*column, ExprId(i as u32));
                }
            }
        }
        let (w0, w1, w2) = (w[&0], w[&1], w[&2]);
        let q = d
            .layer
            .exprs
            .iter()
            .enumerate()
            .find_map(|(i, e)| match e {
                Expr::Add(ch) if ch.len() == 2 && ch.contains(&w0) && ch.contains(&w1) => {
                    Some(ExprId(i as u32))
                }
                _ => None,
            })
            .expect("distilled q = Add(w0, w1)");
        (w0, w1, w2, q)
    }

    /// Drain a value's occurrence stream, returning its total queued count.
    fn drain(streams: &mut OccurrenceStreams, v: ExprId) -> usize {
        let mut n = 0;
        while streams.effective_priority(v).is_some() {
            streams.serve(v);
            n += 1;
        }
        n
    }

    #[test]
    fn replay_serve_counts_match_uncached_emission() {
        let l = lookup_fold_layer();
        let d = distill(&l, crate::BwdRegime::Ext, &HashMap::new(), None);
        // The LookupValue leaf must be gone (rewritten to its query).
        assert!(!d
            .layer
            .sources
            .iter()
            .any(|s| matches!(s.kind, SourceKind::LookupValue { .. })));
        let (w0, w1, w2, q) = find_distilled_ids(&d);
        let root_expr = d.layer.roots[d.root.0 as usize].expr;
        let terms = spine_terms(&d);
        assert_eq!(terms.len(), 2, "spine = [Mul(q,q), w2] after flatten");

        // Replay stream counts.
        let decisions = all_sites(&d);
        let mut streams = OccurrenceStreams::build_bwd_root(
            &d.layer,
            d.root,
            root_expr,
            &terms,
            &decisions,
            &distilled_site_domain(&d),
        );
        assert_eq!(drain(&mut streams, root_expr), 1, "one RootOutput serve");
        assert_eq!(
            drain(&mut streams, q),
            2,
            "q demanded once per Mul operand slot"
        );
        assert_eq!(
            drain(&mut streams, w0),
            2,
            "w0 demanded once per q recompute"
        );
        assert_eq!(drain(&mut streams, w1), 2);
        assert_eq!(
            drain(&mut streams, w2),
            0,
            "w2 is a spine TERM — the driver decomposes it, no operand site of its own"
        );

        // Uncached emission: every serve of a leaf is exactly one Special use.
        let c = compile_distilled(&d, 16, None).expect("uncached compile");
        assert_result_in_acc(&c.program);
        let desc_of = |e: ExprId| *d.leaf_descs.get(&e).expect("fold leaf desc");
        assert_eq!(count_desc_uses(&c.program, desc_of(w0)), 2);
        assert_eq!(count_desc_uses(&c.program, desc_of(w1)), 2);
        assert_eq!(
            count_desc_uses(&c.program, desc_of(w2)),
            1,
            "one use as a term"
        );
        assert_eq!(c.stats_ext.fold_uses, 5);
        assert_eq!(c.stats_ext.fold_traffic, 20);
    }

    #[test]
    fn replay_admission_reflects_in_emission() {
        // With decisions, q (fan-out 2, in the distilled domain) is admitted at
        // its first demand: one recompute (w0/w1 gathered ONCE) + a cell re-read.
        let l = lookup_fold_layer();
        let d = distill(&l, crate::BwdRegime::Ext, &HashMap::new(), None);
        let (w0, w1, w2, _q) = find_distilled_ids(&d);
        let decisions = all_sites(&d);
        let c = compile_distilled(&d, 16, Some(&decisions)).expect("cached compile");
        assert_result_in_acc(&c.program);
        let desc_of = |e: ExprId| *d.leaf_descs.get(&e).expect("fold leaf desc");
        assert_eq!(
            count_desc_uses(&c.program, desc_of(w0)),
            1,
            "q recomputed once (admitted)"
        );
        assert_eq!(count_desc_uses(&c.program, desc_of(w1)), 1);
        assert_eq!(count_desc_uses(&c.program, desc_of(w2)), 1);
        assert!(
            count_smem_reads(&c.program) > 0,
            "q's second use must read its cell"
        );
    }

    // ── bindings invariance ───────────────────────────────────────────────────

    #[test]
    fn program_bytes_invariant_across_bindings() {
        let l = lookup_fold_layer();
        let d = distill(&l, crate::BwdRegime::Ext, &HashMap::new(), None);
        let decisions = all_sites(&d);

        let c1 = compile_distilled(&d, 16, Some(&decisions)).expect("compile 1");
        let b0 = bind(&d, MaterializationPolicy::AlwaysMaterialize, 0);
        let b1 = bind(&d, MaterializationPolicy::LazyUpTo(2), 5);
        assert_ne!(
            b0.states, b1.states,
            "bindings genuinely vary (non-vacuous)"
        );

        let c2 = compile_distilled(&d, 16, Some(&decisions)).expect("compile 2");
        let e1 = encode(&c1.program).expect("encode 1");
        let e2 = encode(&c2.program).expect("encode 2");
        assert_eq!(
            e1, e2,
            "compile takes no bindings: bytes identical across bind() variations"
        );
    }
}
