//! Task 9 (CS-M0): the engine driver [`cs_schedule_bwd_layer`] — the top-level
//! assembly of the hint-model backward-schedule pipeline.
//!
//! ## Revision 4 (hint-model, binding)
//!
//! `compile + certify` is the SOLE decision authority; the offline model is only a
//! ranking hint. This driver wires the four consumed stages into one non-regressing
//! schedule:
//!
//! 1. **Canonical baseline** — `distill(.., None)` + [`compile_distilled_traced`] at
//!    `budget`: the exact uncached per-demand-recompute compile the fixture gates pin.
//!    It is BOTH the non-regression floor and the fallback if the CS path errors or
//!    fails to beat it.
//! 2. **Constructive order** — [`construct_unit_order`] over the canonical reuse
//!    structure yields a deterministic unit permutation; `distill(.., Some(&perm))`
//!    re-interns in that order.
//! 3. **Priced greedy** — [`coordinate_correct_frozen`] seeds the `lower==place==
//!    budget` all-`Bypass` frozen demand, then [`priced_rounds`] runs the
//!    compiler-in-the-loop compound + leaf reclaim (compile+certify validated per
//!    candidate; the model never selects).
//! 4. **Ship + certify** — the returned plan is recompiled to the SHIPPED program via
//!    [`compile_distilled_planned`], then [`certify`]d.
//!
//! ## Non-regression by construction
//!
//! Mirrors `search_bwd_layer` (`bwd/search.rs:475-483`): the CS lexicographic key
//! `(infeasible, traffic, instrs)` must STRICTLY beat the canonical baseline's;
//! otherwise the baseline outcome is returned (`plan: None`, identity permutation,
//! `fell_back_to_baseline: true`). Any `Err` anywhere in the CS path (a
//! `BudgetBelowFloor` from a construction that raised the placement floor above
//! `budget`, or otherwise) also falls back — the engine NEVER panics on a schedule
//! problem. The forward program is untouched: this is a bwd/new-module + test-only
//! addition, so fwd byte-identity is inviolable by construction.
//!
//! ## CS-M5a Task 10: error-isolated fragment candidate with term floor
//!
//! The engine now evaluates TWO CS candidates as INDEPENDENT `Result`s and ships the
//! lexicographic minimum of `{baseline} ∪ {successful candidates}`:
//!
//! * **term-CS** — the constructive-order + priced-greedy [`TermBackend`] pipeline above
//!   (unchanged, byte-identical: `bwd_backend_neutrality` pins it);
//! * **fragment-CS** — the full-decomposition [`FragmentBackend`] pipeline over the
//!   canonical distillation: `construct_fragment_order` →
//!   `coordinate_correct_frozen_with_backend` → `priced_rounds_with_backend` →
//!   `backend.planned` ship → `certify`.
//!
//! Error isolation is genuine: each candidate is a `Result` consulted via `.ok()`, so one
//! candidate's `Err` (e.g. a fragment pricing/compile failure on an R0 layer) NEVER
//! discards the other candidate or the baseline. A certify-`Err` (or a divergent replay)
//! marks the candidate infeasible via [`report_and_feasible`], and an infeasible candidate
//! sorts AFTER the always-feasible baseline — so it can never ship (rejection, not panic).
//! Ties prefer the earlier option (baseline over term over fragment): a candidate replaces
//! the running best ONLY on a STRICT key improvement. `CsOutcome::fragment_order` is
//! `Some` IFF the fragment candidate is the shipped winner (it strictly beat both the term
//! candidate and the baseline).

use std::collections::HashMap;

use gkr_eval_ir::{DagLayer, ExprId, FieldKind, ReadPlace};

use super::compile::{
    compile_distilled_planned, compile_distilled_traced, BwdCompileBackend, BwdCompiledLayer,
    BwdTrafficStats, FragmentBackend,
};
use super::construct::{construct_fragment_order, construct_unit_order};
use super::distill::{distill, stable_distilled_site_domain, DistilledLayer};
use super::fif::{coordinate_correct_frozen, coordinate_correct_frozen_with_backend};
use super::plan::BwdOccurrencePlan;
use super::price::{
    priced_rounds, priced_rounds_with_backend, LeafReclaimCounters, PRODUCTION_GAP_CAP, RECLAIM_N,
};
use super::trace::{certify, BwdCompileTrace, BwdEvent, CertificateReport};
use crate::fwd::error::CompileError;

/// The full outcome of one [`cs_schedule_bwd_layer`] run.
///
/// `compiled` is the SHIPPED backward program — the value-parity gate and the Task-11
/// comparator run against it directly, with no re-derivation — and `pins` (the
/// committed compound cone-suppression set) feeds the comparator ledger.
/// `stats`/`instrs`/`certificate` describe exactly `compiled`; `rounds`/`converged`
/// report the priced-round activity that produced the CS `plan`.
///
/// `fell_back_to_baseline` records whether the CS path failed to beat (or errored out
/// below) the canonical baseline. When it is `true`, `compiled` is the canonical
/// `decisions:None` baseline compile, `plan` is `None`, `unit_permutation` is the
/// identity `0..n`, `pins` is empty, and `rounds`/`converged` are `0`/`false`.
///
/// The TERM-FLOOR probe [`CsOutcome::term_floor`] (CS-M5a Task 10, RR resolution) exposes
/// the program the engine WOULD have shipped WITHOUT the fragment candidate — the
/// lexicographic-min of `{baseline, term-CS}` — so `bwd_backend_neutrality` can keep
/// byte-pinning the TERM pricing path (its constants stay literally unchanged) even when
/// the fragment candidate wins the SHIPPED slot. `term_leaf_calls`/`fragment_leaf_calls`
/// expose each candidate's priced-search cost independently of which one shipped, so the
/// per-search `leaf_calls` guardrail applies PER CANDIDATE.
/// CS-M5a Task 10 (RR resolution): the TERM-FLOOR program — the lexicographic-min of
/// `{baseline, term-CS}`, i.e. what the engine would ship if the fragment candidate did not
/// exist. Carries everything `bwd_backend_neutrality` needs to byte-check the TERM pricing
/// path without regenerating its pinned constants: the compiled program + descriptor table
/// (for the digest) and stats (`compiled`), the certificate counts (`certificate`), and the
/// term-CS plan's `entries_fnv` (`plan_entries_fnv`, `None` when the baseline is the floor —
/// the pre-fragment engine shipped the baseline there, whose `plan` was `None`).
#[derive(Clone, Debug)]
pub struct TermFloorProbe {
    pub compiled: BwdCompiledLayer,
    pub certificate: CertificateReport,
    pub plan_entries_fnv: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct CsOutcome {
    pub unit_permutation: Vec<usize>,
    pub plan: Option<BwdOccurrencePlan>,
    pub compiled: BwdCompiledLayer,
    pub pins: Vec<ExprId>,
    pub stats: BwdTrafficStats,
    pub instrs: usize,
    pub certificate: CertificateReport,
    pub rounds: usize,
    pub converged: bool,
    pub fell_back_to_baseline: bool,
    /// CS-M5a (Task 10): the constructed FRAGMENT order (`construct_fragment_order`, a
    /// permutation of `0..d.fragments.fragments.len()`) IFF the fragment-CS candidate is
    /// the shipped winner — `Some` ⟺ fragment shipped. `None` when the term-CS candidate or
    /// the canonical baseline won. The value-parity gate reconstructs the fragment winner by
    /// replaying `plan` through the fragment pipeline at this order.
    pub fragment_order: Option<Vec<usize>>,
    /// CS-M5a (Task 10, RR resolution): the TERM-FLOOR probe — the lexicographic-min of
    /// `{baseline, term-CS}`, i.e. exactly what the engine would ship if the fragment
    /// candidate did not exist. `bwd_backend_neutrality` compares against THIS so the term
    /// pricing path stays byte-pinned regardless of the shipped winner.
    ///
    /// CS-M5a final-review follow-up: `TermFloorProbe` carries a CLONED
    /// `BwdCompiledLayer` (the whole program + descriptor table), and its only consumer is
    /// `bwd_backend_neutrality`. `None` on every PRODUCTION call ([`cs_schedule_bwd_layer`],
    /// [`cs_schedule_bwd_layer_research`]) — the clone is skipped entirely, not merely
    /// discarded. `Some` only via [`cs_schedule_bwd_layer_with_term_floor`], the probe-
    /// enabled sibling `bwd_backend_neutrality` calls. Winner selection is unaffected
    /// either way: the probe is derived FROM the already-computed candidates, after the
    /// lexicographic-min selection has run.
    pub term_floor: Option<TermFloorProbe>,
    /// CS-M5a (Task 10, RR resolution): the term-CS candidate's priced-search `leaf_calls`
    /// (`None` if that candidate errored out — no completed priced run). Guardrail scope:
    /// the per-search `HARD_MAX` applies to this INDEPENDENTLY of the shipped winner.
    pub term_leaf_calls: Option<usize>,
    /// CS-M5a (Task 10, RR resolution): the fragment-CS candidate's priced-search
    /// `leaf_calls` (`None` if that candidate errored out). Same per-search guardrail scope.
    pub fragment_leaf_calls: Option<usize>,
    /// CS-M4 (Task 2): the priced run's leaf-reclaim counters (Task 2 populates only the
    /// residual-gap fields; the rest arrive in Tasks 3/4). Default (all `0`) on fallback.
    pub counters: LeafReclaimCounters,
    /// CS-M4 (Task 2): any round's leaf reclaim returned `Incomplete` (spec §3). Always
    /// `false` in Task 2; `false` on fallback.
    pub saw_incomplete_round: bool,
    /// CS-M4 (Task 2, spec §5): per-run leaf-search `compile_distilled_planned` count
    /// (the budget-scoped cost). `0` on fallback.
    pub leaf_calls: usize,
    /// CS-M4 (Task 2, spec §5): per-run base+compound compile count (UNBUDGETED,
    /// reported separately from `leaf_calls`). `0` on fallback.
    pub base_compound_calls: usize,
    /// CS-M4 (Task 2, spec §5): `Σ_r G_r` (realized leaf gaps). `0` on fallback.
    pub sum_g: usize,
    /// CS-M4 (Task 2, spec §5): `Σ_r min(G_r, 1200)` (accrual reference quota). `0` on
    /// fallback.
    pub sum_quota: usize,
}

/// The lexicographic non-regression key `(infeasible, traffic, instrs)` — lower is
/// better, feasible (`false`) sorts first. Identical shape to `search_bwd_layer`'s
/// `objective_key`, so the CS driver's non-regression contract matches the GA search's.
fn schedule_key(infeasible: bool, traffic: usize, instrs: usize) -> (bool, usize, usize) {
    (infeasible, traffic, instrs)
}

/// True iff `trace` recorded a replay divergence from its plan.
fn diverged(trace: &BwdCompileTrace) -> bool {
    trace.events.iter().any(|e| matches!(e, BwdEvent::Diverge { .. }))
}

/// The certificate report of a compile+trace (regardless of pass/fail) plus whether the
/// pair is feasible: it certifies EXACTLY (`counted == reported`) AND never diverged.
fn report_and_feasible(
    c: &BwdCompiledLayer,
    trace: &BwdCompileTrace,
) -> (CertificateReport, bool) {
    match certify(c, trace) {
        Ok(r) => (r, !diverged(trace)),
        Err(r) => (r, false),
    }
}

/// One constructed CS candidate (term OR fragment), each computed as an INDEPENDENT
/// `Result` (CS-M5a Task 10): on any compile/pricing/certify error the producer returns
/// `Err`, and the caller consults it via `.ok()` so one candidate's failure never discards
/// the other candidate or the baseline. Returns the constructed permutation, the priced
/// plan/pins/round-counters, and the SHIPPED compile with its certificate report +
/// feasibility. `fragment_order` is `Some` for the fragment candidate (its constructed
/// fragment schedule order) and `None` for the term candidate — it flows into the shipped
/// [`CsOutcome::fragment_order`] IFF this candidate wins.
struct CsPath {
    unit_permutation: Vec<usize>,
    fragment_order: Option<Vec<usize>>,
    plan: BwdOccurrencePlan,
    pins: Vec<ExprId>,
    compiled: BwdCompiledLayer,
    report: CertificateReport,
    feasible: bool,
    rounds: usize,
    converged: bool,
    counters: LeafReclaimCounters,
    saw_incomplete_round: bool,
    leaf_calls: usize,
    base_compound_calls: usize,
    sum_g: usize,
    sum_quota: usize,
}

impl CsPath {
    /// The lexicographic candidate key — the SAME `schedule_key(!feasible, traffic,
    /// program_lanes)` used against the baseline. An infeasible candidate (certify-`Err`
    /// or divergent replay marks `feasible=false`) sorts after the always-feasible
    /// baseline, so it cannot ship.
    fn key(&self) -> (bool, usize, usize) {
        let traffic = self.compiled.stats_ext.global + self.compiled.stats_ext.fold_traffic;
        schedule_key(!self.feasible, traffic, self.compiled.stats.program_lanes)
    }
}

/// The constructive TERM CS path (CS-M5a Task 10: one of the two independent candidates).
/// On any compile error it returns `Err`; the caller consults it via `.ok()`, so a term
/// failure isolates to the term candidate alone (the fragment candidate and the baseline
/// are unaffected). Returns the constructed unit permutation, the priced plan/pins/round-
/// counters, and the SHIPPED compile with its certificate report + feasibility.
#[allow(clippy::too_many_arguments)]
fn try_cs_path(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
    bl_d: &DistilledLayer,
    multiplier: usize,
    gap_cap: usize,
    enforce_budget: bool,
) -> Result<CsPath, CompileError> {
    // (2) constructive order off the canonical distillation's reuse structure.
    let stable_domain = stable_distilled_site_domain(bl_d);
    let perm = construct_unit_order(layer, bl_d, &stable_domain);

    // (3) re-distill in the constructed order, seed the coordinate-correct frozen
    // demand, and run the compiler-in-the-loop priced greedy.
    let d = distill(layer, regime, cross, Some(&perm));
    let frozen0 = coordinate_correct_frozen(&d, budget)?;
    let outcome = priced_rounds(&d, budget, frozen0, multiplier, gap_cap, enforce_budget)?;

    // (4) recompile the returned plan to the SHIPPED program, then certify it.
    let (compiled, trace) = compile_distilled_planned(&d, budget, &outcome.plan)?;
    let (report, feasible) = report_and_feasible(&compiled, &trace);

    Ok(CsPath {
        unit_permutation: perm,
        fragment_order: None,
        plan: outcome.plan,
        pins: outcome.pins,
        compiled,
        report,
        feasible,
        rounds: outcome.rounds,
        converged: outcome.converged,
        counters: outcome.counters,
        saw_incomplete_round: outcome.saw_incomplete_round,
        leaf_calls: outcome.leaf_calls,
        base_compound_calls: outcome.base_compound_calls,
        sum_g: outcome.sum_g,
        sum_quota: outcome.sum_quota,
    })
}

/// The FULL-DECOMPOSITION (fragment) CS path (CS-M5a Task 10) — the term-path sibling of
/// [`try_cs_path`], evaluated as an INDEPENDENT `Result` over the SAME canonical
/// distillation `d` (`distill(.., None)`). It never re-interns units (fragment mode is
/// plan-driven, not order-permuted at the unit level); instead it carries the constructed
/// FRAGMENT order through the [`FragmentBackend`], which the whole pricing stack (Task 6)
/// is parameterized over. The pipeline is exactly the `fif.rs`-mandated fragment seed +
/// priced greedy + ship + certify:
///
/// 1. `order = construct_fragment_order(...)` (Task 7);
/// 2. `frozen0 = coordinate_correct_frozen_with_backend(d, budget, &FragmentBackend{order})`
///    (Task 6 — the doc-mandated planned all-`Bypass` `lower==place==budget` seed);
/// 3. `priced_rounds_with_backend(&FragmentBackend{order}, ..)` (Task 6);
/// 4. `backend.planned(d, budget, &plan)` ship, then [`certify`] via
///    [`report_and_feasible`] (certify-`Err` ⟹ `feasible=false` ⟹ cannot ship).
///
/// Any `Err` (a fragment pricing/compile failure — e.g. the known R0 `ExtCellMisaligned`
/// on some Retain admissions) propagates out; the caller's `.ok()` isolates it so the term
/// candidate and baseline are untouched.
#[allow(clippy::too_many_arguments)]
fn try_fragment_path(
    layer: &DagLayer,
    budget: usize,
    d: &DistilledLayer,
    multiplier: usize,
    gap_cap: usize,
    enforce_budget: bool,
) -> Result<CsPath, CompileError> {
    // (a) constructive FRAGMENT order off the canonical distillation's fragment-granular
    // reuse structure — a permutation of `0..d.fragments.fragments.len()`.
    let stable_domain = stable_distilled_site_domain(d);
    let order = construct_fragment_order(layer, d, &stable_domain);
    let backend = FragmentBackend { order: order.clone() };

    // (b) coordinate-correct fragment freeze (NEVER a raw traced freeze), then the
    // backend-parameterized compiler-in-the-loop priced greedy.
    let frozen0 = coordinate_correct_frozen_with_backend(d, budget, &backend)?;
    let outcome =
        priced_rounds_with_backend(&backend, d, budget, frozen0, multiplier, gap_cap, enforce_budget)?;

    // (c) recompile the returned plan to the SHIPPED fragment program, then certify it.
    let (compiled, trace) = backend.planned(d, budget, &outcome.plan)?;
    let (report, feasible) = report_and_feasible(&compiled, &trace);

    Ok(CsPath {
        // Fragment mode does not permute units; the shipped program is compiled from the
        // canonical distillation. The identity keeps `unit_permutation` well-formed while
        // `fragment_order` carries the fragment schedule the reconstruction replays.
        unit_permutation: (0..d.unit_order.len()).collect(),
        fragment_order: Some(order),
        plan: outcome.plan,
        pins: outcome.pins,
        compiled,
        report,
        feasible,
        rounds: outcome.rounds,
        converged: outcome.converged,
        counters: outcome.counters,
        saw_incomplete_round: outcome.saw_incomplete_round,
        leaf_calls: outcome.leaf_calls,
        base_compound_calls: outcome.base_compound_calls,
        sum_g: outcome.sum_g,
        sum_quota: outcome.sum_quota,
    })
}

/// Assemble the canonical-baseline `CsOutcome` (the non-regression fallback): identity
/// permutation, no plan, no pins, and the baseline compile's own stats/instrs/report.
#[allow(clippy::too_many_arguments)]
fn baseline_outcome(
    n_units: usize,
    bl_c: BwdCompiledLayer,
    bl_report: CertificateReport,
    term_floor: Option<TermFloorProbe>,
    term_leaf_calls: Option<usize>,
    fragment_leaf_calls: Option<usize>,
) -> CsOutcome {
    CsOutcome {
        unit_permutation: (0..n_units).collect(),
        plan: None,
        stats: bl_c.stats_ext,
        instrs: bl_c.stats.program_lanes,
        compiled: bl_c,
        pins: Vec::new(),
        certificate: bl_report,
        rounds: 0,
        converged: false,
        fell_back_to_baseline: true,
        // Fragment candidate did not win (baseline floor): no stored order.
        fragment_order: None,
        term_floor,
        term_leaf_calls,
        fragment_leaf_calls,
        // No priced run happened on fallback (spec §5): counters/costs default to 0/false.
        counters: LeafReclaimCounters::default(),
        saw_incomplete_round: false,
        leaf_calls: 0,
        base_compound_calls: 0,
        sum_g: 0,
        sum_quota: 0,
    }
}

/// Schedule one backward layer × regime at `budget` via the hint-model pipeline
/// (constructive order → coordinate-correct freeze → compiler-in-the-loop priced greedy
/// → certify → non-regression fallback). See the module docs for the full contract.
///
/// PRODUCTION entry: a thin wrapper over [`cs_schedule_bwd_layer_research`] at the fixed
/// production controls `(multiplier=1, gap_cap=PRODUCTION_GAP_CAP=1200, enforce_budget=true)`.
/// CS-M4 T7 banked `gap_cap=1200` after the G-M0 milestone (spec §12): the safety-net
/// floor reaches Tier 0 (all four) + Tier 1 (blake2 8348) there; Tier 2 (GA 7996) is
/// unreachable by the whole-origin machinery even un-starved. The multiplier stays `1`
/// (the credit lever is measured-inert). ~2.4× the CS-M3 `gap_cap=512` wall.
///
/// NEVER panics on a schedule problem: an infeasible or non-improving CS path falls
/// back to the canonical `decisions:None` baseline. It panics ONLY if even that
/// baseline is infeasible at `budget` — a genuine layer/budget problem (the
/// `PINNED_B16_INFEASIBLE` class), mirroring `search_bwd_layer`'s single hard-fail.
pub fn cs_schedule_bwd_layer(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> CsOutcome {
    cs_schedule_bwd_layer_impl(layer, regime, cross, budget, 1, PRODUCTION_GAP_CAP, true, false)
}

/// CS-M5a final-review follow-up: the PROBE-ENABLED sibling of [`cs_schedule_bwd_layer`] —
/// identical production controls `(multiplier=1, gap_cap=PRODUCTION_GAP_CAP, enforce_budget=
/// true)`, but with [`CsOutcome::term_floor`] populated (`Some`). This is the ONLY entry
/// that pays the `TermFloorProbe` clone; every other production/research entry sets it to
/// `None` without constructing it. Exists solely so `bwd_backend_neutrality` can byte-pin
/// the term pricing path — production code should keep calling [`cs_schedule_bwd_layer`].
pub fn cs_schedule_bwd_layer_with_term_floor(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> CsOutcome {
    cs_schedule_bwd_layer_impl(layer, regime, cross, budget, 1, PRODUCTION_GAP_CAP, true, true)
}

/// The RESEARCH entry (CS-M4 Task 2, spec §5): identical pipeline to
/// [`cs_schedule_bwd_layer`] but with the THREE independent leaf-reclaim controls
/// exposed — `multiplier` (scales accrued CREDITS; production 1, harness ≤2), `gap_cap`
/// (bounds Stage-B candidate COUNT; production `PRODUCTION_GAP_CAP`=1200 after T7, the
/// legacy `RECLAIM_N`=512 wall and Phase-0b 1200 are the other studied points), and
/// `enforce_budget` (whether the budget caps/reserves; production `true`, Phase-0b
/// `false` = count-only). This is the general three-knob form; PRODUCTION
/// ([`cs_schedule_bwd_layer`]) pins `(1, PRODUCTION_GAP_CAP, true)` — see its doc for
/// why T7 banked `gap_cap=1200`. Only the milestone/research harness varies these knobs.
///
/// The non-regression contract is UNCHANGED (the CS key must strictly beat the canonical
/// baseline), so a count-only or escalated run that fails to beat the baseline still
/// falls back — but its `leaf_calls`/`base_compound_calls`/`sum_g`/`sum_quota` measure
/// the priced run either way when the CS path ran.
pub fn cs_schedule_bwd_layer_research(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
    multiplier: usize,
    gap_cap: usize,
    enforce_budget: bool,
) -> CsOutcome {
    cs_schedule_bwd_layer_impl(
        layer,
        regime,
        cross,
        budget,
        multiplier,
        gap_cap,
        enforce_budget,
        false,
    )
}

/// The shared implementation behind [`cs_schedule_bwd_layer`],
/// [`cs_schedule_bwd_layer_research`], and [`cs_schedule_bwd_layer_with_term_floor`].
///
/// `probe_term_floor` (CS-M5a final-review follow-up) gates whether
/// [`CsOutcome::term_floor`] is materialized at all: when `false` (every production and
/// research entry) the `TermFloorProbe`'s `BwdCompiledLayer` clone is SKIPPED entirely — not
/// just discarded — since its only consumer is `bwd_backend_neutrality`. The gate sits
/// strictly after the lexicographic-min winner selection below, so it cannot influence
/// which candidate ships.
#[allow(clippy::too_many_arguments)]
fn cs_schedule_bwd_layer_impl(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
    multiplier: usize,
    gap_cap: usize,
    enforce_budget: bool,
    probe_term_floor: bool,
) -> CsOutcome {
    // ── (1) canonical baseline: the non-regression floor AND the fallback ──────────
    let bl_d = distill(layer, regime, cross, None);
    let n_units = bl_d.unit_order.len();
    let (bl_c, bl_trace) = compile_distilled_traced(&bl_d, budget, None).unwrap_or_else(|e| {
        panic!(
            "cs_schedule_bwd_layer: even the no-decisions canonical baseline is \
             infeasible ({regime:?}, budget {budget}, {n_units} units): {e:?}"
        )
    });
    let (bl_report, bl_feasible) = report_and_feasible(&bl_c, &bl_trace);
    let bl_traffic = bl_c.stats_ext.global + bl_c.stats_ext.fold_traffic;
    let bl_key = schedule_key(!bl_feasible, bl_traffic, bl_c.stats.program_lanes);

    // ── (2/3) the two INDEPENDENT CS candidates (CS-M5a Task 10) ───────────────────
    // Each is a `Result` consulted via `.ok()`: a failure in one candidate NEVER discards
    // the other candidate or the baseline (genuine error isolation). The term candidate is
    // byte-identical to the pre-Task-10 pipeline (`bwd_backend_neutrality` pins it).
    let term = try_cs_path(
        layer,
        regime,
        cross,
        budget,
        &bl_d,
        multiplier,
        gap_cap,
        enforce_budget,
    )
    .ok();
    let fragment =
        try_fragment_path(layer, budget, &bl_d, multiplier, gap_cap, enforce_budget).ok();

    // Per-candidate priced-search cost (RR resolution): each search's `leaf_calls` is
    // exposed independently of which candidate ships, so the per-search `HARD_MAX`
    // guardrail keeps its per-search meaning across BOTH candidates. `None` iff that
    // candidate errored out (no completed priced run).
    let term_leaf_calls = term.as_ref().map(|t| t.leaf_calls);
    let fragment_leaf_calls = fragment.as_ref().map(|f| f.leaf_calls);

    // TERM FLOOR (RR resolution): the lexicographic-min of {baseline, term-CS} — exactly
    // what the engine would ship if the fragment candidate did not exist. `bwd_backend_
    // neutrality` byte-checks THIS, so the term pricing path stays pinned even when fragment
    // wins the shipped slot. Built (cloned) BEFORE the selection consumes the candidates.
    //
    // CS-M5a final-review follow-up: `probe_term_floor` gates materialization. On every
    // production/research call (`probe_term_floor == false`) this whole arm is skipped, so
    // the `BwdCompiledLayer` clone (program + descriptor table, thousands of lanes on heavy
    // fixtures) never happens — the probe's only consumer is `bwd_backend_neutrality`, via
    // [`cs_schedule_bwd_layer_with_term_floor`].
    let term_floor = if probe_term_floor {
        Some(match &term {
            Some(t) if t.key() < bl_key => TermFloorProbe {
                compiled: t.compiled.clone(),
                certificate: t.report.clone(),
                plan_entries_fnv: Some(t.plan.entries_fnv),
            },
            _ => TermFloorProbe {
                compiled: bl_c.clone(),
                certificate: bl_report.clone(),
                plan_entries_fnv: None,
            },
        })
    } else {
        None
    };

    // ── (4) ship the lexicographic-min of {baseline} ∪ {successful candidates} ─────
    // Baseline is the floor (always feasible). A candidate replaces the running best ONLY
    // on a STRICT key improvement, and the term candidate is consulted before the fragment
    // candidate — so ties prefer baseline over term over fragment. `fragment_order` in the
    // shipped outcome is `Some` IFF the fragment candidate strictly beat both the term
    // candidate and the baseline (Some ⟺ fragment shipped).
    let mut best_key = bl_key;
    let mut winner: Option<CsPath> = None;
    for cand in [term, fragment].into_iter().flatten() {
        let k = cand.key();
        if k < best_key {
            best_key = k;
            winner = Some(cand);
        }
    }

    match winner {
        Some(cs) => outcome_from_cspath(cs, term_floor, term_leaf_calls, fragment_leaf_calls),
        None => {
            baseline_outcome(n_units, bl_c, bl_report, term_floor, term_leaf_calls, fragment_leaf_calls)
        }
    }
}

/// Assemble the shipped `CsOutcome` from the winning [`CsPath`] (term or fragment).
/// `fragment_order` flows straight through — it is `Some` exactly for a fragment winner —
/// so `Some` ⟺ the fragment candidate shipped.
fn outcome_from_cspath(
    cs: CsPath,
    term_floor: Option<TermFloorProbe>,
    term_leaf_calls: Option<usize>,
    fragment_leaf_calls: Option<usize>,
) -> CsOutcome {
    let instrs = cs.compiled.stats.program_lanes;
    CsOutcome {
        unit_permutation: cs.unit_permutation,
        plan: Some(cs.plan),
        stats: cs.compiled.stats_ext,
        instrs,
        compiled: cs.compiled,
        pins: cs.pins,
        certificate: cs.report,
        rounds: cs.rounds,
        converged: cs.converged,
        fell_back_to_baseline: false,
        fragment_order: cs.fragment_order,
        term_floor,
        term_leaf_calls,
        fragment_leaf_calls,
        counters: cs.counters,
        saw_incomplete_round: cs.saw_incomplete_round,
        leaf_calls: cs.leaf_calls,
        base_compound_calls: cs.base_compound_calls,
        sum_g: cs.sum_g,
        sum_quota: cs.sum_quota,
    }
}
