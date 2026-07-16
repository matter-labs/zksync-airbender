//! Task 5 (CS-M0): the FiF (farthest-in-future) leaf planner over a frozen demand
//! snapshot ([`FrozenDemand`], Task 2). This module (a) lifts the FC0
//! fuzz-validated exact fixed-order ceiling solver (`Gap`/`occ_range`/
//! `fif_select`/`oracle_saved`, verbatim from `tests/bwd_batching_headroom.rs:
//! 391-555`, `Gap::origin` re-typed `usize` -> `ExprId`) into `src`, (b) adds
//! [`plan_leaves`]: the pure leaf-only occurrence PRICER that realizes the FiF
//! selection as a [`BwdOccurrencePlan`] (Task 3) for
//! [`compile_distilled_planned`](super::compile::compile_distilled_planned) to replay,
//! and (c) adds [`feasible_leaf_plan`]: the discount-seed + drop-to-fit FEASIBILITY
//! WRAPPER (RR-directed hybrid, brief Revision 2) that the engine consumes — it always
//! returns a plan `compile_distilled_planned` accepts (no `BudgetBelowFloor`, zero
//! refusals, no divergence).
//!
//! ## Why the wrapper exists (the confirmed fundamental result, Revision 2)
//!
//! Static single-shot FiF pricing against the zero-retention `frozen.free` envelope is
//! CONFIRMED infeasible at b16 on real circuits: realizing retentions inserts admission
//! instructions that reshape the program, so the zero-retention envelope is not a fixed
//! point and the realized placement floor saturates at `budget + baseline_peak`
//! REGARDLESS of kept-gap count (measured 12-lane overshoot on add_sub/bigint/keccak L0,
//! independent of 114 vs 2511 kept gaps). `plan_leaves` stays the pure pricer; the
//! discount + drop-to-fit lives in [`feasible_leaf_plan`], which bounds max concurrent
//! retention so the realized floor stays <= budget by the saturation argument.

use std::collections::{BTreeMap, BTreeSet};

use cs::gkr_compiler::dag_ir::ExprId;

use super::compile::{
    compile_distilled_planned, BwdCompileBackend, BwdCompiledLayer, TermBackend,
};
use super::distill::DistilledLayer;
use super::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use super::trace::{BwdCompileTrace, BwdEvent, FrozenDemand};
use crate::fwd::error::CompileError;

// ── FC0: exact fixed-order ceiling (per-site envelope FiF) ────────────────────
// Lifted verbatim from `tests/bwd_batching_headroom.rs:391-555` (codex-H5 doc
// preserved) — `Gap::origin` re-typed from a transient ledger index (`usize`) to
// the real distilled leaf `ExprId`; `fif_select`/`occ_range`/`oracle_saved` never
// read `origin`, so this retyping changes no behavior.

/// A retention candidate: hold `origin`'s value from its use at instruction `start`
/// to its next use at `end`. Occupancy is `(start, end]` — the cell is stored AFTER
/// the start use's miss is serviced (lower.rs:791-804) and stays live THROUGH the
/// closing read (placement is inclusive [def, last_use], place.rs:138-154). Chained
/// gaps of one origin tile without double-count: [u1+1,u2], [u2+1,u3]. A ZERO-LENGTH
/// gap (same-instruction double use, e.g. x*x) occupies just its own instant
/// [end, end] — the cell is borrowed within the instruction; FC2 must verify the
/// machinery realizes that instant-borrow (FC0 ceiling impact is tiny either way).
#[derive(Clone, Copy, Debug)]
pub struct Gap {
    pub origin: ExprId,
    pub start: usize,
    pub end: usize,
}

/// Occupied instants of a retained gap (closed `(first, last)`; see `Gap`). The
/// SINGLE shared phase definition — solver and oracle both use it, so the fuzz
/// actually exercises the real phase model (codex H5b: revision 1's oracle copied
/// the solver's wrong phase, making the fuzz blind to it).
pub fn occ_range(g: &Gap) -> (usize, usize) {
    if g.start == g.end {
        (g.end, g.end)
    } else {
        (g.start + 1, g.end)
    }
}

/// Exact fixed-order reclaim under a time-varying free-lane envelope: retain a
/// maximum number of gaps s.t. at every t, `4 · |selected occupying t| <= free[t]`
/// (occupancy per `occ_range`). Sweep: admit each gap at its first occupied
/// instant, drop the farthest-LAST active gap on overflow (offline
/// farthest-in-future with bypass, variable capacity — codex exhaustively
/// validated the abstract sweep on 82,944 small cases). This implementation is
/// still fuzzed against the oracle below (same `occ_range`, so the fuzz exercises
/// the real phase model); if the fuzz ever finds a gap, escalate to min-cost-flow
/// (design doc §4) instead of shipping a wrong ceiling.
pub fn fif_select(gaps: &[Gap], free: &[usize]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..gaps.len()).collect();
    order.sort_by_key(|&i| occ_range(&gaps[i]));
    let mut active: BTreeSet<(usize, usize)> = BTreeSet::new(); // (occ last, gap idx)
    let mut kept: Vec<usize> = Vec::new();
    let mut gi = 0usize;
    for t in 0..free.len() {
        while let Some(&(last, idx)) = active.iter().next() {
            if last < t {
                active.remove(&(last, idx));
                kept.push(idx); // survived its whole occupied range: a realized saving
            } else {
                break;
            }
        }
        while gi < order.len() && occ_range(&gaps[order[gi]]).0 == t {
            active.insert((occ_range(&gaps[order[gi]]).1, order[gi]));
            gi += 1;
        }
        while 4 * active.len() > free[t] {
            let &(last, idx) = active.iter().next_back().unwrap(); // farthest last: bypass it
            active.remove(&(last, idx));
        }
    }
    kept.extend(active.into_iter().map(|(_, idx)| idx));
    kept.sort_unstable();
    kept
}

/// Brute-force oracle: max retainable gap count over ALL subsets (≤ 12 gaps).
pub fn oracle_saved(gaps: &[Gap], free: &[usize]) -> usize {
    let mut best = 0usize;
    'outer: for mask in 0u32..(1u32 << gaps.len()) {
        let mut occ = vec![0usize; free.len()];
        for (i, g) in gaps.iter().enumerate() {
            if mask & (1 << i) != 0 {
                let (s, e) = occ_range(g);
                for t in s..=e {
                    occ[t] += 4;
                    if occ[t] > free[t] {
                        continue 'outer;
                    }
                }
            }
        }
        best = best.max(mask.count_ones() as usize);
    }
    best
}

// ── Task 5: the leaf planner ───────────────────────────────────────────────────

/// Build a [`BwdOccurrencePlan`] from a [`FrozenDemand`]: run [`fif_select`] over the
/// per-leaf chained-tiling gaps derived from `frozen.leaf_instants` (leaf `v`'s `m`
/// demand instants tile into `m - 1` gaps: `[instants[0], instants[1]]`,
/// `[instants[1], instants[2]]`, …) against `frozen.free`, then replay
/// `frozen.domain_serves` in stream order: a leaf's `j`-th serve occurrence (0-indexed,
/// counted over exactly the occurrences `leaf_instants` tracks — the all-recompute
/// freeze this is built from serves every domain leaf `Recomputed` in the same order
/// its demand instants were scanned, so the `j`-th stream occurrence and
/// `leaf_instants[v][j]` are the same event) gets [`PlanAction::Retain`] iff it opens a
/// KEPT gap (gap index `j`, since gap `j` opens at instant `j`), [`PlanAction::Bypass`]
/// otherwise. Under the Task-3 interval matcher (`PlanRun`) this realizes the selection
/// exactly: a kept-gap chain replays as `Retain, …, Retain, Bypass`, and an unkept gap's
/// opening occurrence is `Bypass` (the value holds no cell across it). Compound
/// (non-leaf) domain values — absent from `leaf_instants` — get all-`Bypass`: leaf-only
/// planning is this task's whole scope (compound/priced rounds are later CS-M0 tasks).
pub fn plan_leaves(frozen: &FrozenDemand) -> BwdOccurrencePlan {
    // Flatten every domain leaf's chained-tiling gaps into one `gaps` vec, remembering
    // each leaf's own contiguous slice (`flattened start index`, `gap count`) so the
    // replay pass below can test "did MY gap `j` get kept?" via `start + j` without
    // re-deriving the flattening.
    let mut gaps: Vec<Gap> = Vec::new();
    let mut leaf_gap_range: BTreeMap<ExprId, (usize, usize)> = BTreeMap::new();
    for (&v, positions) in &frozen.leaf_instants {
        if positions.len() < 2 {
            continue; // a single demand instant opens no gap
        }
        let start = gaps.len();
        for w in positions.windows(2) {
            gaps.push(Gap { origin: v, start: w[0], end: w[1] });
        }
        leaf_gap_range.insert(v, (start, positions.len() - 1));
    }

    let kept: BTreeSet<usize> = fif_select(&gaps, &frozen.free).into_iter().collect();

    // Per-leaf occurrence counter over the domain_serves stream — advances exactly in
    // step with `leaf_instants`'s own scan order (see the doc above).
    let mut occ_seen: BTreeMap<ExprId, usize> = BTreeMap::new();
    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .map(|&(fp, _from)| {
            let action = match leaf_gap_range.get(&fp.value) {
                Some(&(start, n_gaps)) => {
                    let slot = occ_seen.entry(fp.value).or_insert(0);
                    let j = *slot;
                    *slot += 1;
                    if j < n_gaps && kept.contains(&(start + j)) {
                        PlanAction::Retain
                    } else {
                        PlanAction::Bypass
                    }
                }
                None => PlanAction::Bypass, // compound domain value: no gap model (yet)
            };
            PlanEntry { fp, action }
        })
        .collect();

    BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    }
}

// ── Task 5 (RR hybrid): discount-seed + drop-to-fit feasibility wrapper ─────────

/// An all-`Bypass` plan over `frozen`'s domain serves (the zero-retention terminal /
/// bootstrap). Feasible by construction: no `Retain` means no admission, so the compile
/// is exactly the zero-retention program in `frozen`'s regime.
fn all_bypass_plan(frozen: &FrozenDemand) -> BwdOccurrencePlan {
    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .map(|&(fp, _from)| PlanEntry { fp, action: PlanAction::Bypass })
        .collect();
    BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    }
}

/// The coordinate-correct `lower==place==budget` all-`Bypass` freeze (Task 5 step 1),
/// shared by [`feasible_leaf_plan`], [`priced_rounds`](super::price::priced_rounds), and
/// the CS engine ([`cs_schedule_bwd_layer`](super::engine::cs_schedule_bwd_layer)).
/// Harvest the budget-independent domain-serve fingerprints from a `decisions:None`
/// traced compile, build an all-`Bypass` plan, replay it at `lower==place==budget`
/// (feasible — the zero-retention program in the planned regime), and re-freeze on THAT
/// trace. This is the `frozen0` every priced planner MUST seed from — NEVER the
/// fill-then-trim `compile_distilled_traced` freeze, whose structurally different,
/// ~1.5x-smaller program is the WRONG coordinate system to price a `lower==place==
/// budget` replay against (see the module docs). Feasible by construction: the returned
/// `Err` can only be an upstream compile error, never a schedule/plan mismatch.
pub fn coordinate_correct_frozen(
    d: &DistilledLayer,
    budget: usize,
) -> Result<FrozenDemand, CompileError> {
    coordinate_correct_frozen_with_backend(d, budget, &TermBackend)
}

/// Backend-parameterized [`coordinate_correct_frozen`] (CS-M5a Task 6, codex round-2):
/// `backend.traced` → `all_bypass_plan` → `backend.planned` → `backend.freeze` on THAT
/// (planned, `lower==place==budget`) trace. Every driver-specific step — the uncached
/// traced compile, the plan replay, and the freeze's [`DirectTopCorrection`] — goes
/// through `backend`, so the seed is coordinate-correct in whichever regime the priced
/// replay will run. `coordinate_correct_frozen` is the [`TermBackend`] compat wrapper.
pub fn coordinate_correct_frozen_with_backend(
    d: &DistilledLayer,
    budget: usize,
    backend: &dyn BwdCompileBackend,
) -> Result<FrozenDemand, CompileError> {
    // Step 1a: harvest budget-independent domain-serve fingerprints (any regime).
    let (ft_c, ft_trace) = backend.traced(d, budget)?;
    let frozen_ft = backend.freeze(d, &ft_c, &ft_trace);

    // Step 1b: re-freeze in the coordinate system the planned replay actually uses —
    // the zero-retention `lower==place==budget` program.
    let bootstrap = all_bypass_plan(&frozen_ft);
    let (bypass_c, bypass_trace) = backend.planned(d, budget, &bootstrap)?;
    Ok(backend.freeze(d, &bypass_c, &bypass_trace))
}

/// A copy of `frozen` with its per-instant free envelope capped at `cap` cells
/// (`free[t] = min(free[t], cap)`). Everything else — `domain_serves`,
/// `leaf_instants`, `epoch`, `stream_reductions` — is preserved, so the pricer prices
/// the SAME demand against a tighter headroom (the discount).
fn discount_free(frozen: &FrozenDemand, cap: usize) -> FrozenDemand {
    let mut f = frozen.clone();
    for x in &mut f.free {
        *x = (*x).min(cap);
    }
    f
}

/// Count `Refuse` events and detect any `Diverge` event in a compile trace (the two
/// fidelity signals: a refused `Retain` breaks the predicted == realized identity, a
/// `Diverge` means the plan's serve stream did not match the replayed program).
fn refusals_and_divergence(trace: &BwdCompileTrace) -> (usize, bool) {
    let mut refusals = 0usize;
    let mut diverged = false;
    for e in &trace.events {
        match e {
            BwdEvent::Refuse { .. } => refusals += 1,
            BwdEvent::Diverge { .. } => diverged = true,
            _ => {}
        }
    }
    (refusals, diverged)
}

/// TERM-ONLY (CS-M5a Task 6): seeds via the [`TermBackend`] `coordinate_correct_frozen`
/// and replays through [`compile_distilled_planned`] directly — the fragment path never
/// calls it.
///
/// The discount-seed + drop-to-fit feasibility wrapper (RR-directed hybrid, brief
/// Revision 2). ALWAYS returns a leaf plan that [`compile_distilled_planned`] accepts —
/// no `BudgetBelowFloor`, zero `Refuse`, no `Diverge` — together with its realized
/// compile + trace. The reclaim step (relaxing the discount back toward the FiF optimum
/// by re-pricing against the REALIZED program) is Task 8's re-freeze loop, NOT this
/// seed: `feasible_leaf_plan` returns a single feasible seed (the largest clean
/// discount).
///
/// 1. **Coordinate-correct freeze.** Price in the SAME lowering regime the planned
///    compile uses. The Task-1 `compile_distilled_traced` freeze is fill-then-trim (a
///    structurally different, ~1.5x-smaller program), so its `leaf_instants` /`free` are
///    the WRONG coordinate system to price a `lower==place==budget` replay against. We
///    harvest the (budget-independent) `domain_serves` fingerprints from that trace,
///    build an all-`Bypass` plan, `compile_distilled_planned` it at `lower==place==
///    budget` (feasible — zero-retention program in the right regime), then re-freeze on
///    THAT trace to get `frozen0`.
/// 2. **Discount seed.** `peak = budget - min(frozen0.free)` (= the reduction's own
///    baseline peak); cap the envelope at the reduction margin `budget - peak`
///    (= `min(free)`), bounding max concurrent retention so the realized floor stays
///    <= budget by the saturation argument. Price `plan_leaves` on the discounted copy.
/// 3. **Drop-to-fit iterate (safety net).** If the seed compile is not clean
///    (`BudgetBelowFloor`, or `Ok` with a `Refuse`/`Diverge`), the discount
///    under-estimated: tighten the cap by 4 cells (one Ext bucket) and re-price, for a
///    bounded number of rounds. The `cap == 0` iteration is the all-`Bypass` terminal —
///    guaranteed clean and feasible — so this always terminates with a feasible triple.
pub fn feasible_leaf_plan(
    d: &DistilledLayer,
    budget: usize,
) -> Result<(BwdOccurrencePlan, BwdCompiledLayer, BwdCompileTrace), CompileError> {
    // Step 1: the coordinate-correct `lower==place==budget` all-`Bypass` freeze — the
    // shared `frozen0` (extracted to `coordinate_correct_frozen` so the engine, priced
    // rounds, and the test surface all seed from one implementation).
    let frozen0 = coordinate_correct_frozen(d, budget)?;

    // Step 2: the reduction-margin discount cap (= min(free) = budget - baseline_peak).
    let min_free = frozen0.free.iter().copied().min().unwrap_or(0);
    let peak = budget.saturating_sub(min_free);
    let mut cap = budget.saturating_sub(peak);

    // Step 3: drop-to-fit. Bounded: cap decreases by 4 each miss until the all-Bypass
    // terminal (cap == 0) — which is clean and feasible by construction.
    loop {
        let discounted = discount_free(&frozen0, cap);
        let plan = plan_leaves(&discounted);
        match compile_distilled_planned(d, budget, &plan) {
            Ok((c, t)) => {
                let (refusals, diverged) = refusals_and_divergence(&t);
                if refusals == 0 && !diverged {
                    return Ok((plan, c, t));
                }
                // Discount under-estimated (capacity short mid-emit / stream drift) —
                // tighten. Falls through to the cap step below.
            }
            Err(CompileError::BudgetBelowFloor { .. }) => {
                // Realized floor exceeded budget — tighten.
            }
            Err(e) => return Err(e),
        }
        if cap == 0 {
            // The cap==0 (all-Bypass) iteration must have returned clean above; reaching
            // here means even the zero-retention program is infeasible at `budget`,
            // which contradicts step-1b's successful all-Bypass compile. Surface it.
            return Err(CompileError::BudgetBelowFloor { floor: budget + 1, budget });
        }
        cap = cap.saturating_sub(4);
    }
}
