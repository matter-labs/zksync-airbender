//! Task 8 (CS-M0), Commit 1: removal-set pricing + CELF priced rounds with a
//! re-freeze fixed point.
//!
//! This module turns the frozen all-recompute demand ([`FrozenDemand`], Task 2)
//! into a *priced* schedule: it prices COMPOUND cone-suppression pins (holding a
//! shared compound resident so its later cone re-expansions vanish), commits a
//! batch of them with a CELF lazy-greedy, compiles the batch over the PREDICTED
//! (suppressed) serve stream, re-freezes on the ACTUAL trace, and iterates to a
//! structural fixed point (spec §5, Revision 2).
//!
//! Commit 2 adds the BOUNDED GAP-GRANULAR leaf reclaim (spec §5 step 4, Rev 2 Full
//! scope): after the compound-batch re-freeze, the top-[`RECLAIM_N`] realized leaf
//! gaps (ranked by FiF priority against the realized envelope) are each tentatively
//! retained and KEPT iff a real [`compile_distilled_planned`] stays feasible (no
//! `BudgetBelowFloor`), non-diverging, certifies, and strictly drops `dram_traffic`
//! vs the current best; else reverted. [`PricedOutcome::reclaim_attempted`] /
//! [`PricedOutcome::reclaim_kept`] expose that activity so an inert (all-revert)
//! outcome at b16 is VISIBLE, not silently green.
//!
//! Commit 3 (Revision 4, Full scope) closes the COMPOUND analogue of that gap. The
//! offline pricing model is a NON-AUTHORITATIVE RANKING HINT — `compile + certify` is
//! the SOLE feasibility AND savings authority. The old CELF greedy made the model the
//! SELECTION authority: `price_pin` returns `i64::MIN` for a model-infeasible span, so
//! at b16 (saturated envelope) every compound priced `i64::MIN`, nothing was ever
//! pushed to the heap, and ZERO compound `compile_distilled_planned` calls ran — every
//! compound was dismissed by the MODEL, never TRIED by the compiler. [`reclaim_compounds`]
//! replaces it with the same compiler-in-the-loop greedy as [`reclaim_leaves`]: the
//! top-[`COMPOUND_N`] candidates are RANKED by the `price_pin` hint (ordering ONLY —
//! `i64::MIN` spans are ranked, never filtered) and genuinely tried via a real
//! `compile_distilled_planned`, KEEPING only compiler-feasible, non-diverging, certified,
//! strictly-traffic-dropping pins. [`PricedOutcome::compound_attempted`] /
//! [`PricedOutcome::compound_kept`] expose that a compound was compiler-TRIED (not
//! model-dismissed) — a b16 outcome of "tried N, kept 0" is CORRECT and VISIBLE.
//!
//! ## The removal-set model
//!
//! The emitter serves a value then recurses into its cone PRE-ORDER
//! (`lower_operand_virtual`: `serve_occurrence` at `:1147` BEFORE the miss
//! recursion), so a resident hit deletes exactly the contiguous run of domain
//! serves that follow the hit and lie in the value's cone. [`suppression_ranges`]
//! recovers those runs as index ranges over `frozen.domain_serves`; nested/disjoint
//! composition falls out of the pre-order property (any two ranges are nested or
//! disjoint), applied outermost-first by [`suppressed_indices`].
//!
//! Modeled traffic reconciles against the compiler's own `dram_traffic`
//! (`stats_ext.global + stats_ext.fold_traffic`): the baseline is
//! `nondomain_gather_cells + 4·Σ|leaf_instants|`, and every surviving domain-leaf
//! gather is 4 Ext cells. `nondomain_gather_cells` is a CONSTANT the model carries
//! verbatim — a compound whose suppressed cone contains only NON-domain (fan-out-1)
//! leaves is invisible to the model (its Δ is 0), which is exactly why Commit 2's
//! reclaim validates every retention against the REAL realized program instead.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use cs::gkr_compiler::dag_ir::{Expr, ExprId, FieldKind};

use super::compile::{compile_distilled_planned, BwdCompiledLayer};
use super::distill::{distilled_site_domain, DistilledLayer};
use super::fif::{fif_select, occ_range, Gap};
use super::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use super::structure::expr_width;
use super::trace::{
    certify, freeze_demand, BwdCompileTrace, BwdEvent, BwdFingerprint, BwdServedFrom, FrozenDemand,
};
use crate::fwd::error::CompileError;

/// Default cap on the gap-granular reclaim's candidate count (Commit 2 uses it;
/// exported here so the whole knob lives in one place). `512` (CS-M3 Task 2, raised
/// from `32`) comfortably exceeds blake2's uncapped `feasible_leaf_plan` ceiling
/// (hundreds of certified leaf retentions at b16): at `32` blake2's leaf reclaim was
/// cap-bound (every attempted candidate kept, none reverted — the textbook signature
/// of a cap that binds before the compiler ever says no), so the true candidate count
/// was never explored. Total recompiles stay bounded to `≤ 2·RECLAIM_N` (now `1024`)
/// via the unchanged cost guard at the leaf-reclaim truncate site.
pub const RECLAIM_N: usize = 512;

/// Default cap on the compiler-tried COMPOUND greedy's candidate count (Commit 3).
/// Independent of the leaf reclaim's [`RECLAIM_N`] (CS-M3 Task 1): keccak's compound
/// candidate count (~113) exceeds `RECLAIM_N`'s 32, so sharing the knob left the
/// compound greedy cap-bound (30/32 kept, attempted pinned at 32) well below its true
/// candidate count, throttling cone-suppression retention at saturation. `128` clears
/// keccak's candidate count with headroom while still bounding total compound
/// recompiles to `≤ 2·COMPOUND_N`, same shape as the leaf reclaim's `≤ 2·RECLAIM_N`.
pub const COMPOUND_N: usize = 128;

// ── ABI types ──────────────────────────────────────────────────────────────────

/// The full planner-input signature whose STRUCTURAL equality (spec §5, Rev 2)
/// defines round convergence. Never a hash: refusal *counts* can collide while the
/// refusal *sets* differ, and hash equality is not structural equality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlannerSignature {
    pub domain_serves: Vec<(BwdFingerprint, BwdServedFrom)>,
    pub free: Vec<usize>,
    pub accepted_pins: BTreeSet<ExprId>,
    pub refused: Vec<(ExprId, u32)>,
    pub evictions: Vec<(ExprId, bool)>,
    pub entries: Vec<PlanEntry>,
}

/// The result of [`priced_rounds`]: the best certificate-passing round's plan, the
/// committed compound pins, and the round/convergence + reclaim-activity counters.
/// `reclaim_attempted` / `reclaim_kept` expose the gap-granular leaf reclaim and
/// `compound_attempted` / `compound_kept` the compiler-tried compound greedy, so an
/// inert (all-revert) outcome is VISIBLE, not silently green — in particular
/// `compound_attempted > 0` proves compounds were genuinely COMPILER-tried (not
/// model-dismissed at `i64::MIN`), even when `compound_kept == 0` at b16. All four
/// report the RETURNED (best) round's counts — the same round whose `plan`/`pins`
/// (`pins` = the kept compound set) are returned.
#[derive(Clone, Debug)]
pub struct PricedOutcome {
    pub plan: BwdOccurrencePlan,
    pub pins: Vec<ExprId>,
    pub rounds: usize,
    pub converged: bool,
    pub reclaim_attempted: usize,
    pub reclaim_kept: usize,
    pub compound_attempted: usize,
    pub compound_kept: usize,
}

// ── stream reconstruction (pre-order DFS over the filtered domain serves) ───────

/// Per-serve exclusive end index of each domain serve's domain SUBTREE, recovered
/// from the pre-order stream via the `consumer` (= immediate parent expr) field.
///
/// A serve's consumer is its parent; when the consumer is a domain value it is the
/// currently-open stack top (pre-order), so we pop everything above it (those
/// subtrees have completed) and it stays as the parent. A non-domain / `None`
/// consumer (a spine-term expr or the root output) is never on the stack, so it
/// pops the whole stack and starts a fresh tree — correct for term roots.
///
/// LIMITATION: a NON-domain compound wedged BETWEEN two domain values on one path
/// (e.g. a fan-out-1 `Add` under a `Mul`) is not on the stack, so the inner domain
/// value is treated as a fresh tree root rather than nested. This UNDER-nests
/// (shorter ranges) — conservative for the model; the controlled synthetic layers
/// (tests a/d) are built without such wedges so their ranges are exact.
fn subtree_ends(frozen: &FrozenDemand) -> Vec<usize> {
    let serves = &frozen.domain_serves;
    let n = serves.len();
    let mut end = vec![n; n];
    let mut stack: Vec<(ExprId, usize)> = Vec::new();
    for (k, (fp, _)) in serves.iter().enumerate() {
        let c = fp.consumer;
        while let Some(&(tv, tp)) = stack.last() {
            if Some(tv) == c {
                break;
            }
            end[tp] = k;
            stack.pop();
        }
        stack.push((fp.value, k));
    }
    for (_, tp) in stack {
        end[tp] = n;
    }
    end
}

/// The stream indices at which value `v` is served (ascending).
fn occurrences(frozen: &FrozenDemand, v: ExprId) -> Vec<usize> {
    frozen
        .domain_serves
        .iter()
        .enumerate()
        .filter_map(|(k, (fp, _))| (fp.value == v).then_some(k))
        .collect()
}

/// DYNAMIC removal sets for `v`: for each NON-PRODUCER occurrence of `v` (every
/// occurrence but the first), the contiguous sub-stream of its cone re-expansion
/// that follows `v`'s serve, as an index range over `frozen.domain_serves`. Empty
/// re-expansions (a value whose cone has no domain descendants) are dropped — they
/// remove nothing. Pre-order guarantees any two returned ranges (across values) are
/// nested or disjoint; [`suppressed_indices`] applies them outermost-first.
pub fn suppression_ranges(frozen: &FrozenDemand, v: ExprId) -> Vec<Range<usize>> {
    let end = subtree_ends(frozen);
    occurrences(frozen, v)
        .into_iter()
        .skip(1) // the first occurrence is the producer — its cone is kept
        .map(|i| (i + 1)..end[i])
        .filter(|r| r.start < r.end)
        .collect()
}

/// The union of all pins' suppression ranges, applied OUTERMOST-FIRST: pins are
/// processed by earliest occurrence, each pin's producer is its first SURVIVING
/// (not-yet-suppressed) occurrence, and every later surviving occurrence's cone
/// re-expansion is deleted. Nesting is handled exactly (an inner pin's occurrences
/// already inside an outer pin's range are skipped, so its producer is recomputed
/// on the surviving stream, never over-suppressed).
fn suppressed_indices(
    frozen: &FrozenDemand,
    end: &[usize],
    pins: &BTreeSet<ExprId>,
) -> BTreeSet<usize> {
    let mut pin_occ: Vec<(usize, ExprId, Vec<usize>)> = pins
        .iter()
        .map(|&v| {
            let occ = occurrences(frozen, v);
            (occ.first().copied().unwrap_or(usize::MAX), v, occ)
        })
        .collect();
    pin_occ.sort();

    let mut suppressed: BTreeSet<usize> = BTreeSet::new();
    for (_, _v, occ) in pin_occ {
        let mut producer_found = false;
        for idx in occ {
            if suppressed.contains(&idx) {
                continue; // this occurrence is nested under an already-applied outer pin
            }
            if !producer_found {
                producer_found = true; // first surviving occurrence recomputes (keeps its cone)
                continue;
            }
            for j in (idx + 1)..end[idx] {
                suppressed.insert(j);
            }
        }
    }
    suppressed
}

/// Map each domain-serve stream index that is a LEAF serve to its final-program
/// instruction position, aligning `leaf_instants` (program scan order) with the
/// leaf's occurrences in the serve stream (both are recompute-order in the
/// coordinate-correct all-`Bypass` freeze). Non-leaf serves are absent.
fn leaf_stream_positions(frozen: &FrozenDemand) -> BTreeMap<usize, usize> {
    let mut out = BTreeMap::new();
    let mut seen: BTreeMap<ExprId, usize> = BTreeMap::new();
    for (k, (fp, _)) in frozen.domain_serves.iter().enumerate() {
        if let Some(positions) = frozen.leaf_instants.get(&fp.value) {
            let slot = seen.entry(fp.value).or_insert(0);
            if *slot < positions.len() {
                out.insert(k, positions[*slot]);
            }
            *slot += 1;
        }
    }
    out
}

/// The program-position span `[lo, hi]` over which a compound `v`'s cone is active,
/// bracketed by the leaf gathers inside its occurrence subtrees (`None` = no domain
/// leaf in the cone — no residency footprint the leaf-position model can see).
fn compound_span(
    frozen: &FrozenDemand,
    end: &[usize],
    leaf_pos: &BTreeMap<usize, usize>,
    v: ExprId,
) -> Option<(usize, usize)> {
    let mut lo = usize::MAX;
    let mut hi = 0usize;
    let mut any = false;
    for i in occurrences(frozen, v) {
        for k in i..end[i] {
            if let Some(&p) = leaf_pos.get(&k) {
                lo = lo.min(p);
                hi = hi.max(p);
                any = true;
            }
        }
    }
    any.then_some((lo, hi))
}

/// The surviving leaf chained-tiling gaps under a suppressed-index set: per leaf,
/// the program positions of its surviving occurrences tile into consecutive gaps
/// (identical to [`super::fif::plan_leaves`]'s tiling, restricted to survivors).
fn surviving_leaf_gaps(
    frozen: &FrozenDemand,
    leaf_pos: &BTreeMap<usize, usize>,
    suppressed: &BTreeSet<usize>,
) -> Vec<Gap> {
    let mut per_leaf: BTreeMap<ExprId, Vec<usize>> = BTreeMap::new();
    for (k, (fp, _)) in frozen.domain_serves.iter().enumerate() {
        if suppressed.contains(&k) {
            continue;
        }
        if frozen.leaf_instants.contains_key(&fp.value) {
            if let Some(&p) = leaf_pos.get(&k) {
                per_leaf.entry(fp.value).or_default().push(p);
            }
        }
    }
    let mut gaps = Vec::new();
    for (v, positions) in per_leaf {
        for w in positions.windows(2) {
            gaps.push(Gap {
                origin: v,
                start: w[0],
                end: w[1],
            });
        }
    }
    gaps
}

/// Modeled DRAM traffic (cells) of a pinned state, or `None` if the optional
/// `charge` residency (one compound at a given width across its whole span) is
/// infeasible against the free envelope. `nondomain_gather_cells` rides as the
/// constant term; surviving domain-leaf gathers are 4 cells each; `fif_select`
/// reclaim (against the charged envelope) subtracts 4 per kept leaf gap.
fn modeled_traffic(
    frozen: &FrozenDemand,
    end: &[usize],
    leaf_pos: &BTreeMap<usize, usize>,
    pins: &BTreeSet<ExprId>,
    charge: Option<(ExprId, usize)>,
) -> Option<i64> {
    let suppressed = suppressed_indices(frozen, end, pins);

    let mut free: Vec<i64> = frozen.free.iter().map(|&f| f as i64).collect();
    if let Some((cand, w)) = charge {
        if let Some((lo, hi)) = compound_span(frozen, end, leaf_pos, cand) {
            let hi = hi.min(free.len().saturating_sub(1));
            for slot in free.iter_mut().take(hi + 1).skip(lo) {
                *slot -= w as i64;
                if *slot < 0 {
                    return None; // whole-span residency infeasible
                }
            }
        }
    }

    let gaps = surviving_leaf_gaps(frozen, leaf_pos, &suppressed);
    let free_u: Vec<usize> = free.iter().map(|&f| f.max(0) as usize).collect();
    let kept = fif_select(&gaps, &free_u).len();

    let survive_gathers = frozen
        .domain_serves
        .iter()
        .enumerate()
        .filter(|(k, (fp, _))| {
            frozen.leaf_instants.contains_key(&fp.value) && !suppressed.contains(k)
        })
        .count();

    Some(frozen.nondomain_gather_cells as i64 + 4 * survive_gathers as i64 - 4 * kept as i64)
}

/// Cached-input pricer: Δ modeled traffic (a positive value = a REDUCTION) from
/// adding `candidate` at `width_lanes` to `pinned`, or `i64::MIN` if the
/// candidate's whole-span residency is infeasible. Marginal: only the candidate's
/// residency is charged (prior pins' effect enters via their suppression), so the
/// fif tradeoff of the new pin is priced against the current envelope.
fn price_pin_with(
    frozen: &FrozenDemand,
    end: &[usize],
    leaf_pos: &BTreeMap<usize, usize>,
    pinned: &BTreeSet<ExprId>,
    candidate: ExprId,
    width_lanes: usize,
) -> i64 {
    let before = modeled_traffic(frozen, end, leaf_pos, pinned, None)
        .expect("a no-charge modeled_traffic is always feasible");
    let mut after_pins = pinned.clone();
    after_pins.insert(candidate);
    match modeled_traffic(
        frozen,
        end,
        leaf_pos,
        &after_pins,
        Some((candidate, width_lanes)),
    ) {
        None => i64::MIN,
        Some(after) => before - after,
    }
}

/// Offline replay pricer (spec §5): the Δ modeled traffic (positive = reduction,
/// `i64::MIN` = infeasible span) of pinning `candidate` at its INFERRED
/// `width_lanes` on top of the current `pinned` set. Recomputes the stream
/// reconstruction per call; the round loop uses [`price_pin_with`] with cached
/// inputs.
pub fn price_pin(
    frozen: &FrozenDemand,
    pinned: &BTreeSet<ExprId>,
    candidate: ExprId,
    width_lanes: usize,
) -> i64 {
    let end = subtree_ends(frozen);
    let leaf_pos = leaf_stream_positions(frozen);
    price_pin_with(frozen, &end, &leaf_pos, pinned, candidate, width_lanes)
}

/// The modeled DRAM-traffic REDUCTION (cells) attributable purely to `pins`' cone
/// suppression: `4 × (domain-leaf gathers the pins delete)`, i.e. `4 × (survivors
/// with no pins − survivors with the pins)` where a survivor is a not-yet-suppressed
/// domain-leaf serve (4 Ext cells each). Deliberately EXCLUDES the leaf-reclaim term
/// — the reclaim's savings are the caller's `4 × reclaim_kept`, kept separate so the
/// fidelity gate (test (e)) reconciles modeled `pins_suppression + 4·reclaim_kept`
/// against the realized `baseline − final` delta. The model cannot see NON-domain
/// (fan-out-1) leaves a pin also deletes — they ride `nondomain_gather_cells` as a
/// constant — so on a pin whose cone reaches non-domain leaves this UNDER-predicts;
/// that gap is exactly why Commit 2 validates every retention against the real
/// program instead of trusting the coarse model.
pub fn pins_suppression_savings(frozen: &FrozenDemand, pins: &BTreeSet<ExprId>) -> i64 {
    let end = subtree_ends(frozen);
    let survivors = |p: &BTreeSet<ExprId>| -> i64 {
        let suppressed = suppressed_indices(frozen, &end, p);
        frozen
            .domain_serves
            .iter()
            .enumerate()
            .filter(|(k, (fp, _))| {
                frozen.leaf_instants.contains_key(&fp.value) && !suppressed.contains(k)
            })
            .count() as i64
    };
    4 * (survivors(&BTreeSet::new()) - survivors(pins))
}

// ── compound candidates, pricing model + compiler-tried compound greedy ─────────

/// The compound (non-leaf) domain values that recur (≥ 2 serve occurrences) — the
/// only values a cone-suppression pin can save anything on.
pub fn compound_candidates(d: &DistilledLayer, frozen: &FrozenDemand) -> Vec<ExprId> {
    let domain: BTreeSet<ExprId> = distilled_site_domain(d)
        .into_iter()
        .map(|s| s.value)
        .collect();
    let mut counts: BTreeMap<ExprId, usize> = BTreeMap::new();
    for (fp, _) in &frozen.domain_serves {
        if domain.contains(&fp.value) {
            *counts.entry(fp.value).or_insert(0) += 1;
        }
    }
    counts
        .into_iter()
        .filter(|&(v, n)| {
            n >= 2 && matches!(d.layer.exprs[v.0 as usize], Expr::Add(_) | Expr::Mul(_))
        })
        .map(|(v, _)| v)
        .collect()
}

/// Inferred residency width (lanes) of `v` — 1 (Base) or 4 (Ext); never hard-coded.
fn width_of(d: &DistilledLayer, v: ExprId, memo: &mut [Option<FieldKind>]) -> usize {
    expr_width(d, v, memo)
}

/// Public width accessor — `v`'s inferred residency width (1 Base / 4 Ext), never
/// hard-coded. Allocates a fresh field memo per call (for one-off pricing callers).
pub fn value_width(d: &DistilledLayer, v: ExprId) -> usize {
    let mut memo = vec![None; d.layer.exprs.len()];
    expr_width(d, v, &mut memo)
}

/// FULL modeled traffic of a pin set: like [`modeled_traffic`] but charges EVERY
/// pin's residency (at its own width) across its whole span, returning `None` if any
/// span overflows the free envelope. The exhaustive-oracle scorer (test `priced_
/// oracle_gap`) and Commit 2's fidelity reconciliation share this one model.
pub fn modeled_traffic_full(frozen: &FrozenDemand, pins: &BTreeMap<ExprId, usize>) -> Option<i64> {
    let end = subtree_ends(frozen);
    let leaf_pos = leaf_stream_positions(frozen);
    let pin_set: BTreeSet<ExprId> = pins.keys().copied().collect();
    let suppressed = suppressed_indices(frozen, &end, &pin_set);

    let mut free: Vec<i64> = frozen.free.iter().map(|&f| f as i64).collect();
    for (&v, &w) in pins {
        if let Some((lo, hi)) = compound_span(frozen, &end, &leaf_pos, v) {
            let hi = hi.min(free.len().saturating_sub(1));
            for slot in free.iter_mut().take(hi + 1).skip(lo) {
                *slot -= w as i64;
                if *slot < 0 {
                    return None;
                }
            }
        }
    }

    let gaps = surviving_leaf_gaps(frozen, &leaf_pos, &suppressed);
    let free_u: Vec<usize> = free.iter().map(|&f| f.max(0) as usize).collect();
    let kept = fif_select(&gaps, &free_u).len();
    let survive = frozen
        .domain_serves
        .iter()
        .enumerate()
        .filter(|(k, (fp, _))| {
            frozen.leaf_instants.contains_key(&fp.value) && !suppressed.contains(k)
        })
        .count();
    Some(frozen.nondomain_gather_cells as i64 + 4 * survive as i64 - 4 * kept as i64)
}

/// Compiler-tried COMPOUND retention greedy (Commit 3, Revision 4 Full scope). Closes
/// the gap where the CELF greedy made the offline model the SELECTION authority: at b16
/// every compound spans an over-subscribed envelope so `price_pin_with` returns
/// `i64::MIN`, nothing was pushed to the heap, and ZERO compound
/// `compile_distilled_planned` calls ever ran — every compound was dismissed by the
/// MODEL, never TRIED by the compiler. This mirrors [`reclaim_leaves`]: the offline
/// `price_pin_with` marginal against the EMPTY set is a RANKING key ONLY (descending;
/// `ExprId` ascending tie-break — deterministic, `i64::MIN` sorts LAST but is NEVER
/// filtered), the top-[`COMPOUND_N`] are genuinely tried, and the COMPILER is the sole
/// selection authority.
///
/// Starting from the feasible all-`Bypass` base compound plan `base_plan` (empty pins;
/// already compiled clean into `base_c`/`base_trace`), for each ranked candidate in
/// order tentatively add it to the kept pin set, rebuild the compound-batch plan
/// (`Retain` at every SURVIVING occurrence but the last, `Bypass` at the last, suppressed
/// cone re-expansions dropped) over the GROWING set, `compile_distilled_planned`, and
/// KEEP iff the compile is feasible (no `BudgetBelowFloor`), non-diverging, certifies,
/// AND its `dram_traffic` STRICTLY drops vs the current best; else revert. Total
/// recompiles are bounded to `≤ 2·COMPOUND_N`. A single candidate's `BudgetBelowFloor`
/// or `Diverge` only reverts THAT candidate (the greedy moves on) — the round-level
/// fail-closed break stays with the base compile in [`priced_rounds`]. Returns
/// `(kept pins, best plan, its compile, its trace, attempted, kept)`; `best_plan` always
/// equals `compound_batch_plan_with(frozen, &kept_pins, end)`.
#[allow(clippy::too_many_arguments)]
fn reclaim_compounds(
    d: &DistilledLayer,
    budget: usize,
    frozen: &FrozenDemand,
    end: &[usize],
    leaf_pos: &BTreeMap<usize, usize>,
    width_memo: &mut [Option<FieldKind>],
    base_plan: BwdOccurrencePlan,
    base_c: BwdCompiledLayer,
    base_trace: BwdCompileTrace,
) -> Result<
    (BTreeSet<ExprId>, BwdOccurrencePlan, BwdCompiledLayer, BwdCompileTrace, usize, usize),
    CompileError,
> {
    // Hint-ranked candidates: the offline marginal price against the EMPTY set is an
    // ORDERING key ONLY — infeasible (`i64::MIN`) spans are ranked (sorted last), never
    // filtered; the compiler decides feasibility AND savings. Deterministic (ExprId
    // tie-break, no hashmap-iteration order).
    let mut ranked: Vec<(i64, ExprId)> = compound_candidates(d, frozen)
        .into_iter()
        .map(|c| {
            let w = width_of(d, c, width_memo);
            (price_pin_with(frozen, end, leaf_pos, &BTreeSet::new(), c, w), c)
        })
        .collect();
    ranked.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    ranked.truncate(COMPOUND_N);

    let mut pinned: BTreeSet<ExprId> = BTreeSet::new();
    let mut best_traffic = base_c.stats_ext.global + base_c.stats_ext.fold_traffic;
    let mut best_plan = base_plan;
    let mut best_c = base_c;
    let mut best_trace = base_trace;
    let mut attempted = 0usize;
    let mut kept = 0usize;
    let mut compiles = 0usize;

    for (_hint, c) in ranked {
        if compiles >= 2 * COMPOUND_N {
            break; // recompile budget guard (≤ 2N)
        }
        attempted += 1;
        pinned.insert(c); // tentative add
        let trial = compound_batch_plan_with(frozen, &pinned, end);
        compiles += 1;
        match compile_distilled_planned(d, budget, &trial) {
            Ok((tc, tt)) => {
                let dram = tc.stats_ext.global + tc.stats_ext.fold_traffic;
                let clean = certify(&tc, &tt).is_ok() && !diverged(&tt);
                if clean && dram < best_traffic {
                    best_traffic = dram;
                    best_plan = trial;
                    best_c = tc;
                    best_trace = tt;
                    kept += 1; // KEEP: leave `c` in the pin set (chained into later trials)
                } else {
                    pinned.remove(&c); // revert (infeasible-by-model verdict NOT trusted;
                                       // reverted only because the COMPILER declined it)
                }
            }
            // The compound chain's realized floor exceeded the budget → revert this
            // candidate; the greedy moves on (the model-infeasible span the hint
            // predicted, now compiler-confirmed for THIS candidate only).
            Err(CompileError::BudgetBelowFloor { .. }) => {
                pinned.remove(&c);
            }
            Err(e) => return Err(e),
        }
    }

    Ok((pinned, best_plan, best_c, best_trace, attempted, kept))
}

// ── plan construction ───────────────────────────────────────────────────────────

/// Build the compound-batch plan over the PREDICTED (suppressed) stream: every
/// pinned compound `Retain`s at each surviving occurrence but its last, `Bypass` at
/// the last; all leaves and non-pinned values `Bypass`. Suppressed serves (the
/// deleted cone re-expansions) are dropped, so the entries are exactly the stream
/// the compiler is predicted to produce.
pub fn compound_batch_plan(frozen: &FrozenDemand, pins: &BTreeSet<ExprId>) -> BwdOccurrencePlan {
    let end = subtree_ends(frozen);
    compound_batch_plan_with(frozen, pins, &end)
}

fn compound_batch_plan_with(
    frozen: &FrozenDemand,
    pins: &BTreeSet<ExprId>,
    end: &[usize],
) -> BwdOccurrencePlan {
    let suppressed = suppressed_indices(frozen, end, pins);

    // The last SURVIVING occurrence index of each pinned value (Bypass there; Retain
    // before). A pinned value with a single surviving occurrence gets no Retain.
    let mut last_surviving: BTreeMap<ExprId, usize> = BTreeMap::new();
    for (k, (fp, _)) in frozen.domain_serves.iter().enumerate() {
        if !suppressed.contains(&k) && pins.contains(&fp.value) {
            last_surviving.insert(fp.value, k);
        }
    }

    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .enumerate()
        .filter(|(k, _)| !suppressed.contains(k))
        .map(|(k, (fp, _))| {
            let action = if pins.contains(&fp.value) && last_surviving.get(&fp.value) != Some(&k) {
                PlanAction::Retain
            } else {
                PlanAction::Bypass
            };
            PlanEntry { fp: *fp, action }
        })
        .collect();

    BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    }
}

// ── signature ────────────────────────────────────────────────────────────────────

/// Build the [`PlannerSignature`] from a round's (frozen, trace, pins, plan) — the
/// structural convergence key.
pub fn planner_signature(
    frozen: &FrozenDemand,
    trace: &BwdCompileTrace,
    accepted_pins: &BTreeSet<ExprId>,
    plan: &BwdOccurrencePlan,
) -> PlannerSignature {
    let refused = trace
        .events
        .iter()
        .filter_map(|e| match e {
            BwdEvent::Refuse { value, need } => Some((*value, *need)),
            _ => None,
        })
        .collect();
    let evictions = trace
        .events
        .iter()
        .filter_map(|e| match e {
            BwdEvent::Evict { value, expired } => Some((*value, *expired)),
            _ => None,
        })
        .collect();
    PlannerSignature {
        domain_serves: frozen.domain_serves.clone(),
        free: frozen.free.clone(),
        accepted_pins: accepted_pins.clone(),
        refused,
        evictions,
        entries: plan.entries.clone(),
    }
}

// ── bounded gap-granular leaf reclaim (Commit 2) ────────────────────────────────

/// A [`BwdOccurrencePlan`] over `base`'s `(epoch, stream_reductions)` regime with a
/// freshly-rehashed `entries_fnv` for the mutated `entries` — the plan-construction
/// helper the reclaim's tentative flips round-trip through.
fn plan_from(base: &BwdOccurrencePlan, entries: Vec<PlanEntry>) -> BwdOccurrencePlan {
    BwdOccurrencePlan {
        epoch: base.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: base.stream_reductions,
        entries,
    }
}

/// Bounded gap-granular leaf reclaim (spec §5 step 4, Rev 2 Full scope). Starting
/// from the all-`Bypass`-leaves compound-batch plan `base_plan` (already compiled
/// clean into `base_c`/`base_trace`), rank the REALIZED (`observed`) per-leaf gaps by
/// FiF priority against the realized envelope, take the top [`RECLAIM_N`], and for
/// each in priority order flip its opening occurrence to [`PlanAction::Retain`],
/// [`compile_distilled_planned`], and KEEP the flip iff the compile is feasible (no
/// `BudgetBelowFloor`), non-diverging, certifies, AND its `dram_traffic` STRICTLY
/// drops vs the current best; else revert it. Each candidate is validated against the
/// REAL realized program — the faithful "iterate" that recovers the single-retention
/// -feasible cases the coarse compound discount discards. Total recompiles are bounded
/// to `≤ 2·RECLAIM_N`. Returns `(final plan, its compile, its trace, attempted, kept)`.
///
/// The gap↔plan-entry alignment is exact: `base_plan.entries` are the non-diverging
/// realized serve stream, so `observed.domain_serves[k]` is `base_plan.entries[k]` and
/// a leaf's `j`-th plan occurrence is its `j`-th `leaf_instants` demand instant (the
/// same alignment [`super::fif::plan_leaves`] relies on). Retaining gap `j` flips the
/// `j`-th occurrence; the `(j+1)`-th (always present — a gap needs a closing use) keeps
/// the `PlanRun::new` "a Retain has a next serve for its value" invariant.
fn reclaim_leaves(
    d: &DistilledLayer,
    budget: usize,
    observed: &FrozenDemand,
    base_plan: &BwdOccurrencePlan,
    base_c: BwdCompiledLayer,
    base_trace: BwdCompileTrace,
) -> Result<(BwdOccurrencePlan, BwdCompiledLayer, BwdCompileTrace, usize, usize), CompileError> {
    // Each domain leaf's opening-occurrence entry indices within the base plan.
    let mut occ_idx: BTreeMap<ExprId, Vec<usize>> = BTreeMap::new();
    for (k, e) in base_plan.entries.iter().enumerate() {
        if observed.leaf_instants.contains_key(&e.fp.value) {
            occ_idx.entry(e.fp.value).or_default().push(k);
        }
    }

    // Realized per-leaf chained-tiling gaps (program-position coordinates) + parallel
    // metadata (leaf value, gap index j) — identical tiling to `plan_leaves`.
    let mut gaps: Vec<Gap> = Vec::new();
    let mut meta: Vec<(ExprId, usize)> = Vec::new();
    for (&v, instants) in &observed.leaf_instants {
        if instants.len() < 2 {
            continue;
        }
        for j in 0..instants.len() - 1 {
            gaps.push(Gap { origin: v, start: instants[j], end: instants[j + 1] });
            meta.push((v, j));
        }
    }

    // FiF-priority ranking against the REALIZED envelope: gaps FiF admits first, then
    // by occupied-instant range, then by opening entry index (fully deterministic).
    let fif_kept: BTreeSet<usize> = fif_select(&gaps, &observed.free).into_iter().collect();
    let mut order: Vec<usize> = (0..gaps.len()).collect();
    order.sort_by_key(|&gi| {
        let (v, j) = meta[gi];
        let entry = occ_idx.get(&v).and_then(|o| o.get(j)).copied().unwrap_or(usize::MAX);
        (!fif_kept.contains(&gi), occ_range(&gaps[gi]), entry)
    });
    order.truncate(RECLAIM_N);

    let mut entries = base_plan.entries.clone();
    let mut best_traffic = base_c.stats_ext.global + base_c.stats_ext.fold_traffic;
    let mut best_c = base_c;
    let mut best_trace = base_trace;
    let mut attempted = 0usize;
    let mut kept = 0usize;
    let mut compiles = 0usize;

    for gi in order {
        if compiles >= 2 * RECLAIM_N {
            break; // recompile budget guard (≤ 2N)
        }
        let (v, j) = meta[gi];
        let occ = match occ_idx.get(&v) {
            Some(o) if j + 1 < o.len() => o,
            _ => continue, // no closing occurrence in the plan — cannot open a gap
        };
        let entry_idx = occ[j];
        if entries[entry_idx].action != PlanAction::Bypass {
            continue; // already retained via a chain — nothing to add here
        }

        attempted += 1;
        entries[entry_idx].action = PlanAction::Retain; // tentative flip
        let trial = plan_from(base_plan, entries.clone());
        compiles += 1;
        match compile_distilled_planned(d, budget, &trial) {
            Ok((c, t)) => {
                let dram = c.stats_ext.global + c.stats_ext.fold_traffic;
                let clean = certify(&c, &t).is_ok() && !diverged(&t);
                if clean && dram < best_traffic {
                    best_traffic = dram;
                    best_c = c;
                    best_trace = t;
                    kept += 1; // KEEP: leave the flip standing in `entries`
                } else {
                    entries[entry_idx].action = PlanAction::Bypass; // revert
                }
            }
            // Realized floor exceeded budget with this retention — revert (a value that
            // fit alone but not after a compound pin would surface here as a Task-4
            // finding; the caller's fidelity gate makes any such surprise visible).
            Err(CompileError::BudgetBelowFloor { .. }) => {
                entries[entry_idx].action = PlanAction::Bypass;
            }
            Err(e) => return Err(e),
        }
    }

    let final_plan = plan_from(base_plan, entries);
    Ok((final_plan, best_c, best_trace, attempted, kept))
}

// ── CS-M4 Task 1: realized-retention model ─────────────────────────────────────

/// A single decrementing leaf-search budget (spec §5). Task 1 ships the MINIMAL
/// stub — one credit per top-level `compile_distilled_planned` a leaf search spends;
/// Task 2 enriches it with per-round dynamic accrual (`multiplier`/gap quotas).
/// [`Self::try_spend`] is the only debit [`normalize`] uses: it spends one credit
/// iff strictly more than `reserve` remain (the reserve keeps a credit for the
/// mandatory following `normalize`, spec §5), so the debit is ALWAYS checked — never
/// an underflowing bare spend.
#[derive(Clone, Copy, Debug, Default)]
pub struct TrialBudget {
    pub available: usize,
}

impl TrialBudget {
    /// Spend one credit iff strictly more than `reserve` remain; return whether it
    /// was spent. Checked (never underflows): a caller with `available <= reserve`
    /// gets `false` and spends nothing.
    pub fn try_spend(&mut self, reserve: usize) -> bool {
        if self.available > reserve {
            self.available -= 1;
            true
        } else {
            false
        }
    }

    /// Unconditionally spend one credit, saturating at zero.
    pub fn spend(&mut self) {
        self.available = self.available.saturating_sub(1);
    }
}

/// The set of plan-entry indices whose `Retain` is REALIZED against `trace` (spec
/// §3). A `Retain` at value `v`'s occurrence `j` is realized iff `v`'s occurrence
/// `j+1` served `from: Resident` — the OFF-BY-ONE that is the crux: `serve_occurrence`
/// (`lower.rs:513`) records the `Serve` BEFORE any admission, so a first successful
/// admission's OWN serve is `Recomputed` (`v` was not yet resident); its residency
/// only shows at the NEXT serve. A refused admission never becomes resident, so its
/// next serve is `Recomputed` too — unrealized. Matching `j`'s own serve would
/// wrongly demote every successful first admission (a traffic regression).
///
/// Alignment: the plan drives the compile serve-by-serve, so for a non-diverging
/// trace value `v`'s serves appear in the same order as its plan entries — `v`'s
/// `j`-th serve is `v`'s `j`-th plan occurrence (the same alignment [`reclaim_leaves`]
/// relies on at `price.rs:713-719`). `v` is a domain value (it carries plan entries),
/// so ALL of `v`'s trace serves are domain serves — no separate domain filter is
/// needed. A `Diverge` in the trace voids the alignment: return the empty set (all
/// unrealized) and let the caller's non-diverge gate reject.
pub fn realized_openings(plan: &BwdOccurrencePlan, trace: &BwdCompileTrace) -> BTreeSet<usize> {
    if trace.events.iter().any(|e| matches!(e, BwdEvent::Diverge { .. })) {
        return BTreeSet::new(); // alignment void — treat every Retain as unrealized
    }
    // Per value, its `Serve` events' `from` in program order.
    let mut serves_from: BTreeMap<ExprId, Vec<BwdServedFrom>> = BTreeMap::new();
    for e in &trace.events {
        if let BwdEvent::Serve { fp, from } = e {
            serves_from.entry(fp.value).or_default().push(*from);
        }
    }
    // Walk plan entries in order; the running per-value count is this entry's
    // occurrence index `j`. A `Retain` at `j` is realized iff `v`'s `(j+1)`-th serve
    // is `Resident` (`.get` yields the safe "no next serve → unrealized" for the last
    // occurrence, which a `Retain` can never realize anyway).
    let mut occ: BTreeMap<ExprId, usize> = BTreeMap::new();
    let mut realized = BTreeSet::new();
    for (k, e) in plan.entries.iter().enumerate() {
        let slot = occ.entry(e.fp.value).or_insert(0);
        let this_j = *slot;
        *slot += 1;
        if e.action != PlanAction::Retain {
            continue;
        }
        let next_resident = serves_from
            .get(&e.fp.value)
            .and_then(|froms| froms.get(this_j + 1))
            .is_some_and(|from| *from == BwdServedFrom::Resident);
        if next_resident {
            realized.insert(k);
        }
    }
    realized
}

/// Demote every UNREALIZED `Retain` in `plan` to `Bypass` in a single behavior- and
/// traffic-neutral pass (spec §3), recompiling AT MOST once. Returns
/// `(plan', c', trace', demoted, unrealized_after)`:
/// - no unrealized `Retain` → return the inputs unchanged, `(0, 0)`, spending NOTHING
///   (the idempotent no-op — a normalized plan re-normalizes to itself);
/// - some unrealized but no budget credit (`!try_spend(0)`) → return the inputs,
///   `(0, unrealized_count)` WITHOUT recompiling; the caller reads `unrealized_after
///   > 0` as budget-exhausted-before-recompile and returns `Incomplete`;
/// - else demote all unrealized to `Bypass`, `compile_distilled_planned` + `certify`
///   once (fail-closed on a certificate mismatch), return `(plan', c', trace', demoted, 0)`.
///
/// SINGLE PASS (§3): a `Retain` is unrealized only when its admission was refused,
/// and a refused admission never incremented `live_width` (`lower.rs:653-659`) while
/// plan mode never preempts a live retention (`lower.rs:651`); so an unrealized
/// `Retain` held ZERO capacity and demoting it frees nothing — it cannot make another
/// `Retain` newly realize or newly refuse. One pass suffices; no fixed-point loop, no
/// unchecked `spend()`.
pub fn normalize(
    d: &DistilledLayer,
    budget: usize,
    plan: BwdOccurrencePlan,
    c: BwdCompiledLayer,
    trace: BwdCompileTrace,
    budget_ctr: &mut TrialBudget,
) -> Result<(BwdOccurrencePlan, BwdCompiledLayer, BwdCompileTrace, usize, usize), CompileError> {
    let realized = realized_openings(&plan, &trace);
    let unrealized: Vec<usize> = plan
        .entries
        .iter()
        .enumerate()
        .filter(|(k, e)| e.action == PlanAction::Retain && !realized.contains(k))
        .map(|(k, _)| k)
        .collect();
    if unrealized.is_empty() {
        return Ok((plan, c, trace, 0, 0)); // every Retain realized — no-op, spend nothing
    }
    if !budget_ctr.try_spend(0) {
        // No credit for the mandatory recompile — signal Incomplete WITHOUT recompiling.
        return Ok((plan, c, trace, 0, unrealized.len()));
    }
    let mut entries = plan.entries.clone();
    for &k in &unrealized {
        entries[k].action = PlanAction::Bypass;
    }
    let plan2 = plan_from(&plan, entries);
    let (c2, trace2) = compile_distilled_planned(d, budget, &plan2)?;
    // Spec §3 mandates `compile_distilled_planned + certify ONCE`. Neutrality (§3) makes
    // the recompile balance redundant today, but this is the foundational path every
    // downstream stage (T3/T4/T5 + the terminal ship) routes through, and the binding
    // constraint is exact-integer certificate equality on every shipped compile — so
    // fail-closed here rather than trust the proof.
    if let Err(report) = certify(&c2, &trace2) {
        return Err(CompileError::InvalidSchedule(format!(
            "normalize recompile failed certificate: counted_traffic {} != reported_traffic {}",
            report.counted_traffic, report.reported_traffic,
        )));
    }
    Ok((plan2, c2, trace2, unrealized.len(), 0))
}

/// Per-run leaf-reclaim activity counters (spec §6). Task 1 DEFINES the type; Tasks
/// 2+ populate it and thread it through `RoundResult` → [`PricedOutcome`] → the
/// engine's `CsOutcome`.
#[derive(Clone, Debug, Default)]
pub struct LeafReclaimCounters {
    pub whole_origin_attempted: usize,
    pub whole_origin_kept: usize,
    pub swaps_attempted: usize,
    pub swaps_kept: usize,
    pub refused_retains_normalized: usize,
    pub normalize_calls: usize,
    pub residual_gap_attempted: usize,
    pub residual_gap_kept: usize,
    pub fully_realized_origins: usize,
}

/// The outcome of the two-stage leaf reclaim (spec §3/§4). Task 1 DEFINES the type;
/// Task 2 switches [`reclaim_leaves`] to return it (always `Complete` until Task 5),
/// and Task 5 adds the `Incomplete` selection semantics (an unnormalized plan — the
/// shared budget was exhausted before a `normalize` could run — is INELIGIBLE to
/// ship, spec §3). `Complete` asserts zero unrealized `Retain`; `Incomplete` carries
/// the residual `unrealized` count as a diagnostic.
#[derive(Clone, Debug)]
pub enum LeafReclaimResult {
    Complete {
        plan: BwdOccurrencePlan,
        c: BwdCompiledLayer,
        trace: BwdCompileTrace,
        counters: LeafReclaimCounters,
    },
    Incomplete {
        plan: BwdOccurrencePlan,
        c: BwdCompiledLayer,
        trace: BwdCompileTrace,
        counters: LeafReclaimCounters,
        unrealized: usize,
    },
}

// ── priced rounds ────────────────────────────────────────────────────────────────

/// One round's certificate-passing outcome, for the lexicographic best-round pick.
struct RoundResult {
    plan: BwdOccurrencePlan,
    pins: Vec<ExprId>,
    feasible: bool,
    traffic: usize,
    instrs: usize,
    reclaim_attempted: usize,
    reclaim_kept: usize,
    compound_attempted: usize,
    compound_kept: usize,
}

impl RoundResult {
    /// Lexicographic objective key: prefer feasible, then min traffic, then min
    /// instrs (`!feasible` puts `false` — feasible — first).
    fn key(&self) -> (bool, usize, usize) {
        (!self.feasible, self.traffic, self.instrs)
    }
}

fn diverged(trace: &BwdCompileTrace) -> bool {
    trace
        .events
        .iter()
        .any(|e| matches!(e, BwdEvent::Diverge { .. }))
}

/// Priced rounds (spec §5, Rev 2). `frozen0` MUST be the coordinate-correct
/// `lower==place==budget` all-`Bypass` freeze (Task 5's `feasible_leaf_plan` step 1),
/// NOT the fill-then-trim `compile_distilled_traced` freeze.
///
/// Per round: (1) compile the feasible all-`Bypass` base compound plan (empty pins) —
/// the greedy's start AND the round's fail-closed fallback (a `BudgetBelowFloor` or a
/// `Diverge` on the BASE drops the round fail-closed and exits with the previous best);
/// (2) [`reclaim_compounds`] — the compiler-tried compound greedy (hint-ranked,
/// compile+certify-validated; the model is NOT the selection authority); (3) re-freeze
/// on the best compound compile's ACTUAL trace; (4) [`reclaim_leaves`] — the bounded
/// gap-granular leaf reclaim validated against the real program (Commit 2); (5) build
/// the [`PlannerSignature`] and stop on structural equality with the previous round.
/// Cap 3 rounds; on non-convergence return the best certificate-passing round by the
/// lexicographic objective. COMPOSITION ORDER: compounds FIRST (they reshape the serve
/// stream by suppressing cone re-expansions), THEN leaves (fine-grained retention on the
/// reshaped, re-frozen stream) — both greedies are compiler-validated per candidate.
pub fn priced_rounds(
    d: &DistilledLayer,
    budget: usize,
    frozen0: FrozenDemand,
) -> Result<PricedOutcome, CompileError> {
    let mut width_memo: Vec<Option<FieldKind>> = vec![None; d.layer.exprs.len()];
    let mut current_frozen = frozen0;

    // Coordinate-correct all-`Bypass` baseline: guaranteed feasible (it is the
    // program `current_frozen` was frozen from), and the fallback if every round
    // drops fail-closed.
    let base_end = subtree_ends(&current_frozen);
    let base_plan = compound_batch_plan_with(&current_frozen, &BTreeSet::new(), &base_end);
    let (base_c, base_trace) = compile_distilled_planned(d, budget, &base_plan)?;
    let base_cert = certify(&base_c, &base_trace);
    let mut best = RoundResult {
        plan: base_plan,
        pins: Vec::new(),
        feasible: base_cert.is_ok() && !diverged(&base_trace),
        traffic: base_c.stats_ext.global + base_c.stats_ext.fold_traffic,
        instrs: base_c.stats.program_lanes,
        reclaim_attempted: 0,
        reclaim_kept: 0,
        compound_attempted: 0,
        compound_kept: 0,
    };

    let mut prev_sig: Option<PlannerSignature> = None;
    let mut converged = false;
    let mut rounds_run = 0usize;

    for _round in 0..3 {
        rounds_run += 1;
        let end = subtree_ends(&current_frozen);
        let leaf_pos = leaf_stream_positions(&current_frozen);

        // (1) compile the feasible all-`Bypass` compound base — the greedy's start AND
        // the round's fail-closed fallback (a `BudgetBelowFloor`/`Diverge` on the base
        // drops the round and exits with the previous best).
        let round_base_plan = compound_batch_plan_with(&current_frozen, &BTreeSet::new(), &end);
        let (rb_c, rb_trace) = match compile_distilled_planned(d, budget, &round_base_plan) {
            Ok(x) => x,
            Err(CompileError::BudgetBelowFloor { .. }) => break,
            Err(e) => return Err(e),
        };
        if diverged(&rb_trace) {
            break;
        }

        // (2) compiler-TRIED compound greedy: hint-ranked candidates (`i64::MIN` spans
        // ranked, never filtered), each KEPT only on a real compile that is feasible,
        // non-diverging, and strictly-traffic-dropping — the model is the ranking hint,
        // never the selection authority.
        let (pinned, compound_plan, cbatch_c, cbatch_trace, c_attempted, c_kept) =
            reclaim_compounds(
                d,
                budget,
                &current_frozen,
                &end,
                &leaf_pos,
                &mut width_memo,
                round_base_plan,
                rb_c,
                rb_trace,
            )?;

        // (3) re-freeze on the best compound compile's ACTUAL trace (realized suppression).
        let observed = freeze_demand(d, &cbatch_trace, &cbatch_c.program, &cbatch_c.specials);

        // (4) Re-plan + BOUNDED GAP-GRANULAR leaf reclaim on the observed (realized)
        // demand: start from the all-`Bypass`-leaves compound batch and greedily retain
        // the top-N realized leaf gaps that (feasibly, non-divergingly) drop dram_traffic
        // against the REAL program (Commit 2, spec §5 step 4).
        let (final_plan, final_c, final_trace, r_attempted, r_kept) =
            reclaim_leaves(d, budget, &observed, &compound_plan, cbatch_c, cbatch_trace)?;
        let cert = certify(&final_c, &final_trace);
        let result = RoundResult {
            plan: final_plan.clone(),
            pins: pinned.iter().copied().collect(),
            feasible: cert.is_ok() && !diverged(&final_trace),
            traffic: final_c.stats_ext.global + final_c.stats_ext.fold_traffic,
            instrs: final_c.stats.program_lanes,
            reclaim_attempted: r_attempted,
            reclaim_kept: r_kept,
            compound_attempted: c_attempted,
            compound_kept: c_kept,
        };
        // `<=` (not `<`): on an inert tie with the pre-loop base a reclaim round still
        // adopts the outcome, so `reclaim_attempted` (the lever RAN) stays visible; ties
        // are objective-equivalent and the round sequence is deterministic.
        if result.key() <= best.key() {
            best = RoundResult {
                plan: result.plan.clone(),
                pins: result.pins.clone(),
                feasible: result.feasible,
                traffic: result.traffic,
                instrs: result.instrs,
                reclaim_attempted: result.reclaim_attempted,
                reclaim_kept: result.reclaim_kept,
                compound_attempted: result.compound_attempted,
                compound_kept: result.compound_kept,
            };
        }

        // (5) structural fixed point.
        let sig = planner_signature(&observed, &final_trace, &pinned, &final_plan);
        if prev_sig.as_ref() == Some(&sig) {
            converged = true;
            break;
        }
        prev_sig = Some(sig);
        current_frozen = observed;
    }

    Ok(PricedOutcome {
        plan: best.plan,
        pins: best.pins,
        rounds: rounds_run,
        converged,
        reclaim_attempted: best.reclaim_attempted,
        reclaim_kept: best.reclaim_kept,
        compound_attempted: best.compound_attempted,
        compound_kept: best.compound_kept,
    })
}
