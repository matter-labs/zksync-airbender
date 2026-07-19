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

use super::compile::{BwdCompileBackend, BwdCompiledLayer, TermBackend};
use super::distill::{distilled_site_domain, DistilledLayer};
use super::fif::{fif_select, occ_range, Gap};
use super::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use super::structure::expr_width;
use super::trace::{
    certify, BwdCompileTrace, BwdEvent, BwdFingerprint, BwdServedFrom, FrozenDemand,
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

/// CS-M4 T7 (spec §2/§12): the PRODUCTION Stage-B candidate cap (`gap_cap`) shipped by
/// [`cs_schedule_bwd_layer`]. Banked at `1200` after the G-M0 milestone: the Tiers were
/// set from the `gap_cap=1200` regime, and the no-regression safety-net floor `best_B`
/// reaches Tier 0 (all four G-M0 fixtures) + Tier 1 (blake2 8348) there — keccak 14580,
/// blake2 8348, bigint 18056, unified 3668. Tier 2 (GA's blake2 7996) is unreachable by
/// the whole-origin machinery even un-starved (measured), so `1200` is the shipped
/// Partial (~2.4× the `RECLAIM_N=512` wall). The multiplier stays `1` (the credit lever
/// is inert — measured mult2 ≈ mult1). `RECLAIM_N` is retained as the legacy per-gap cap
/// for the research entry + direct-`priced_rounds` tests, which pass it explicitly.
pub const PRODUCTION_GAP_CAP: usize = 1200;

/// Default cap on the compiler-tried COMPOUND greedy's candidate count (Commit 3).
/// Independent of the leaf reclaim's [`RECLAIM_N`] (CS-M3 Task 1): keccak's compound
/// candidate count (~113) exceeds `RECLAIM_N`'s 32, so sharing the knob left the
/// compound greedy cap-bound (30/32 kept, attempted pinned at 32) well below its true
/// candidate count, throttling cone-suppression retention at saturation. `128` clears
/// keccak's candidate count with headroom while still bounding total compound
/// recompiles to `≤ 2·COMPOUND_N`, same shape as the leaf reclaim's `≤ 2·RECLAIM_N`.
pub const COMPOUND_N: usize = 128;

/// CS-M4 Task 3 (spec §4): cap on Stage A's whole-origin candidate COUNT. Stage A ranks
/// realized domain-leaf origins (≥2 occurrences) by yield-per-cell and accumulatingly
/// retains each whole interval that strictly drops traffic; this bounds how many origins
/// it TRIES per round. `2048` comfortably exceeds every G-M0 fixture's realized origin
/// count at b16 (blake2 ~1012 is the widest), so the effective truncate
/// `min(candidate_count, LEAF_ORIGIN_N)` is candidate-bound in practice, not cap-bound;
/// the shared per-round `TrialBudget` (with a reserved `normalize` credit) is the real
/// cost bound (spec §5), NOT this count.
pub const LEAF_ORIGIN_N: usize = 2048;

/// CS-M4 Task 4 (spec §4): cap on Stage A' candidate SWAP count per round. Stage A' walks
/// the rejected origins highest-yield-per-cell first and, for each, tries ONE bounded
/// one-in/K-out swap; this bounds how many swaps it TRIES. `64` is small (each swap is a
/// full `compile_distilled_planned`) yet ample to un-stick the top misallocations; the
/// shared per-round `TrialBudget` (reserve 1 for the following `normalize`) is the real
/// cost bound (spec §5), NOT this count.
pub const SWAP_N: usize = 64;

/// CS-M4 Task 4 (spec §4): cap on the swap REMOVAL set size (origins evicted to admit one
/// higher-yield rejected origin `R`). Small and fixed — a "one-in/K-out" swap removes at
/// most `K` accepted origins (ascending yield-per-cell, resident at `R`'s pressure point);
/// if `K` removals cannot free `R`'s `need`, `R` is skipped (never compiled).
pub const K: usize = 3;

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
    /// CS-M4 (Task 2): the RETURNED (best) round's leaf-reclaim activity counters.
    /// Task 2 populates only the residual-gap fields (from the per-gap loop); the
    /// Stage-A/A'/normalize fields stay `0` until Tasks 3/4.
    pub counters: LeafReclaimCounters,
    /// CS-M4 (Task 2): `true` iff ANY round's leaf reclaim returned `Incomplete` —
    /// OR-ed across ALL rounds, independent of the best-round selection (spec §3).
    /// Always `false` in Task 2 (`reclaim_leaves` is always `Complete`); Task 5 wires
    /// the selection.
    pub saw_incomplete_round: bool,
    /// CS-M4 (Task 2, spec §5): per-run leaf-search `compile_distilled_planned` count
    /// (the budget-scoped cost), summed across rounds.
    pub leaf_calls: usize,
    /// CS-M4 (Task 2, spec §5): per-run base+compound compile count (essential,
    /// UNBUDGETED), summed across rounds and reported separately from `leaf_calls`.
    pub base_compound_calls: usize,
    /// CS-M4 (Task 2, spec §5): `Σ_r G_r` (realized leaf gaps) across rounds.
    pub sum_g: usize,
    /// CS-M4 (Task 2, spec §5): `Σ_r min(G_r, 1200)` (the accrual reference quota)
    /// across rounds — the generic allowance a run accrues at `multiplier = 1`.
    pub sum_quota: usize,
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
    backend: &dyn BwdCompileBackend,
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
    (BTreeSet<ExprId>, BwdOccurrencePlan, BwdCompiledLayer, BwdCompileTrace, usize, usize, usize),
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
        match backend.planned(d, budget, &trial) {
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

    // `compiles` is the count of compound `compile_distilled_planned` calls (each an
    // essential, UNBUDGETED base/compound compile, spec §5) — reported separately from
    // the leaf-search `leaf_calls`.
    Ok((pinned, best_plan, best_c, best_trace, attempted, kept, compiles))
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

/// The per-gap leaf reclaim loop (spec §4 Stage B; the CS-M3 body). Starting from
/// `entries`/`best_c`/`best_trace`, walk the FiF-ranked `order` and for each candidate
/// gap whose opening occurrence is still `Bypass`, flip it to `Retain`,
/// [`compile_distilled_planned`], and KEEP iff feasible ∧ non-diverging ∧ certifies ∧
/// `dram_traffic` STRICTLY drops vs best; else revert. `reserve` is the [`TrialBudget`]
/// credit held back for a following op (0 for the B-only floor which has no following
/// `normalize`; 1 for the A+B residual which precedes the terminal normalize). Recompiles
/// bounded to `≤ 2·gap_cap`. Returns `(entries, best_c, best_trace, attempted, kept)`.
///
/// CS-M4 Task 3 (RR no-regression safety net): this is called TWICE per round from
/// [`reclaim_leaves`] over the SAME `order`/`meta`/`occ_idx` — once from the compound
/// base (the CS-M3-reproducing B-only floor) and once from the post-Stage-A normalized
/// plan (the A+B residual) — sharing the one round `TrialBudget`.
#[allow(clippy::too_many_arguments)]
fn per_gap_reclaim(
    backend: &dyn BwdCompileBackend,
    d: &DistilledLayer,
    budget: usize,
    plan_template: &BwdOccurrencePlan,
    occ_idx: &BTreeMap<ExprId, Vec<usize>>,
    order: &[usize],
    meta: &[(ExprId, usize)],
    gap_cap: usize,
    reserve: usize,
    mut entries: Vec<PlanEntry>,
    mut best_c: BwdCompiledLayer,
    mut best_trace: BwdCompileTrace,
    trial_budget: &mut TrialBudget,
) -> Result<(Vec<PlanEntry>, BwdCompiledLayer, BwdCompileTrace, usize, usize), CompileError> {
    let mut best_traffic = best_c.stats_ext.global + best_c.stats_ext.fold_traffic;
    let mut attempted = 0usize;
    let mut kept = 0usize;
    let mut compiles = 0usize;

    for &gi in order {
        if compiles >= 2 * gap_cap {
            break; // recompile budget guard (≤ 2·gap_cap)
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

        // Charge one leaf-search credit, reserving `reserve` (0 = B-only floor, no
        // following normalize; 1 = A+B residual, reserve for the terminal normalize). A
        // refusal (budget exhausted) stops the loop with the best-so-far plan.
        if !trial_budget.try_spend(reserve) {
            break;
        }
        attempted += 1;
        entries[entry_idx].action = PlanAction::Retain; // tentative flip
        let trial = plan_from(plan_template, entries.clone());
        compiles += 1;
        match backend.planned(d, budget, &trial) {
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
            // Realized floor exceeded budget with this retention — revert.
            Err(CompileError::BudgetBelowFloor { .. }) => {
                entries[entry_idx].action = PlanAction::Bypass;
            }
            Err(e) => return Err(e),
        }
    }
    Ok((entries, best_c, best_trace, attempted, kept))
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
/// CS-M4 Task 4 (spec §4): compact Stage-A rejection metadata for the Stage A' swap. Holds
/// ONLY what a swap needs — never the full trial program/trace (memory: a wide layer rejects
/// hundreds/thousands of origins). `pressure_k` is `R`'s FIRST-unrealized-opening PLAN-ENTRY
/// index (the first `Retain` occurrence of `R` its Stage-A trial did NOT realize), which is
/// STABLE across programs because every plan in the reclaim pipeline shares
/// `base_plan.entries`' indexing (only the per-entry `action` differs). `need` is `R`'s
/// residency width (cells); `(num, den)` is its yield-per-cell (gaps closed / summed occupied
/// cell-instants) for the descending swap-priority order.
struct StageARejection {
    v: ExprId,
    pressure_k: usize,
    need: usize,
    num: usize,
    den: usize,
}

/// CS-M4 Task 4 (spec §4): the residency set at the PRE-ADMISSION boundary of plan-entry
/// `k` — the live residents (→ their occupied width in cells) immediately BEFORE `k`'s own
/// admission is attempted. Reconstructed from `trace` by walking events with (i) a
/// DOMAIN-serve cursor incremented ONLY on a `Serve` whose value is in `domain_values` (the
/// `trace.rs:265` filter that makes domain serves align 1:1 with plan entries) and (ii) the
/// live residency set (`Admit` inserts, `Evict` removes). A plan-entry index is NOT a raw
/// event index — `trace.events` interleaves `Serve`/`TrafficRead`/`Admit`/`Evict`, and only
/// the cursor recovers the alignment. STOPS the instant it reaches the domain `Serve` whose
/// cursor == `k` (that serve's own admit/evict fire LATER in the stream, so they are excluded
/// — the boundary is pre-`k`-admission). Returns `None` if the trace diverged (the
/// cursor↔entry alignment is void) or `k` is never reached.
fn residency_before_entry(
    trace: &BwdCompileTrace,
    domain_values: &BTreeSet<ExprId>,
    k: usize,
) -> Option<BTreeMap<ExprId, usize>> {
    let mut resident: BTreeMap<ExprId, usize> = BTreeMap::new();
    let mut cursor = 0usize;
    for e in &trace.events {
        match e {
            BwdEvent::Diverge { .. } => return None,
            BwdEvent::Admit { value, width } => {
                resident.insert(*value, *width as usize);
            }
            BwdEvent::Evict { value, .. } => {
                resident.remove(value);
            }
            BwdEvent::Serve { fp, .. } if domain_values.contains(&fp.value) => {
                if cursor == k {
                    return Some(resident); // pre-admission boundary for entry k
                }
                cursor += 1;
            }
            _ => {}
        }
    }
    None
}

/// TERM-backend compat wrapper for [`reclaim_leaves_with_backend`] (CS-M5a Task 6):
/// preserves the pre-Task-6 public signature, so the direct callers in `bwd_cs_engine.rs`
/// compile unchanged.
pub fn reclaim_leaves(
    d: &DistilledLayer,
    budget: usize,
    observed: &FrozenDemand,
    base_plan: &BwdOccurrencePlan,
    base_c: BwdCompiledLayer,
    base_trace: BwdCompileTrace,
    gap_cap: usize,
    trial_budget: &mut TrialBudget,
) -> Result<LeafReclaimResult, CompileError> {
    reclaim_leaves_with_backend(
        &TermBackend,
        d,
        budget,
        observed,
        base_plan,
        base_c,
        base_trace,
        gap_cap,
        trial_budget,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn reclaim_leaves_with_backend(
    backend: &dyn BwdCompileBackend,
    d: &DistilledLayer,
    budget: usize,
    observed: &FrozenDemand,
    base_plan: &BwdOccurrencePlan,
    base_c: BwdCompiledLayer,
    base_trace: BwdCompileTrace,
    gap_cap: usize,
    trial_budget: &mut TrialBudget,
) -> Result<LeafReclaimResult, CompileError> {
    // Each domain leaf's opening-occurrence entry indices within the base plan.
    let mut occ_idx: BTreeMap<ExprId, Vec<usize>> = BTreeMap::new();
    for (k, e) in base_plan.entries.iter().enumerate() {
        if observed.leaf_instants.contains_key(&e.fp.value) {
            occ_idx.entry(e.fp.value).or_default().push(k);
        }
    }

    // Realized per-leaf chained-tiling gaps (program-position coordinates) + parallel
    // metadata (leaf value, gap index j) — identical tiling to `plan_leaves`. SHARED by
    // BOTH per-gap searches below (the B-only floor + the A+B residual).
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
    // `gap_cap` (production `PRODUCTION_GAP_CAP`=1200 after T7; the legacy `RECLAIM_N`=512
    // research/Phase-0b point still passed explicitly by the research entry + direct tests)
    // bounds the per-gap candidate COUNT — INDEPENDENT of the accrued budget (anchored on
    // `min(G_r,1200)`) and of the `multiplier` (spec §5). Truncation is shared by both
    // per-gap searches.
    order.truncate(gap_cap);

    // ══ CS-M4 Task 3 — RR no-regression safety net: ship lexicographic-min(A+B, B-only) ══
    // Compute BOTH candidate plans from the SAME compound base, sharing the ONE round
    // `TrialBudget`, and ship the lexicographic-min by `(traffic, instrs)` (EXACT tie →
    // B-only). The B-only candidate is the pure per-gap floor at whatever `gap_cap`
    // production passes (T7's 1200; = CS-M3 byte-for-byte only at `gap_cap=512`). Because a
    // wider `gap_cap` only ADMITS more strict-drop retentions, that floor is ≤ CS-M3's at
    // any `gap_cap ≥ 512`, so CS-M4 is NEVER worse than CS-M3 on any fixture; Stage A's
    // whole-origin coverage ships only where it STRICTLY beats that floor.

    // ── Candidate B-only: the pure per-gap reclaim from the compound base — the per-gap
    // floor at `gap_cap` (the CS-M3 floor exactly when `gap_cap=512`). It runs FIRST with
    // reserve 0, so it makes the per-gap greedy's full decisions: this round's fresh
    // accrual `min(G_r,1200) ≥` its `≤ min(G_r, gap_cap)` candidate count (equality at the
    // production `gap_cap=1200`), so — running before the A+B path drains anything — it is
    // never budget-refused and makes exactly the per-gap decisions at that cap (= CS-M3's
    // when `gap_cap=512`). No `normalize` follows it, so reserve 0 (a reserve here would
    // drop the last gap on a budget-tight small fixture and break the floor).
    let (b_entries, b_c, b_trace, b_attempted, b_kept) = per_gap_reclaim(
        backend,
        d,
        budget,
        base_plan,
        &occ_idx,
        &order,
        &meta,
        gap_cap,
        /*reserve*/ 0,
        base_plan.entries.clone(),
        base_c.clone(),
        base_trace.clone(),
        trial_budget,
    )?;
    let b_key = (b_c.stats_ext.global + b_c.stats_ext.fold_traffic, b_c.stats.program_lanes);

    // ── Candidate A+B: Stage A whole-origin greedy → post-stage normalize → per-gap
    // residual. Stage A candidate origins = realized domain leaves with ≥2 occurrences.
    // RANK by YIELD-PER-CELL (spec §4): numerator = gathers the whole-interval residency
    // saves (`len−1` closed gaps); denominator = summed occupied cell-instants over the
    // value's live interval (`width(v)·(last_instant − first_instant)`, `width` via
    // [`width_of`]). Descending, `ExprId` tie-break — in an accumulating greedy ORDER IS
    // the selection authority, so the ranking is deterministic (cross-multiplied
    // fractions, never float). Truncate to `LEAF_ORIGIN_N` (→ `min(candidate_count, 2048)`).
    let mut width_memo: Vec<Option<FieldKind>> = vec![None; d.layer.exprs.len()];
    let mut origins: Vec<(ExprId, usize, usize)> = observed
        .leaf_instants
        .iter()
        .filter(|(_, instants)| instants.len() >= 2)
        .map(|(&v, instants)| {
            let num = instants.len() - 1; // gaps the whole-interval residency closes
            let span = instants[instants.len() - 1] - instants[0];
            let den = width_of(d, v, &mut width_memo) * span; // summed occupied cell-instants
            (v, num, den)
        })
        .collect();
    origins.sort_by(|a, b| {
        let lhs = (a.1 as u128) * (b.2 as u128);
        let rhs = (b.1 as u128) * (a.2 as u128);
        rhs.cmp(&lhs).then_with(|| a.0.cmp(&b.0))
    });
    origins.truncate(LEAF_ORIGIN_N);

    // Accumulate whole-interval retains ON TOP of the compound base `acc_entries` (never
    // from scratch): each accepted origin's retains chain into later origins' trials.
    let mut acc_entries = base_plan.entries.clone();
    let mut a_best_traffic = base_c.stats_ext.global + base_c.stats_ext.fold_traffic;
    let mut a_best_c = base_c;
    let mut a_best_trace = base_trace;
    let mut whole_origin_attempted = 0usize;
    let mut whole_origin_kept = 0usize;
    // CS-M4 Task 4 (spec §4): compact Stage-A metadata the Stage A' swap consumes.
    // `accepted_origins`: each KEPT whole-origin → its yield-per-cell `(num, den)` (the swap
    // removal set ranks these ascending). `rejected`: each REJECTED origin with a genuine
    // first-unrealized opening → its pressure point + `need` + yield (the swap admits these
    // highest-yield first). Neither holds any trial program/trace (memory, spec §4 / Step 3).
    let mut accepted_origins: BTreeMap<ExprId, (usize, usize)> = BTreeMap::new();
    let mut rejected: Vec<StageARejection> = Vec::new();

    for (v, num, den) in origins {
        let occ = match occ_idx.get(&v) {
            Some(o) if o.len() >= 2 => o.clone(),
            _ => continue, // no multi-occurrence plan footprint — nothing to retain
        };
        // Charge one leaf-search credit, RESERVING 1 for the post-stage `normalize`
        // (spec §5). A refusal (budget exhausted — B-only already spent its share) stops
        // Stage A with the best-so-far accumulated plan.
        if !trial_budget.try_spend(1) {
            break;
        }
        whole_origin_attempted += 1;
        let last = occ.len() - 1;
        // Mirror `compound_batch_plan_with` (`price.rs:598-627`) for a SINGLE leaf: Retain
        // every occurrence but the last, Bypass the last — applied on top of `acc_entries`.
        // Save prior actions so a reject reverts the WHOLE origin.
        let saved: Vec<PlanAction> = occ.iter().map(|&k| acc_entries[k].action).collect();
        for (i, &k) in occ.iter().enumerate() {
            acc_entries[k].action =
                if i < last { PlanAction::Retain } else { PlanAction::Bypass };
        }
        let trial = plan_from(base_plan, acc_entries.clone());
        match backend.planned(d, budget, &trial) {
            Ok((c, t)) => {
                let dram = c.stats_ext.global + c.stats_ext.fold_traffic;
                let clean = certify(&c, &t).is_ok() && !diverged(&t);
                if clean && dram < a_best_traffic {
                    a_best_traffic = dram;
                    a_best_c = c;
                    a_best_trace = t;
                    whole_origin_kept += 1; // KEEP: whole-interval retain stays in acc_entries
                    // Record the KEPT origin's yield-per-cell — a Stage A' swap removal
                    // candidate (Stage A' swaps OUT low-yield accepted origins, §4).
                    accepted_origins.insert(v, (num, den));
                } else {
                    // REJECTED: record compact swap metadata (spec §4) — `R`'s FIRST
                    // unrealized opening is its pressure point (a PLAN-ENTRY index, stable
                    // across programs). If EVERY opening realized (no capacity shortfall a
                    // swap can fix) record nothing; a diverged trial yields an empty realized
                    // set → the pressure point is the first opening.
                    let realized = realized_openings(&trial, &t);
                    if let Some(&pk) = occ[..last].iter().find(|k| !realized.contains(k)) {
                        rejected.push(StageARejection {
                            v,
                            pressure_k: pk,
                            need: width_of(d, v, &mut width_memo),
                            num,
                            den,
                        });
                    }
                    for (&k, &a) in occ.iter().zip(saved.iter()) {
                        acc_entries[k].action = a; // revert the WHOLE origin
                    }
                }
            }
            // The whole-interval retain's realized floor exceeded the budget — revert whole.
            Err(CompileError::BudgetBelowFloor { .. }) => {
                for (&k, &a) in occ.iter().zip(saved.iter()) {
                    acc_entries[k].action = a;
                }
            }
            Err(e) => return Err(e),
        }
    }

    // Post-stage `normalize` (spec §4): demote Stage A's own refused (unrealized) retains
    // to `Bypass` — behavior- and traffic-neutral (spec §3). `_unrealized` is 0 given the
    // reserved credit; the TERMINAL normalize / `Incomplete` selection is Task 5, NOT here
    // (this `reclaim_leaves` still returns `Complete`).
    let stage_a_plan = plan_from(base_plan, acc_entries);
    let (norm_plan, norm_c, norm_trace, demoted_a, _unrealized) =
        normalize_with_backend(backend, d, budget, stage_a_plan, a_best_c, a_best_trace, trial_budget)?;

    // ── A+B BASELINE (the Task-3 A+B path): per-gap residual over the post-Stage-A
    // normalized plan. Runs HERE — right after Stage A's normalize and BEFORE Stage A' — so
    // it sees the EXACT budget state Task-3's A+B saw (b_only + Stage A + normalize spent),
    // reproducing Task-3's A+B decisions byte-for-byte. This is `best_AB`'s FLOOR: Stage A'
    // (on the shared, DECREMENTING budget) can only be a bonus candidate, never a regression
    // — a swap that steals budget from a later per-gap cannot push the shipped result above
    // this floor, since we ship `min(ab_baseline, ab_aprime)` below (spec §4 monotone intent;
    // the two-candidate `min(best_AB, best_B)` net alone does NOT bound `best_AB` from below
    // its own Task-3 value, because Stage B is a budget-shared, path-dependent greedy).
    // Reserve 1 for the terminal normalize (Task 5); shares the round budget.
    let (abb_entries, abb_c, abb_trace, abb_attempted, abb_kept) = per_gap_reclaim(
        backend,
        d,
        budget,
        base_plan,
        &occ_idx,
        &order,
        &meta,
        gap_cap,
        /*reserve*/ 1,
        norm_plan.entries.clone(),
        norm_c.clone(),
        norm_trace.clone(),
        trial_budget,
    )?;
    let abb_key =
        (abb_c.stats_ext.global + abb_c.stats_ext.fold_traffic, abb_c.stats.program_lanes);

    // ══ CS-M4 Task 4 (spec §4) — Stage A': bounded one-in/K-out swap ══
    // Un-stick Stage A's greedy misallocations: for each REJECTED origin `R` (highest
    // yield-per-cell first), swap ≤`K` low-yield ACCEPTED origins (resident at `R`'s pressure
    // point) OUT to admit `R`'s whole interval. KEEP a swap only if it certifies, does not
    // diverge, and realized traffic (`global + fold_traffic`) STRICTLY drops vs the current
    // best (else revert the WHOLE swap). Accumulating over the normalized Stage-A plan; the
    // shared `TrialBudget` reserves 1 for the following `normalize`. Monotone — A' can only
    // improve `best_AB`, never regress (the safety net still ships `min(A+B, B-only)`).
    let domain_values: BTreeSet<ExprId> =
        distilled_site_domain(d).into_iter().map(|s| s.value).collect();
    let mut swaps_attempted = 0usize;
    let mut swaps_kept = 0usize;
    let mut ap_entries = norm_plan.entries.clone();
    let mut ap_c = norm_c;
    let mut ap_trace = norm_trace;
    let mut ap_best_traffic = ap_c.stats_ext.global + ap_c.stats_ext.fold_traffic;

    // Rejected swap candidates: highest yield-per-cell FIRST (desc, `ExprId` tie-break) —
    // the SAME cross-multiplied fraction order Stage A ranks by (never float). Cap `SWAP_N`.
    rejected.sort_by(|a, b| {
        let lhs = (a.num as u128) * (b.den as u128);
        let rhs = (b.num as u128) * (a.den as u128);
        rhs.cmp(&lhs).then_with(|| a.v.cmp(&b.v))
    });
    rejected.truncate(SWAP_N);

    for r in &rejected {
        // Reconstruct the residency set at `R`'s pressure point from the CURRENT-best trace
        // (accumulating: earlier kept swaps reshape it). A non-diverging best is required for
        // the cursor↔entry alignment; a clean Stage-A/normalize best never diverges, but if
        // one ever did, every remaining swap's pressure point is void → stop.
        let resident = match residency_before_entry(&ap_trace, &domain_values, r.pressure_k) {
            Some(m) => m,
            None => break,
        };
        // Removal set: ACCEPTED origins RESIDENT at the pressure point, ascending
        // yield-per-cell (tie `ExprId`), greedily added until freed width ≥ `R`'s `need`,
        // capped at `K`. Freed width is the origin's OWN residency width at that point (from
        // its `Admit`), never capacity it holds elsewhere. An accepted origin not resident
        // here contributes nothing (overlap-elsewhere is a non-guarantee, spec §4).
        let mut cands: Vec<(usize, usize, ExprId, usize)> = resident
            .iter()
            .filter_map(|(&ov, &w)| accepted_origins.get(&ov).map(|&(n, dsum)| (n, dsum, ov, w)))
            .collect();
        cands.sort_by(|a, b| {
            let lhs = (a.0 as u128) * (b.1 as u128);
            let rhs = (b.0 as u128) * (a.1 as u128);
            lhs.cmp(&rhs).then_with(|| a.2.cmp(&b.2))
        });
        let mut removal: Vec<ExprId> = Vec::new();
        let mut freed = 0usize;
        for (_, _, ov, w) in cands {
            if freed >= r.need || removal.len() >= K {
                break;
            }
            removal.push(ov);
            freed += w;
        }
        if freed < r.need {
            continue; // ≤K removals cannot free `R`'s need — skip `R` (no compile, no spend)
        }
        // Charge one leaf-search credit, reserving 1 for the post-A' `normalize` (spec §5).
        if !trial_budget.try_spend(1) {
            break;
        }
        swaps_attempted += 1;
        // Apply the swap on a CLONE of the current best entries: `Bypass` EVERY occurrence of
        // each removed origin; add `R` whole-interval (`Retain` occ[0..last], `Bypass` the
        // last — mirrors `compound_batch_plan_with`). A reject discards the clone (whole-swap
        // revert); a keep adopts it.
        let mut trial_entries = ap_entries.clone();
        for ov in &removal {
            if let Some(occ) = occ_idx.get(ov) {
                for &k in occ {
                    trial_entries[k].action = PlanAction::Bypass;
                }
            }
        }
        if let Some(r_occ) = occ_idx.get(&r.v) {
            let r_last = r_occ.len() - 1;
            for (i, &k) in r_occ.iter().enumerate() {
                trial_entries[k].action =
                    if i < r_last { PlanAction::Retain } else { PlanAction::Bypass };
            }
        }
        let trial = plan_from(base_plan, trial_entries.clone());
        match backend.planned(d, budget, &trial) {
            Ok((c, t)) => {
                let dram = c.stats_ext.global + c.stats_ext.fold_traffic;
                let clean = certify(&c, &t).is_ok() && !diverged(&t);
                if clean && dram < ap_best_traffic {
                    ap_best_traffic = dram;
                    ap_entries = trial_entries; // commit the swap
                    ap_c = c;
                    ap_trace = t;
                    swaps_kept += 1;
                }
                // else: discard the clone (whole swap reverted)
            }
            // The swapped plan's realized floor exceeded the budget — revert (discard clone).
            Err(CompileError::BudgetBelowFloor { .. }) => {}
            Err(e) => return Err(e),
        }
    }

    // Post-A' `normalize` (spec §4): demote any A'-added unrealized retains — behavior- and
    // traffic-neutral (spec §3). `normalize_calls` is now 2; `refused_retains_normalized`
    // accumulates both passes. `_unrealized2` ignored (Task 5 wires the terminal normalize /
    // `Incomplete` selection — this `reclaim_leaves` still returns `Complete`).
    let stage_ap_plan = plan_from(base_plan, ap_entries);
    let (norm2_plan, norm2_c, norm2_trace, demoted_ap, _unrealized2) =
        normalize_with_backend(backend, d, budget, stage_ap_plan, ap_c, ap_trace, trial_budget)?;

    // A+B (A'-augmented) residual: per-gap over the (twice-)NORMALIZED plan's `Bypass` gaps
    // (Stage A/A' retained occurrences are non-`Bypass` → skipped by the loop). Runs on the
    // budget LEFT after the A+B baseline + Stage A'; reserve 1 for the terminal normalize
    // (Task 5). Shares the round budget with B-only + Stage A + baseline + Stage A'.
    let (abp_entries, abp_c, abp_trace, abp_attempted, abp_kept) = per_gap_reclaim(
        backend,
        d,
        budget,
        base_plan,
        &occ_idx,
        &order,
        &meta,
        gap_cap,
        /*reserve*/ 1,
        norm2_plan.entries.clone(),
        norm2_c,
        norm2_trace,
        trial_budget,
    )?;
    let abp_key =
        (abp_c.stats_ext.global + abp_c.stats_ext.fold_traffic, abp_c.stats.program_lanes);

    // `best_AB` = the lexicographic-better of the Task-3 FLOOR (`ab_baseline`) and the
    // A'-augmented candidate (`ab_aprime`); an EXACT tie keeps the floor (byte-stable). Since
    // the floor reproduces Task-3's A+B exactly, `best_AB ≤ Task-3's A+B` — Stage A' is
    // strictly a potential improvement, never a regression.
    let (ab_entries, ab_c, ab_trace, ab_attempted, ab_kept, ab_key) = if abp_key < abb_key {
        (abp_entries, abp_c, abp_trace, abp_attempted, abp_kept, abp_key)
    } else {
        (abb_entries, abb_c, abb_trace, abb_attempted, abb_kept, abb_key)
    };

    // ── Pick the lexicographic-min by `(traffic, instrs)`; EXACT tie → B-only (keeps
    // byte-identity with CS-M3 when A+B adds nothing). Counters describe the SHIPPED plan.
    let (shipped_plan, shipped_c, shipped_trace, mut counters) = if ab_key < b_key {
        let final_plan = plan_from(base_plan, ab_entries);
        let counters = LeafReclaimCounters {
            whole_origin_attempted,
            whole_origin_kept,
            swaps_attempted,
            swaps_kept,
            refused_retains_normalized: demoted_a + demoted_ap,
            normalize_calls: 2,
            residual_gap_attempted: ab_attempted,
            residual_gap_kept: ab_kept,
            safety_net_chose_b_only: false,
            terminal_demoted: 0, // set by the terminal normalize below
        };
        (final_plan, ab_c, ab_trace, counters)
    } else {
        // B-only shipped: the SHIPPED plan has no whole-origin retains and no intermediate
        // `normalize`, so those counter fields are 0 (they describe the shipped plan). The
        // A+B path still RAN — its cost is folded into the shared `leaf_calls`;
        // `safety_net_chose_b_only` flags the fallback for T6 diagnostics.
        let final_plan = plan_from(base_plan, b_entries);
        let counters = LeafReclaimCounters {
            residual_gap_attempted: b_attempted,
            residual_gap_kept: b_kept,
            safety_net_chose_b_only: true,
            ..LeafReclaimCounters::default()
        };
        (final_plan, b_c, b_trace, counters)
    };

    // ══ CS-M4 Task 5 (spec §3/§4) — TERMINAL normalize on the SHIPPED (min) plan ══
    // Stage B never leaves an unrealized `Retain` of its OWN (it keeps a gap flip only on a
    // strict traffic drop, which requires the retention to realize), but a Stage-B addition
    // CAN — by taking capacity at admission — strand an EARLIER whole-origin (A/A') `Retain`
    // whose realization the intermediate normalizes had confirmed. This single, behavior- and
    // traffic-NEUTRAL pass (spec §3: an unrealized `Retain` held zero capacity, so demoting it
    // frees nothing and changes no traffic) demotes exactly those stranded retains to `Bypass`,
    // closing the pipeline to the zero-unrealized-`Retain` shipped-plan invariant.
    //
    // Because it is traffic-neutral, it does NOT change which candidate was the min — so it
    // runs AFTER the selection above, on whichever plan won. It is a CHECKED spend
    // (`try_spend(0)`): if no credit remains it returns WITHOUT recompiling (no underflow, no
    // `HARD_MAX` breach), signalling `Incomplete`. The reserved credit each earlier stage keeps
    // (`try_spend(1)` throughout A/A'/B) funds it in the common case, so `Incomplete` is rare.
    let (norm_plan, norm_c, norm_trace, demoted_t, unrealized_after) =
        normalize_with_backend(backend, d, budget, shipped_plan, shipped_c, shipped_trace, trial_budget)?;
    counters.refused_retains_normalized += demoted_t;
    counters.terminal_demoted = demoted_t;
    counters.normalize_calls += 1;

    if unrealized_after == 0 {
        // The shipped-plan invariant (spec §3): a `Complete` plan has ZERO unrealized `Retain`
        // (`Retain` ⟺ realized). Re-derive it from the normalized trace and assert — a defensive
        // gate on the terminal normalize, NOT a runtime branch (the `== 0` already decided it).
        debug_assert!(
            {
                let realized = realized_openings(&norm_plan, &norm_trace);
                norm_plan
                    .entries
                    .iter()
                    .enumerate()
                    .all(|(k, e)| e.action != PlanAction::Retain || realized.contains(&k))
            },
            "terminal normalize returned Complete but the plan still holds an unrealized Retain",
        );
        Ok(LeafReclaimResult::Complete { plan: norm_plan, c: norm_c, trace: norm_trace, counters })
    } else {
        // Budget was exhausted before the terminal normalize could recompile: the plan is NOT
        // an honest-residency record. INELIGIBLE to ship — `priced_rounds` marks the round
        // `feasible = false` (best-round selection skips it, the engine falls back to the
        // coordinate-correct baseline) and OR-s `saw_incomplete_round` as a diagnostic.
        Ok(LeafReclaimResult::Incomplete {
            plan: norm_plan,
            c: norm_c,
            trace: norm_trace,
            counters,
            unrealized: unrealized_after,
        })
    }
}

// ── CS-M4 Task 1: realized-retention model ─────────────────────────────────────

/// A single decrementing leaf-search budget (spec §5) shared across all rounds of one
/// [`priced_rounds`] run. Task 2 enriches Task 1's minimal stub with per-round dynamic
/// accrual ([`Self::accrue`]: `available += multiplier · quota_r`, credits roll
/// forward) and leaf-call counting.
///
/// THREE independent controls (spec §5 — never coupled): `multiplier` scales accrued
/// CREDITS (the [`Self::accrue`] argument); `gap_cap` bounds Stage-B candidate COUNT
/// (a [`reclaim_leaves`] arg, not this type); `enforce` toggles whether the budget
/// actually caps/reserves. In COUNT-ONLY mode (`enforce == false`, spec §5 / Phase-0b)
/// every [`Self::try_spend`] succeeds and never reserves — it ONLY increments
/// `leaf_calls`, measuring the full @1200 leaf-call shape without the reserve rule
/// shaving a candidate. In ENFORCE mode (`enforce == true`, production) `try_spend`
/// spends one credit iff strictly more than `reserve` remain (the reserve keeps a
/// credit for the mandatory following `normalize`, spec §5).
///
/// `leaf_calls` counts EVERY [`Self::try_spend`]/[`Self::spend`] — the leaf-search
/// `compile_distilled_planned` calls the whole cost model (spec §5, `COST_CEILING`/
/// `HARD_MAX`) is scoped to; base/compound compiles are counted separately by the
/// caller and are NOT routed through this budget.
#[derive(Clone, Copy, Debug)]
pub struct TrialBudget {
    pub available: usize,
    pub spent: usize,
    pub leaf_calls: usize,
    pub enforce: bool,
}

impl Default for TrialBudget {
    /// Zero credits, nothing spent, ENFORCING (production default): a fresh budget
    /// only spends after [`Self::accrue`] rolls in a round's quota.
    fn default() -> Self {
        Self { available: 0, spent: 0, leaf_calls: 0, enforce: true }
    }
}

impl TrialBudget {
    /// A fresh budget in the given enforcement mode: `available = 0` (accrues per
    /// round), nothing spent yet. `enforce = false` is count-only (spec §5).
    pub fn new(enforce: bool) -> Self {
        Self { available: 0, spent: 0, leaf_calls: 0, enforce }
    }

    /// Roll `multiplier · quota` credits forward into `available` (spec §5, saturating).
    /// Called on entering each round's leaf reclaim, before any spend; unused credits
    /// from earlier rounds persist.
    pub fn accrue(&mut self, quota: usize, multiplier: usize) {
        self.available = self.available.saturating_add(quota.saturating_mul(multiplier));
    }

    /// Charge one leaf-search call, reserving `reserve` credits for a following
    /// mandatory op. ALWAYS increments `leaf_calls`. In count-only mode (`!enforce`) it
    /// always succeeds and never caps/reserves (nothing debited from `available`). In
    /// enforce mode it spends one credit iff strictly more than `reserve` remain
    /// (checked — never underflows): a caller with `available <= reserve` gets `false`
    /// and debits nothing.
    pub fn try_spend(&mut self, reserve: usize) -> bool {
        self.leaf_calls += 1;
        if !self.enforce {
            self.spent += 1;
            return true;
        }
        if self.available > reserve {
            self.available -= 1;
            self.spent += 1;
            true
        } else {
            false
        }
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
    normalize_with_backend(&TermBackend, d, budget, plan, c, trace, budget_ctr)
}

/// Backend-parameterized [`normalize`] (CS-M5a Task 6): the single recompile routes through
/// `backend.planned`; `normalize` is the [`TermBackend`] compat wrapper.
#[allow(clippy::too_many_arguments)]
pub fn normalize_with_backend(
    backend: &dyn BwdCompileBackend,
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
    let (c2, trace2) = backend.planned(d, budget, &plan2)?;
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
    /// CS-M4 Task 3 (RR no-regression safety net): `true` iff this round shipped the
    /// pure per-gap B-only candidate (the CS-M3 floor) because the A+B candidate did NOT
    /// strictly beat it on `(traffic, instrs)`. When set, all `whole_origin_*` /
    /// `normalize_*` fields are `0` (they describe the SHIPPED plan, which has no
    /// whole-origin retains); the A+B path still RAN (its cost is in `leaf_calls`), it
    /// just lost the lexicographic-min. A T6 diagnostic hook.
    pub safety_net_chose_b_only: bool,
    /// CS-M4 Task 5 (spec §3/§4): retains the TERMINAL normalize demoted on the SHIPPED
    /// (min) plan — Stage-B-created stranded retains cleaned to close the zero-unrealized
    /// invariant. `0` on the common (nothing stranded) path; `> 0` witnesses that the
    /// terminal normalize was load-bearing on this run. Also counted in the
    /// `refused_retains_normalized` total.
    pub terminal_demoted: usize,
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
    /// This round's leaf-reclaim counters (the RETURNED round's are carried to
    /// [`PricedOutcome::counters`]).
    counters: LeafReclaimCounters,
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
#[allow(clippy::too_many_arguments)]
pub fn priced_rounds_with_backend(
    backend: &dyn BwdCompileBackend,
    d: &DistilledLayer,
    budget: usize,
    frozen0: FrozenDemand,
    multiplier: usize,
    gap_cap: usize,
    enforce_budget: bool,
) -> Result<PricedOutcome, CompileError> {
    let mut width_memo: Vec<Option<FieldKind>> = vec![None; d.layer.exprs.len()];
    let mut current_frozen = frozen0;

    // CS-M4 Task 2 (spec §5): ONE decrementing leaf-search budget shared across all
    // rounds. `available` starts at 0 and accrues `multiplier · min(G_r,1200)` per round
    // (credits roll forward). `enforce_budget=false` is count-only (Phase-0b): it tallies
    // `leaf_calls` but never caps/reserves. `sum_g`/`sum_quota` bank the accrual shape.
    let mut trial_budget = TrialBudget::new(enforce_budget);
    // Base+compound compiles are essential and UNBUDGETED (spec §5) — counted here,
    // reported separately from the leaf-search `leaf_calls`.
    let mut base_compound_calls = 0usize;
    let mut sum_g = 0usize;
    let mut sum_quota = 0usize;
    // OR-ed across ALL rounds, independent of best-round selection (spec §3/Finding-4).
    let mut saw_incomplete_round = false;

    // Coordinate-correct all-`Bypass` baseline: guaranteed feasible (it is the
    // program `current_frozen` was frozen from), and the fallback if every round
    // drops fail-closed.
    let base_end = subtree_ends(&current_frozen);
    let base_plan = compound_batch_plan_with(&current_frozen, &BTreeSet::new(), &base_end);
    let (base_c, base_trace) = backend.planned(d, budget, &base_plan)?;
    base_compound_calls += 1;
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
        counters: LeafReclaimCounters::default(),
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
        base_compound_calls += 1;
        let (rb_c, rb_trace) = match backend.planned(d, budget, &round_base_plan) {
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
        let (pinned, compound_plan, cbatch_c, cbatch_trace, c_attempted, c_kept, c_compiles) =
            reclaim_compounds(
                backend,
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
        base_compound_calls += c_compiles;

        // (3) re-freeze on the best compound compile's ACTUAL trace (realized suppression).
        let observed = backend
            .freeze(d, &cbatch_c, &cbatch_trace)
            .ok_or(CompileError::FrozenDemandFailure)?;

        // CS-M4 Task 2 (spec §5): accrue THIS round's leaf-search credit BEFORE the
        // reclaim. `G_r` (realized leaf gaps) is known only now (post re-freeze), so
        // credit accrues per round — never a pre-summed `Σ_r`. The quota reference is
        // the FIXED 1200 (`min(G_r,1200)`), NOT `gap_cap` — coupling them would shrink the
        // quota to `gap_cap` (e.g. to 512 under the legacy `RECLAIM_N` research entry) and
        // break the accrual math; keeping it fixed holds the accrual reference constant
        // across every `gap_cap` the research entry sweeps (spec §5).
        let g_r: usize =
            observed.leaf_instants.values().map(|i| i.len().saturating_sub(1)).sum();
        let quota_r = g_r.min(1200);
        sum_g += g_r;
        sum_quota += quota_r;
        trial_budget.accrue(quota_r, multiplier);

        // (4) Re-plan + BOUNDED GAP-GRANULAR leaf reclaim on the observed (realized)
        // demand: start from the all-`Bypass`-leaves compound batch and greedily retain
        // the top-N realized leaf gaps that (feasibly, non-divergingly) drop dram_traffic
        // against the REAL program (Commit 2, spec §5 step 4).
        let reclaim = reclaim_leaves_with_backend(
            backend,
            d,
            budget,
            &observed,
            &compound_plan,
            cbatch_c,
            cbatch_trace,
            gap_cap,
            &mut trial_budget,
        )?;
        // Task 2: `reclaim_leaves` is always `Complete`; the `Incomplete` arm is
        // future-proofing for Task 5's selection (unreachable here). `reclaim_attempted`
        // / `reclaim_kept` mirror the residual-gap counters (the per-gap loop = spec §4
        // Stage B).
        let (final_plan, final_c, final_trace, counters, round_incomplete) = match reclaim {
            LeafReclaimResult::Complete { plan, c, trace, counters } => {
                (plan, c, trace, counters, false)
            }
            LeafReclaimResult::Incomplete { plan, c, trace, counters, .. } => {
                (plan, c, trace, counters, true)
            }
        };
        // OR incompleteness across ALL rounds, independent of best-round selection.
        saw_incomplete_round |= round_incomplete;
        let cert = certify(&final_c, &final_trace);
        let result = RoundResult {
            plan: final_plan.clone(),
            pins: pinned.iter().copied().collect(),
            // An `Incomplete` round is INELIGIBLE to ship (spec §3): mark it infeasible so
            // best-round selection skips it. (No-op in Task 2 — always `Complete`.)
            feasible: cert.is_ok() && !diverged(&final_trace) && !round_incomplete,
            traffic: final_c.stats_ext.global + final_c.stats_ext.fold_traffic,
            instrs: final_c.stats.program_lanes,
            reclaim_attempted: counters.residual_gap_attempted,
            reclaim_kept: counters.residual_gap_kept,
            compound_attempted: c_attempted,
            compound_kept: c_kept,
            counters,
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
                counters: result.counters.clone(),
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
        // Counters from the RETURNED (best) round; `saw_incomplete_round` OR-ed across
        // ALL rounds (spec §3/Finding-4); `leaf_calls` from the shared budget.
        counters: best.counters,
        saw_incomplete_round,
        leaf_calls: trial_budget.leaf_calls,
        base_compound_calls,
        sum_g,
        sum_quota,
    })
}

/// TERM-backend compat wrapper for [`priced_rounds_with_backend`] (CS-M5a Task 6):
/// preserves the pre-Task-6 public signature, so the engine and the direct test callers
/// compile unchanged.
pub fn priced_rounds(
    d: &DistilledLayer,
    budget: usize,
    frozen0: FrozenDemand,
    multiplier: usize,
    gap_cap: usize,
    enforce_budget: bool,
) -> Result<PricedOutcome, CompileError> {
    priced_rounds_with_backend(&TermBackend, d, budget, frozen0, multiplier, gap_cap, enforce_budget)
}
