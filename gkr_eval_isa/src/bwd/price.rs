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
//! Commit 1 leaves the leaves ALL-`Bypass` (no leaf reclaim yet — the bounded
//! gap-granular reclaim is Commit 2). [`PricedOutcome::reclaim_attempted`] /
//! [`PricedOutcome::reclaim_kept`] are therefore `0` here.
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

use std::collections::{BTreeMap, BTreeSet, BinaryHeap};
use std::ops::Range;

use cs::gkr_compiler::dag_ir::{Expr, ExprId, FieldKind};

use super::compile::{compile_distilled_planned, BwdCompiledLayer};
use super::distill::{distilled_site_domain, DistilledLayer};
use super::fif::{fif_select, Gap};
use super::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use super::structure::expr_width;
use super::trace::{
    certify, freeze_demand, BwdCompileTrace, BwdEvent, BwdFingerprint, BwdServedFrom, FrozenDemand,
};
use crate::fwd::error::CompileError;

/// Default cap on the gap-granular reclaim's candidate count (Commit 2 uses it;
/// exported here so the whole knob lives in one place).
pub const RECLAIM_N: usize = 32;

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
/// `reclaim_attempted` / `reclaim_kept` expose the gap-granular reclaim so an inert
/// (all-revert) outcome is VISIBLE, not silently green (Commit 1: both `0`).
#[derive(Clone, Debug)]
pub struct PricedOutcome {
    pub plan: BwdOccurrencePlan,
    pub pins: Vec<ExprId>,
    pub rounds: usize,
    pub converged: bool,
    pub reclaim_attempted: usize,
    pub reclaim_kept: usize,
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

// ── CELF compound batch ─────────────────────────────────────────────────────────

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

/// CELF lazy-greedy over the compound candidates: a max-heap of stale upper bounds,
/// re-evaluated at the top against the current committed set with [`price_pin_with`],
/// committing while Δ > 0 and span-feasible.
fn celf(
    d: &DistilledLayer,
    frozen: &FrozenDemand,
    end: &[usize],
    leaf_pos: &BTreeMap<usize, usize>,
    width_memo: &mut [Option<FieldKind>],
) -> BTreeSet<ExprId> {
    let mut pinned: BTreeSet<ExprId> = BTreeSet::new();
    // Heap items: (Δ upper bound, candidate, epoch = pinned.len() at evaluation).
    let mut heap: BinaryHeap<(i64, ExprId, usize)> = BinaryHeap::new();
    for c in compound_candidates(d, frozen) {
        let w = width_of(d, c, width_memo);
        let b = price_pin_with(frozen, end, leaf_pos, &pinned, c, w);
        if b > 0 {
            heap.push((b, c, 0));
        }
    }
    while let Some((bound, c, epoch)) = heap.pop() {
        if bound <= 0 {
            break;
        }
        if epoch == pinned.len() {
            pinned.insert(c); // bound still valid against the current set → commit
        } else {
            let w = width_of(d, c, width_memo);
            let b = price_pin_with(frozen, end, leaf_pos, &pinned, c, w);
            if b > 0 {
                heap.push((b, c, pinned.len()));
            }
        }
    }
    pinned
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

// ── priced rounds ────────────────────────────────────────────────────────────────

/// One round's certificate-passing outcome, for the lexicographic best-round pick.
struct RoundResult {
    plan: BwdOccurrencePlan,
    pins: Vec<ExprId>,
    feasible: bool,
    traffic: usize,
    instrs: usize,
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
/// Per round: (1) CELF a compound-suppression batch; (2) compile the batch over the
/// predicted stream (a `BudgetBelowFloor` or a `Diverge` drops the round fail-closed
/// and exits with the previous best); (3) re-freeze on the ACTUAL trace; (4) merge
/// leaves — COMMIT 1: ALL-`Bypass` (the gap-granular reclaim is Commit 2) — into the
/// final plan, compile, certify; (5) build the [`PlannerSignature`] and stop on
/// structural equality with the previous round. Cap 3 rounds; on non-convergence
/// return the best certificate-passing round by the lexicographic objective.
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
    };

    let mut prev_sig: Option<PlannerSignature> = None;
    let mut converged = false;
    let mut rounds_run = 0usize;

    for _round in 0..3 {
        rounds_run += 1;
        let end = subtree_ends(&current_frozen);
        let leaf_pos = leaf_stream_positions(&current_frozen);

        // (1) CELF compound batch.
        let pinned = celf(d, &current_frozen, &end, &leaf_pos, &mut width_memo);

        // (2) compile the compound batch over the predicted (suppressed) stream.
        let compound_plan = compound_batch_plan_with(&current_frozen, &pinned, &end);
        let (cbatch_c, cbatch_trace) = match compile_distilled_planned(d, budget, &compound_plan) {
            Ok(x) => x,
            // The batch can't even place its compound chains → drop fail-closed,
            // exit with the previous best (a finding, not a crash).
            Err(CompileError::BudgetBelowFloor { .. }) => break,
            Err(e) => return Err(e),
        };
        // Prediction wrong (over-subscription / eviction reshaped the stream) → drop
        // the batch fail-closed, exit with the previous best.
        if diverged(&cbatch_trace) {
            break;
        }

        // (3) re-freeze on the ACTUAL trace (the realized suppression).
        let observed = freeze_demand(d, &cbatch_trace, &cbatch_c.program, &cbatch_c.specials);

        // (4) merge leaves. COMMIT 1: all-`Bypass` — the final plan IS the compound
        // batch (the gap-granular leaf reclaim is Commit 2).
        let final_plan = compound_plan;
        let final_c = cbatch_c;
        let final_trace = cbatch_trace;
        let cert = certify(&final_c, &final_trace);
        let result = RoundResult {
            plan: final_plan.clone(),
            pins: pinned.iter().copied().collect(),
            feasible: cert.is_ok() && !diverged(&final_trace),
            traffic: final_c.stats_ext.global + final_c.stats_ext.fold_traffic,
            instrs: final_c.stats.program_lanes,
        };
        if result.key() < best.key() {
            best = RoundResult {
                plan: result.plan.clone(),
                pins: result.pins.clone(),
                feasible: result.feasible,
                traffic: result.traffic,
                instrs: result.instrs,
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
        reclaim_attempted: 0,
        reclaim_kept: 0,
    })
}
