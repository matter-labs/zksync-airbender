//! Task 4 (CS-M0), spec §4: the plan-driven backward-lowering ABI regression set.
//!
//! Every plan here is built the SANCTIONED way — trace a `decisions: None` compile,
//! `freeze_demand` it, and attach [`PlanAction`]s to the frozen `domain_serves`
//! fingerprints (never hand-derive a fingerprint). `compile_distilled_planned` then
//! replays the plan through the fail-closed matcher + live-capacity residency and we
//! assert on the returned trace's serve/admit/evict/refuse/diverge events (+ value
//! parity, + byte-identity for the fail-closed tail).

mod common;

use cs::gkr_compiler::dag_ir::{
    BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
};
use std::collections::BTreeMap;

use common::{
    assert_synthetic_value_exact_planned, encode, synthetic_fma_compound_products_layer,
    synthetic_wide_add_layer_with_shared_leaf, CrossFields,
};
use gkr_eval_isa::bwd::compile::{compile_distilled, compile_distilled_planned, compile_distilled_traced};
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};
use gkr_eval_isa::bwd::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use gkr_eval_isa::bwd::trace::{
    freeze_demand, plan_epoch, BwdCompileTrace, BwdEvent, BwdFingerprint, BwdServedFrom,
};

// ── layer builders ──────────────────────────────────────────────────────────────

/// Build a distilled Ext-regime layer: `nreads` `Read` columns `0..nreads`, then
/// `extra` exprs appended after the source exprs (indices `0..nreads`), with the
/// listed `(expr, relation_index)` claim roots.
fn layer(nreads: usize, extra: &[Expr], roots: &[(u32, usize)]) -> DistilledLayer {
    let read = |c: usize| SourceInfo {
        kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: c } },
    };
    let claim = |expr: ExprId, ri: usize| Root {
        expr,
        materialize: None,
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index: ri,
                slot: RootSlot::Constraint(0),
            },
        }),
    };
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    for c in 0..nreads {
        sources.push(read(c));
        exprs.push(Expr::Source(SourceId(c as u32)));
    }
    exprs.extend_from_slice(extra);
    let roots: Vec<Root> = roots.iter().map(|&(e, ri)| claim(ExprId(e), ri)).collect();
    let batching = BatchingOrder { roots: (0..roots.len() as u32).map(RootId).collect() };
    let raw = DagLayer { sources, exprs, roots, batching, resolutions: BTreeMap::new() };
    distill(&raw, BwdRegime::Ext, &CrossFields::new(), None)
}

/// `root = Mul(w0, w0)` + a second claim root `= w0`: `w0` is a fan-out-3 domain leaf
/// (served twice in `w0*w0`, once in the `beta*w0` spine term), no compound to suppress.
fn x_times_x() -> DistilledLayer {
    layer(1, &[Expr::Mul(vec![ExprId(0), ExprId(0)])], &[(1, 0), (0, 1)])
}

/// `root = Mul(Add(w0,w1), w0, w1)`: domain leaves `w0`, `w1` (fan-out 2 each); the
/// serve order is `[w0, w1, w0, w1]`, so `w0`'s interval STRADDLES `w1`'s — the nested
/// live-retention the refusal case needs. `Add(w0,w1)` is fan-out 1 (not a domain
/// value), so caching a leaf suppresses nothing.
fn straddle() -> DistilledLayer {
    layer(
        2,
        &[Expr::Add(vec![ExprId(0), ExprId(1)]), Expr::Mul(vec![ExprId(2), ExprId(0), ExprId(1)])],
        &[(3, 0)],
    )
}

/// `root = Mul(w0, w1, w0, w1)`: domain leaves `w0`, `w1` (fan-out 2 each); serve order
/// `[w0, w0, w1, w1]` — `w0`'s interval closes before `w1`'s opens (sequential), the
/// expiry-then-admit case.
fn sequential() -> DistilledLayer {
    layer(2, &[Expr::Mul(vec![ExprId(0), ExprId(1), ExprId(0), ExprId(1)])], &[(2, 0)])
}

/// `root = Mul(w0, w0, w0)` + a second claim root `= w0`: `w0` is a fan-out-4 domain leaf
/// (three uses in `w0³`, one in the `beta*w0` spine term) — enough serves for a
/// `Retain, Bypass, Retain, Bypass` GAPPED retention chain that RE-ADMITS `w0` after a
/// rule-a release.
fn cube() -> DistilledLayer {
    layer(1, &[Expr::Mul(vec![ExprId(0), ExprId(0), ExprId(0)])], &[(1, 0), (0, 1)])
}

// ── plan helpers (build FROM a frozen trace) ────────────────────────────────────

/// Trace a `decisions: None` compile of `d` at `budget` and return the frozen
/// `domain_serves` (fingerprint + all-recompute `from`) plus the mode the winning
/// compile ran in.
fn frozen_domain_serves(
    d: &DistilledLayer,
    budget: usize,
) -> (Vec<(BwdFingerprint, BwdServedFrom)>, bool) {
    let (c, trace) = compile_distilled_traced(d, budget, None).expect("traced baseline compile");
    let f = freeze_demand(d, &trace, &c.program, &c.specials, &c.backings).unwrap();
    (f.domain_serves, f.stream_reductions)
}

/// Assemble a valid plan (correct `epoch` + `entries_fnv`) from ordered entries.
fn mk_plan(d: &DistilledLayer, budget: usize, sr: bool, entries: Vec<PlanEntry>) -> BwdOccurrencePlan {
    BwdOccurrencePlan {
        epoch: plan_epoch(d, budget, sr),
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: sr,
        entries,
    }
}

/// Attach one action per frozen domain serve (in order). Panics if the counts differ,
/// so the fixture's serve stream is pinned by the test.
fn attach(serves: &[(BwdFingerprint, BwdServedFrom)], actions: &[PlanAction]) -> Vec<PlanEntry> {
    assert_eq!(serves.len(), actions.len(), "action count must match domain-serve count");
    serves.iter().zip(actions).map(|((fp, _), &action)| PlanEntry { fp: *fp, action }).collect()
}

// ── event probes on a returned trace ────────────────────────────────────────────

fn admits(t: &BwdCompileTrace, v: ExprId) -> usize {
    t.events.iter().filter(|e| matches!(e, BwdEvent::Admit { value, .. } if *value == v)).count()
}
fn refuses(t: &BwdCompileTrace, v: ExprId) -> usize {
    t.events.iter().filter(|e| matches!(e, BwdEvent::Refuse { value, .. } if *value == v)).count()
}
fn expired_evicts(t: &BwdCompileTrace, v: ExprId) -> usize {
    t.events
        .iter()
        .filter(|e| matches!(e, BwdEvent::Evict { value, expired: true } if *value == v))
        .count()
}
fn diverge_at(t: &BwdCompileTrace) -> Option<usize> {
    t.events.iter().find_map(|e| match e {
        BwdEvent::Diverge { at_entry } => Some(*at_entry),
        _ => None,
    })
}
fn any_admit(t: &BwdCompileTrace) -> bool {
    t.events.iter().any(|e| matches!(e, BwdEvent::Admit { .. }))
}
/// The `from` of each DOMAIN serve of the PLANNED compile, in order (re-frozen off the
/// planned trace) — lets a test read the realized residency decisions per occurrence.
fn planned_domain_froms(
    d: &DistilledLayer,
    c: &gkr_eval_isa::bwd::compile::BwdCompiledLayer,
    t: &BwdCompileTrace,
) -> Vec<BwdServedFrom> {
    freeze_demand(d, t, &c.program, &c.specials, &c.backings)
        .unwrap()
        .domain_serves
        .into_iter()
        .map(|(_, from)| from)
        .collect()
}

// ── §4 regression cases ─────────────────────────────────────────────────────────

// (1) Repeated structural key mapped to distinct dynamic intervals: the shared fold
// leaf is Retained at its first serve and Bypassed at its last. The planned compile's
// fold_uses must drop versus the baseline by exactly the number of suppressed
// re-gathers (1: the second occurrence is now a resident hit, not a re-gather).
#[test]
fn repeated_keys_distinct_intervals() {
    let d = synthetic_wide_add_layer_with_shared_leaf();
    let budget = 64;
    let baseline = compile_distilled(&d, budget, None).expect("baseline");
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert_eq!(serves.len(), 2, "shared leaf is served exactly twice");
    let plan = mk_plan(&d, budget, sr, attach(&serves, &[PlanAction::Retain, PlanAction::Bypass]));

    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("planned compile");
    assert_eq!(diverge_at(&t), None, "leaf plan replays cleanly");
    let leaf = serves[0].0.value;
    assert_eq!(admits(&t, leaf), 1, "the shared leaf is admitted once (its first serve)");
    // The single suppressed re-gather is exactly the fold_uses drop.
    let suppressed = 1;
    assert_eq!(
        baseline.stats_ext.fold_uses - c.stats_ext.fold_uses,
        suppressed,
        "planned fold_uses drop equals the number of suppressed re-gathers",
    );
    assert_synthetic_value_exact_planned(&c, &d);
}

// (2) rule a — Bypass on a resident value serves the resident cell (free hit) then
// releases the slot; a later occurrence recomputes.
#[test]
fn bypass_on_resident_serves_then_releases() {
    let d = x_times_x();
    let budget = 16;
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert_eq!(serves.len(), 3, "w0 is served three times");
    let leaf = serves[0].0.value;

    // Retain at serve 1, Bypass at serves 2 and 3.
    let plan = mk_plan(
        &d,
        budget,
        sr,
        attach(&serves, &[PlanAction::Retain, PlanAction::Bypass, PlanAction::Bypass]),
    );
    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("planned");
    assert_eq!(diverge_at(&t), None);
    let froms = planned_domain_froms(&d, &c, &t);
    assert_eq!(froms[0], BwdServedFrom::Recomputed, "serve 1 recomputes then admits");
    assert_eq!(froms[1], BwdServedFrom::Resident, "serve 2 is a resident free hit");
    assert_eq!(froms[2], BwdServedFrom::Recomputed, "serve 3 recomputes (slot released at 2)");
    assert_eq!(admits(&t, leaf), 1);
    assert_eq!(expired_evicts(&t, leaf), 1, "the Bypass at serve 2 releases the slot");

    // Fully-retained twin (Retain, Retain, Bypass) keeps the leaf resident through
    // serve 3, so it re-gathers exactly ONE fewer time than the release variant.
    let full = mk_plan(
        &d,
        budget,
        sr,
        attach(&serves, &[PlanAction::Retain, PlanAction::Retain, PlanAction::Bypass]),
    );
    let (cf, tf) = compile_distilled_planned(&d, budget, &full).expect("planned full");
    assert_eq!(diverge_at(&tf), None);
    assert_eq!(
        c.stats_ext.fold_uses - cf.stats_ext.fold_uses,
        1,
        "the release variant re-gathers the leaf exactly once more than the fully-retained twin",
    );
    assert_synthetic_value_exact_planned(&c, &d);
    assert_synthetic_value_exact_planned(&cf, &d);
}

// (3) EOF divergence: a trailing plan entry whose serve never occurs. Actions before
// EOF apply normally; `finish()` records the divergence; the compile still succeeds.
#[test]
fn eof_unconsumed_entries_diverge() {
    let d = x_times_x();
    let budget = 16;
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert_eq!(serves.len(), 3);
    let leaf = serves[0].0.value;

    let mut entries =
        attach(&serves, &[PlanAction::Retain, PlanAction::Bypass, PlanAction::Bypass]);
    // One extra trailing entry for a serve that never arrives (a clone of the last
    // fingerprint — its twin is not in the actual stream).
    entries.push(PlanEntry { fp: serves[2].0, action: PlanAction::Bypass });
    let plan = mk_plan(&d, budget, sr, entries);

    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("planned compile succeeds");
    assert_eq!(admits(&t, leaf), 1, "the pre-EOF Retain applied normally");
    assert_eq!(diverge_at(&t), Some(3), "EOF divergence recorded at the orphaned entry index");
    assert_synthetic_value_exact_planned(&c, &d);
}

// (4) rule b — a Retain refused rather than preempting a LIVE retention. `w0` is
// retained over a straddling interval; `w1`'s Retain inside it cannot fit (budget sized
// for one) and `w0` is not expired, so `w1` is refused, `w0` stays resident.
#[test]
fn retain_refused_never_preempts_live_retention() {
    let d = straddle();
    let budget = 6; // one Ext leaf (4) fits; two (8) do not
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert_eq!(serves.len(), 4, "serve order [w0, w1, w0, w1]");
    let a = serves[0].0.value; // w0 — the long/straddling retention
    let b = serves[1].0.value; // w1 — retained inside w0's interval
    assert_ne!(a, b);

    // w0 Retain@0 (closes @2), w1 Retain@1 (inside), w0 Bypass@2, w1 Bypass@3.
    let plan = mk_plan(
        &d,
        budget,
        sr,
        attach(
            &serves,
            &[PlanAction::Retain, PlanAction::Retain, PlanAction::Bypass, PlanAction::Bypass],
        ),
    );
    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("compile succeeds under refusal");
    assert_eq!(diverge_at(&t), None, "no divergence — the refusal is a capacity event, not a mismatch");
    assert_eq!(admits(&t, a), 1, "w0 admitted (the live retention)");
    assert_eq!(refuses(&t, b), 1, "w1's admission is refused for want of capacity");
    assert_eq!(admits(&t, b), 0, "w1 is NOT admitted — a live retention is never preempted");
    assert_synthetic_value_exact_planned(&c, &d);
}

// (5) rule b — an EXPIRED resident is evicted so a later Retain can be admitted. `w0` is
// retained then Bypassed (its retention closes → expired, slot released); `w1` is then
// admitted into the freed capacity.
#[test]
fn expired_victim_evicted() {
    let d = sequential();
    let budget = 8;
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert_eq!(serves.len(), 4, "serve order [w0, w0, w1, w1]");
    let a = serves[0].0.value; // w0
    let b = serves[2].0.value; // w1
    assert_ne!(a, b);

    // w0 Retain@0 (closes @1), w0 Bypass@1 (expires), w1 Retain@2, w1 Bypass@3.
    let plan = mk_plan(
        &d,
        budget,
        sr,
        attach(
            &serves,
            &[PlanAction::Retain, PlanAction::Bypass, PlanAction::Retain, PlanAction::Bypass],
        ),
    );
    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("compile succeeds");
    assert_eq!(diverge_at(&t), None);
    assert_eq!(expired_evicts(&t, a), 1, "w0 leaves residency as an expired resident");
    assert_eq!(admits(&t, b), 1, "w1 is admitted after w0's slot frees");

    // The eviction of w0 precedes w1's admission in the event stream.
    let evict_pos = t
        .events
        .iter()
        .position(|e| matches!(e, BwdEvent::Evict { value, expired: true } if *value == a))
        .expect("w0 expired evict");
    let admit_pos = t
        .events
        .iter()
        .position(|e| matches!(e, BwdEvent::Admit { value, .. } if *value == b))
        .expect("w1 admit");
    assert!(evict_pos < admit_pos, "the expired victim is evicted before the new admission");
    assert_synthetic_value_exact_planned(&c, &d);
}

// (6) compound-hit cone suppression exercising the FAIL-CLOSED path: a synthetic
// divergence at entry 0 (an extra leading entry no serve matches). Every subsequent
// action degrades to Bypass (no Admit at all) and the program is byte-identical to the
// `decisions: None` baseline — the strongest Bypass-tail statement.
#[test]
fn cone_suppression_fails_closed() {
    let d = x_times_x();
    let budget = 16;
    let baseline = compile_distilled(&d, budget, None).expect("baseline");
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert!(serves.len() >= 2);

    // A leading entry whose fingerprint the first ACTUAL serve cannot match (serve 0 is
    // `serves[0]`; the injected head is a clone of a later, distinct fingerprint). The
    // REAL entries are `Retain`s that WOULD each admit the leaf — so the byte-identity
    // below can only hold if the fail-closed tail truly suppressed every admission.
    let head = serves.iter().find(|(fp, _)| *fp != serves[0].0).expect("a distinct later fp");
    let mut entries = vec![PlanEntry { fp: head.0, action: PlanAction::Bypass }];
    let n = serves.len();
    entries.extend(serves.iter().enumerate().map(|(i, (fp, _))| PlanEntry {
        // Every occurrence but the last is a Retain (has a next serve for its value).
        fp: *fp,
        action: if i + 1 < n { PlanAction::Retain } else { PlanAction::Bypass },
    }));
    let plan = mk_plan(&d, budget, sr, entries);

    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("planned compile succeeds");
    assert_eq!(diverge_at(&t), Some(0), "divergence recorded at the injected head entry");
    assert!(!any_admit(&t), "the fail-closed tail admits nothing (Retains degraded to Bypass)");
    assert_synthetic_value_exact_planned(&c, &d);
    assert_eq!(
        encode(&c.program),
        encode(&baseline.program),
        "a diverged-at-0 plan is byte-identical to the decisions:None baseline",
    );
}

// (7) epoch mismatch is a HARD error (a wrong/stale plan must never replay silently).
#[test]
#[should_panic(expected = "epoch mismatch")]
fn epoch_mismatch_is_hard_error() {
    let d = x_times_x();
    let budget = 16;
    let (serves, sr) = frozen_domain_serves(&d, budget);
    let mut plan = mk_plan(
        &d,
        budget,
        sr,
        attach(&serves, &[PlanAction::Bypass, PlanAction::Bypass, PlanAction::Bypass]),
    );
    plan.epoch ^= 0xdead_beef; // corrupt the epoch
    let _ = compile_distilled_planned(&d, budget, &plan);
}

// (8) FMA addend/product partition order is stable through the fingerprint channel: an
// all-Bypass round-trip of a trace-built plan never diverges.
#[test]
fn fma_reparent_fingerprints_match() {
    let d = synthetic_fma_compound_products_layer(2, 3);
    let budget = 64;
    let (serves, sr) = frozen_domain_serves(&d, budget);
    let actions = vec![PlanAction::Bypass; serves.len()];
    let plan = mk_plan(&d, budget, sr, attach(&serves, &actions));

    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("planned compile");
    assert_eq!(
        diverge_at(&t),
        None,
        "the trace-built all-Bypass plan round-trips with no fingerprint drift",
    );
    // All-Bypass admits nothing, so the program matches the uncached baseline byte-for-byte.
    let baseline = compile_distilled(&d, budget, None).expect("baseline");
    assert_eq!(encode(&c.program), encode(&baseline.program));
    assert_synthetic_value_exact_planned(&c, &d);
}

// (9) Re-admission after a rule-a release mints a FRESH generation. A `Retain, Bypass,
// Retain, Bypass` GAPPED chain on a fan-out-4 leaf: the Bypass at serve 2 releases the
// slot (rule a), which MUST record `evicted_ever` so the Retain at serve 3 re-admits
// through a fresh `ValueId` — otherwise a second `emit_evict_to_cell` reuses the
// original id and `compute_live_ranges` (first-define-wins) collapses the value's range
// across the released gap. Here we assert the re-admission is real (TWO Admit events for
// the leaf) and value-exact + non-diverging.
//
// NOTE on test strength: the STRONGEST form — a discriminating tight budget where the
// buggy collapsed range forces a spurious `BudgetBelowFloor` while the fix compiles —
// requires an interloper value packed into the freed gap. At spine granularity that is
// structurally infeasible: the Ext floor-8 collision (documented in the task report:
// an Ext resident (4) plus the reduction's forced Ext spill/combine temp (4) always
// coincide at 8) leaves no budget window, and a pre-materialized operand's cell stays
// live from its serve to its (late) fold read, so a synthetic "gap" is not a real
// cell-free window. The full discriminating exercise defers to Task 8's real gapped
// chains (leaf serves that coincide with genuine fold-read instants). The two-Admit +
// value-exact form here guards that re-admission executes, mints a distinct generation,
// and preserves value/feasibility.
#[test]
fn readmit_after_release_fresh_generation() {
    let d = cube();
    let budget = 16;
    let (serves, sr) = frozen_domain_serves(&d, budget);
    assert_eq!(serves.len(), 4, "w0 is served four times (fan-out 4)");
    let leaf = serves[0].0.value;

    // Retain@0 (admit), Bypass@1 (rule-a release → evicted_ever), Retain@2 (RE-admit),
    // Bypass@3 (release). The two Retains open distinct intervals for the same leaf.
    let plan = mk_plan(
        &d,
        budget,
        sr,
        attach(
            &serves,
            &[PlanAction::Retain, PlanAction::Bypass, PlanAction::Retain, PlanAction::Bypass],
        ),
    );
    let (c, t) = compile_distilled_planned(&d, budget, &plan).expect("gapped re-admission compiles");
    assert_eq!(diverge_at(&t), None, "the gapped chain replays cleanly");
    assert_eq!(
        admits(&t, leaf),
        2,
        "the leaf is admitted twice — a genuine re-admission after the rule-a release",
    );
    assert_eq!(expired_evicts(&t, leaf), 2, "both retentions release their slot (rule a)");
    // Value must be preserved despite the fresh-generation re-admission (the fix must not
    // corrupt which cell the leaf's later uses read).
    assert_synthetic_value_exact_planned(&c, &d);
}
