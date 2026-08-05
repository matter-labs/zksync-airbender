mod common;
use std::collections::{BTreeMap, BTreeSet};

use common::*;
use gkr_eval_ir::{DagLayer, ExprId, claim_roots};
use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::compile::{
    compile_distilled, compile_distilled_at_planned_lb, compile_distilled_fragments_planned,
    compile_distilled_planned, compile_distilled_traced,
};
use gkr_eval_isa::bwd::construct::construct_unit_order;
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill, stable_distilled_site_domain};
use gkr_eval_isa::bwd::engine::{CsOutcome, cs_schedule_bwd_layer, cs_schedule_bwd_layer_research};
use gkr_eval_isa::bwd::fif::{Gap, feasible_leaf_plan, fif_select, oracle_saved, plan_leaves};
use gkr_eval_isa::bwd::plan::{BwdOccurrencePlan, PlanAction, PlanEntry, plan_entries_fnv};
use gkr_eval_isa::bwd::price::{
    RECLAIM_N, compound_batch_plan, compound_candidates, modeled_traffic_full, planner_signature,
    price_pin, priced_rounds, suppression_ranges, value_width,
};
use gkr_eval_isa::bwd::trace::{
    BwdEvent, BwdServeKind, BwdServedFrom, FrozenDemand, certify, freeze_demand, live_profile,
};

/// Tracing is observation only: program byte-identical to the untraced compile.
#[test]
fn traced_compile_is_byte_identical() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let base = compile_distilled(&d, 16, None).unwrap();
        let (traced, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        assert_eq!(encode(&base.program), encode(&traced.program), "L{li}");
        assert_eq!(trace.budget, 16);
        assert_eq!(trace.free.len(), traced.program.instrs.len(), "L{li}");
        assert!(
            trace
                .events
                .iter()
                .any(|e| matches!(e, BwdEvent::Serve { .. })),
            "L{li}"
        );
    }
}

/// TrafficRead events recount to EXACTLY the tally's traffic (certificate seed).
#[test]
fn trace_traffic_reads_match_tally() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let counted: usize = trace
            .events
            .iter()
            .filter_map(|e| match e {
                BwdEvent::TrafficRead { cells, .. } => Some(*cells as usize),
                _ => None,
            })
            .sum();
        assert_eq!(
            counted,
            c.stats_ext.global + c.stats_ext.fold_traffic,
            "L{li}"
        );
    }
}

/// Serve fingerprints walk the spine terms in order (term index nondecreasing 0..n).
#[test]
fn trace_terms_are_monotone() {
    for (_li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (_c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let mut last = 0u32;
        for e in &trace.events {
            if let BwdEvent::Serve { fp, .. } = e {
                assert!(fp.term >= last, "term regressed {} -> {}", last, fp.term);
                last = fp.term;
            }
        }
    }
}

/// Leaf demand instants (DOMAIN leaves only): k-th physical read in the program
/// == k-th Recomputed serve of that leaf in the trace (per-leaf counts must agree
/// exactly). Non-domain reads are accounted in nondomain_gather_cells instead.
#[test]
fn frozen_leaf_instants_align_with_serves() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let frozen = freeze_demand(
            &d,
            &trace,
            &c.program,
            &c.specials,
            &c.backings,
            &c.source_windows,
        )
        .unwrap();
        assert_eq!(frozen.epoch, trace.epoch);
        for (v, instants) in &frozen.leaf_instants {
            let serves = frozen
                .domain_serves
                .iter()
                .filter(|(fp, from)| fp.value == *v && matches!(from, BwdServedFrom::Recomputed))
                .count();
            assert_eq!(instants.len(), serves, "L{li} leaf {v:?}");
        }
        assert!(frozen.free.iter().all(|&f| f <= 16), "L{li}");
    }
}

// ── Task 5 (CS-M0): FiF leaf planner (`plan_leaves`) ──────────────────────────

fn lcg(state: &mut u64, m: u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    (*state >> 33) % m
}

/// (a) Port of `bwd_batching_headroom.rs`'s `fc0_fif_solver_matches_oracle` gate against
/// the SRC `fif_select`/`oracle_saved` (same LCG-seeded fuzz, <=12 gaps, exhaustive oracle)
/// — Task 5's own copy of the exactness gate every downstream FiF number depends on.
#[test]
fn fif_fuzz_matches_oracle() {
    let mut st = 0x243F_6A88_85A3_08D3u64; // deterministic — wall-clock seeding is banned
    for case in 0..300 {
        let n = 10 + lcg(&mut st, 50) as usize;
        let n_origins = 2 + lcg(&mut st, 6) as usize;
        let mut gaps: Vec<Gap> = Vec::new();
        for o in 0..n_origins {
            let uses = 2 + lcg(&mut st, 4) as usize;
            let mut pos: Vec<usize> = (0..uses).map(|_| lcg(&mut st, n as u64) as usize).collect();
            // Duplicates are DELIBERATELY kept and injected: a repeated position is a
            // same-instruction double use (x*x) -> a zero-length gap.
            if lcg(&mut st, 3) == 0 {
                let dup = pos[lcg(&mut st, pos.len() as u64) as usize];
                pos.push(dup);
            }
            pos.sort_unstable();
            for w in pos.windows(2) {
                gaps.push(Gap {
                    origin: ExprId(o as u32),
                    start: w[0],
                    end: w[1],
                });
            }
        }
        gaps.truncate(12); // oracle is 2^|gaps|
        let free: Vec<usize> = (0..n).map(|_| 4 * lcg(&mut st, 4) as usize).collect();
        assert_eq!(
            fif_select(&gaps, &free).len(),
            oracle_saved(&gaps, &free),
            "case {case}: gaps={gaps:?} free={free:?}"
        );
    }
}

/// (b) Synthetic shared-leaf layer (fan-out 2, one gap in the whole layer) at a headroom
/// budget (b16, well above the streamed K=1 peak): `plan_leaves` must retain the shared
/// leaf across its one gap, so the planned compile's `fold_uses` strictly beats the
/// all-recompute baseline's — and the value stays exact under the plan.
#[test]
fn leaf_plan_beats_baseline_on_shared_leaf() {
    const BUDGET: usize = 16;
    let d = synthetic_wide_add_layer_with_shared_leaf();

    let (baseline_c, baseline_trace) =
        compile_distilled_traced(&d, BUDGET, None).expect("baseline traced compile @ b16");
    let frozen = freeze_demand(
        &d,
        &baseline_trace,
        &baseline_c.program,
        &baseline_c.specials,
        &baseline_c.backings,
        &baseline_c.source_windows,
    )
    .unwrap();
    let plan = plan_leaves(&frozen);

    let (planned_c, _planned_trace) =
        compile_distilled_planned(&d, BUDGET, &plan).expect("planned compile @ b16");

    assert!(
        planned_c.stats_ext.fold_uses < baseline_c.stats_ext.fold_uses,
        "planned fold_uses {} !< baseline fold_uses {}",
        planned_c.stats_ext.fold_uses,
        baseline_c.stats_ext.fold_uses
    );
    assert_synthetic_value_exact_planned(&planned_c, &d);
}

/// (b2) Coverage of the WRAPPER's retaining (non-degenerate) return path. Test (b) proves
/// the pricer (`plan_leaves`) retains, but drives it directly; this drives
/// `feasible_leaf_plan` end-to-end on a headroom fixture whose single fan-out-2 leaf gap
/// survives the coordinate-correct-freeze + discount (its working-set peak is small), so
/// the wrapper's `kept_gaps > 0` path — the amendment's core deliverable, reused by Task 8
/// — actually executes. If it degrades to all-`Bypass` here that is a real wrapper finding
/// (the coordinate-correct freeze + discount would then be strictly stricter than the
/// direct pricer, retaining nothing anywhere); reported honestly, not weakened.
#[test]
fn feasible_leaf_plan_retains_with_headroom() {
    const BUDGET: usize = 16;
    let d = synthetic_wide_add_layer_with_shared_leaf();

    let (plan, planned_c, planned_trace) =
        feasible_leaf_plan(&d, BUDGET).expect("feasible_leaf_plan must return Ok");
    let kept_gaps = plan
        .entries
        .iter()
        .filter(|e| e.action == PlanAction::Retain)
        .count();

    assert!(
        kept_gaps > 0,
        "wrapper degraded to all-Bypass on a headroom fixture (kept_gaps == 0) — the \
         coordinate-correct freeze + discount retained nothing; report as a finding"
    );

    let diverge = planned_trace
        .events
        .iter()
        .find(|e| matches!(e, BwdEvent::Diverge { .. }));
    assert!(diverge.is_none(), "returned compile diverged: {diverge:?}");
    let refusals = planned_trace
        .events
        .iter()
        .filter(|e| matches!(e, BwdEvent::Refuse { .. }))
        .count();
    assert_eq!(refusals, 0, "returned compile had {refusals} Refuse events");

    assert_synthetic_value_exact_planned(&planned_c, &d);

    // Retention actually saved traffic THROUGH the wrapper vs the coordinate-correct
    // all-Bypass baseline (the same regime `feasible_leaf_plan` prices in).
    let baseline_c = coordinate_correct_baseline(&d, BUDGET);
    assert!(
        planned_c.stats_ext.fold_uses < baseline_c.stats_ext.fold_uses,
        "wrapper fold_uses {} !< coord-correct baseline fold_uses {} (kept_gaps={kept_gaps})",
        planned_c.stats_ext.fold_uses,
        baseline_c.stats_ext.fold_uses
    );
    eprintln!(
        "feasible_leaf_plan_retains_with_headroom: kept_gaps={kept_gaps} baseline_fold={} planned_fold={}",
        baseline_c.stats_ext.fold_uses, planned_c.stats_ext.fold_uses
    );
}

/// (c) THE alignment + feasibility gate for the whole seam (feasibility now PRECEDES
/// divergence — the point of the hybrid seed): `feasible_leaf_plan` on `add_sub` L0 @ b16
/// must return `Ok`, and its returned compile must have NO `Diverge` event and ZERO
/// `Refuse` events. (Single-shot static pricing is infeasible here; the discount-seed +
/// drop-to-fit wrapper is what makes a clean replay reachable at all.)
#[test]
fn feasible_leaf_plan_never_diverges() {
    let (layer, cross) = load_layer("add_sub_lui_auipc_mop_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);

    let (_plan, _c, trace) =
        feasible_leaf_plan(&d, 16).expect("feasible_leaf_plan must always return Ok");
    let diverge = trace
        .events
        .iter()
        .find(|e| matches!(e, BwdEvent::Diverge { .. }));
    assert!(diverge.is_none(), "returned compile diverged: {diverge:?}");
    let refusals = trace
        .events
        .iter()
        .filter(|e| matches!(e, BwdEvent::Refuse { .. }))
        .count();
    assert_eq!(refusals, 0, "returned compile had {refusals} Refuse events");
}

/// (d) THE model->compiler fidelity gate (FB3 risk this milestone exists to surface):
/// bigint + keccak Ext L0 @ b16. `feasible_leaf_plan` must return `Ok`; its compile must
/// (i) never diverge, (ii) never refuse an admission (a refusal means the plan's retains
/// weren't all realized — the predicted == realized identity would break), and (iii)
/// realize the prediction EXACTLY ON THE RETURNED (converged) plan: every `Retain` in the
/// returned plan saves exactly one fold-source gather (4 Ext cells) — no more, no less.
/// A certificate alone cannot catch a plan whose retains were all refused (it only
/// recounts realized traffic); this pins predicted == realized on the heavy circuits.
///
/// The baseline is the COORDINATE-CORRECT zero-retention compile (the all-`Bypass` planned
/// compile at `lower==place==budget`, the same regime `feasible_leaf_plan` prices in), so
/// the `fold_uses` delta is apples-to-apples. Per the brief: `kept_gaps == 0` on a fixture
/// (drop-to-fit stripped everything to all-`Bypass`) makes the equality trivially true but
/// means leaf retention captured nothing at b16 — reported (not weakened) in the Task-5
/// report, per RR's instruction.
#[test]
fn feasible_leaf_plan_fidelity_heavy() {
    const HEAVY: &[&str] = &[
        "bigint_with_extended_control_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
    ];
    for &name in HEAVY {
        let (layer, cross) = load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);

        let (plan, planned_c, planned_trace) = feasible_leaf_plan(&d, 16)
            .unwrap_or_else(|e| panic!("{name}: feasible_leaf_plan must return Ok, got {e:?}"));
        let kept_gaps = plan
            .entries
            .iter()
            .filter(|e| e.action == PlanAction::Retain)
            .count();

        let diverge = planned_trace
            .events
            .iter()
            .find(|e| matches!(e, BwdEvent::Diverge { .. }));
        assert!(
            diverge.is_none(),
            "{name}: returned compile diverged: {diverge:?}"
        );
        let refusals = planned_trace
            .events
            .iter()
            .filter(|e| matches!(e, BwdEvent::Refuse { .. }))
            .count();
        assert_eq!(
            refusals, 0,
            "{name}: {refusals} Refuse events (model/compiler mismatch)"
        );

        // Coordinate-correct baseline: the all-Bypass planned compile at lower==place==b16.
        let baseline_c = coordinate_correct_baseline(&d, 16);
        let baseline_fold = baseline_c.stats_ext.fold_uses;
        let planned_fold = planned_c.stats_ext.fold_uses;
        assert_eq!(
            baseline_fold - planned_fold,
            kept_gaps,
            "{name}: fold_uses delta {} != kept_gaps {kept_gaps} (baseline {baseline_fold}, planned {planned_fold})",
            baseline_fold - planned_fold,
        );

        let baseline_traffic = baseline_c.stats_ext.global + baseline_c.stats_ext.fold_traffic;
        let planned_traffic = planned_c.stats_ext.global + planned_c.stats_ext.fold_traffic;
        assert_eq!(
            baseline_traffic - planned_traffic,
            4 * kept_gaps,
            "{name}: traffic delta {} != 4*kept_gaps {} (baseline {baseline_traffic}, planned {planned_traffic})",
            baseline_traffic - planned_traffic,
            4 * kept_gaps,
        );
        eprintln!(
            "{name}: kept_gaps={kept_gaps} baseline_fold={baseline_fold} planned_fold={planned_fold} traffic {baseline_traffic}->{planned_traffic}"
        );
    }
}

/// The coordinate-correct zero-retention baseline compile: an all-`Bypass` plan (built
/// from a `decisions:None` trace's budget-independent domain-serve fingerprints) replayed
/// at `lower==place==budget` — the SAME regime `feasible_leaf_plan` prices in, so its
/// `fold_uses` is apples-to-apples with the returned planned compile.
fn coordinate_correct_baseline(
    d: &gkr_eval_isa::bwd::distill::DistilledLayer,
    budget: usize,
) -> gkr_eval_isa::bwd::compile::BwdCompiledLayer {
    use gkr_eval_isa::bwd::plan::{BwdOccurrencePlan, PlanEntry, plan_entries_fnv};
    let (ft_c, ft_trace) = compile_distilled_traced(d, budget, None).expect("baseline traced");
    let frozen = freeze_demand(
        d,
        &ft_trace,
        &ft_c.program,
        &ft_c.specials,
        &ft_c.backings,
        &ft_c.source_windows,
    )
    .unwrap();
    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .map(|&(fp, _from)| PlanEntry {
            fp,
            action: PlanAction::Bypass,
        })
        .collect();
    let all_bypass = BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    };
    compile_distilled_planned(d, budget, &all_bypass)
        .expect("all-Bypass compile feasible")
        .0
}

// ── Task 6 (CS-M0): schedule certificate (`certify`) ──────────────────────────

/// (a) THE cross-circuit certificate gate: for all 12 `FIXTURES`, Ext L0 (skipping
/// fixtures whose L0 has no bwd roots), `certify` must return `Ok` on BOTH the
/// all-recompute baseline traced compile (`compile_distilled_traced`) and the
/// leaf-planned compile (`feasible_leaf_plan`, which always returns feasible — at
/// b16 on heavy fixtures it degrades to all-Bypass, which is fine, the
/// certificate still applies).
///
/// This also closes a Task-1 open question: Task 1's `TrafficRead` hook classifies
/// a `FoldSource` leaf as read-origin via `layer.sources[sid].kind == Read`, while
/// `stats_ext.fold_traffic` classifies by the `BwdSpecial` desc-origin. The two
/// classifications were validated equal only on `add_sub` at Task 1 — if they
/// diverge on some other circuit, `certify` returns `Err` there and this test
/// reports the per-fixture counted/reported numbers rather than weakening the
/// equality.
#[test]
fn certificate_exact_on_baseline_and_planned() {
    let mut checked = 0usize;
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if claim_roots(&layer).is_empty() {
            continue; // L0 has no backward roots for this fixture
        }
        let d = distill(&layer, BwdRegime::Ext, &cross, None);

        let (baseline_c, baseline_trace) = compile_distilled_traced(&d, 16, None)
            .unwrap_or_else(|e| panic!("{name}: baseline traced compile @ b16 failed: {e:?}"));
        let baseline_report = certify(&baseline_c, &baseline_trace);
        assert!(
            baseline_report.is_ok(),
            "{name}: baseline certify diverged: {baseline_report:?}"
        );

        let (_plan, planned_c, planned_trace) = feasible_leaf_plan(&d, 16)
            .unwrap_or_else(|e| panic!("{name}: feasible_leaf_plan must return Ok, got {e:?}"));
        let planned_report = certify(&planned_c, &planned_trace);
        assert!(
            planned_report.is_ok(),
            "{name}: planned certify diverged: {planned_report:?}"
        );

        checked += 1;
    }
    assert!(
        checked > 0,
        "no fixture's L0 had bwd roots — enumeration broke"
    );
    println!(
        "certificate_exact_on_baseline_and_planned: {checked}/{} fixtures held (Ext L0)",
        FIXTURES.len()
    );
}

/// (b) `certify` must reject a doctored trace: a bogus extra `TrafficRead` pushed
/// onto an otherwise-genuine trace inflates `counted_traffic` past `reported_traffic`
/// (the tally never moves — it is read straight off the compile), so `certify` must
/// return `Err`, and the returned report's counted/reported fields must reflect
/// exactly the injected discrepancy.
#[test]
fn certificate_rejects_doctored_trace() {
    let (layer, cross) = load_layer("add_sub_lui_auipc_mop_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    let (c, mut trace) =
        compile_distilled_traced(&d, 16, None).expect("baseline traced compile @ b16");

    // Sanity: the untouched trace certifies clean.
    assert!(certify(&c, &trace).is_ok(), "untouched trace must certify");

    let reported = c.stats_ext.global + c.stats_ext.fold_traffic;
    trace.events.push(BwdEvent::TrafficRead {
        value: ExprId(0),
        cells: 1,
    });

    let report = certify(&c, &trace);
    let err = report.expect_err("doctored trace must fail certification");
    assert_eq!(err.counted_traffic, reported + 1);
    assert_eq!(err.reported_traffic, reported);
}

// ── Task 7 (CS-M0): constructive backward unit order (`construct_unit_order`) ─

/// (b) For all 12 `FIXTURES`, Ext L0 (skipping fixtures whose L0 has no bwd
/// roots): `construct_unit_order` returns a valid permutation of
/// `0..unit_count`, and re-distilling under that permutation still compiles
/// at b16 — feasibility unchanged by reordering (the streaming fallback stays
/// intact). If some permutation ever made a fixture infeasible at b16 that
/// would be a genuine finding, reported via the panic message, not hidden.
#[test]
fn construct_order_is_permutation_all_fixtures() {
    let mut checked = 0usize;
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if claim_roots(&layer).is_empty() {
            continue; // L0 has no backward roots for this fixture
        }
        let d0 = distill(&layer, BwdRegime::Ext, &cross, None);
        let n_units = d0.unit_order.len();
        let stable_domain = stable_distilled_site_domain(&d0);

        let order = construct_unit_order(&layer, &d0, &stable_domain);

        assert_eq!(order.len(), n_units, "{name}: permutation length");
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        for &unit in &order {
            assert!(
                unit < n_units,
                "{name}: unit {unit} out of range (n_units={n_units})"
            );
            assert!(
                seen.insert(unit),
                "{name}: unit {unit} repeated in permutation"
            );
        }
        assert_eq!(
            seen.len(),
            n_units,
            "{name}: permutation must cover every unit"
        );

        let reordered = distill(&layer, BwdRegime::Ext, &cross, Some(&order));
        compile_distilled(&reordered, 16, None).unwrap_or_else(|e| {
            panic!("{name}: constructed-order compile @ b16 failed (feasibility regression): {e:?}")
        });

        checked += 1;
    }
    assert!(
        checked > 0,
        "no fixture's L0 had bwd roots — enumeration broke"
    );
    println!(
        "construct_order_is_permutation_all_fixtures: {checked}/{} fixtures held (Ext L0)",
        FIXTURES.len()
    );
}

/// (c) Determinism: two `construct_unit_order` calls over the same inputs are
/// byte-equal (no wall-clock or hashmap-iteration-order dependence).
#[test]
fn construct_order_is_deterministic() {
    let (layer, cross) = load_layer("add_sub_lui_auipc_mop_layout_gkr.json", 0);
    let d0 = distill(&layer, BwdRegime::Ext, &cross, None);
    let stable_domain = stable_distilled_site_domain(&d0);

    let a = construct_unit_order(&layer, &d0, &stable_domain);
    let b = construct_unit_order(&layer, &d0, &stable_domain);
    assert_eq!(a, b, "construct_unit_order must be deterministic");
}

// ── Task 8 (CS-M0), Commit 1: removal-set pricing + CELF priced rounds ─────────

/// The coordinate-correct `lower==place==budget` all-`Bypass` freeze (Task 5 step 1):
/// the `frozen0` Task-8 pricing and the CS engine MUST seed from (never the fill-then-
/// trim traced freeze). Now a thin wrapper over the SRC `fif::coordinate_correct_frozen`
/// (extracted in Task 9, deduped here) — called fully-qualified so it does not collide
/// with this local helper's name.
fn coordinate_correct_frozen(d: &DistilledLayer, budget: usize) -> FrozenDemand {
    gkr_eval_isa::bwd::fif::coordinate_correct_frozen(d, budget)
        .expect("coordinate-correct frozen: all-Bypass compile feasible @ budget")
}

/// (a) Removal sets over the controlled shared-compound layer: `V ⊃ W ⊃ U` with
/// hand-verifiable cone re-expansions, including the nested-pin case (V's single
/// range strictly contains a W range). Exclusive reachability: each non-producer
/// occurrence's range covers exactly that occurrence's domain descendants.
#[test]
fn suppression_ranges_exclusive_reachability() {
    let d = synthetic_shared_compound_layer();
    let frozen = coordinate_correct_frozen(&d, 16);
    let (u, w, v) = find_shared_compounds(&d);

    let covered = |ranges: &[std::ops::Range<usize>]| -> Vec<Vec<ExprId>> {
        ranges
            .iter()
            .map(|r| {
                frozen.domain_serves[r.clone()]
                    .iter()
                    .map(|(fp, _)| fp.value)
                    .collect()
            })
            .collect()
    };

    let rv = suppression_ranges(&frozen, v);
    let rw = suppression_ranges(&frozen, w);
    let ru = suppression_ranges(&frozen, u);

    // V has 2 occurrences → 1 non-producer → 1 range, covering [W, U] (pre-order).
    assert_eq!(rv.len(), 1, "V ranges: {rv:?}");
    assert_eq!(
        covered(&rv),
        vec![vec![w, u]],
        "V's non-producer cone re-expansion = [W, U]"
    );

    // W has 3 occurrences → 2 non-producer → 2 ranges, each covering exactly [U].
    assert_eq!(rw.len(), 2, "W ranges: {rw:?}");
    assert_eq!(
        covered(&rw),
        vec![vec![u], vec![u]],
        "each W cone re-expansion = [U]"
    );

    // U has no domain descendants → every cone re-expansion is empty → dropped.
    assert!(
        ru.is_empty(),
        "U ranges must be empty (no domain descendants): {ru:?}"
    );

    // Nested-pin case: V's range strictly contains one of W's ranges.
    let vr = rv[0].clone();
    assert!(
        rw.iter().any(|r| {
            vr.start <= r.start && r.end <= vr.end && (vr.start < r.start || r.end < vr.end)
        }),
        "V range {vr:?} must strictly contain a nested W range {rw:?}"
    );
}

/// (b) O1 priced-oracle gap (spec §7): on keccak Ext L0 @ b16, take the top-12
/// candidates by initial upper bound, exhaustively score all 2^12 subsets through
/// `modeled_traffic_full`, and assert the CELF-committed subset (scored via the same
/// full model) is within 1% modeled traffic of the oracle optimum. `#[ignore]` —
/// exhaustive; still runs at Task 11 (needs `RUST_MIN_STACK`, may exceed 5 min).
#[test]
#[ignore = "priced-oracle gap: exhaustive 2^12; runs at Task 11 (RUST_MIN_STACK, may exceed 5 min)"]
fn priced_oracle_gap() {
    let (layer, cross) = load_layer("keccak_special5_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    let frozen = coordinate_correct_frozen(&d, 16);

    let mut ranked: Vec<(i64, ExprId)> = compound_candidates(&d, &frozen)
        .into_iter()
        .map(|c| {
            (
                price_pin(&frozen, &BTreeSet::new(), c, value_width(&d, c)),
                c,
            )
        })
        .collect();
    ranked.sort_by(|a, b| b.0.cmp(&a.0));
    ranked.truncate(12);
    let top: Vec<ExprId> = ranked.iter().map(|&(_, c)| c).collect();
    let width = |c: ExprId| value_width(&d, c);
    let widths = |set: &BTreeSet<ExprId>| -> BTreeMap<ExprId, usize> {
        set.iter().map(|&c| (c, width(c))).collect()
    };

    // Oracle: min modeled traffic over all feasible subsets of `top`.
    let baseline = modeled_traffic_full(&frozen, &BTreeMap::new()).expect("baseline feasible");
    let mut oracle = baseline;
    for mask in 0u32..(1u32 << top.len()) {
        let pins: BTreeMap<ExprId, usize> = top
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, &c)| (c, width(c)))
            .collect();
        if let Some(t) = modeled_traffic_full(&frozen, &pins) {
            oracle = oracle.min(t);
        }
    }

    // CELF restricted to `top` (marginal greedy), scored via the SAME full model.
    let mut committed: BTreeSet<ExprId> = BTreeSet::new();
    loop {
        let best = top
            .iter()
            .filter(|c| !committed.contains(c))
            .map(|&c| (price_pin(&frozen, &committed, c, width(c)), c))
            .filter(|&(delta, _)| delta > 0)
            .max_by_key(|&(delta, _)| delta);
        match best {
            Some((_, c)) => {
                committed.insert(c);
            }
            None => break,
        }
    }
    let celf_traffic =
        modeled_traffic_full(&frozen, &widths(&committed)).expect("CELF set feasible");

    assert!(
        (celf_traffic as f64) <= oracle as f64 * 1.01,
        "CELF traffic {celf_traffic} > 1% above oracle {oracle} (baseline {baseline}, top {})",
        top.len()
    );
    eprintln!(
        "priced_oracle_gap: baseline={baseline} oracle={oracle} celf={celf_traffic} candidates={}",
        top.len()
    );
}

/// (c) Priced rounds converge or cap: add_sub + keccak Ext L0 @ b16 — `rounds <= 3`,
/// the RETURNED round's plan certifies exactly with no divergence, `priced_rounds`
/// is deterministic, and two identical rounds produce structurally-`==`
/// `PlannerSignature`s (never a hash).
#[test]
fn priced_rounds_converge_or_cap() {
    for name in [
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
    ] {
        let (layer, cross) = load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let frozen0 = coordinate_correct_frozen(&d, 16);

        let outcome = priced_rounds(&d, 16, frozen0.clone(), 1, RECLAIM_N, true)
            .unwrap_or_else(|e| panic!("{name}: priced_rounds must return Ok, got {e:?}"));
        assert!(outcome.rounds <= 3, "{name}: rounds {} > 3", outcome.rounds);
        // Commit 2: the gap-granular reclaim runs each round; kept ⊆ attempted, and at
        // b16 it may be inert (0 kept) — that is visible (printed below), not asserted
        // away.
        assert!(
            outcome.reclaim_kept <= outcome.reclaim_attempted,
            "{name}: reclaim_kept {} > reclaim_attempted {}",
            outcome.reclaim_kept,
            outcome.reclaim_attempted
        );

        // The returned round's plan certifies exactly, with no divergence.
        let (c, t) = compile_distilled_planned(&d, 16, &outcome.plan)
            .unwrap_or_else(|e| panic!("{name}: returned plan must compile, got {e:?}"));
        let report = certify(&c, &t);
        assert!(
            report.is_ok(),
            "{name}: returned plan certify diverged: {report:?}"
        );
        assert!(
            !t.events
                .iter()
                .any(|e| matches!(e, BwdEvent::Diverge { .. })),
            "{name}: returned plan diverged"
        );

        // `priced_rounds` is deterministic (no wall-clock / hashmap-order dependence).
        let outcome2 =
            priced_rounds(&d, 16, frozen0.clone(), 1, RECLAIM_N, true).expect("second run");
        assert_eq!(
            outcome.plan.entries, outcome2.plan.entries,
            "{name}: plan not deterministic"
        );
        assert_eq!(
            outcome.pins, outcome2.pins,
            "{name}: pins not deterministic"
        );

        // Two identical rounds → structurally-== signatures (independent compiles).
        let pins: BTreeSet<ExprId> = outcome.pins.iter().copied().collect();
        let (_c_a, t_a) = compile_distilled_planned(&d, 16, &outcome.plan).expect("compile a");
        let (_c_b, t_b) = compile_distilled_planned(&d, 16, &outcome.plan).expect("compile b");
        let sig_a = planner_signature(&frozen0, &t_a, &pins, &outcome.plan);
        let sig_b = planner_signature(&frozen0, &t_b, &pins, &outcome.plan);
        assert_eq!(
            sig_a, sig_b,
            "{name}: PlannerSignature must be structurally equal (never a hash)"
        );

        eprintln!(
            "priced_rounds_converge_or_cap {name}: rounds={} converged={} pins={} \
             reclaim_attempted={} reclaim_kept={} traffic={}",
            outcome.rounds,
            outcome.converged,
            outcome.pins.len(),
            outcome.reclaim_attempted,
            outcome.reclaim_kept,
            c.stats_ext.global + c.stats_ext.fold_traffic
        );
    }
}

/// (d) Compound-batch prediction == realization on the controlled layer: pin `V`,
/// build the compound-batch plan over the predicted (suppressed) stream, compile it,
/// and assert (i) NO divergence, (ii) the re-frozen domain-serve stream equals the
/// predicted stream (plan entries) EXACTLY, (iii) suppression actually deleted
/// serves. Exercises Task-4 rule-a/rule-b (V's admission + expired-resident release).
#[test]
fn compound_batch_prediction_realized() {
    let d = synthetic_shared_compound_layer();
    let frozen = coordinate_correct_frozen(&d, 16);
    let (_u, _w, v) = find_shared_compounds(&d);
    let pins: BTreeSet<ExprId> = [v].into_iter().collect();

    let plan = compound_batch_plan(&frozen, &pins);
    assert!(
        plan.entries
            .iter()
            .any(|e| e.fp.value == v && e.action == PlanAction::Retain),
        "V must be retained at its producer occurrence"
    );

    let (c, t) = compile_distilled_planned(&d, 16, &plan).expect("compound-batch compile");
    let diverge = t
        .events
        .iter()
        .find(|e| matches!(e, BwdEvent::Diverge { .. }));
    assert!(
        diverge.is_none(),
        "compound batch diverged (Task-4 machinery?): {diverge:?}"
    );

    let observed = freeze_demand(
        &d,
        &t,
        &c.program,
        &c.specials,
        &c.backings,
        &c.source_windows,
    )
    .unwrap();
    let predicted: Vec<_> = plan.entries.iter().map(|e| e.fp).collect();
    let realized: Vec<_> = observed.domain_serves.iter().map(|(fp, _)| *fp).collect();
    assert_eq!(
        predicted, realized,
        "predicted suppressed stream != observed re-frozen stream"
    );

    assert!(
        observed.domain_serves.len() < frozen.domain_serves.len(),
        "pinning V must suppress at least one cone re-expansion ({} !< {})",
        observed.domain_serves.len(),
        frozen.domain_serves.len()
    );
    eprintln!(
        "compound_batch_prediction_realized: stream {} -> {} (suppressed {})",
        frozen.domain_serves.len(),
        observed.domain_serves.len(),
        frozen.domain_serves.len() - observed.domain_serves.len()
    );
}

// ── Task 8 (CS-M0), Commit 2: bounded gap-granular reclaim (capture) ───────────

/// (e) THE reclaim CAPTURE + compiler-validation gate (superseding the retired
/// `priced_reclaim_fidelity_heavy` fidelity gate — architecture pivot, see below):
/// bigint + keccak Ext L0 @ b16. Run `priced_rounds` from the coordinate-correct
/// `frozen0` and assert only what the compiler/certificate actually guarantees about
/// the RETURNED round: it certifies exactly (no `Diverge`), its realized traffic is
/// never worse than the coordinate-correct all-`Bypass` baseline, and the greedy
/// reclaim actually ran (`reclaim_attempted > 0`).
///
/// This is NOT a fidelity gate. Per the architecture pivot (RR-directed), the offline
/// pricing model is a non-authoritative RANKING HINT; `compile + certify` is the sole
/// decision authority. Investigation showed the model cannot be made a faithful
/// predictor — chained-program residency is non-local (retaining one occurrence of a
/// heavily-shared leaf changes that leaf's global eviction trajectory elsewhere; no
/// static model predicts the cascade). The now-removed `modeled_reduction ==
/// realized_reduction` assertion was exactly that retired predictor-fidelity gate
/// (it broke on keccak: modeled 44 vs realized 88, an under-prediction of a
/// non-local cascade, not a reclaim bug). The reclaim itself stays correct and
/// load-bearing: `reclaim_leaves` (`price.rs`) only KEEPS a tentative retention when
/// a real `compile_distilled_planned` on the actual program certifies clean AND
/// strictly drops `dram_traffic` versus the current best — so whatever it captures
/// is real and compiler-validated regardless of what the hint predicted. The
/// printed capture table (pins_kept / reclaim_attempted / reclaim_kept /
/// baseline→final traffic) is the visibility Task 11's G-M0 adjudication needs — an
/// inert outcome (0 kept) must be visible, not silently green.
#[test]
fn priced_reclaim_capture_heavy() {
    const HEAVY: &[&str] = &[
        "bigint_with_extended_control_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
    ];
    println!(
        "priced_reclaim_capture_heavy capture table (b16):\n  \
         fixture | pins_kept | compound_attempted | compound_kept | \
         reclaim_attempted | reclaim_kept | baseline_traffic -> final_traffic | \
         rounds | converged"
    );
    for &name in HEAVY {
        let (layer, cross) = load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let frozen0 = coordinate_correct_frozen(&d, 16);

        // Realized baseline: the coordinate-correct all-`Bypass` compile (the same
        // program `frozen0` was frozen from) — the reduction's apples-to-apples zero.
        let baseline_c = coordinate_correct_baseline(&d, 16);
        let baseline_traffic = baseline_c.stats_ext.global + baseline_c.stats_ext.fold_traffic;

        let outcome = priced_rounds(&d, 16, frozen0.clone(), 1, RECLAIM_N, true)
            .unwrap_or_else(|e| panic!("{name}: priced_rounds must return Ok, got {e:?}"));

        // The RETURNED round's realized final traffic, re-derived from the returned
        // plan — the certificate is the correctness guarantee, not the model.
        let (final_c, final_trace) = compile_distilled_planned(&d, 16, &outcome.plan)
            .unwrap_or_else(|e| panic!("{name}: returned plan must compile, got {e:?}"));
        let report = certify(&final_c, &final_trace);
        assert!(
            report.is_ok(),
            "{name}: returned round certify diverged: {report:?}"
        );
        assert!(
            !final_trace
                .events
                .iter()
                .any(|e| matches!(e, BwdEvent::Diverge { .. })),
            "{name}: returned round diverged"
        );
        let final_traffic = final_c.stats_ext.global + final_c.stats_ext.fold_traffic;

        println!(
            "  {name} | {} | {} | {} | {} | {} | {} -> {} | {} | {}",
            outcome.pins.len(),
            outcome.compound_attempted,
            outcome.compound_kept,
            outcome.reclaim_attempted,
            outcome.reclaim_kept,
            baseline_traffic,
            final_traffic,
            outcome.rounds,
            outcome.converged,
        );

        // The reclaim only ever KEEPS a certified, strictly-traffic-dropping
        // retention (never a regression), so the returned round can never realize
        // worse traffic than the coordinate-correct all-`Bypass` baseline.
        assert!(
            final_traffic <= baseline_traffic,
            "{name}: final traffic {final_traffic} > baseline {baseline_traffic} — \
             the reclaim must never regress traffic vs all-Bypass",
        );
        // The greedy reclaim must actually have run on this fixture (visibility: an
        // inert 0-attempted round would silently defeat the point of this gate).
        assert!(
            outcome.reclaim_attempted > 0,
            "{name}: reclaim_attempted == 0 — reclaim did not run"
        );
        // Compounds must be genuinely COMPILER-tried (hint-ranked, compile+certify-validated),
        // not model-dismissed at `i64::MIN`. `compound_kept` may be 0 at b16 (compounds
        // inert — no compound span fits) and that is a correct, honest outcome; the point
        // is `compound_attempted > 0` proves the compiler, not the model, made the call.
        assert!(
            outcome.compound_attempted > 0,
            "{name}: compound_attempted == 0 — compounds were not compiler-tried",
        );
    }
}

// ── Task 9 (CS-M0): engine driver (`cs_schedule_bwd_layer`) ────────────────────

/// CS-M5a Task 10: the shipped winner's identity, for the per-fixture census line —
/// `FRAGMENT` (fragment-CS candidate won), `TERM-CS` (term candidate won), or `BASELINE`
/// (fell back to the canonical floor).
fn winner_label(outcome: &CsOutcome) -> &'static str {
    if outcome.fell_back_to_baseline {
        "BASELINE"
    } else if outcome.fragment_order.is_some() {
        "FRAGMENT"
    } else {
        "TERM-CS "
    }
}

/// CS-M5a Task 10: value-parity on the engine's SHIPPED program, RECONSTRUCTING whichever
/// candidate won. A FRAGMENT winner (`fragment_order` `Some`) is reconstructed by replaying
/// the shipped `plan` through the fragment pipeline (`compile_distilled_fragments_planned`)
/// at the stored fragment order over the canonical (`None`) distillation, then value-
/// checking THAT program — a genuine reconstruction from the persisted order, not a reuse
/// of `outcome.compiled`. A TERM-CS winner re-interns units in `unit_permutation`; a
/// BASELINE winner uses the canonical distill (the pre-Task-10 reconstruction for both).
fn assert_shipped_value_parity(layer: &DagLayer, cross: &CrossFields, outcome: &CsOutcome) {
    if let Some(order) = &outcome.fragment_order {
        let d = distill(layer, BwdRegime::Ext, cross, None);
        let plan = outcome
            .plan
            .as_ref()
            .expect("a fragment winner always carries a plan");
        let (compiled, _t) = compile_distilled_fragments_planned(&d, 16, plan, Some(order))
            .expect("fragment-winner replay must recompile cleanly");
        assert_bwd_value_parity(&compiled, &d, layer);
    } else if outcome.fell_back_to_baseline {
        let bl_d = distill(layer, BwdRegime::Ext, cross, None);
        assert_bwd_value_parity(&outcome.compiled, &bl_d, layer);
    } else {
        let d = distill(
            layer,
            BwdRegime::Ext,
            cross,
            Some(&outcome.unit_permutation),
        );
        assert_bwd_value_parity(&outcome.compiled, &d, layer);
    }
}

/// (a) THE cross-circuit engine gate + G-M0 preview: for all 12 `FIXTURES`, Ext L0
/// (skipping fixtures whose L0 has no bwd roots), `cs_schedule_bwd_layer` returns a
/// SHIPPED program that certifies exactly (no divergence), whose `(traffic, instrs)`
/// stats key is NEVER worse than the canonical `decisions:None` baseline (guaranteed by
/// the non-regression fallback), with `rounds <= 3`. Prints the per-fixture improved-vs-
/// fell-back table (baseline traffic vs CS traffic) — the Task-11 G-M0 story of which
/// fixtures CS actually helps on.
///
/// Also the value-parity spot gate on the SHIPPED program: for add_sub + keccak, the
/// engine's `outcome.compiled` must be field-bit exact against the independent oracle
/// over the RAW canonical layer, using the DISTILLED layer the engine actually shipped
/// (the constructed-order `d` when it improved, the canonical `bl_d` when it fell back).
#[test]
fn engine_runs_all_fixtures_b16() {
    const VALUE_PARITY: &[&str] = &[
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
    ];
    // CS-M4 T7 (spec §12) regression guard: the 4 G-M0-tracked fixtures' shipped CS traffic
    // must never regress above the CS-M4 banked values. These are the `gap_cap=1200`
    // (PRODUCTION_GAP_CAP) milestone results — Tier 0 (all four) + Tier 1 (blake2 8348),
    // reached by the no-regression safety-net floor; Tier 2 (GA 7996) is unreachable by the
    // whole-origin machinery even un-starved (measured). `<=` so future improvements still
    // pass; only a regression fails. Only the milestone-tracked metrics are pinned (not all
    // 12) to avoid brittleness. (Superseded the CS-M3 @512 ceilings 18764/16240/9528/3800.)
    const CS_M4_TRAFFIC_CEILINGS: &[(&str, usize)] = &[
        ("bigint_with_extended_control_layout_gkr.json", 18056),
        ("keccak_special5_layout_gkr.json", 14580),
        ("blake2_with_extended_control_layout_gkr.json", 8348),
        ("unified_reduced_machine_layout_gkr.json", 3668),
    ];
    // CS-M4 (spec §5, Phase-0b): per-fixture `HARD_MAX` = 2× the banked @1200 leaf-reclaim
    // baseline — the research emergency ceiling. Production (`multiplier=1, gap_cap=1200`)
    // stays well under it (keccak 1203, blake2 2406, bigint 1203, unified 1163); Stage
    // A/A'/B + normalize leaf-search compiles per run must never exceed it. Only the 4
    // G-M0-tracked fixtures have a banked baseline.
    // CS-M5a Task 10 (RR-adjudicated): keccak's entry is 2406 = the EXACT 2×1203 (its
    // banked term baseline). The prior 2400 was a rounded-DOWN 2× that stayed latent because
    // the term keccak search is 1203 (far under either value); the per-candidate check
    // exposed it when the fragment keccak search hit its own 2406 (== 2×1203). This is a
    // correction of the pin to match this table's own "2× baseline" definition, NOT a
    // relaxation — term keccak remains 1203.
    const LEAF_CALL_HARD_MAX: &[(&str, usize)] = &[
        ("keccak_special5_layout_gkr.json", 2406),
        ("blake2_with_extended_control_layout_gkr.json", 4800),
        ("bigint_with_extended_control_layout_gkr.json", 2400),
        ("unified_reduced_machine_layout_gkr.json", 2320),
    ];
    let mut checked = 0usize;
    let mut blake2_shipped: Option<usize> = None; // CS-M5a Task 10.3 headline
    let mut leaf_violations: Vec<String> = Vec::new(); // CS-M5a Task 10: per-candidate cap
    println!(
        "engine_runs_all_fixtures_b16 (Ext L0, b16):\n  \
         fixture | result | winner | baseline_traffic -> cs_traffic | pins | rounds | converged"
    );
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if claim_roots(&layer).is_empty() {
            continue; // L0 has no backward roots for this fixture
        }

        // Canonical baseline traffic (byte-identical program to the engine's internal
        // baseline) for the never-worse comparison + the printed delta.
        let bl_d = distill(&layer, BwdRegime::Ext, &cross, None);
        let bl_c = compile_distilled(&bl_d, 16, None)
            .unwrap_or_else(|e| panic!("{name}: canonical baseline compile @ b16 failed: {e:?}"));
        let baseline_traffic = bl_c.stats_ext.global + bl_c.stats_ext.fold_traffic;

        let outcome = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);

        // The SHIPPED program certifies exactly, with no divergence.
        assert_eq!(
            outcome.certificate.counted_traffic, outcome.certificate.reported_traffic,
            "{name}: shipped program certificate must be Ok (counted == reported)"
        );
        assert!(
            outcome.certificate.diverged.is_none(),
            "{name}: shipped program diverged"
        );

        // Never worse than the canonical baseline (fallback guarantees this), rounds capped.
        let cs_traffic = outcome.stats.global + outcome.stats.fold_traffic;
        assert!(
            cs_traffic <= baseline_traffic,
            "{name}: CS traffic {cs_traffic} > baseline {baseline_traffic} — non-regression broke"
        );
        assert!(outcome.rounds <= 3, "{name}: rounds {} > 3", outcome.rounds);

        // CS-M4 banked-value regression guard (present-fixture only; a fixture in the
        // table that never runs here is simply not checked, not silently skipped).
        if let Some(&(_, ceiling)) = CS_M4_TRAFFIC_CEILINGS
            .iter()
            .find(|&&(fixture, _)| fixture == name)
        {
            assert!(
                cs_traffic <= ceiling,
                "{name}: CS traffic {cs_traffic} > CS-M4 banked ceiling {ceiling} — regression \
                 vs the G-M0-milestone shipped value (gap_cap=1200)"
            );
        }

        // CS-M4 (spec §5) + CS-M5a Task 10 (RR resolution): the priced-search compile count
        // must stay within the banked `HARD_MAX` PER CANDIDATE — term search AND fragment
        // search each independently, since both run every call and the guardrail's meaning
        // is per-search (not per-shipped-winner). The `HARD_MAX` value is unchanged (2× the
        // banked @1200 term baseline); only the accounting scope widened to both candidates.
        // A candidate that errored out (`None`) had no completed priced run — trivially
        // within any ceiling. Violations are collected and asserted after the census prints,
        // so the full per-candidate leaf_calls table is always visible.
        if let Some(&(_, hard_max)) = LEAF_CALL_HARD_MAX
            .iter()
            .find(|&&(fixture, _)| fixture == name)
        {
            for (which, lc) in [
                ("term", outcome.term_leaf_calls),
                ("fragment", outcome.fragment_leaf_calls),
            ] {
                if let Some(lc) = lc {
                    if lc > hard_max {
                        leaf_violations.push(format!(
                            "{name}: {which} leaf_calls {lc} > HARD_MAX {hard_max}"
                        ));
                    }
                }
            }
        }

        // Value-parity spot gate on the shipped program (add_sub + keccak), reconstructing
        // whichever candidate the engine actually shipped (CS-M5a Task 10).
        if VALUE_PARITY.contains(&name) {
            assert_shipped_value_parity(&layer, &cross, &outcome);
        }

        // CS-M4 T7 (spec §12): the 4 G-M0-tracked fixtures' shipped traffic + winner.
        if name == "blake2_with_extended_control_layout_gkr.json" {
            blake2_shipped = Some(cs_traffic);
        }

        println!(
            "  {name} | {} | winner {} | {baseline_traffic} -> {cs_traffic} | pins {} | \
             leaf_calls(ship {} term {:?} frag {:?}) | swaps {}/{} | wo_kept {} | r{} | {}",
            if outcome.fell_back_to_baseline {
                "FELL_BACK"
            } else {
                "IMPROVED "
            },
            winner_label(&outcome),
            outcome.pins.len(),
            outcome.leaf_calls,
            outcome.term_leaf_calls,
            outcome.fragment_leaf_calls,
            outcome.counters.swaps_kept,
            outcome.counters.swaps_attempted,
            outcome.counters.whole_origin_kept,
            outcome.rounds,
            outcome.converged,
        );
        checked += 1;
    }
    assert!(
        leaf_violations.is_empty(),
        "per-candidate leaf-search cost bound broke: {leaf_violations:?}"
    );
    assert!(
        checked > 0,
        "no fixture's L0 had bwd roots — enumeration broke"
    );
    println!(
        "engine_runs_all_fixtures_b16: {checked}/{} fixtures held (Ext L0)",
        FIXTURES.len()
    );

    // CS-M5a Task 10.3 headline: blake2_ext shipped traffic vs the CS-M4 ceiling (8348,
    // MUST `<=` — enforced by the CS_M4_TRAFFIC_CEILINGS guard above) and the GA Tier-2
    // target (7996, SHOULD `<` — REPORTED only, never asserted).
    if let Some(t) = blake2_shipped {
        println!(
            "HEADLINE blake2_ext: shipped_traffic={t} | vs ceiling 8348 => {} (MUST) | \
             vs GA-target 7996 => {} (SHOULD, report-only)",
            if t <= 8348 { "OK <=" } else { "FAIL >" },
            if t < 7996 { "MET <" } else { "not-met >=" },
        );
    }
}

/// CS-M4 Phase-0b baseline banking (spec §5/§8): re-run the @1200 per-gap leaf
/// reclaim in COUNT-ONLY mode (`enforce_budget=false`, so the reserve rule never
/// shaves a candidate) with `gap_cap=1200` (bounds Stage-B candidates, replacing the
/// legacy `RECLAIM_N=512` truncate WITHOUT any manual constant flip) and `multiplier=1`.
/// Banks, per fixture per complete run (summed across rounds): the leaf-reclaim
/// `compile_distilled_planned` count (`leaf_calls`), the base+compound compile count
/// (`base_compound_calls`), `Σ_r G_r` (`sum_g`), and `Σ_r min(G_r,1200)` (`sum_quota`),
/// plus end-to-end wall time. The banked `leaf_calls` sets `COST_CEILING`/`HARD_MAX`
/// (§2). Asserts the generic accrual `sum_quota <= leaf_calls` — the ONLY per-fixture
/// comparison, and it lives here in the test, never in scheduler code.
///
/// NOTE: this run's TRAFFIC is the @1200 count-only traffic (14580/8348/…), NOT CS-M3's
/// 16240/9528 — Phase-0b is a MEASUREMENT (`enforce_budget=false`), not the traffic-
/// preservation gate. That gate is `engine_runs_all_fixtures_b16`, which runs the
/// PRODUCTION entry (`multiplier=1, gap_cap=1200, enforce_budget=true`); post-T7 both use
/// `gap_cap=1200`, so they now differ only in `enforce_budget` (count-only vs enforced).
#[test]
#[ignore] // heavy (~minutes); banks the Phase-0b @1200 baseline via gap_cap + count-only mode (no RECLAIM_N edit).
fn phase0b_leaf_call_baseline() {
    for name in [
        "keccak_special5_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "unified_reduced_machine_layout_gkr.json",
    ] {
        let (layer, cross) = load_layer(name, 0);
        let t0 = std::time::Instant::now();
        let out = cs_schedule_bwd_layer_research(
            &layer,
            BwdRegime::Ext,
            &cross,
            16,
            /*multiplier*/ 1,
            /*gap_cap*/ 1200,
            /*enforce_budget*/ false,
        );
        let wall = t0.elapsed();
        let cs_traffic = out.stats.global + out.stats.fold_traffic;
        eprintln!(
            "{name}: leaf_calls={} base_compound_calls={} sum_G={} sum_quota={} \
             traffic={} rounds={} wall={:.1}s",
            out.leaf_calls,
            out.base_compound_calls,
            out.sum_g,
            out.sum_quota,
            cs_traffic,
            out.rounds,
            wall.as_secs_f64(),
        );
        assert!(
            out.sum_quota <= out.leaf_calls,
            "{name}: accrual (sum_quota {}) must not exceed the banked @1200 leaf baseline \
             (leaf_calls {})",
            out.sum_quota,
            out.leaf_calls,
        );
    }
}

/// CS-M4 Task 3 (spec §4): Stage A — whole-origin accumulating greedy + post-stage
/// normalize — must LOWER traffic vs CS-M3, or at worst HOLD at the CS-M3 ceilings, on
/// the two G-M0 fixtures whose deficit is caching COVERAGE (keccak = depth, blake2 =
/// breadth). Exercised via the RESEARCH entry at `gap_cap=512` (`RECLAIM_N`), where the
/// whole-origin path is ACTIVE (keccak ships `best_AB` with `whole_origin_kept>0`).
/// PRODUCTION (`cs_schedule_bwd_layer`, T7's `gap_cap=1200`) ships the pure-per-gap
/// safety-net floor `best_B` (`whole_origin_kept=0` on all four G-M0 fixtures), so it does
/// NOT exercise this mechanism — see `engine_runs_all_fixtures_b16` for the shipped-@1200
/// gate. Asserting `whole_origin_kept>0` at the production entry would therefore assert the
/// negation of shipped behavior; the @512 research entry is where the mechanism lives.
/// This pins: (a) the shipped program certifies exactly; (b) traffic ≤ the CS-M3 ceiling
/// (keccak 16240, blake2 9528) AND ≤ the Task-2 baseline (Stage A only keeps strict-drop
/// origins, so it can never regress) — @512 CS-M4 reaches 15924/9320, both ≤ the ceilings;
/// (c) `whole_origin_kept > 0` on keccak (depth wins realized — Stage A must retain ≥1
/// whole origin). The zero-unrealized-`Retain` shipped invariant is NOT asserted here (a
/// Stage-B addition can strand an earlier retention until Task 5's TERMINAL normalize);
/// `saw_incomplete_round` stays `false` (no `Incomplete` selection until Task 5).
#[test]
#[ignore] // heavy (~minutes): full keccak + blake2 priced runs at b16 (research entry, gap_cap=512).
fn stage_a_whole_origin_lowers_or_holds() {
    for (name, m3_ceiling) in [
        ("keccak_special5_layout_gkr.json", 16240usize),
        ("blake2_with_extended_control_layout_gkr.json", 9528),
    ] {
        let (layer, cross) = load_layer(name, 0);
        // Stage A is active only at the CS-M3-reproducing `gap_cap=512`; PRODUCTION's
        // `gap_cap=1200` ships the `best_B` floor (whole_origin_kept=0). Use the RESEARCH
        // entry at `RECLAIM_N` so the whole-origin path is exercised.
        let out = cs_schedule_bwd_layer_research(
            &layer,
            BwdRegime::Ext,
            &cross,
            16,
            /*multiplier*/ 1,
            RECLAIM_N,
            /*enforce_budget*/ true,
        );
        let traffic = out.stats.global + out.stats.fold_traffic;
        assert!(
            out.certificate.counted_traffic == out.certificate.reported_traffic,
            "{name} cert"
        );
        assert!(
            traffic <= m3_ceiling,
            "{name} traffic {traffic} regressed past {m3_ceiling}"
        );
        // whole-origin activity + normalized invariant surfaced via counters:
        eprintln!(
            "{name}: traffic={traffic} whole_kept={} residual_kept={} saw_incomplete={}",
            out.counters.whole_origin_kept,
            out.counters.residual_gap_kept,
            out.saw_incomplete_round
        );
        assert!(!out.saw_incomplete_round, "{name} saw an Incomplete round");
        if name.starts_with("keccak") {
            assert!(
                out.counters.whole_origin_kept > 0,
                "Stage A must retain ≥1 whole origin on keccak (depth)"
            );
        }
    }
}

/// CS-M4 Task 4 (spec §4): Stage A' — bounded one-in/k-out swap — must NEVER regress vs
/// Stage A alone. Inserted into the A+B pipeline AFTER Stage A's post-stage normalize and
/// BEFORE Stage B, it swaps ≤`K` low-yield accepted origins out to admit a higher-yield
/// rejected origin `R`, KEEPING a swap only on a strict realized-traffic drop (else full
/// revert). Because the safety net still ships lexicographic-`min(A+B, B-only)` and every
/// swap is strict-drop-or-revert, this is a MONOTONE non-regression test: it PASSES at the
/// Task-3 (Stage-A-only) traffic both BEFORE Stage A' is added (`swaps_*` = 0, traffic ==
/// Task-3's) and AFTER (traffic can only drop). Pins: (a) shipped program certifies
/// exactly; (b) traffic ≤ the recorded Task-3 traffic (keccak 15924, blake2 9320);
/// (c) `!saw_incomplete_round` (no `Incomplete` selection until Task 5); (d) `swaps_kept
/// <= swaps_attempted` (every kept swap is a strict drop — surfaced by the monotone ≤
/// baseline). Records whether `swaps_kept > 0`.
#[test]
#[ignore] // heavy (~minutes): full production keccak + blake2 priced runs at b16.
fn stage_a_prime_swap_only_strict_drops() {
    for (name, task3_traffic) in [
        ("keccak_special5_layout_gkr.json", 15924usize),
        ("blake2_with_extended_control_layout_gkr.json", 9320),
    ] {
        let (layer, cross) = load_layer(name, 0);
        let out = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
        let traffic = out.stats.global + out.stats.fold_traffic;
        eprintln!(
            "{name}: traffic={traffic} (Task-3 {task3_traffic}) swaps_kept={}/{} leaf_calls={}",
            out.counters.swaps_kept, out.counters.swaps_attempted, out.leaf_calls
        );
        assert!(
            out.certificate.counted_traffic == out.certificate.reported_traffic,
            "{name}: shipped program certificate must be Ok (counted == reported)"
        );
        assert!(!out.saw_incomplete_round, "{name} saw an Incomplete round");
        assert!(
            out.counters.swaps_kept <= out.counters.swaps_attempted,
            "{name}: swaps_kept {} > swaps_attempted {}",
            out.counters.swaps_kept,
            out.counters.swaps_attempted
        );
        assert!(
            traffic <= task3_traffic,
            "{name}: Stage A' regressed traffic {traffic} above the Task-3 baseline {task3_traffic}"
        );
    }
}

/// (b) Determinism: two `cs_schedule_bwd_layer` runs on keccak L0 @ b16 produce
/// byte-equal outcomes — same permutation, same plan (entries + epoch + fnv), same
/// stats, same pins, same fallback verdict. No wall-clock / hashmap-iteration-order
/// dependence anywhere in the assembled pipeline.
#[test]
fn engine_deterministic() {
    let (layer, cross) = load_layer("keccak_special5_layout_gkr.json", 0);
    let a = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
    let b = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);

    assert_eq!(
        a.unit_permutation, b.unit_permutation,
        "permutation not deterministic"
    );
    assert_eq!(
        a.fell_back_to_baseline, b.fell_back_to_baseline,
        "fallback verdict not deterministic"
    );
    // CS-M5a Task 10: the winner identity + any persisted fragment order are deterministic.
    assert_eq!(
        a.fragment_order, b.fragment_order,
        "fragment_order not deterministic"
    );
    assert_eq!(a.pins, b.pins, "pins not deterministic");
    assert_eq!(a.stats, b.stats, "stats not deterministic");
    assert_eq!(a.instrs, b.instrs, "instrs not deterministic");
    assert_eq!(a.rounds, b.rounds, "rounds not deterministic");
    assert_eq!(a.converged, b.converged, "converged not deterministic");
    // `BwdOccurrencePlan` is not `PartialEq`; compare its ABI fields explicitly.
    match (&a.plan, &b.plan) {
        (Some(pa), Some(pb)) => {
            assert_eq!(pa.entries, pb.entries, "plan entries not deterministic");
            assert_eq!(pa.epoch, pb.epoch, "plan epoch not deterministic");
            assert_eq!(
                pa.entries_fnv, pb.entries_fnv,
                "plan entries_fnv not deterministic"
            );
            assert_eq!(
                pa.stream_reductions, pb.stream_reductions,
                "plan regime not deterministic"
            );
        }
        (None, None) => {}
        _ => panic!("plan Option mismatch between identical runs"),
    }
}

// ── Task 11 (CS-M0): full-corpus value-correctness gate on the shipped program ─

/// THE full-corpus value-correctness gate on the CS engine's SHIPPED program
/// (closes the CS-M0 coverage gap Task 9's spot-gate left open — that gate only
/// covered add_sub + keccak): for ALL 12 `FIXTURES`, Ext L0 (skipping fixtures
/// whose L0 has no bwd roots), reconstruct the distilled layer `d` the engine
/// actually compiled against — the constructed-order `d` when
/// `cs_schedule_bwd_layer` improved on the baseline, the canonical (unpermuted,
/// unplanned) `d` when it fell back — and assert the SHIPPED `outcome.compiled`
/// program is field-bit exact against the independent expression oracle over the
/// RAW layer (`assert_bwd_value_parity`), plus the certificate is `Ok` (counted ==
/// reported traffic) as a belt-and-suspenders.
///
/// `bwd_search_smoke` (unchanged, pre-existing) shows the GA's PERMUTED distill can
/// diverge from the oracle on bigint ("permuted distilled root value mismatch").
/// This test is the direct check of whether the CS engine's own CONSTRUCTED
/// permutation ever ships that same value-wrong program. A failure here —
/// especially on bigint — is a real CS-M0 correctness bug, not a flake to paper
/// over.
#[test]
fn engine_value_parity_all_fixtures() {
    let mut checked = 0usize;
    println!(
        "engine_value_parity_all_fixtures (Ext L0, b16):\n  fixture | fell_back | value_parity"
    );
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if claim_roots(&layer).is_empty() {
            continue; // L0 has no backward roots for this fixture
        }

        let outcome = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);

        // Reconstruct whichever candidate the engine shipped and value-check it (CS-M5a
        // Task 10): a FRAGMENT winner is rebuilt from the persisted `fragment_order` via
        // the fragment pipeline; a TERM-CS / BASELINE winner keeps the pre-Task-10
        // reconstruction. See `assert_shipped_value_parity`.
        assert_shipped_value_parity(&layer, &cross, &outcome);

        // Belt-and-suspenders: the shipped program's own certificate must be Ok.
        assert_eq!(
            outcome.certificate.counted_traffic, outcome.certificate.reported_traffic,
            "{name}: shipped program certificate must be Ok (counted == reported)"
        );

        println!(
            "  {name} | {} | winner {} | value_parity OK",
            if outcome.fell_back_to_baseline {
                "FELL_BACK"
            } else {
                "IMPROVED "
            },
            winner_label(&outcome),
        );
        checked += 1;
    }
    assert!(
        checked > 0,
        "no fixture's L0 had bwd roots — enumeration broke"
    );
    println!(
        "engine_value_parity_all_fixtures: {checked}/{} fixtures held (Ext L0)",
        FIXTURES.len()
    );
}

// ── Task 4 (CS-M3): fill-then-trim realizer for the plan-driven compile ────────

/// The STRUCTURAL-CORE gate for CS-M3 Stage 2: the plan-driven compile
/// (`compile_distilled_planned`) now fill-then-trims — lower with eviction effectively
/// disabled (`lower_budget = FILL`) so every planned `Retain` lands, then let
/// `plan_placement` at the real `budget` be the 2-D feasibility oracle, binary-searching
/// the largest `lower_budget` that place-fits. The pre-Stage-2 behavior lowered at
/// `lower == place == budget`, whose 1-D admission gate over-reserves cells vs the 2-D
/// placement oracle and starves residency at saturation (keccak, blake2).
///
/// The `baseline` arm reproduces that pre-Stage-2 behavior byte-for-byte via the now-`pub`
/// inner `compile_distilled_at_planned_lb(d, budget, budget, plan)` (the old
/// `compile_distilled_at_planned` called `compile_bwd_program` at exactly `(budget,
/// budget)`), so this single run captures the pre-refactor vs post-refactor relationship on
/// a FIXED CS plan. Asserts the DURABLE guard: both certify exactly (counted == reported),
/// the realized (winning) trace never diverges, and the fill-then-trim traffic is MONOTONE
/// `<=` the `lower == budget` baseline (`plan_placement` never spuriously overflows where the
/// baseline compiled). The observed `baseline -> realized` traffic drop is printed as the
/// structural-improvement evidence (reported, not asserted as a hardcoded constant).
#[test]
fn planned_fill_then_trim_monotone() {
    const HEAVY: &[&str] = &[
        "keccak_special5_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
    ];
    const BUDGET: usize = 16;
    for &name in HEAVY {
        let (layer, cross) = load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let frozen0 = coordinate_correct_frozen(&d, BUDGET);

        // The CS plan (same construction as `priced_rounds_converge_or_cap`).
        let outcome = priced_rounds(&d, BUDGET, frozen0, 1, RECLAIM_N, true)
            .unwrap_or_else(|e| panic!("{name}: priced_rounds must return Ok, got {e:?}"));
        let plan = &outcome.plan;
        let retains = plan
            .entries
            .iter()
            .filter(|e| e.action == PlanAction::Retain)
            .count();

        // baseline = the pre-Stage-2 `lower == place == budget` single lowering (inner).
        let (baseline_c, baseline_t) = compile_distilled_at_planned_lb(&d, BUDGET, BUDGET, plan)
            .unwrap_or_else(|e| panic!("{name}: baseline lower==budget compile failed: {e:?}"));
        // realized = the fill-then-trim wrapper (with the epoch/fnv asserts on the way in).
        let (realized_c, realized_t) = compile_distilled_planned(&d, BUDGET, plan)
            .unwrap_or_else(|e| panic!("{name}: fill-then-trim compile failed: {e:?}"));

        // (a) Both certify exactly (counted == reported).
        assert!(
            certify(&baseline_c, &baseline_t).is_ok(),
            "{name}: baseline certificate must be Ok"
        );
        assert!(
            certify(&realized_c, &realized_t).is_ok(),
            "{name}: realized certificate must be Ok"
        );

        // (b) The realized (winning) trace never diverges.
        let diverge = realized_t
            .events
            .iter()
            .find(|e| matches!(e, BwdEvent::Diverge { .. }));
        assert!(
            diverge.is_none(),
            "{name}: realized trace diverged: {diverge:?}"
        );

        // (c) Monotone: fill-then-trim is never worse than the lower==budget baseline.
        let baseline_traffic = baseline_c.stats_ext.global + baseline_c.stats_ext.fold_traffic;
        let realized_traffic = realized_c.stats_ext.global + realized_c.stats_ext.fold_traffic;
        assert!(
            realized_traffic <= baseline_traffic,
            "{name}: fill-then-trim traffic {realized_traffic} > lower==budget baseline {baseline_traffic}"
        );

        // Diagnostics: traffic can be pinned at a `global`-DRAM floor (keccak) even when
        // the structural fix bites — so also surface refusals eliminated / fold_uses.
        let baseline_refusals = baseline_t
            .events
            .iter()
            .filter(|e| matches!(e, BwdEvent::Refuse { .. }))
            .count();
        let realized_refusals = realized_t
            .events
            .iter()
            .filter(|e| matches!(e, BwdEvent::Refuse { .. }))
            .count();
        eprintln!(
            "planned_fill_then_trim_monotone {name}: retains={retains} \
             traffic {baseline_traffic}->{realized_traffic} (drop={}) \
             fold_uses {}->{} refusals {}->{} max_live {}->{}",
            baseline_traffic - realized_traffic,
            baseline_c.stats_ext.fold_uses,
            realized_c.stats_ext.fold_uses,
            baseline_refusals,
            realized_refusals,
            baseline_c.stats.max_live_cells,
            realized_c.stats.max_live_cells,
        );
    }
}

// ── CS-M4 Task 1: realized-retention model (`realized_openings` + `normalize`) ──

/// Deterministic synthetic witness for the realized-retention model. Builds
/// [`synthetic_refusable_whole_origin_layer`] (3 shared Ext fold leaves, each used in
/// both sibling reduction terms `P`/`Q`), a coordinate-correct whole-origin plan
/// retaining every shared leaf, and compiles it with a TIGHT eviction dial
/// (`lower_budget = 8` = 2 Ext buckets) at a GENEROUS `place_budget = 12`. Two leaves
/// admit (and REALIZE — held resident through their `Q` serve), one REFUSES (its
/// admission declined once `live_width` fills), so the trace carries BOTH a realized and
/// a refused opening while staying feasible and certifying. Returns
/// `(d, place_budget, plan, c, trace)`; `assert!`s both openings are present so the
/// witness can never silently degrade. Reused by Task 5's stranded-retain test.
///
/// Why the split budget: with fully-concurrent Ext retentions (retention width == acc
/// width == 4) the refusal threshold (`live_width + 4 > budget`) coincides EXACTLY with
/// the placement floor, so a single `compile_distilled_planned` either fully realizes or
/// hits `BudgetBelowFloor` — the same reason keccak's roomy b16 shows no refusal (a
/// verified CS-M4 Task-1 finding). The fill-then-trim's own `lower_budget` dial
/// (`compile.rs` `compile_distilled_at_planned`) separates the two: a tight `lower_budget`
/// forces refusals during lowering while the generous `place_budget` lets the survivors
/// place — a genuine feasible-with-refusal, exactly the pressure Stage-A accumulation
/// exerts in the full pipeline.
#[cfg(test)]
fn synthetic_layer_with_refusable_whole_origin() -> (
    DistilledLayer,
    usize,
    BwdOccurrencePlan,
    gkr_eval_isa::bwd::compile::BwdCompiledLayer,
    gkr_eval_isa::bwd::trace::BwdCompileTrace,
) {
    use gkr_eval_isa::bwd::price::realized_openings;
    const N_SHARED: usize = 3;
    const PLACE_BUDGET: usize = 12; // fits the 2 survivors + acc (2*4 + 4 = 12)
    const LOWER_BUDGET: usize = 8; // 2 Ext buckets → the 3rd admission refuses

    let d = synthetic_refusable_whole_origin_layer(N_SHARED);
    let frozen = coordinate_correct_frozen(&d, PLACE_BUDGET);
    // Whole-origin retention of every shared fold leaf (retain each opening but its last).
    let pins: BTreeSet<ExprId> = frozen.leaf_instants.keys().copied().collect();
    let plan = compound_batch_plan(&frozen, &pins);
    let (c, trace) = compile_distilled_at_planned_lb(&d, PLACE_BUDGET, LOWER_BUDGET, &plan)
        .expect("split-budget compile must place-fit at PLACE_BUDGET");

    // The witness must exhibit BOTH a realized and a refused opening (never silently pass).
    let realized = realized_openings(&plan, &trace);
    let requested: Vec<usize> = plan
        .entries
        .iter()
        .enumerate()
        .filter(|(_, e)| e.action == PlanAction::Retain)
        .map(|(k, _)| k)
        .collect();
    assert!(
        requested.iter().any(|k| realized.contains(k)),
        "witness must have a realized opening (an admitted, still-resident leaf)"
    );
    assert!(
        requested.iter().any(|k| !realized.contains(k)),
        "witness must have a refused (unrealized) opening"
    );
    (d, PLACE_BUDGET, plan, c, trace)
}

/// Task-1 minimal permissive `TrialBudget` stub (Task 2 enriches it with dynamic
/// accrual). Large `available` so `normalize` never runs out of credit here.
#[cfg(test)]
fn trial_budget_stub() -> gkr_eval_isa::bwd::price::TrialBudget {
    // Large `available` + enforcing so `normalize` never runs out of credit here; the
    // enriched (Task 2) fields default to the zero/enforce state via `..Default::default()`.
    gkr_eval_isa::bwd::price::TrialBudget {
        available: 1 << 20,
        ..Default::default()
    }
}

/// The realized-retention model unit gate (CS-M4 Task 1). On the deterministic synthetic
/// witness (a whole-origin retention that partially refuses): (a) certify is `Ok` despite
/// refusals; (b) `realized_openings` EXCLUDES the refused opening but INCLUDES a
/// successful first-admission opening (the next-occurrence off-by-one guard — a first
/// admission's OWN serve is `Recomputed`, its NEXT is `Resident`); (c) after `normalize`
/// every remaining `Retain` is realized, the refused occurrences are `Bypass`, and traffic
/// is unchanged; (d) a second `normalize` demotes nothing (idempotent) and spends no
/// budget.
#[test]
fn normalize_demotes_refused_retain_and_is_idempotent() {
    use gkr_eval_isa::bwd::price::{normalize, realized_openings};
    let (d, budget, plan0, c0, trace0) = synthetic_layer_with_refusable_whole_origin();

    // (a) refusals do not gate the certificate.
    assert!(
        certify(&c0, &trace0).is_ok(),
        "refusals do not gate certify"
    );

    // (b) off-by-one guard: a refused opening is EXCLUDED, a first-admission opening INCLUDED.
    let realized0 = realized_openings(&plan0, &trace0);
    let requested: Vec<usize> = plan0
        .entries
        .iter()
        .enumerate()
        .filter(|(_, e)| e.action == PlanAction::Retain)
        .map(|(k, _)| k)
        .collect();
    assert!(
        requested.iter().any(|k| !realized0.contains(k)),
        "test must exercise a refusal"
    );
    assert!(
        requested.iter().any(|k| realized0.contains(k)),
        "a successful retention must stay"
    );

    // (c) normalize demotes only the refused Retains, once, traffic-neutral.
    let mut budget_ctr = trial_budget_stub(); // Task 1: permissive stub; real TrialBudget in Task 2
    let base_traffic = c0.stats_ext.global + c0.stats_ext.fold_traffic;
    let (plan1, c1, trace1, demoted, unrealized1) =
        normalize(&d, budget, plan0, c0, trace0, &mut budget_ctr).unwrap();
    assert!(demoted >= 1, "at least one refused Retain demoted");
    assert_eq!(
        unrealized1, 0,
        "permissive stub budget → normalize fully completes"
    );
    assert_eq!(
        c1.stats_ext.global + c1.stats_ext.fold_traffic,
        base_traffic,
        "normalize is traffic-neutral"
    );
    let realized1 = realized_openings(&plan1, &trace1);
    for (k, e) in plan1.entries.iter().enumerate() {
        if e.action == PlanAction::Retain {
            assert!(
                realized1.contains(&k),
                "no unrealized Retain remains after normalize"
            );
        }
    }

    // (d) idempotent + spends no budget on a fully-realized plan.
    let available_before = budget_ctr.available;
    let (plan2, _c2, _t2, demoted2, unrealized2) =
        normalize(&d, budget, plan1, c1, trace1, &mut budget_ctr).unwrap();
    assert_eq!(demoted2, 0, "normalize is idempotent");
    assert_eq!(unrealized2, 0);
    assert_eq!(
        budget_ctr.available, available_before,
        "idempotent normalize spends no budget"
    );
    let _ = plan2;
}

// ── CS-M4 Task 5: terminal normalize + Complete/Incomplete + zero-unrealized invariant ──

/// THE deterministic (fast, non-ignored) red for the terminal normalize (spec §3/§4).
///
/// Part A — the terminal-normalize LOGIC is load-bearing on a genuinely stranded plan.
/// A single-budget `compile_distilled_planned` cannot express a feasible-with-refusal on
/// uniform-Ext fold leaves — the acc-width == retention-width coincidence means it either
/// fully realizes or hits `BudgetBelowFloor`, so a synthetic Stage-B addition never strands
/// through `reclaim_leaves`' own compiles (a verified CS-M4 finding; the real fixtures also
/// happen not to strand at b16). We therefore reproduce the STRANDED accumulated plan — the
/// exact shape a Stage-B gap-retention leaves when it consumes capacity at an earlier
/// whole-origin retain's admission — via the split lower-budget dial (the Task-1 witness).
/// This IS the min plan `reclaim_leaves` ships BEFORE its terminal pass; the terminal pass is
/// exactly the `normalize` call that pass makes. Assert: BEFORE ≥1 unrealized (stranded)
/// Retain; AFTER the terminal `normalize`, ZERO unrealized and realized traffic UNCHANGED
/// (spec §3: an unrealized Retain held zero capacity, so demoting it frees nothing). Without
/// the terminal pass the stranded Retain would ship; with it the plan is an honest-residency
/// record.
///
/// Part B — the `reclaim_leaves` WIRING: the terminal normalize runs on the shipped min plan
/// and the returned `Complete` plan is a zero-unrealized record. On the (clean-by-construction)
/// P/Q synthetic `reclaim_leaves` ships the B-only floor, whose `normalize_calls` is exactly
/// the ONE terminal pass — `0` without the Task-5 terminal normalize, so this assertion is a
/// genuine fail-without / pass-with signal for the wiring.
#[test]
fn terminal_normalize_cleans_stage_b_stranded_retain() {
    use gkr_eval_isa::bwd::price::{
        LeafReclaimResult, TrialBudget, normalize, realized_openings, reclaim_leaves,
    };

    // ── Part A: the terminal normalize cleans a stranded (Stage-B-shaped) plan ──────────
    let (d, budget, stranded_plan, c, trace) = synthetic_layer_with_refusable_whole_origin();
    let realized_before = realized_openings(&stranded_plan, &trace);
    let unreal_before = stranded_plan
        .entries
        .iter()
        .enumerate()
        .filter(|(k, e)| e.action == PlanAction::Retain && !realized_before.contains(k))
        .count();
    assert!(
        unreal_before >= 1,
        "witness must carry ≥1 stranded (unrealized) Retain BEFORE"
    );
    let traffic_before = c.stats_ext.global + c.stats_ext.fold_traffic;

    let mut tb = TrialBudget {
        available: 1 << 20,
        ..Default::default()
    };
    let (clean_plan, clean_c, clean_trace, demoted, unrealized_after) =
        normalize(&d, budget, stranded_plan, c, trace, &mut tb).unwrap();
    assert!(
        demoted >= 1,
        "terminal normalize must demote the stranded Retain(s)"
    );
    assert_eq!(
        unrealized_after, 0,
        "terminal normalize must leave ZERO unrealized"
    );
    let realized_after = realized_openings(&clean_plan, &clean_trace);
    for (k, e) in clean_plan.entries.iter().enumerate() {
        if e.action == PlanAction::Retain {
            assert!(
                realized_after.contains(&k),
                "unrealized Retain @ {k} survived terminal normalize"
            );
        }
    }
    assert_eq!(
        clean_c.stats_ext.global + clean_c.stats_ext.fold_traffic,
        traffic_before,
        "terminal normalize is traffic-neutral (an unrealized Retain held zero capacity)",
    );

    // ── Part B: reclaim_leaves ships a Complete, zero-unrealized plan; the terminal pass
    // is wired (normalize_calls accounts for it). ─────────────────────────────────────────
    let dq = synthetic_refusable_whole_origin_layer(3);
    let bud = 16usize;
    let frozen0 = coordinate_correct_frozen(&dq, bud);
    let base0 = compound_batch_plan(&frozen0, &BTreeSet::new());
    let (bc0, bt0) = compile_distilled_planned(&dq, bud, &base0).unwrap();
    let observed = freeze_demand(
        &dq,
        &bt0,
        &bc0.program,
        &bc0.specials,
        &bc0.backings,
        &bc0.source_windows,
    )
    .unwrap();
    let base = compound_batch_plan(&observed, &BTreeSet::new());
    let (bc, bt) = compile_distilled_planned(&dq, bud, &base).unwrap();
    let mut tb2 = TrialBudget {
        available: 1 << 20,
        ..Default::default()
    };
    let res = reclaim_leaves(&dq, bud, &observed, &base, bc, bt, RECLAIM_N, &mut tb2).unwrap();
    let (plan, trace, counters) = match res {
        LeafReclaimResult::Complete {
            plan,
            trace,
            counters,
            ..
        } => (plan, trace, counters),
        LeafReclaimResult::Incomplete { unrealized, .. } => {
            panic!(
                "reclaim_leaves must return Complete on the ample-budget synthetic, got Incomplete({unrealized})"
            )
        }
    };
    let realized = realized_openings(&plan, &trace);
    for (k, e) in plan.entries.iter().enumerate() {
        if e.action == PlanAction::Retain {
            assert!(
                realized.contains(&k),
                "reclaim_leaves shipped an unrealized Retain @ {k}"
            );
        }
    }
    // The terminal normalize always runs (spec §3): it is +1 `normalize_calls` over the
    // pre-terminal count (0 for the B-only floor, 2 for the A+B path). Removing it drops this.
    let expected = if counters.safety_net_chose_b_only {
        1
    } else {
        3
    };
    assert_eq!(
        counters.normalize_calls, expected,
        "terminal normalize must be counted (sn_b={})",
        counters.safety_net_chose_b_only,
    );
}

/// Heavy G-M0 integration gate (spec §3): for all four tracked fixtures the shipped CS plan
/// is a zero-unrealized `Complete` honest-residency record, its certificate holds by exact
/// integer equality, and the shipped program is value-exact. No round returns `Incomplete`
/// (the reserve funds the terminal normalize). None strands at b16 in practice, so this is
/// the invariant gate rather than the red — but it is the through-`reclaim_leaves` proof that
/// the pipeline closes on real data.
#[test]
#[ignore] // heavy (~minutes): full production priced runs at b16 on the four G-M0 fixtures.
fn pipeline_returns_complete_zero_unrealized() {
    use gkr_eval_isa::bwd::price::realized_openings;
    for name in [
        "keccak_special5_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "unified_reduced_machine_layout_gkr.json",
    ] {
        let (layer, cross) = load_layer(name, 0);
        let out = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);

        // (a) no round exhausted its normalization budget; none of the four falls back.
        assert!(
            !out.saw_incomplete_round,
            "{name}: a round returned Incomplete"
        );
        assert!(
            !out.fell_back_to_baseline,
            "{name}: CS path unexpectedly fell back to baseline"
        );

        // (b) zero unrealized Retain on the shipped plan (re-distill + recompile for the trace).
        if let Some(plan) = out.plan.as_ref() {
            let d = distill(&layer, BwdRegime::Ext, &cross, Some(&out.unit_permutation));
            let (_c, trace) = compile_distilled_planned(&d, 16, plan).unwrap();
            let realized = realized_openings(plan, &trace);
            for (k, e) in plan.entries.iter().enumerate() {
                if e.action == PlanAction::Retain {
                    assert!(realized.contains(&k), "{name}: unrealized Retain @ {k}");
                }
            }
        }

        // (c) certificate exact-integer equality on the shipped compile.
        assert_eq!(
            out.certificate.counted_traffic, out.certificate.reported_traffic,
            "{name}: shipped program certificate must be Ok (counted == reported)",
        );

        // (d) value-parity on the shipped program (same reconstruction as the engine gate).
        let d_used = (!out.fell_back_to_baseline)
            .then(|| distill(&layer, BwdRegime::Ext, &cross, Some(&out.unit_permutation)));
        let bl_d;
        let d_ref = match &d_used {
            Some(d) => d,
            None => {
                bl_d = distill(&layer, BwdRegime::Ext, &cross, None);
                &bl_d
            }
        };
        assert_bwd_value_parity(&out.compiled, d_ref, &layer);

        eprintln!(
            "{name}: Complete zero-unrealized, term_demoted={} normalize_calls={} traffic={}",
            out.counters.terminal_demoted,
            out.counters.normalize_calls,
            out.stats.global + out.stats.fold_traffic,
        );
    }
}

/// Heavy reserve gate (spec §5): the reserved normalization credit (each stage admits only
/// while `available > 1`) funds the mandatory terminal normalize, so a run never spuriously
/// returns `Incomplete`. Run the research entry across production and escalated multipliers;
/// assert `!saw_incomplete_round` and that the shipped plan is `Complete` (did not fall back
/// to the baseline because a round went Incomplete). `unified` is the fastest G-M0 fixture.
#[test]
#[ignore] // heavy (~tens of seconds): unified priced runs at b16 across two multipliers.
fn normalize_reserve_prevents_spurious_incomplete() {
    let name = "unified_reduced_machine_layout_gkr.json";
    let (layer, cross) = load_layer(name, 0);
    for multiplier in [1usize, 2] {
        let out = cs_schedule_bwd_layer_research(
            &layer,
            BwdRegime::Ext,
            &cross,
            16,
            multiplier,
            RECLAIM_N,
            /*enforce_budget*/ true,
        );
        assert!(
            !out.saw_incomplete_round,
            "{name} (mult={multiplier}): reserved credit failed to fund the terminal normalize",
        );
        assert!(
            !out.fell_back_to_baseline,
            "{name} (mult={multiplier}): shipped plan is not Complete (fell back to baseline)",
        );
        assert_eq!(
            out.certificate.counted_traffic, out.certificate.reported_traffic,
            "{name} (mult={multiplier}): shipped certificate must be Ok",
        );
    }
}
