mod common;
use std::collections::{BTreeMap, BTreeSet};

use common::*;
use gkr_eval_isa::bwd::compile::{compile_distilled, compile_distilled_planned, compile_distilled_traced};
use gkr_eval_isa::bwd::construct::construct_unit_order;
use gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer;
use gkr_eval_isa::bwd::distill::{distill, stable_distilled_site_domain, DistilledLayer};
use gkr_eval_isa::bwd::fif::{feasible_leaf_plan, fif_select, oracle_saved, plan_leaves, Gap};
use gkr_eval_isa::bwd::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use gkr_eval_isa::bwd::price::{
    compound_batch_plan, compound_candidates, modeled_traffic_full, planner_signature, price_pin,
    priced_rounds, suppression_ranges, value_width,
};
use gkr_eval_isa::bwd::trace::{
    certify, freeze_demand, live_profile, BwdEvent, BwdServedFrom, BwdServeKind, FrozenDemand,
};
use cs::gkr_compiler::dag_ir::{bwd_roots, BwdRegime, ExprId};

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
        assert!(trace.events.iter().any(|e| matches!(e, BwdEvent::Serve { .. })), "L{li}");
    }
}

/// TrafficRead events recount to EXACTLY the tally's traffic (certificate seed).
#[test]
fn trace_traffic_reads_match_tally() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let counted: usize = trace.events.iter()
            .filter_map(|e| match e { BwdEvent::TrafficRead { cells, .. } => Some(*cells as usize), _ => None })
            .sum();
        assert_eq!(counted, c.stats_ext.global + c.stats_ext.fold_traffic, "L{li}");
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

/// Leaf demand instants (DOMAIN leaves only): k-th FoldSource use in the program
/// == k-th Recomputed serve of that leaf in the trace (per-leaf counts must agree
/// exactly). Non-domain gathers are accounted in nondomain_gather_cells instead.
#[test]
fn frozen_leaf_instants_align_with_serves() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let frozen = freeze_demand(&d, &trace, &c.program, &c.specials);
        assert_eq!(frozen.epoch, trace.epoch);
        for (v, instants) in &frozen.leaf_instants {
            let serves = frozen.domain_serves.iter()
                .filter(|(fp, from)| fp.value == *v && matches!(from, BwdServedFrom::Recomputed))
                .count();
            assert_eq!(instants.len(), serves, "L{li} leaf {v:?}");
        }
        assert!(frozen.free.iter().all(|&f| f <= 16), "L{li}");
    }
}

// ── Task 5 (CS-M0): FiF leaf planner (`plan_leaves`) ──────────────────────────

fn lcg(state: &mut u64, m: u64) -> u64 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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
                gaps.push(Gap { origin: ExprId(o as u32), start: w[0], end: w[1] });
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
    let frozen = freeze_demand(&d, &baseline_trace, &baseline_c.program, &baseline_c.specials);
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
    let kept_gaps = plan.entries.iter().filter(|e| e.action == PlanAction::Retain).count();

    assert!(
        kept_gaps > 0,
        "wrapper degraded to all-Bypass on a headroom fixture (kept_gaps == 0) — the \
         coordinate-correct freeze + discount retained nothing; report as a finding"
    );

    let diverge = planned_trace.events.iter().find(|e| matches!(e, BwdEvent::Diverge { .. }));
    assert!(diverge.is_none(), "returned compile diverged: {diverge:?}");
    let refusals =
        planned_trace.events.iter().filter(|e| matches!(e, BwdEvent::Refuse { .. })).count();
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
    let diverge = trace.events.iter().find(|e| matches!(e, BwdEvent::Diverge { .. }));
    assert!(diverge.is_none(), "returned compile diverged: {diverge:?}");
    let refusals = trace.events.iter().filter(|e| matches!(e, BwdEvent::Refuse { .. })).count();
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
    const HEAVY: &[&str] =
        &["bigint_with_extended_control_layout_gkr.json", "keccak_special5_layout_gkr.json"];
    for &name in HEAVY {
        let (layer, cross) = load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);

        let (plan, planned_c, planned_trace) = feasible_leaf_plan(&d, 16)
            .unwrap_or_else(|e| panic!("{name}: feasible_leaf_plan must return Ok, got {e:?}"));
        let kept_gaps = plan.entries.iter().filter(|e| e.action == PlanAction::Retain).count();

        let diverge = planned_trace.events.iter().find(|e| matches!(e, BwdEvent::Diverge { .. }));
        assert!(diverge.is_none(), "{name}: returned compile diverged: {diverge:?}");
        let refusals =
            planned_trace.events.iter().filter(|e| matches!(e, BwdEvent::Refuse { .. })).count();
        assert_eq!(refusals, 0, "{name}: {refusals} Refuse events (model/compiler mismatch)");

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
        eprintln!("{name}: kept_gaps={kept_gaps} baseline_fold={baseline_fold} planned_fold={planned_fold} traffic {baseline_traffic}->{planned_traffic}");
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
    use gkr_eval_isa::bwd::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanEntry};
    let (ft_c, ft_trace) = compile_distilled_traced(d, budget, None).expect("baseline traced");
    let frozen = freeze_demand(d, &ft_trace, &ft_c.program, &ft_c.specials);
    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .map(|&(fp, _from)| PlanEntry { fp, action: PlanAction::Bypass })
        .collect();
    let all_bypass = BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    };
    compile_distilled_planned(d, budget, &all_bypass).expect("all-Bypass compile feasible").0
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
        if bwd_roots(&layer).is_empty() {
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
    assert!(checked > 0, "no fixture's L0 had bwd roots — enumeration broke");
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
    trace.events.push(BwdEvent::TrafficRead { value: ExprId(0), cells: 1 });

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
        if bwd_roots(&layer).is_empty() {
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
            assert!(seen.insert(unit), "{name}: unit {unit} repeated in permutation");
        }
        assert_eq!(seen.len(), n_units, "{name}: permutation must cover every unit");

        let reordered = distill(&layer, BwdRegime::Ext, &cross, Some(&order));
        compile_distilled(&reordered, 16, None).unwrap_or_else(|e| {
            panic!("{name}: constructed-order compile @ b16 failed (feasibility regression): {e:?}")
        });

        checked += 1;
    }
    assert!(checked > 0, "no fixture's L0 had bwd roots — enumeration broke");
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
            .map(|r| frozen.domain_serves[r.clone()].iter().map(|(fp, _)| fp.value).collect())
            .collect()
    };

    let rv = suppression_ranges(&frozen, v);
    let rw = suppression_ranges(&frozen, w);
    let ru = suppression_ranges(&frozen, u);

    // V has 2 occurrences → 1 non-producer → 1 range, covering [W, U] (pre-order).
    assert_eq!(rv.len(), 1, "V ranges: {rv:?}");
    assert_eq!(covered(&rv), vec![vec![w, u]], "V's non-producer cone re-expansion = [W, U]");

    // W has 3 occurrences → 2 non-producer → 2 ranges, each covering exactly [U].
    assert_eq!(rw.len(), 2, "W ranges: {rw:?}");
    assert_eq!(covered(&rw), vec![vec![u], vec![u]], "each W cone re-expansion = [U]");

    // U has no domain descendants → every cone re-expansion is empty → dropped.
    assert!(ru.is_empty(), "U ranges must be empty (no domain descendants): {ru:?}");

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
        .map(|c| (price_pin(&frozen, &BTreeSet::new(), c, value_width(&d, c)), c))
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
    let celf_traffic = modeled_traffic_full(&frozen, &widths(&committed)).expect("CELF set feasible");

    assert!(
        (celf_traffic as f64) <= oracle as f64 * 1.01,
        "CELF traffic {celf_traffic} > 1% above oracle {oracle} (baseline {baseline}, top {})",
        top.len()
    );
    eprintln!("priced_oracle_gap: baseline={baseline} oracle={oracle} celf={celf_traffic} candidates={}", top.len());
}

/// (c) Priced rounds converge or cap: add_sub + keccak Ext L0 @ b16 — `rounds <= 3`,
/// the RETURNED round's plan certifies exactly with no divergence, `priced_rounds`
/// is deterministic, and two identical rounds produce structurally-`==`
/// `PlannerSignature`s (never a hash).
#[test]
fn priced_rounds_converge_or_cap() {
    for name in ["add_sub_lui_auipc_mop_layout_gkr.json", "keccak_special5_layout_gkr.json"] {
        let (layer, cross) = load_layer(name, 0);
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let frozen0 = coordinate_correct_frozen(&d, 16);

        let outcome = priced_rounds(&d, 16, frozen0.clone())
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
        assert!(report.is_ok(), "{name}: returned plan certify diverged: {report:?}");
        assert!(
            !t.events.iter().any(|e| matches!(e, BwdEvent::Diverge { .. })),
            "{name}: returned plan diverged"
        );

        // `priced_rounds` is deterministic (no wall-clock / hashmap-order dependence).
        let outcome2 = priced_rounds(&d, 16, frozen0.clone()).expect("second run");
        assert_eq!(outcome.plan.entries, outcome2.plan.entries, "{name}: plan not deterministic");
        assert_eq!(outcome.pins, outcome2.pins, "{name}: pins not deterministic");

        // Two identical rounds → structurally-== signatures (independent compiles).
        let pins: BTreeSet<ExprId> = outcome.pins.iter().copied().collect();
        let (_c_a, t_a) = compile_distilled_planned(&d, 16, &outcome.plan).expect("compile a");
        let (_c_b, t_b) = compile_distilled_planned(&d, 16, &outcome.plan).expect("compile b");
        let sig_a = planner_signature(&frozen0, &t_a, &pins, &outcome.plan);
        let sig_b = planner_signature(&frozen0, &t_b, &pins, &outcome.plan);
        assert_eq!(sig_a, sig_b, "{name}: PlannerSignature must be structurally equal (never a hash)");

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
        plan.entries.iter().any(|e| e.fp.value == v && e.action == PlanAction::Retain),
        "V must be retained at its producer occurrence"
    );

    let (c, t) = compile_distilled_planned(&d, 16, &plan).expect("compound-batch compile");
    let diverge = t.events.iter().find(|e| matches!(e, BwdEvent::Diverge { .. }));
    assert!(diverge.is_none(), "compound batch diverged (Task-4 machinery?): {diverge:?}");

    let observed = freeze_demand(&d, &t, &c.program, &c.specials);
    let predicted: Vec<_> = plan.entries.iter().map(|e| e.fp).collect();
    let realized: Vec<_> = observed.domain_serves.iter().map(|(fp, _)| *fp).collect();
    assert_eq!(predicted, realized, "predicted suppressed stream != observed re-frozen stream");

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
    const HEAVY: &[&str] =
        &["bigint_with_extended_control_layout_gkr.json", "keccak_special5_layout_gkr.json"];
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

        let outcome = priced_rounds(&d, 16, frozen0.clone())
            .unwrap_or_else(|e| panic!("{name}: priced_rounds must return Ok, got {e:?}"));

        // The RETURNED round's realized final traffic, re-derived from the returned
        // plan — the certificate is the correctness guarantee, not the model.
        let (final_c, final_trace) = compile_distilled_planned(&d, 16, &outcome.plan)
            .unwrap_or_else(|e| panic!("{name}: returned plan must compile, got {e:?}"));
        let report = certify(&final_c, &final_trace);
        assert!(report.is_ok(), "{name}: returned round certify diverged: {report:?}");
        assert!(
            !final_trace.events.iter().any(|e| matches!(e, BwdEvent::Diverge { .. })),
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
        assert!(outcome.reclaim_attempted > 0, "{name}: reclaim_attempted == 0 — reclaim did not run");
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
    const VALUE_PARITY: &[&str] =
        &["add_sub_lui_auipc_mop_layout_gkr.json", "keccak_special5_layout_gkr.json"];
    let mut checked = 0usize;
    println!(
        "engine_runs_all_fixtures_b16 (Ext L0, b16):\n  \
         fixture | result | baseline_traffic -> cs_traffic | pins | rounds | converged"
    );
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if bwd_roots(&layer).is_empty() {
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
        assert!(outcome.certificate.diverged.is_none(), "{name}: shipped program diverged");

        // Never worse than the canonical baseline (fallback guarantees this), rounds capped.
        let cs_traffic = outcome.stats.global + outcome.stats.fold_traffic;
        assert!(
            cs_traffic <= baseline_traffic,
            "{name}: CS traffic {cs_traffic} > baseline {baseline_traffic} — non-regression broke"
        );
        assert!(outcome.rounds <= 3, "{name}: rounds {} > 3", outcome.rounds);

        // Value-parity spot gate on the shipped program (add_sub + keccak).
        if VALUE_PARITY.contains(&name) {
            let d_used = (!outcome.fell_back_to_baseline)
                .then(|| distill(&layer, BwdRegime::Ext, &cross, Some(&outcome.unit_permutation)));
            let d_ref = d_used.as_ref().unwrap_or(&bl_d);
            assert_bwd_value_parity(&outcome.compiled, d_ref, &layer);
        }

        println!(
            "  {name} | {} | {baseline_traffic} -> {cs_traffic} | {} | {} | {}",
            if outcome.fell_back_to_baseline { "FELL_BACK" } else { "IMPROVED " },
            outcome.pins.len(),
            outcome.rounds,
            outcome.converged,
        );
        checked += 1;
    }
    assert!(checked > 0, "no fixture's L0 had bwd roots — enumeration broke");
    println!(
        "engine_runs_all_fixtures_b16: {checked}/{} fixtures held (Ext L0)",
        FIXTURES.len()
    );
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

    assert_eq!(a.unit_permutation, b.unit_permutation, "permutation not deterministic");
    assert_eq!(a.fell_back_to_baseline, b.fell_back_to_baseline, "fallback verdict not deterministic");
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
            assert_eq!(pa.entries_fnv, pb.entries_fnv, "plan entries_fnv not deterministic");
            assert_eq!(pa.stream_reductions, pb.stream_reductions, "plan regime not deterministic");
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
    println!("engine_value_parity_all_fixtures (Ext L0, b16):\n  fixture | fell_back | value_parity");
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if bwd_roots(&layer).is_empty() {
            continue; // L0 has no backward roots for this fixture
        }

        let outcome = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);

        // Reconstruct the distilled layer the engine actually shipped against —
        // same reconstruction Task 9's spot gate uses (`engine_runs_all_fixtures_b16`).
        let d_used = (!outcome.fell_back_to_baseline)
            .then(|| distill(&layer, BwdRegime::Ext, &cross, Some(&outcome.unit_permutation)));
        let bl_d;
        let d_ref = match &d_used {
            Some(d) => d,
            None => {
                bl_d = distill(&layer, BwdRegime::Ext, &cross, None);
                &bl_d
            }
        };

        assert_bwd_value_parity(&outcome.compiled, d_ref, &layer);

        // Belt-and-suspenders: the shipped program's own certificate must be Ok.
        assert_eq!(
            outcome.certificate.counted_traffic, outcome.certificate.reported_traffic,
            "{name}: shipped program certificate must be Ok (counted == reported)"
        );

        println!(
            "  {name} | {} | value_parity OK",
            if outcome.fell_back_to_baseline { "FELL_BACK" } else { "IMPROVED " },
        );
        checked += 1;
    }
    assert!(checked > 0, "no fixture's L0 had bwd roots — enumeration broke");
    println!(
        "engine_value_parity_all_fixtures: {checked}/{} fixtures held (Ext L0)",
        FIXTURES.len()
    );
}
