mod common;
use std::collections::BTreeSet;

use common::*;
use gkr_eval_isa::bwd::compile::{compile_distilled, compile_distilled_planned, compile_distilled_traced};
use gkr_eval_isa::bwd::construct::construct_unit_order;
use gkr_eval_isa::bwd::distill::{distill, stable_distilled_site_domain};
use gkr_eval_isa::bwd::fif::{feasible_leaf_plan, fif_select, oracle_saved, plan_leaves, Gap};
use gkr_eval_isa::bwd::plan::PlanAction;
use gkr_eval_isa::bwd::trace::{
    certify, freeze_demand, live_profile, BwdEvent, BwdServedFrom, BwdServeKind,
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
