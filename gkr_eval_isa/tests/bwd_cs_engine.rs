mod common;
use common::*;
use gkr_eval_isa::bwd::compile::{compile_distilled, compile_distilled_planned, compile_distilled_traced};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::fif::{feasible_leaf_plan, fif_select, oracle_saved, plan_leaves, Gap};
use gkr_eval_isa::bwd::plan::PlanAction;
use gkr_eval_isa::bwd::trace::{
    freeze_demand, live_profile, BwdEvent, BwdServedFrom, BwdServeKind,
};
use cs::gkr_compiler::dag_ir::{BwdRegime, ExprId};

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
