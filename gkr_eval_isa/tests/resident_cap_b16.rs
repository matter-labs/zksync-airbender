//! Task 8/8a: b16 add_sub L0 `MaterializePolicy::Decisions` feasibility.
//!
//! Step-0 (findings in `.superpowers/sdd/task-8-report.md`) found `try_admit` had
//! no way to DECLINE an admission while capacity was free: the resident set
//! greedily filled the whole placement budget and starved the concurrent
//! evaluation temps, so every genome was `BudgetBelowFloor` at b16.
//!
//! Task 8a fixed this by capping the `Decisions` resident-admission budget at
//! `budget - legacy_recompute_floor` (`scorer::resident_cap_for_order` /
//! `LayerCtx::resident_cap`) — residents may only consume cells pure computation
//! doesn't need. The tests below are the promoted, no-longer-`#[ignore]`d Step-0
//! probes: they pin the now-fixed b16 feasibility (test 1, the load-bearing one)
//! and the cap's graceful degeneracy to `LegacyRecompute` when there is no
//! headroom to spare (test 2).

mod common;

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{lower_dag, validate, DagCircuit, FieldKind, LayerSchedule, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_layer_with_policy, MaterializePolicy,
};
use gkr_eval_isa::schedule_search::genome::Genome;
use gkr_eval_isa::schedule_search::scorer::{decode_schedule, resident_cap_for_order, score, LayerCtx};

use common::load_fixture;

const ADD_SUB: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

fn load_dag(
    fixture: &str,
) -> (DagCircuit, GKRCircuitArtifact<BabyBearField>, HashMap<ReadPlace, FieldKind>) {
    let artifact = load_fixture(fixture);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{fixture}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{fixture}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    (dag, artifact, cross)
}

/// The load-bearing regression: b16 add_sub L0 under `Decisions` with a plain
/// (neutral) genome is FEASIBLE, and its traffic beats `LegacyRecompute`'s at the
/// same budget. This is exactly the scenario Step-0 found `BudgetBelowFloor` for
/// every genome at every budget below ~40 (probe table in the Task-8 report).
#[test]
fn b16_add_sub_l0_decisions_feasible_beats_legacy() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];
    const BUDGET: usize = 16;

    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, BUDGET);
    let genome = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    let sched = decode_schedule(&genome, &ctx);

    let legacy_traffic = compile_layer_with_policy(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &sched,
        BUDGET,
        MaterializePolicy::LegacyRecompute,
    )
    .unwrap_or_else(|e| panic!("LegacyRecompute must be feasible at budget {BUDGET}: {e:?}"))
    .stats
    .dram_traffic;

    let decisions_score = score(&genome, &ctx);
    assert!(
        !decisions_score.infeasible,
        "Decisions must be feasible at budget {BUDGET} for add_sub L0 (Task 8a resident cap)"
    );
    assert!(
        decisions_score.dram_traffic < legacy_traffic,
        "Decisions traffic ({}) must beat LegacyRecompute's ({}) at budget {BUDGET}",
        decisions_score.dram_traffic,
        legacy_traffic
    );
    println!(
        "b16 add_sub L0: legacy traffic={legacy_traffic} decisions(neutral) traffic={} \
         (resident_cap={})",
        decisions_score.dram_traffic,
        ctx.resident_cap(&sched.order)
    );
}

/// Cap degeneracy: at `budget == legacy_recompute_floor`, the resident cap is 0
/// (no headroom to spare), so `Decisions` admits nothing and must match
/// `LegacyRecompute`'s own traffic exactly (zero admissions -> same emission).
#[test]
fn resident_cap_degenerates_to_legacy_at_zero_headroom() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];

    // Find `legacy_recompute_floor` for the neutral-genome order via the same
    // derivation the scorer uses, at a generously large probe budget (the floor
    // itself doesn't depend on the probe budget once it's above the true floor —
    // `resident_cap_for_order` reads it straight off `Placement::max_live_cells`).
    let probe_ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, 4096);
    let genome = Genome::neutral(probe_ctx.n_order_keys(), probe_ctx.n_sites());
    let sched = decode_schedule(&genome, &probe_ctx);
    let legacy_floor = 4096
        - resident_cap_for_order(
            layer,
            &artifact.layers[0],
            &artifact.scratch_space_mapping,
            &cross,
            &sched.order,
            4096,
        );

    // Re-derive the cap AT budget == legacy_floor: must be exactly 0.
    let cap_at_floor = resident_cap_for_order(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &sched.order,
        legacy_floor,
    );
    assert_eq!(cap_at_floor, 0, "resident cap must be 0 when budget == legacy floor (no headroom)");

    let legacy_schedule = LayerSchedule {
        order: sched.order.clone(),
        sites: Vec::new(),
        predicted_traffic: 0,
        floor: 0,
    };
    let legacy_compiled = compile_layer_with_policy(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &legacy_schedule,
        legacy_floor,
        MaterializePolicy::LegacyRecompute,
    )
    .unwrap_or_else(|e| panic!("LegacyRecompute must be feasible at its own floor: {e:?}"));

    let decisions = SiteDecisions::new(sched.sites.iter().copied());
    let decisions_compiled = compile_layer_with_policy(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &sched,
        legacy_floor,
        MaterializePolicy::Decisions { decisions, budget: cap_at_floor },
    )
    .unwrap_or_else(|e| {
        panic!("Decisions at cap=0 must still be feasible (== LegacyRecompute): {e:?}")
    });

    assert_eq!(
        decisions_compiled.stats.dram_traffic, legacy_compiled.stats.dram_traffic,
        "Decisions with a zero resident cap must match LegacyRecompute's traffic exactly"
    );
}
