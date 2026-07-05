//! Task 8/8a/8b: b16 add_sub L0 `compile_layer`'s `decisions: Some(&SiteDecisions)` feasibility.
//!
//! Step-0 (findings in `.superpowers/sdd/task-8-report.md`) found `try_admit` had
//! no way to DECLINE an admission while capacity was free: the resident set
//! greedily filled the whole placement budget and starved the concurrent
//! evaluation temps, so every genome was `BudgetBelowFloor` at b16.
//!
//! Task 8a fixed this by capping the `Decisions` resident-admission budget at a
//! STATIC `budget - legacy_recompute_floor` derived once per `(layer, order)`
//! (`scorer::resident_cap_for_order` / `LayerCtx::resident_cap`, since deleted).
//!
//! Task 8b replaced that static pre-reservation with DEMAND-DRIVEN eviction
//! (`lower.rs`'s `DecisionsState`/`evict_to_fit`): residents are admitted against
//! the FULL placement budget and only evicted when an expression-temp allocation
//! actually needs the room, rather than reserving worst-case compute headroom for
//! the whole layer up front. `Decisions.budget` is now always the plain placement
//! budget — there is no separate cap to derive or degenerate. The tests below are
//! Task 8b's versions of the original Step-0/Task-8a probes: test 1 (the
//! load-bearing one) pins b16 feasibility + a traffic win over `decisions: None`;
//! test 2 replaces the deleted static-cap degeneracy check (`resident_cap ==
//! 0` at `budget == legacy_floor`) with the analogous demand-driven property: at
//! a budget with NO headroom above the `decisions: None` floor, `Decisions` must
//! still be feasible (temps always win eviction pressure against residents) and
//! must never do WORSE than `decisions: None`'s own traffic.
//!
//! Sub-project 3 note: the old materialization-policy enum and its legacy-recompute
//! case are gone (Task 2's public collapse). `compile_layer`'s `decisions: None` is
//! the uncached baseline these tests call "legacy" below; `Some(&SiteDecisions)` is
//! the residency machine formerly named `Decisions`.

mod common;

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{lower_dag, validate, DagCircuit, FieldKind, LayerSchedule, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::schedule_search::genome::Genome;
use gkr_eval_isa::schedule_search::scorer::{decode_schedule, score, LayerCtx};

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
/// (neutral) genome is FEASIBLE, and its traffic beats `decisions: None`'s at the
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

    let legacy_traffic = compile_layer(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &sched,
        BUDGET,
        None,
    )
    .unwrap_or_else(|e| panic!("decisions: None must be feasible at budget {BUDGET}: {e:?}"))
    .stats
    .dram_traffic;

    let decisions_score = score(&genome, &ctx);
    assert!(
        !decisions_score.infeasible,
        "Decisions must be feasible at budget {BUDGET} for add_sub L0 (demand-driven eviction)"
    );
    // Absolute pins (captured pre-migration; `decisions: None` ≡ the old legacy
    // recompute — Task 2 brief).
    assert_eq!(legacy_traffic, 59, "legacy (decisions: None) traffic pin");
    assert_eq!(decisions_score.dram_traffic, 43, "decisions(neutral) traffic pin");
    assert!(
        decisions_score.dram_traffic < legacy_traffic,
        "Decisions traffic ({}) must beat the decisions-None baseline's ({}) at budget {BUDGET}",
        decisions_score.dram_traffic,
        legacy_traffic
    );
    println!(
        "b16 add_sub L0: legacy traffic={legacy_traffic} decisions(neutral) traffic={} (budget={BUDGET})",
        decisions_score.dram_traffic,
    );
}

/// Demand-driven analogue of the deleted static-cap degeneracy test: at a budget
/// with almost NO headroom above `decisions: None`'s own peak live-cell width,
/// `Decisions` must still be feasible and must never do WORSE than
/// `decisions: None`'s own traffic (any resident that survives even briefly
/// before being evicted under pressure is a pure win, never a loss, since
/// eviction emits no instruction and the value is simply recomputed on the next
/// miss exactly as `decisions: None` always does).
///
/// NOT exactly `legacy_floor` (the literal zero-headroom point the deleted
/// static-cap test pinned): `evict_to_fit`'s `pending_reads` guard (see
/// `lower.rs`) can legitimately hold a resident's width a FEW cells past its
/// logical eviction point when a sibling child already queued a not-yet-emitted
/// read for it — the correctness-preserving cost of never underestimating
/// relative to `plan_placement` (see this crate's Task 8b design doc). A small,
/// fixed `+4` margin (one quad) comfortably absorbs that and is still a "no
/// meaningful headroom" budget for this exercise's purpose (also side-steps an
/// unrelated pre-existing `place.rs::clear_quad_for_ext` panic on non-4-aligned
/// budgets whose target-quad index computation doesn't account for a trailing
/// partial quad — out of this task's scope; see the Task 8b report's concerns).
#[test]
fn decisions_feasible_and_no_worse_than_legacy_near_zero_headroom() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];

    // Find `decisions: None`'s own peak live-cell width for the neutral-genome
    // order at a generously large probe budget (a real compile's `max_live_cells`,
    // not a binary-searched approximation).
    let probe_ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, 4096);
    let genome = Genome::neutral(probe_ctx.n_order_keys(), probe_ctx.n_sites());
    let sched = decode_schedule(&genome, &probe_ctx);
    let legacy_schedule = LayerSchedule {
        order: sched.order.clone(),
        sites: Vec::new(),
        predicted_traffic: 0,
        floor: 0,
    };
    let legacy_probe = compile_layer(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &legacy_schedule,
        4096,
        None,
    )
    .unwrap_or_else(|e| panic!("decisions: None must be feasible at a generous budget: {e:?}"));
    let legacy_floor = legacy_probe.stats.max_live_cells;

    // Re-run the None-decisions baseline AT its own floor (its own peak fits its own floor by
    // construction) as the traffic baseline `Decisions` must not exceed.
    let legacy_at_floor = compile_layer(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &legacy_schedule,
        legacy_floor,
        None,
    )
    .unwrap_or_else(|e| panic!("decisions: None must be feasible at its own floor: {e:?}"));

    let decisions = SiteDecisions::new(sched.sites.iter().copied());
    let decisions_at_floor = compile_layer(
        layer,
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        &sched,
        legacy_floor + 4,
        Some(&decisions),
    )
    .unwrap_or_else(|e| {
        panic!(
            "Decisions at near-zero headroom above the decisions-None floor ({legacy_floor}) must \
             still be feasible (demand-driven eviction always makes room for temps): {e:?}"
        )
    });

    // Absolute pins (captured pre-migration; `decisions: None` ≡ the old legacy
    // recompute — Task 2 brief).
    assert_eq!(legacy_floor, 8, "legacy floor (max_live_cells) pin");
    assert_eq!(legacy_at_floor.stats.dram_traffic, 59, "legacy_at_floor traffic pin");
    assert_eq!(decisions_at_floor.stats.dram_traffic, 47, "decisions_at_floor traffic pin");
    assert!(
        decisions_at_floor.stats.dram_traffic <= legacy_at_floor.stats.dram_traffic,
        "Decisions with zero headroom ({}) must not do WORSE than decisions-None ({})",
        decisions_at_floor.stats.dram_traffic,
        legacy_at_floor.stats.dram_traffic
    );
}
