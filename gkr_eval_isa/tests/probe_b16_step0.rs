//! Task-8 Step-0 probes (all `#[ignore]`d, run explicitly): why is add_sub L0
//! `BudgetBelowFloor` at production budget 16 under `MaterializePolicy::Decisions`?
//! Hypotheses tested (findings in .superpowers/sdd/task-8-report.md):
//!  (a) placement floor moved with the simplified DAG (policy-independent)
//!      -> REFUTED: `LegacyRecompute` compiles at every budget down to 8.
//!  (b) Decisions admission inflates liveness beyond placement capacity
//!      -> CONFIRMED: `try_admit` admits unconditionally while resident width
//!      fits `budget` (priority genes only rank EVICTION victims), so the
//!      resident set greedily fills the whole budget and the concurrent
//!      evaluation temps push the placement floor to ~budget+3 at EVERY
//!      budget until all reused values fit with headroom to spare (~b40).
//!      The split-budget probe shows placement=16 becomes feasible once the
//!      resident budget is capped <= 8 (traffic 36 vs legacy 59).
//!  (c) search quality -> REFUTED: no genome can decline admission, so a
//!      pop=32/evals=8000 search is still infeasible at b16.

mod common;

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{
    lower_dag, validate, DagCircuit, FieldKind, ReadPlace,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_layer_with_policy, MaterializePolicy,
};
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::schedule_search::genome::Genome;
use gkr_eval_isa::schedule_search::scorer::{decode_schedule, LayerCtx};
use gkr_eval_isa::schedule_search::search::{search_layer, SearchConfig};

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

fn describe(r: &Result<usize, CompileError>) -> String {
    match r {
        Ok(traffic) => format!("OK traffic={traffic}"),
        Err(CompileError::BudgetBelowFloor { floor, budget }) => {
            format!("BudgetBelowFloor floor={floor} budget={budget}")
        }
        Err(e) => format!("ERR {e:?}"),
    }
}

#[test]
#[ignore = "step-0 probe, run explicitly"]
fn probe_budget_sweep_legacy_vs_decisions() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];

    for budget in [8usize, 12, 16, 20, 24, 28, 32, 36, 40, 48, 64] {
        let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, budget);
        let genome = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
        let sched = decode_schedule(&genome, &ctx);

        let legacy = compile_layer_with_policy(
            layer,
            &artifact.layers[0],
            &artifact.scratch_space_mapping,
            &cross,
            &sched,
            budget,
            MaterializePolicy::LegacyRecompute,
        )
        .map(|c| c.stats.dram_traffic);

        let decisions = SiteDecisions::new(sched.sites.iter().copied());
        let dec = compile_layer_with_policy(
            layer,
            &artifact.layers[0],
            &artifact.scratch_space_mapping,
            &cross,
            &sched,
            budget,
            MaterializePolicy::Decisions { decisions, budget },
        )
        .map(|c| c.stats.dram_traffic);

        println!(
            "budget={budget:>3}  legacy: {:<40}  decisions(neutral): {}",
            describe(&legacy),
            describe(&dec)
        );
    }
}

/// Decouple resident budget from placement budget: placement fixed at 16, resident
/// admission budget swept below it. If feasibility appears once the resident set is
/// forced to leave working-set headroom, the (b) mechanism is confirmed and the
/// "reserve headroom in try_admit" emitter fix is validated in principle.
#[test]
#[ignore = "step-0 probe, run explicitly"]
fn probe_split_resident_budget_b16() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];
    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, 16);
    let genome = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    let sched = decode_schedule(&genome, &ctx);

    for resident_budget in [0usize, 2, 4, 6, 8, 10, 12, 14, 16] {
        let decisions = SiteDecisions::new(sched.sites.iter().copied());
        let dec = compile_layer_with_policy(
            layer,
            &artifact.layers[0],
            &artifact.scratch_space_mapping,
            &cross,
            &sched,
            16,
            MaterializePolicy::Decisions { decisions, budget: resident_budget },
        )
        .map(|c| c.stats.dram_traffic);
        println!("placement=16 resident_budget={resident_budget:>2}  {}", describe(&dec));
    }
}

#[test]
#[ignore = "step-0 probe, run explicitly"]
fn probe_big_search_b16() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];
    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, 16);
    println!(
        "add_sub L0: units={} sites={} floor={}",
        ctx.n_order_keys(),
        ctx.n_sites(),
        ctx.floor
    );
    // search_layer panics if best is infeasible; catch it so the probe reports.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let cfg = SearchConfig { pop: 32, evals: 8000, seed: 0 };
        search_layer(&ctx, &cfg)
    }));
    match result {
        Ok(outcome) => println!(
            "b16 search FEASIBLE: predicted_traffic={} floor={} compiles={} wall={:.1}s",
            outcome.schedule.predicted_traffic,
            outcome.schedule.floor,
            outcome.compiles,
            outcome.wall.as_secs_f64()
        ),
        Err(_) => println!("b16 search INFEASIBLE even at pop=32 evals=8000"),
    }
}
