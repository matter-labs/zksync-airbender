//! Phase 2 memetic-GA gates (Task 1): real-fixture tests for the generational
//! GA driver and its memetic local-descent operator. These need a concrete
//! `LayerCtx` (a compiled fixture layer), so they live here rather than in the
//! lib unit module — the `load_dag`/`LayerCtx::new` loader below mirrors
//! `schedule_search_gates.rs`. Pure-operator tests (blx_alpha / crossover /
//! mutate / tournament) stay in the `search.rs` `#[cfg(test)]` module.
//!
//! All configs are TINY (`pop=8, evals=400`) on purpose: the 20k default would
//! turn each of these into a multi-minute compile run.

mod common;

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{lower_dag, validate, DagCircuit, FieldKind, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::schedule_search::genome::Genome;
use gkr_eval_isa::schedule_search::scorer::{
    decode_schedule, genome_from_schedule, objective_key, score, LayerCtx,
};
use gkr_eval_isa::schedule_search::search::{
    ga_local_descent, optimize_from_population, seeded_population, SearchConfig,
};

use common::load_fixture;

/// The pinned production cache budget (b16), feasible for add_sub L0.
const REAL_BUDGET: usize = 16;
const ADD_SUB: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

/// Tiny GA config for the real-fixture gates (NOT the 20k default).
fn tiny_cfg() -> SearchConfig {
    SearchConfig { pop: 8, evals: 400, seed: 0, ..SearchConfig::default() }
}

fn load_dag(
    fixture: &str,
) -> (DagCircuit, GKRCircuitArtifact<BabyBearField>, HashMap<ReadPlace, FieldKind>) {
    let artifact = load_fixture(fixture);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{fixture}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{fixture}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    (dag, artifact, cross)
}

/// `ga_local_descent` never returns a candidate worse (by `objective_key`) than
/// its input: it only adopts strictly-improving neighbors and otherwise stops.
#[test]
fn ga_local_descent_never_worsens() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let ctx = LayerCtx::new(&dag.layers[0], &artifact.layers[0], &artifact, &cross, REAL_BUDGET);

    // A random (non-neutral) start so descent actually has neighbors to try.
    let start = seeded_population(&ctx, 8, 0).into_iter().last().expect("seeded tail");
    let start_score = score(&start, &ctx);

    let mut evals = 0usize;
    let (_g, out_score) = ga_local_descent(&ctx, start.clone(), start_score, 4, &mut evals, 400);

    assert!(
        objective_key(&out_score) <= objective_key(&start_score),
        "local descent worsened the candidate: {out_score:?} > {start_score:?}"
    );
    assert!(evals > 0, "descent must have scored at least one neighbor batch");
}

/// The GA is deterministic: same `seed` + `cfg` + `ctx` -> identical winner.
#[test]
fn optimize_from_population_is_deterministic() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let ctx = LayerCtx::new(&dag.layers[0], &artifact.layers[0], &artifact, &cross, REAL_BUDGET);
    let cfg = tiny_cfg();

    let seeds_a = seeded_population(&ctx, cfg.pop.min(cfg.evals), cfg.seed);
    let seeds_b = seeded_population(&ctx, cfg.pop.min(cfg.evals), cfg.seed);
    let a = optimize_from_population(&ctx, seeds_a, &cfg);
    let b = optimize_from_population(&ctx, seeds_b, &cfg);

    assert_eq!(a.best_genome, b.best_genome, "GA best_genome must be deterministic");
    assert_eq!(a.best_score, b.best_score, "GA best_score must be deterministic");
    assert_eq!(a.evals, b.evals, "GA eval count must be deterministic");
}

/// The GA never does worse than the neutral seed's own compile (elitism keeps
/// the neutral genome, which `seeded_population` always includes first).
#[test]
fn ga_beats_or_matches_neutral_seed() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let ctx = LayerCtx::new(&dag.layers[0], &artifact.layers[0], &artifact, &cross, REAL_BUDGET);

    let neutral = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    let neutral_score = score(&neutral, &ctx);
    assert!(!neutral_score.infeasible, "neutral seed must be feasible at budget {REAL_BUDGET}");

    let cfg = tiny_cfg();
    let seeds = seeded_population(&ctx, cfg.pop.min(cfg.evals), cfg.seed);
    let opt = optimize_from_population(&ctx, seeds, &cfg);

    assert!(!opt.best_score.infeasible, "GA winner must be feasible");
    assert!(
        opt.best_score.dram_traffic <= neutral_score.dram_traffic,
        "GA traffic {} exceeded the neutral seed's {}",
        opt.best_score.dram_traffic,
        neutral_score.dram_traffic
    );
    println!(
        "ga_beats_or_matches_neutral_seed: neutral={} ga_best={} delta={} (pop={} evals={})",
        neutral_score.dram_traffic,
        opt.best_score.dram_traffic,
        neutral_score.dram_traffic as i64 - opt.best_score.dram_traffic as i64,
        cfg.pop,
        cfg.evals
    );
}

/// `genome_from_schedule` inverts `decode_schedule`: a genome decoded to a
/// schedule, re-inverted, then decoded again reproduces the same schedule
/// (unit order + per-site priorities), so an incumbent is scored as itself.
#[test]
fn genome_from_schedule_round_trips() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let ctx = LayerCtx::new(&dag.layers[0], &artifact.layers[0], &artifact, &cross, REAL_BUDGET);

    // A non-trivial genome: reversed unit keys + a deterministic priority sweep.
    let mut g0 = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    let n = g0.root_order_key.len();
    let denom = n.max(1) as f64;
    for (i, k) in g0.root_order_key.iter_mut().enumerate() {
        *k = (n - 1 - i) as f64 / denom;
    }
    for (i, p) in g0.cache_priority.iter_mut().enumerate() {
        *p = (((i * 37) % 200) as f64 / 100.0) - 1.0;
    }

    let ls = decode_schedule(&g0, &ctx);
    let g1 = genome_from_schedule(&ls, &ctx);
    let ls2 = decode_schedule(&g1, &ctx);

    assert_eq!(ls2.units, ls.units, "unit order must round-trip");
    assert_eq!(ls2.sites, ls.sites, "site priorities must round-trip");
    // Scoring the inverted genome reproduces the original's compile exactly.
    assert_eq!(score(&g1, &ctx), score(&g0, &ctx), "incumbent scores as itself");
}
