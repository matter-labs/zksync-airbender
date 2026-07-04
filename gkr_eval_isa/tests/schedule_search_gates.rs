//! Task 6 gates: compile-in-loop scorer + search + `CircuitSchedule` producer.
//!
//! Covers the three scorer contracts from the Task-6 brief (`infeasible_ranks_last`,
//! `score_deterministic`, `small_search_roundtrip_add_sub` — the mini GATE-D), plus
//! the env-gated schedule-regeneration entry (`produce_all_schedules`) that moved
//! here from the deleted `tests/s3_gap_experiment.rs` producer (v1-schema version
//! deleted in Task 4; this is its schema-v2, library-backed successor).

mod common;

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{
    lower_dag, validate, validate_circuit_schedule, DagCircuit, FieldKind, ReadPlace,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_layer_with_policy, MaterializePolicy,
};
use gkr_eval_isa::schedule_search::genome::Genome;
use gkr_eval_isa::schedule_search::producer::produce_circuit_schedule;
use gkr_eval_isa::schedule_search::scorer::{objective_key, score, LayerCtx};
use gkr_eval_isa::schedule_search::search::SearchConfig;

use common::{compiled_circuit_dir, load_fixture, schedule_stem};

/// The real production budget convention (`*_schedule_b16_gkr.json`) — used ONLY by
/// the `#[ignore]`d regen entry point below, which this task does not actually run.
/// NOTE (known gap, see task-6-report.md): under the current `Decisions` emitter
/// admission model, add_sub L0's neutral genome needs budget ~40 to become feasible
/// at all (probed while writing this test: infeasible through budget 32, feasible at
/// 40); reaching production's aspirational 16 for this layer needs either a much
/// stronger search than this task's reimplementation or an emitter admission-model
/// improvement — both out of this task's scope (compile-in-loop wiring, not search-
/// quality/emitter tuning).
const REAL_BUDGET: usize = 16;
/// A generously large budget for tests that just need SOME feasible compile to compare
/// against (not a search-quality claim).
const GENEROUS_BUDGET: usize = 4096;
/// A budget the tiny (`pop=4, evals=40`) mini-GATE-D search reliably satisfies for
/// add_sub L0 (probed: feasible from budget 40 up; 64 leaves headroom) — see the
/// `REAL_BUDGET` doc above for why this isn't 16.
const SEARCH_TEST_BUDGET: usize = 64;
const ADD_SUB: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

/// Every compiled cache-layout GKR circuit fixture in `cs/compiled_circuits` (the
/// same list the deleted `s3_gap_experiment::ALL_FIXTURES` swept).
const ALL_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

fn load_dag(
    fixture: &str,
) -> (DagCircuit, GKRCircuitArtifact<BabyBearField>, HashMap<ReadPlace, FieldKind>) {
    let artifact = load_fixture(fixture);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{fixture}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{fixture}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    (dag, artifact, cross)
}

/// Infeasible (`BudgetBelowFloor` at budget 1) ranks strictly after any feasible score.
#[test]
fn infeasible_ranks_last() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];

    let feasible_ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, GENEROUS_BUDGET);
    let genome = Genome::neutral(feasible_ctx.n_order_keys(), feasible_ctx.n_sites());
    let feasible = score(&genome, &feasible_ctx);
    assert!(!feasible.infeasible, "add_sub L0 must be feasible at budget {GENEROUS_BUDGET}");

    let tight_ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, 1);
    let infeasible = score(&genome, &tight_ctx);
    assert!(infeasible.infeasible, "budget 1 must be BudgetBelowFloor on add_sub L0");

    assert!(
        objective_key(&feasible) < objective_key(&infeasible),
        "any feasible score must rank strictly before an infeasible one"
    );
    assert!(feasible < infeasible, "CandidateScore Ord must agree with objective_key");
}

/// `score()` is deterministic: same genome twice -> identical `CandidateScore`.
#[test]
fn score_deterministic() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let layer = &dag.layers[0];
    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, GENEROUS_BUDGET);

    // A non-neutral genome (perturbed order + biases) so determinism is checked on a
    // candidate that actually exercises admit/evict decisions, not the trivial seed.
    let mut genome = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    for (i, k) in genome.root_order_key.iter_mut().enumerate() {
        *k = ((i * 7919) % 1000) as f64 / 1000.0;
    }
    for (i, b) in genome.cache_priority.iter_mut().enumerate() {
        *b = (((i * 104729) % 2000) as f64 / 1000.0) - 1.0;
    }

    let a = score(&genome, &ctx);
    let b = score(&genome, &ctx);
    assert_eq!(a, b, "score() must be deterministic for a fixed genome");
    assert!(!a.infeasible, "perturbed genome must still be feasible at budget {GENEROUS_BUDGET}");
}

/// End-to-end smoke (mini GATE-D): tiny search (pop=4, evals=40) on add_sub produces
/// a `validate_circuit_schedule`-clean schedule whose per-layer `predicted_traffic`
/// equals an immediate recompile from the persisted `(order, sites)`.
#[test]
fn small_search_roundtrip_add_sub() {
    let (dag, artifact, cross) = load_dag(ADD_SUB);
    let cfg = SearchConfig { pop: 4, evals: 40, seed: 0 };
    let stem = schedule_stem(ADD_SUB);

    let mut sched = produce_circuit_schedule(&dag, &artifact, SEARCH_TEST_BUDGET, &cfg);
    // `produce_circuit_schedule` leaves `circuit` empty (see its doc: no fixture-name
    // metadata is derivable from `DagCircuit`/`GKRCircuitArtifact` alone) — the caller
    // stamps it, exactly as the real fixture-regen entry point below does.
    sched.circuit = stem.to_string();
    assert_eq!(sched.budget, SEARCH_TEST_BUDGET);
    validate_circuit_schedule(&dag, &sched).expect("search output must validate");
    assert!(
        sched.layers.iter().any(|l| !l.order.is_empty()),
        "add_sub must have at least one scheduled layer"
    );

    // Serde round-trip stays exact (f64 genes included).
    let json = serde_json::to_string(&sched).unwrap();
    let back: cs::gkr_compiler::dag_ir::CircuitSchedule = serde_json::from_str(&json).unwrap();
    assert_eq!(back, sched);

    // GATE-D: recompiling each searched layer from its persisted (order, sites) under
    // the same budget must reproduce predicted_traffic exactly.
    for (li, (layer, ls)) in dag.layers.iter().zip(&back.layers).enumerate() {
        if ls.order.is_empty() {
            continue;
        }
        let decisions = SiteDecisions::new(ls.sites.iter().copied());
        let compiled = compile_layer_with_policy(
            layer,
            &artifact.layers[li],
            &artifact.scratch_space_mapping,
            &cross,
            ls,
            SEARCH_TEST_BUDGET,
            MaterializePolicy::Decisions { decisions, budget: SEARCH_TEST_BUDGET },
        )
        .unwrap_or_else(|e| panic!("layer {li}: winning schedule failed to recompile: {e:?}"));
        assert_eq!(
            compiled.stats.dram_traffic, ls.predicted_traffic,
            "layer {li}: predicted_traffic must equal an immediate recompile"
        );
        assert!(ls.floor <= ls.predicted_traffic, "layer {li}: floor above achieved traffic");
        if li == 0 {
            println!(
                "mini GATE-D add_sub L0: predicted_traffic={} floor={} (pop={} evals={})",
                ls.predicted_traffic, ls.floor, cfg.pop, cfg.evals
            );
        }
    }
}

/// Env-gated schedule regeneration (moved from the deleted v1 producer in
/// `s3_gap_experiment.rs`): writes `cs/compiled_circuits/{stem}_schedule_b16_gkr.json`
/// for every fixture. `#[ignore]`d and additionally gated on `GKR_PRODUCE_SCHEDULES=1`
/// (and skipped in CI) so it only ever runs as an explicit, on-demand regen.
/// Search knobs come from `GKR_SCHEDULE_POP` / `GKR_SCHEDULE_EVALS` / `GKR_SCHEDULE_SEED`
/// (`search_config_from_env`). Output paths are anchored on `CARGO_MANIFEST_DIR`
/// (`common::compiled_circuit_dir`), so the write lands in `cs/compiled_circuits`
/// regardless of the invoking CWD (the CWD-relative `serialize_to_file` gotcha
/// applies to cs's own fixture generators, not this writer — but we still run this
/// from `cs/` by convention per the brief, matching `load_dag_sched`'s expectations).
#[test]
#[ignore = "on-demand artifact regen: set GKR_PRODUCE_SCHEDULES=1 and run with --ignored"]
fn produce_all_schedules() {
    if std::env::var("GKR_PRODUCE_SCHEDULES").is_err() || std::env::var("CI").is_ok() {
        eprintln!("skipping producer (set GKR_PRODUCE_SCHEDULES=1, not in CI)");
        return;
    }
    let cfg = gkr_eval_isa::schedule_search::search::search_config_from_env();
    for fixture in ALL_FIXTURES {
        let (dag, artifact, _cross) = load_dag(fixture);
        // Reverse trim order (review CA-2/#4 of the deleted v1 producer): the
        // `_preprocessed_layout_gkr.json` variant ends with `_layout_gkr.json` too, so
        // the broad trim must come SECOND — this yields `inits_and_teardowns`, matching
        // the committed `inits_and_teardowns_schedule_b16_gkr.json`. (NOT
        // `common::schedule_stem`, which does not strip `_preprocessed`.)
        let stem = fixture
            .trim_end_matches("_preprocessed_layout_gkr.json")
            .trim_end_matches("_layout_gkr.json");
        let mut sched = produce_circuit_schedule(&dag, &artifact, REAL_BUDGET, &cfg);
        sched.circuit = stem.to_string();
        let out = compiled_circuit_dir()
            .join(format!("{}_schedule_b{}_gkr.json", sched.circuit, REAL_BUDGET));
        let mut f = std::fs::File::create(&out).unwrap();
        serde_json::to_writer_pretty(&mut f, &sched).unwrap();
        eprintln!("wrote {}", out.display());
    }
}
