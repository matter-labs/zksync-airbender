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
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::schedule_search::genome::Genome;
use gkr_eval_isa::schedule_search::producer::produce_circuit_schedule;
use gkr_eval_isa::schedule_search::scorer::{objective_key, score, LayerCtx};
use gkr_eval_isa::schedule_search::search::SearchConfig;

use common::{compiled_circuit_dir, load_fixture, schedule_stem};

/// The real production budget convention (`*_schedule_b16_gkr.json`) — used by the
/// `#[ignore]`d regen entry point below AND (Task 8a/8b) the mini GATE-D roundtrip.
/// NOTE (Task 8a, supersedes the old task-6-report.md "known gap" note): b16 add_sub
/// L0 was `Decisions`-admission-infeasible for EVERY genome because `try_admit` had
/// no way to decline an admission while capacity was free — the resident set
/// greedily filled the whole placement budget and starved the concurrent evaluation
/// temps. Task 8a fixed this with a static resident cap (`budget -
/// legacy_recompute_floor`); Task 8b replaced that cap with demand-driven eviction
/// (`lower.rs`'s `DecisionsState`/`evict_to_fit`, `.superpowers/sdd/task-8-report.md`)
/// that evicts residents on-demand under temp pressure instead of pre-reserving a
/// fixed headroom — `Decisions.budget` is now the plain placement budget. 16 is
/// feasible and is the pinned budget for both the regen entry point and the mini
/// GATE-D search below.
const REAL_BUDGET: usize = 16;
/// A generously large budget for tests that just need SOME feasible compile to compare
/// against (not a search-quality claim).
const GENEROUS_BUDGET: usize = 4096;
/// The mini (`pop=4, evals=40`) GATE-D search now runs at the real production budget
/// (Task 8a unblocked b16 — see `REAL_BUDGET`'s doc).
const SEARCH_TEST_BUDGET: usize = REAL_BUDGET;
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
    "unified_reduced_machine_layout_gkr.json",
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
    let cfg = SearchConfig { pop: 4, evals: 40, seed: 0, ..SearchConfig::default() };
    let stem = schedule_stem(ADD_SUB);

    let mut sched = produce_circuit_schedule(&dag, &artifact, SEARCH_TEST_BUDGET, &cfg, None);
    // `produce_circuit_schedule` leaves `circuit` empty (see its doc: no fixture-name
    // metadata is derivable from `DagCircuit`/`GKRCircuitArtifact` alone) — the caller
    // stamps it, exactly as the real fixture-regen entry point below does.
    sched.circuit = stem.to_string();
    assert_eq!(sched.budget, SEARCH_TEST_BUDGET);
    validate_circuit_schedule(&dag, &sched).expect("search output must validate");
    assert!(
        sched.layers.iter().any(|l| !l.units.is_empty()),
        "add_sub must have at least one scheduled layer"
    );

    // Serde round-trip: structure + integer fields exact; priority genes are
    // continuous f64 and serde_json's DEFAULT parser is not guaranteed 1-ULP-exact
    // (it was, trivially, when priorities were dyadic — the tuned GA now emits
    // arbitrary f64). The property that actually matters — a loaded schedule
    // recompiles to its recorded traffic — is asserted in the GATE-D loop below
    // (on `back`) and by the production load gates; a sub-ULP priority shift never
    // reorders a cache decision (all fixture gates pass on the loaded values).
    let json = serde_json::to_string(&sched).unwrap();
    let back: cs::gkr_compiler::dag_ir::CircuitSchedule = serde_json::from_str(&json).unwrap();
    assert_eq!(back.circuit, sched.circuit);
    assert_eq!(back.budget, sched.budget);
    assert_eq!(back.layers.len(), sched.layers.len());
    for (b, s) in back.layers.iter().zip(&sched.layers) {
        assert_eq!(b.units, s.units, "units must round-trip exactly");
        assert_eq!(b.predicted_traffic, s.predicted_traffic);
        assert_eq!(b.floor, s.floor);
        assert_eq!(b.sites.len(), s.sites.len());
        for ((bk, bv), (sk, sv)) in b.sites.iter().zip(&s.sites) {
            assert_eq!(bk, sk, "site keys must round-trip exactly");
            assert!((bv - sv).abs() < 1e-9, "site priority round-trip within tol: {bv} vs {sv}");
        }
    }

    // GATE-D: recompiling each searched layer from its persisted (order, sites) under
    // the same budget must reproduce predicted_traffic exactly.
    for (li, (layer, ls)) in dag.layers.iter().zip(&back.layers).enumerate() {
        if ls.units.is_empty() {
            continue;
        }
        // Task 8b: `score()` compiled the winning schedule with `Decisions.budget ==
        // SEARCH_TEST_BUDGET` directly (demand-driven eviction, no separate
        // resident-admission cap to re-derive) — reproducing `predicted_traffic`
        // exactly just means recompiling at that same budget.
        let decisions = SiteDecisions::new(ls.sites.iter().copied());
        let compiled = compile_layer(
            layer,
            &artifact.layers[li],
            &artifact.scratch_space_mapping,
            &cross,
            ls,
            SEARCH_TEST_BUDGET,
            Some(&decisions),
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
    // Optional substring filter (`GKR_SCHEDULE_ONLY=jump_branch,add_sub`): regenerate
    // only the matching fixtures. The full-corpus sweep runs a production-budget
    // search per layer for EVERY circuit just to conclude "kept, no rewrite" on the
    // unchanged ones — when only specific circuits changed structurally, filter to
    // those (use `validate_all_committed_schedules` below to enumerate them).
    let only = std::env::var("GKR_SCHEDULE_ONLY").ok();
    for fixture in ALL_FIXTURES {
        if let Some(filter) = &only {
            if !filter.split(',').any(|s| !s.trim().is_empty() && fixture.contains(s.trim())) {
                eprintln!("skipped {fixture} (GKR_SCHEDULE_ONLY={filter})");
                continue;
            }
        }
        let (dag, artifact, _cross) = load_dag(fixture);
        // Reverse trim order (review CA-2/#4 of the deleted v1 producer): the
        // `_preprocessed_layout_gkr.json` variant ends with `_layout_gkr.json` too, so
        // the broad trim must come SECOND — this yields `inits_and_teardowns`, matching
        // the committed `inits_and_teardowns_schedule_b16_gkr.json`. (NOT
        // `common::schedule_stem`, which does not strip `_preprocessed`.)
        let stem = fixture
            .trim_end_matches("_preprocessed_layout_gkr.json")
            .trim_end_matches("_layout_gkr.json");
        let out = compiled_circuit_dir()
            .join(format!("{stem}_schedule_b{REAL_BUDGET}_gkr.json"));
        // Load the OLD committed schedule BEFORE overwriting and seed the GA with
        // it: elitism then guarantees the regenerated schedule never regresses
        // below the persisted traffic (non-regression by construction), while the
        // tuned GA improves where it can. A missing committed file (should not
        // happen — the corpus is fully committed) degrades to seed-from-scratch.
        // A STALE incumbent (fails `validate_circuit_schedule` against the current
        // DAG, e.g. after a circuit-semantics change) must also degrade to
        // seed-from-scratch: `search_layer`'s post-hoc non-regression floor keeps the
        // incumbent's RAW structure whenever its genome projection scores <= the GA
        // result — but the projection silently drops stale sites, so a kept stale
        // incumbent round-trips its invalid site into the output and fails the
        // producer's final validation.
        let incumbent = gkr_eval_isa::fwd::compile::load_committed_schedule(&out)
            .ok()
            .filter(|s| match validate_circuit_schedule(&dag, s) {
                Ok(()) => true,
                Err(e) => {
                    eprintln!("NOTE: stale incumbent for {stem} ({e}); seeding from scratch");
                    false
                }
            });
        if incumbent.is_none() {
            eprintln!("NOTE: no (valid) committed incumbent for {stem}; seeding from scratch");
        }
        let mut sched =
            produce_circuit_schedule(&dag, &artifact, REAL_BUDGET, &cfg, incumbent.as_ref());
        sched.circuit = stem.to_string();

        // Persist ONLY on a strict corpus-traffic improvement over the committed
        // incumbent. Rationale (RR): the search never regresses (per-layer floor),
        // so re-running compounds — but re-serializing a NON-improving schedule
        // still churns the committed bytes, because the incumbent was loaded through
        // serde_json whose default f64 parser is not 1-ULP-exact, so a kept
        // (floored) layer round-trips to slightly different priority bytes at
        // identical traffic. Skipping the write when traffic did not strictly
        // improve makes regen IDEMPOTENT: once no circuit improves, no file is
        // rewritten, so iterating to a fixed point terminates (byte-stable) and the
        // committed corpus is self-verifying (`regen == no-op`).
        let new_traffic: usize = sched.layers.iter().map(|l| l.predicted_traffic).sum();
        let old_traffic =
            incumbent.as_ref().map(|s| s.layers.iter().map(|l| l.predicted_traffic).sum::<usize>());
        match old_traffic {
            Some(old) if new_traffic >= old => {
                eprintln!("kept {stem} (traffic {new_traffic} >= committed {old}; no rewrite)");
            }
            _ => {
                let mut f = std::fs::File::create(&out).unwrap();
                serde_json::to_writer_pretty(&mut f, &sched).unwrap();
                eprintln!(
                    "wrote {} (traffic {new_traffic}{})",
                    out.display(),
                    old_traffic.map(|o| format!(" < committed {o}")).unwrap_or_default()
                );
            }
        }
    }
}

/// Diagnostic sweep: validate EVERY committed `*_schedule_b{REAL_BUDGET}_gkr.json`
/// against its (re)generated layout fixture WITHOUT aborting at the first stale
/// circuit (the corpus-loop gates panic at the first failure, masking later ones).
/// Prints one PASS/STALE line per stem and fails listing all stale stems — feed
/// those to `GKR_SCHEDULE_ONLY` for a targeted `produce_all_schedules` run.
#[test]
#[ignore = "diagnostic: run explicitly with --ignored to enumerate stale schedules"]
fn validate_all_committed_schedules() {
    let mut stale: Vec<String> = Vec::new();
    for fixture in ALL_FIXTURES {
        let (dag, _artifact, _cross) = load_dag(fixture);
        let stem = fixture
            .trim_end_matches("_preprocessed_layout_gkr.json")
            .trim_end_matches("_layout_gkr.json");
        let path = compiled_circuit_dir().join(format!("{stem}_schedule_b{REAL_BUDGET}_gkr.json"));
        let result = gkr_eval_isa::fwd::compile::load_committed_schedule(&path)
            .map_err(|e| format!("{e:?}"))
            .and_then(|sched| validate_circuit_schedule(&dag, &sched));
        match result {
            Ok(()) => eprintln!("PASS  {stem}"),
            Err(e) => {
                eprintln!("STALE {stem}: {e}");
                stale.push(stem.to_string());
            }
        }
    }
    assert!(stale.is_empty(), "stale committed schedules: {stale:?}");
}
