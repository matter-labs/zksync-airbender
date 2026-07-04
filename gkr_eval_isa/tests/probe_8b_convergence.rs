//! Task 8b review probe: is the +79 corpus-traffic regression (bigint L0 +18,
//! blake2_ext L0 +54) search under-convergence, or genuine `never_readmit`
//! exile loss?
//!
//! `#[ignore]`d — on-demand, not part of the default suite (a 100k-200k eval
//! search on blake2_ext L0 takes minutes). Run with:
//!   RUSTFLAGS="-Awarnings" cargo test -p gkr_eval_isa --release --test \
//!     probe_8b_convergence -- --ignored --nocapture
//!
//! Findings are appended to `.superpowers/sdd/task-8-report.md` (Task 8b
//! section) rather than asserted here — this is an investigation probe, not a
//! regression gate.

//! Note: a companion eviction-accounting probe (forced-eviction /
//! `never_readmit`-blocked-readmission counts on these same two layers) was
//! also run for this investigation via TEMPORARY atomic counters patched into
//! `lower.rs::try_admit`/`evict_to_fit`, then reverted — those counters are
//! not shipped (probe-only instrumentation, not a semantics change). Results
//! are recorded in `.superpowers/sdd/task-8-report.md`'s Task 8b section, not
//! re-derivable from this file alone.

mod common;
use common::load_fixture;

use cs::gkr_compiler::dag_ir::{lower_dag, validate};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::schedule_search::scorer::LayerCtx;
use gkr_eval_isa::schedule_search::search::{search_layer, SearchConfig};

const REAL_BUDGET: usize = 16;

fn probe_layer0(fixture: &str, evals: usize, pop: usize) {
    let artifact = load_fixture(fixture);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{fixture}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{fixture}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];

    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, REAL_BUDGET);
    let cfg = SearchConfig { pop, evals, seed: 0 };
    let t0 = std::time::Instant::now();
    let outcome = search_layer(&ctx, &cfg);
    let wall = t0.elapsed();
    eprintln!(
        "[probe_8b] {fixture} L0: pop={pop} evals(cap)={evals} actual_evals={} \
         predicted_traffic={} floor={} wall={:.1}s compiles={}",
        evals, outcome.schedule.predicted_traffic, outcome.schedule.floor, wall.as_secs_f64(), outcome.compiles,
    );
}

#[test]
#[ignore = "on-demand convergence probe; run with --ignored --release"]
fn probe_bigint_l0_100k() {
    probe_layer0("bigint_with_extended_control_layout_gkr.json", 100_000, 32);
}

#[test]
#[ignore = "on-demand convergence probe; run with --ignored --release"]
fn probe_blake2_ext_l0_100k() {
    probe_layer0("blake2_with_extended_control_layout_gkr.json", 100_000, 64);
}

#[test]
#[ignore = "on-demand convergence probe; run with --ignored --release"]
fn probe_blake2_ext_l0_200k() {
    probe_layer0("blake2_with_extended_control_layout_gkr.json", 200_000, 64);
}

/// Rule out "stuck in the same local optimum" rather than "converged budget
/// doesn't matter": bigger population + a different RNG seed.
#[test]
#[ignore = "on-demand convergence probe; run with --ignored --release"]
fn probe_blake2_ext_l0_multiseed() {
    let artifact = load_fixture("blake2_with_extended_control_layout_gkr.json");
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];
    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, REAL_BUDGET);
    for (pop, seed) in [(64usize, 1u64), (128, 7), (256, 42)] {
        let cfg = SearchConfig { pop, evals: 150_000, seed };
        let t0 = std::time::Instant::now();
        let outcome = search_layer(&ctx, &cfg);
        eprintln!(
            "[probe_8b multiseed] pop={pop} seed={seed} predicted_traffic={} floor={} \
             compiles={} wall={:.1}s",
            outcome.schedule.predicted_traffic,
            outcome.schedule.floor,
            outcome.compiles,
            t0.elapsed().as_secs_f64()
        );
    }
}

#[test]
#[ignore = "on-demand convergence probe; run with --ignored --release"]
fn probe_bigint_l0_multiseed() {
    let artifact = load_fixture("bigint_with_extended_control_layout_gkr.json");
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];
    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, REAL_BUDGET);
    for (pop, seed) in [(32usize, 1u64), (64, 7), (128, 42)] {
        let cfg = SearchConfig { pop, evals: 150_000, seed };
        let t0 = std::time::Instant::now();
        let outcome = search_layer(&ctx, &cfg);
        eprintln!(
            "[probe_8b multiseed] pop={pop} seed={seed} predicted_traffic={} floor={} \
             compiles={} wall={:.1}s",
            outcome.schedule.predicted_traffic,
            outcome.schedule.floor,
            outcome.compiles,
            t0.elapsed().as_secs_f64()
        );
    }
}
