mod s3_gap;

use s3_gap::driver::{oracle_available, run_oracle, Mode};
use s3_gap::instance::{distinct_live_values, extract_instance};

use std::collections::HashMap;
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, validate, DagCircuit, FieldKind, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};

// ── Fixture loading (copied verbatim from fwd_parity.rs:130-140) ──────────────

fn compiled_circuit_dir() -> PathBuf {
    // This test lives in the `gkr_eval_isa` crate; `cs/compiled_circuits` is at
    // `<workspace>/cs/compiled_circuits`, a sibling of this crate.
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

/// Deserialize one fixture JSON → `GKRCircuitArtifact<BabyBearField>`.
fn load_fixture(path: &PathBuf) -> Option<GKRCircuitArtifact<BabyBearField>> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

// ── load_layer_source ─────────────────────────────────────────────────────────

fn load_layer_source(
    fixture: &str,
) -> (DagCircuit, GKRCircuitArtifact<BabyBearField>, HashMap<ReadPlace, FieldKind>) {
    let artifact = load_fixture(&compiled_circuit_dir().join(fixture))
        .expect("fixture load failed: check compiled_circuits path");
    let dag = lower_dag(&artifact).expect("lower_dag failed");
    validate(&dag).expect("validate failed");
    let cross = build_cross_layer_field_map(&dag);
    (dag, artifact, cross)
}

// ── S3 gap smoke test — add_sub L0 ───────────────────────────────────────────

/// Smoke test for the S3 gap experiment fixture loaders + oracle driver.
///
/// Loads `add_sub_lui_auipc_mop_layout_gkr.json` layer 0, extracts the oracle
/// instance, and runs `Mode::J` at budget 16.
///
/// ## What this test determines
///
/// The oracle's within-stage capacity charge is intentionally over-strict for
/// cones with many folds (documented Task-4 limitation: per-stage transients SUM
/// rather than take a sequential max). add_sub L0 roots are arithmetic gates
/// (sums-of-products = multiple folds per cone), so the oracle MIGHT find L0
/// infeasible at budget 16 even though the real compiler compiles it at floor 8.
/// Determining this is the *point* of the smoke test — it tells us whether
/// Task 4 needs the per-stage-MAX relaxation before the full experiment (8c)
/// can produce a meaningful J for real layers.
///
/// ## Assertions
///
/// - Instance is non-empty (nodes + roots > 0) and oracle is available.
/// - The oracle ran and returned a parseable result (no tool error).
/// - If status == "optimal" at budget 16: the model handles real add_sub-L0 ✓.
/// - If status != "optimal" at budget 16: sweeps budgets [24,32,48,64,128] and
///   asserts at least one of them yields "optimal" (model + extraction correct,
///   just over-strict). Prints the budget cliff loudly.
#[test]
#[ignore = "S3 Phase-1 smoke: needs python3+ortools; run on demand with --ignored"]
fn s3_gap_add_sub_l0_oracle_smoke() {
    if !oracle_available() {
        eprintln!("[SMOKE] SKIP: python3+ortools absent");
        return;
    }

    let fixture = "add_sub_lui_auipc_mop_layout_gkr.json";
    let (dag, artifact, cross) = load_layer_source(fixture);
    let layer = &dag.layers[0];

    let budget = 16usize;
    let inst = extract_instance(layer, &cross, budget);

    // Basic non-emptiness assertions: fixture + extraction must produce real data.
    assert!(!inst.nodes.is_empty(), "instance must have nodes");
    assert!(!inst.roots.is_empty(), "instance must have roots");

    let live = distinct_live_values(&inst);
    eprintln!(
        "[SMOKE] add_sub-L0 @ budget {budget}: nodes={} roots={} live_values≈{}",
        inst.nodes.len(),
        inst.roots.len(),
        live,
    );

    // Also print C (compile_layer result) for context.
    match compile_layer(layer, &artifact.layers[0], &artifact.scratch_space_mapping, &cross, budget) {
        Ok(cl) => eprintln!("[SMOKE] compile_layer traffic={}", cl.stats.dram_traffic),
        Err(e) => eprintln!("[SMOKE] compile_layer error (expected if below floor): {e:?}"),
    }

    let result = run_oracle(&inst, Mode::J, 0.01, 300)
        .expect("oracle must run and return a parseable result");

    eprintln!(
        "[SMOKE] J @budget={budget}: status={} traffic={} wall_ms={}",
        result.status, result.traffic, result.wall_ms,
    );

    if result.status == "optimal" {
        eprintln!("[SMOKE] J OPTIMAL at budget 16 — Task-4 over-strictness is NOT a blocker for add_sub-L0");
        // If optimal at 16, we're done — the model handles the real layer.
    } else {
        // Infeasible (or feasible/timeout) at budget 16.
        // Sweep to find the cliff — the smallest budget at which J becomes optimal.
        eprintln!(
            "[SMOKE] J NOT optimal at budget 16 (status={}). \
             Task-4 over-strictness IS a blocker for add_sub-L0 at real budget. \
             Sweeping budgets to find cliff...",
            result.status
        );

        let sweep_budgets = [24usize, 32, 48, 64, 128];
        let mut cliff_budget: Option<usize> = None;

        for &b in &sweep_budgets {
            let inst_b = extract_instance(layer, &cross, b);
            let r = run_oracle(&inst_b, Mode::J, 0.01, 300)
                .expect("oracle must run at sweep budget");
            eprintln!("[SMOKE]   J @budget={b}: status={} traffic={}", r.status, r.traffic);
            if r.status == "optimal" && cliff_budget.is_none() {
                cliff_budget = Some(b);
            }
        }

        match cliff_budget {
            Some(b) => {
                eprintln!(
                    "[SMOKE] BUDGET CLIFF: J becomes optimal at budget {b} (real floor=8 budget=16 is over-strict). \
                     Task-4 per-stage-MAX relaxation needed before 8c experiment is meaningful."
                );
            }
            None => {
                eprintln!(
                    "[SMOKE] J NOT optimal at ANY sweep budget up to 128. \
                     Model or extraction may be incorrect — investigate before proceeding."
                );
            }
        }

        // Assert that SOME budget in the sweep yields optimal.
        // This confirms: model + extraction are correct; the issue is over-strictness only.
        assert!(
            cliff_budget.is_some(),
            "J must be optimal at some budget in [24,32,48,64,128]; \
             if all infeasible, the model or extraction is wrong"
        );
    }
}
