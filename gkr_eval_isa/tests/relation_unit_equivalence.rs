//! Phase 2 non-regression + consistency gate for the committed relation-unit
//! schedules (`cs/compiled_circuits/*_schedule_b16_gkr.json`).
//!
//! A corpus regeneration (tuned memetic GA, seeded from the Phase-1 incumbent) is
//! intentionally changing the committed schedules layer by layer in search of lower
//! `predicted_traffic`, so the old byte-identical golden asserts no longer apply.
//! This test instead checks that whatever the regenerated schedule looks like, it is
//! (a) internally consistent — a valid, truthfully-costed compiled program — and
//! (b) never worse than the pre-GA baseline captured in
//! `tests/golden/{stem}_schedule_b16_gkr.pretraffic.json` (`{ "layers": [
//! {"predicted_traffic", "floor"}, ... ] }`, one entry per DAG layer, in order).
//!
//! Per fixture, per layer:
//!   1. Consistency: the committed schedule `validate_circuit_schedule`s against the
//!      DAG, and recompiling the stored `(units, sites)` reproduces the persisted
//!      `predicted_traffic` exactly (the emitter/artifact cross-check carried over
//!      from Phase 1); `floor <= predicted_traffic`.
//!   2. Non-regression: `floor` is structural and must equal the baseline `floor`
//!      exactly; `predicted_traffic` must never exceed the baseline (the GA is
//!      seeded from the Phase-1 incumbent, so it can only match or improve).
//!   3. Improvement is informational per layer (some layers are already optimal —
//!      no strict-improvement assert there) but is enforced in aggregate: the
//!      corpus-wide sum of `predicted_traffic` must not regress versus baseline.
//!
//! Hand-editing a fixture or a `.pretraffic.json` baseline to make this pass
//! defeats its purpose — regenerate honestly instead.

mod common;
use common::{compiled_circuit_dir, load_fixture};

use std::path::PathBuf;

use gkr_eval_ir::{lower_dag, validate};
use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_layer, layer_needs_compile, load_committed_schedule,
};
use gkr_eval_isa::validate_circuit_schedule;

/// (layout fixture file, committed schedule stem) for all 11 cache-layout circuits —
/// the stem differs from the fixture stem only for `inits_and_teardowns` (fixture is
/// `..._preprocessed_layout_gkr.json`, schedule/baseline stem is `inits_and_teardowns`).
/// Mirrors `stage3_schedule_driven::COMMITTED_CORPUS`.
const COMMITTED_CORPUS: &[(&str, &str)] = &[
    ("add_sub_lui_auipc_mop_layout_gkr.json", "add_sub_lui_auipc_mop"),
    ("bigint_with_extended_control_layout_gkr.json", "bigint_with_extended_control"),
    ("blake2_g_function_layout_gkr.json", "blake2_g_function"),
    ("blake2_with_extended_control_layout_gkr.json", "blake2_with_extended_control"),
    ("inits_and_teardowns_preprocessed_layout_gkr.json", "inits_and_teardowns"),
    ("jump_branch_slt_layout_gkr.json", "jump_branch_slt"),
    ("keccak_special5_layout_gkr.json", "keccak_special5"),
    ("mem_subword_only_layout_gkr.json", "mem_subword_only"),
    ("mem_word_only_layout_gkr.json", "mem_word_only"),
    ("shift_binop_layout_gkr.json", "shift_binop"),
    ("unsigned_mul_div_layout_gkr.json", "unsigned_mul_div"),
];

/// Pre-GA per-layer `(predicted_traffic, floor)` baseline for one circuit, captured
/// from the committed schedules BEFORE the memetic-GA regeneration. The non-regression
/// floor.
#[derive(serde::Deserialize)]
struct PretrafficBaseline {
    layers: Vec<PretrafficLayer>,
}

#[derive(serde::Deserialize)]
struct PretrafficLayer {
    predicted_traffic: usize,
    floor: usize,
}

fn schedule_path(stem: &str) -> PathBuf {
    compiled_circuit_dir().join(format!("{stem}_schedule_b16_gkr.json"))
}

fn pretraffic_path(stem: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden")
        .join(format!("{stem}_schedule_b16_gkr.pretraffic.json"))
}

fn load_pretraffic(stem: &str) -> PretrafficBaseline {
    let p = pretraffic_path(stem);
    let bytes = std::fs::read(&p)
        .unwrap_or_else(|e| panic!("read pretraffic baseline {p:?}: {e} (must exist — regenerate it, don't skip this gate)"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse pretraffic baseline {p:?}: {e}"))
}

/// Full-corpus Phase-2 non-regression + consistency gate (see module docs).
#[test]
fn regenerated_schedules_are_consistent_and_non_regressed() {
    let mut layers_checked = 0usize;
    let mut recompiled = 0usize;
    let mut corpus_sum_new = 0usize;
    let mut corpus_sum_baseline = 0usize;

    for (name, stem) in COMMITTED_CORPUS {
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));

        // The (possibly GA-regenerated) committed schedule. `load_committed_schedule`
        // deserializes the `units:` form and would ERROR on a still-OLD `order:` file.
        let sched = load_committed_schedule(&schedule_path(stem))
            .unwrap_or_else(|e| panic!("[{name}] load_committed_schedule: {e:?}"));
        validate_circuit_schedule(&dag, &sched)
            .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));

        let baseline = load_pretraffic(stem);
        assert_eq!(
            sched.layers.len(),
            baseline.layers.len(),
            "[{name}] layer count drift vs pretraffic baseline"
        );

        let cross = build_cross_layer_field_map(&dag);
        let mut circuit_sum_new = 0usize;
        let mut circuit_sum_baseline = 0usize;

        for (li, (layer, ls)) in dag.layers.iter().zip(&sched.layers).enumerate() {
            let b = &baseline.layers[li];

            // (1) Consistency: floor <= predicted_traffic (soundness-adjacent sanity —
            // floor is a lower bound on any valid schedule's traffic).
            assert!(
                ls.floor <= ls.predicted_traffic || ls.units.is_empty(),
                "[{name}] L{li}: floor above predicted_traffic"
            );

            // (1') Consistency: recompiling the stored (units, sites) under Decisions
            // at the persisted budget reproduces predicted_traffic EXACTLY — proves
            // the persisted scalar is truthful, not stale (emitter/artifact
            // cross-check, GATE-D-equivalent applied to the reshaped artifact).
            if layer_needs_compile(ls.units.is_empty(), layer) {
                let decisions = SiteDecisions::new(ls.sites.iter().copied());
                let compiled = compile_layer(
                    layer,
                    &artifact.layers[li],
                    &artifact.scratch_space_mapping,
                    &cross,
                    ls,
                    sched.budget,
                    Some(&decisions),
                )
                .unwrap_or_else(|e| panic!("[{name}] L{li}: recompile failed: {e:?}"));
                assert_eq!(
                    compiled.stats.dram_traffic, ls.predicted_traffic,
                    "[{name}] L{li}: recompiled dram_traffic != persisted predicted_traffic"
                );
                recompiled += 1;
            }

            // (2) Non-regression vs the pre-GA baseline. `floor` is structural (a
            // property of the DAG layer, not the search), so it must be unchanged;
            // `predicted_traffic` must never exceed the baseline — the GA is seeded
            // from the Phase-1 incumbent, so it can only match or improve.
            assert_eq!(
                ls.floor, b.floor,
                "[{name}] L{li}: floor changed vs pretraffic baseline ({} -> {}) — floor is structural, this should be impossible",
                b.floor, ls.floor
            );
            assert!(
                ls.predicted_traffic <= b.predicted_traffic,
                "[{name}] L{li}: predicted_traffic regressed vs pretraffic baseline ({} -> {})",
                b.predicted_traffic,
                ls.predicted_traffic
            );

            circuit_sum_new += ls.predicted_traffic;
            circuit_sum_baseline += b.predicted_traffic;
            layers_checked += 1;
        }

        eprintln!(
            "[relation-unit-equiv] {name}: before={circuit_sum_baseline} after={circuit_sum_new} \
             delta={} ({} layers)",
            circuit_sum_new as i64 - circuit_sum_baseline as i64,
            sched.layers.len()
        );
        corpus_sum_new += circuit_sum_new;
        corpus_sum_baseline += circuit_sum_baseline;
    }

    assert!(layers_checked > 0, "vacuous: no layers checked");
    assert!(recompiled > 0, "vacuous: no layers recompiled");
    assert!(
        corpus_sum_new <= corpus_sum_baseline,
        "corpus-wide predicted_traffic regressed vs pretraffic baseline ({corpus_sum_baseline} -> {corpus_sum_new})"
    );
    eprintln!(
        "[relation-unit-equiv] {}/{} fixtures, {layers_checked} layers checked, {recompiled} recompiled, \
         corpus traffic before={corpus_sum_baseline} after={corpus_sum_new} delta={}",
        COMMITTED_CORPUS.len(),
        COMMITTED_CORPUS.len(),
        corpus_sum_new as i64 - corpus_sum_baseline as i64
    );
}
