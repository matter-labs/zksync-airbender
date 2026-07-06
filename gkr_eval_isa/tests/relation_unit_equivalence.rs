//! Phase 1 golden-equivalence regression: the regenerated relation-unit-shaped
//! schedules (`cs/compiled_circuits/*_schedule_b16_gkr.json`, now `units:`) must be
//! **content-identical** to the pre-Phase-1 flat-`order` schedules — only the JSON
//! SHAPE changed (`order: Vec<RootId>` → `units: Vec<RelationUnit>`).
//!
//! The golden snapshots in `tests/golden/*.golden.json` were captured (jq) from the
//! OLD committed fixtures BEFORE regeneration and pin, per layer, the flat atom
//! `order`, the `sites` genome, `predicted_traffic`, and `floor`. This test loads the
//! REGENERATED (new-shape) committed fixture, validates it against the DAG, and
//! asserts:
//!   1. `LayerSchedule::atom_order()` (flattened `units`) == golden flat `order`;
//!   2. `sites` == golden `sites` (typed f64 compare — the corpus priorities are all
//!      dyadic, exact in f64, so this is an exact byte-for-content check);
//!   3. `predicted_traffic` / `floor` == golden;
//!   4. recompiling each layer's stored `(units, sites)` under `Decisions` at the
//!      persisted budget reproduces `predicted_traffic` EXACTLY (emitter/artifact
//!      cross-check — a GATE-D-equivalent applied to the reshaped artifact).
//!
//! This is the Phase-1 gate. NEVER weaken it or hand-edit a fixture to make it pass.

mod common;
use common::{compiled_circuit_dir, load_fixture};

use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, validate, validate_circuit_schedule, SiteKey};
use gkr_eval_isa::fwd::compile::decisions::SiteDecisions;
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_layer, layer_needs_compile, load_committed_schedule,
};

/// (layout fixture file, committed schedule stem) for all 11 cache-layout circuits —
/// the stem differs from the fixture stem only for `inits_and_teardowns` (fixture is
/// `..._preprocessed_layout_gkr.json`, schedule/golden stem is `inits_and_teardowns`).
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

/// The golden snapshot of ONE circuit's pre-Phase-1 schedule content. Deserialized
/// with the SAME typed `(SiteKey, f64)` site shape the live schedule uses, so `sites`
/// compares as typed f64 pairs (no int-vs-float `serde_json::Value` pitfall; the
/// corpus priorities are all dyadic rationals that round-trip exactly).
#[derive(serde::Deserialize)]
struct GoldenCircuit {
    budget: usize,
    circuit: String,
    layers: Vec<GoldenLayer>,
}

#[derive(serde::Deserialize)]
struct GoldenLayer {
    /// The pre-Phase-1 flat atom execution order (bare `RootId` integers).
    order: Vec<u32>,
    sites: Vec<(SiteKey, f64)>,
    predicted_traffic: usize,
    floor: usize,
}

fn schedule_path(stem: &str) -> PathBuf {
    compiled_circuit_dir().join(format!("{stem}_schedule_b16_gkr.json"))
}

fn golden_path(stem: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden")
        .join(format!("{stem}.golden.json"))
}

fn load_golden(stem: &str) -> GoldenCircuit {
    let p = golden_path(stem);
    let bytes = std::fs::read(&p).unwrap_or_else(|e| panic!("read golden {p:?}: {e}"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse golden {p:?}: {e}"))
}

/// Full-corpus Phase-1 equivalence gate (see module docs).
#[test]
fn regenerated_schedules_are_content_identical_to_golden() {
    let mut layers_checked = 0usize;
    let mut recompiled = 0usize;
    for (name, stem) in COMMITTED_CORPUS {
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));

        // The regenerated, new-shape committed schedule. `load_committed_schedule`
        // deserializes the `units:` form and would ERROR on a still-OLD `order:` file
        // — so this test also proves the regen landed.
        let sched = load_committed_schedule(&schedule_path(stem))
            .unwrap_or_else(|e| panic!("[{name}] load_committed_schedule: {e:?}"));
        validate_circuit_schedule(&dag, &sched)
            .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));

        let golden = load_golden(stem);
        assert_eq!(sched.budget, golden.budget, "[{name}] budget drift");
        assert_eq!(sched.circuit, golden.circuit, "[{name}] circuit name drift");
        assert_eq!(
            sched.layers.len(),
            golden.layers.len(),
            "[{name}] layer count drift"
        );

        let cross = build_cross_layer_field_map(&dag);
        for (li, (layer, ls)) in dag.layers.iter().zip(&sched.layers).enumerate() {
            let g = &golden.layers[li];

            // (1) Flattened atom order == golden flat `order` (the compiled program's
            // root execution sequence is unchanged).
            let atom_order: Vec<u32> = ls.atom_order().iter().map(|r| r.0).collect();
            assert_eq!(
                atom_order, g.order,
                "[{name}] L{li}: atom_order (flattened units) != golden flat order"
            );

            // (2) sites genome identical (typed f64 pairs).
            assert_eq!(ls.sites, g.sites, "[{name}] L{li}: sites genome drift");

            // (3) provenance scalars identical.
            assert_eq!(
                ls.predicted_traffic, g.predicted_traffic,
                "[{name}] L{li}: predicted_traffic drift"
            );
            assert_eq!(ls.floor, g.floor, "[{name}] L{li}: floor drift");
            assert!(
                ls.floor <= ls.predicted_traffic || ls.units.is_empty(),
                "[{name}] L{li}: floor above predicted_traffic"
            );

            // (4) Recompile cross-check: the stored (units, sites) must reproduce
            // predicted_traffic exactly under Decisions at the persisted budget —
            // GATE-D applied to the reshaped artifact (proves the compiled program,
            // and thus GPU parity, is preserved).
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
            layers_checked += 1;
        }
        eprintln!("[relation-unit-equiv] {name}: OK ({} layers)", sched.layers.len());
    }
    assert!(layers_checked > 0, "vacuous: no layers checked");
    assert!(recompiled > 0, "vacuous: no layers recompiled");
    eprintln!(
        "[relation-unit-equiv] {}/{} fixtures, {layers_checked} layers checked, {recompiled} recompiled",
        COMMITTED_CORPUS.len(),
        COMMITTED_CORPUS.len()
    );
}
