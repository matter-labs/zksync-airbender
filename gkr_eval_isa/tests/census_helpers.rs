//! Shared helpers for the SP2 strategy-coverage census.
//!
//! `FIXTURES`, `load_fixture`, and `compiled_circuit_dir` are copied verbatim
//! from `fwd_parity.rs`. `lower`, `compile_one_layer`, and `special_strategies`
//! are the census-specific additions.

use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, DagCircuit, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::fwd::context::CompiledLayer;
use gkr_eval_isa::fwd::source::SpecialStrategy;
use std::collections::HashMap;

// ── Fixture directory (verbatim from fwd_parity.rs) ────────────────────────

pub fn compiled_circuit_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

// ── Fixture list (22 names, verbatim from fwd_parity.rs) ───────────────────

pub const FIXTURES: &[&str] = &[
    // _layout_gkr.json variants
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
    // _layout_no_caches_gkr.json variants
    "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    "bigint_with_extended_control_layout_no_caches_gkr.json",
    "blake2_g_function_layout_no_caches_gkr.json",
    "blake2_with_extended_control_layout_no_caches_gkr.json",
    "inits_and_teardowns_layout_no_caches_gkr.json",
    "jump_branch_slt_layout_no_caches_gkr.json",
    "keccak_special5_layout_no_caches_gkr.json",
    "mem_subword_only_layout_no_caches_gkr.json",
    "mem_word_only_layout_no_caches_gkr.json",
    "shift_binop_layout_no_caches_gkr.json",
    "unsigned_mul_div_layout_no_caches_gkr.json",
];

// ── Fixture loading (verbatim from fwd_parity.rs) ──────────────────────────

/// Deserialize one fixture JSON → `GKRCircuitArtifact<BabyBearField>`.
/// Returns `None` if the file is missing or fails to deserialize.
pub fn load_fixture(name: &str) -> Option<GKRCircuitArtifact<BabyBearField>> {
    let path = compiled_circuit_dir().join(name);
    let bytes = std::fs::read(&path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

// ── DAG lowering ────────────────────────────────────────────────────────────

pub fn lower(artifact: &GKRCircuitArtifact<BabyBearField>) -> DagCircuit {
    lower_dag(artifact).expect("lower_dag failed")
}

// ── Per-layer compilation ───────────────────────────────────────────────────

const BUDGET: usize = 1024;

/// Compile a single layer from the given `DagCircuit` + artifact, mirroring
/// the per-layer compile call in `fwd_parity.rs::check_fixture` (lines 183–194).
pub fn compile_one_layer(
    artifact: &GKRCircuitArtifact<BabyBearField>,
    dag: &DagCircuit,
    layer_idx: usize,
) -> CompiledLayer {
    let cross_layer_fields: HashMap<ReadPlace, _> = build_cross_layer_field_map(dag);
    let dag_layer = &dag.layers[layer_idx];
    let art_layer = &artifact.layers[layer_idx];
    compile_layer(
        dag_layer,
        art_layer,
        &artifact.scratch_space_mapping,
        &cross_layer_fields,
        BUDGET,
    )
    .unwrap_or_else(|e| panic!("layer {layer_idx}: compile_layer failed: {e:?}"))
}

// ── Strategy extraction ─────────────────────────────────────────────────────

/// Return the `SpecialStrategy` of every descriptor in `compiled.ctx.specials`.
pub fn special_strategies(compiled: &CompiledLayer) -> Vec<SpecialStrategy> {
    compiled
        .ctx
        .specials
        .iter()
        .map(|d| d.strategy.clone())
        .collect()
}
