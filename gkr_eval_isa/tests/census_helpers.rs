//! Shared helpers for the SP2 strategy-coverage census.
//!
//! `FIXTURES`, `load_fixture`, and `compiled_circuit_dir` are copied verbatim
//! from `fwd_parity.rs`. `lower`, `compile_one_layer`, and `special_strategies`
//! are the census-specific additions.

use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, DagCircuit};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::fwd::compile::analyze::{analyze_layer, materialize_descriptors};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::context::{build_forward_actions, DagForwardContext};
use gkr_eval_isa::fwd::source::SpecialStrategy;

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

// ── Per-layer lowering context ───────────────────────────────────────────────

/// Build the layer lowering context (actions + interned special descriptors) WITHOUT
/// compiling a program. `ctx.specials` is produced by the same
/// `analyze_layer` + `materialize_descriptors` pass the schedule-driven compiler runs
/// (`lower.rs`) and is schedule-INDEPENDENT — so the strategy census needs no committed
/// schedule (it also covers the `no_caches` fixtures, which have none). Post-T3b this
/// replaces the old 5-arg `compile_layer` call the census used only for `ctx.specials`.
pub fn layer_ctx(
    artifact: &GKRCircuitArtifact<BabyBearField>,
    dag: &DagCircuit,
    layer_idx: usize,
) -> DagForwardContext {
    let dag_layer = &dag.layers[layer_idx];
    let art_layer = &artifact.layers[layer_idx];
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(dag_layer, art_layer, &artifact.scratch_space_mapping)
        .unwrap_or_else(|e| panic!("layer {layer_idx}: build_forward_actions failed: {e:?}"));
    ctx.cross_layer_fields = build_cross_layer_field_map(dag);
    let graph = analyze_layer(dag_layer, &ctx);
    materialize_descriptors(&graph.descriptors, dag_layer, &mut ctx);
    ctx
}

// ── Strategy extraction ─────────────────────────────────────────────────────

/// Return the `SpecialStrategy` of every descriptor in `ctx.specials`.
pub fn special_strategies(ctx: &DagForwardContext) -> Vec<SpecialStrategy> {
    ctx.specials.iter().map(|d| d.strategy.clone()).collect()
}
