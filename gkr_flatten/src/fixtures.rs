//! On-disk fixture loading. Mirrors gkr_eval_isa/tests/common/mod.rs:255-302,
//! which is integration-test-only and unreachable from other crates.
use std::collections::HashMap;
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, validate, DagCircuit, FieldKind, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
// Field type: mirror the import at cs/src/gkr_compiler/dag_ir/eval.rs:21.
// `cs` does not re-export `BabyBearField` under this name, so depend on `field`
// directly (same dependency line `gkr_eval_isa/Cargo.toml` uses).
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

pub const FIXTURES: [&str; 12] = [
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
    "unified_reduced_machine_layout_gkr.json",
];

pub fn compiled_circuit_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

pub fn load_artifact(name: &str) -> GKRCircuitArtifact<BabyBearField> {
    let path = compiled_circuit_dir().join(name);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {path:?}: {e}"))
}

pub fn load_circuit(name: &str) -> (DagCircuit, HashMap<ReadPlace, FieldKind>) {
    let artifact = load_artifact(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    (dag, cross)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_fixtures_load_and_validate() {
        for name in FIXTURES {
            let (dag, cross) = load_circuit(name);
            assert!(!dag.layers.is_empty(), "{name}: no layers");
            assert!(
                dag.layers[0].roots.len() > 0,
                "{name}: L0 has no roots"
            );
            let _ = cross; // cross map may legitimately be empty for single-layer circuits
        }
    }
}
