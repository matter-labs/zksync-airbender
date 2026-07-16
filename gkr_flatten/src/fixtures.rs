//! On-disk fixture loading. Mirrors gkr_eval_isa/tests/common/mod.rs:255-302,
//! which is integration-test-only and unreachable from other crates.
//!
//! Also owns the searchable-layer [`Instance`] and its `fwd_instance`/
//! `bwd_instance` builders (moved verbatim from `tests/m2_search.rs`), so the
//! M2 regression sweep and the M3 re-baseline sweep share one definition.
use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{
    lower_dag, validate, BwdRegime, DagCircuit, DagLayer, ExprId, FieldKind, ReadPlace,
};
use cs::gkr_compiler::GKRCircuitArtifact;
// Field type: mirror the import at cs/src/gkr_compiler/dag_ir/eval.rs:21.
// `cs` does not re-export `BabyBearField` under this name, so depend on `field`
// directly (same dependency line `gkr_eval_isa/Cargo.toml` uses).
use field::baby_bear::base::BabyBearField;
use gkr_eval_isa::bwd::distill::distill;
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

/// One searchable layer instance: a fwd L0 or a bwd Ext-distilled L0, with
/// whatever the LayerView needs kept alive.
pub struct Instance {
    pub label: String,
    pub layer: DagLayer,
    pub cross: HashMap<ReadPlace, FieldKind>,
    // The bwd distill's per-expr field overrides. `distill(..).field_overrides`
    // and `LayerView::new`'s third parameter are both `BTreeMap<ExprId,
    // FieldKind>` in the landed code (the brief's skeleton showed a `HashMap`
    // placeholder — the landed type wins). `None` for fwd layers.
    pub overrides: Option<BTreeMap<ExprId, FieldKind>>,
}

// bwd instances hard-fail here (no silent_catch): M1 measured 0 construct
// skips, so a new panic is a regression to surface, not to skip.

/// Forward L0: load the circuit, own a clone of layer 0 and its cross-layer
/// field map. No field overrides on the forward path.
pub fn fwd_instance(name: &str) -> Instance {
    let (dag, cross) = load_circuit(name);
    Instance { label: format!("{name} [fwd L0]"), layer: dag.layers[0].clone(), cross, overrides: None }
}

/// Backward Ext-distilled L0: distill layer 0 in the `Ext` regime and own the
/// rebuilt layer, its merged cross-layer field map, and the per-expr field
/// overrides — mirrors `tests/m1_parity.rs::probe_fixture`. The distilled
/// layer owns all three, so they move straight into the `Instance`.
pub fn bwd_instance(name: &str) -> Instance {
    let (dag, cross) = load_circuit(name);
    let distilled = distill(&dag.layers[0], BwdRegime::Ext, &cross, None);
    Instance {
        label: format!("{name} [bwd Ext L0]"),
        layer: distilled.layer,
        cross: distilled.cross_fields,
        overrides: Some(distilled.field_overrides),
    }
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
