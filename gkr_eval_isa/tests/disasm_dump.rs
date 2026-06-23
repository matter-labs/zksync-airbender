//! Ad-hoc disassembly dump: compile one layer at a chosen budget and print the
//! annotated forward-eval VM program via `gkr_eval_isa::fwd::disasm`. CPU-only
//! (no `circuit_prover` build / no `RUST_MIN_STACK`). Static compile of the
//! layer's expression DAG — no witness/VM run needed.
//!
//! Run:
//!   RUSTFLAGS="-Awarnings" cargo test -p gkr_eval_isa --test disasm_dump \
//!     dump_add_sub_l0 -- --ignored --nocapture

use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, validate};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::fwd::disasm::disassemble_layer;

/// Compile `fixture`'s `layer_idx` at `budget` cells and return the annotated
/// disassembly. The `_layout_gkr.json` fixtures are the WITH-CACHING variant
/// (the `_layout_no_caches_gkr.json` siblings are caches=false).
fn dump(fixture: &str, layer_idx: usize, budget: usize) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../cs/compiled_circuits")
        .join(fixture);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {fixture}: {e}"));
    let artifact: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_slice(&bytes).expect("deserialize fixture");
    let dag = lower_dag(&artifact).expect("lower_dag");
    validate(&dag).expect("validate");
    let cross = build_cross_layer_field_map(&dag);
    let compiled = compile_layer(
        &dag.layers[layer_idx],
        &artifact.layers[layer_idx],
        &artifact.scratch_space_mapping,
        &cross,
        budget,
    )
    .unwrap_or_else(|e| panic!("compile_layer({fixture} L{layer_idx} @budget {budget}): {e:?}"));
    disassemble_layer(
        &format!("{fixture}  layer-{layer_idx}  (budget {budget} cells, with caching)"),
        &compiled,
        Some(&dag.layers[layer_idx]),
    )
}

/// Budget in cells, overridable: `DISASM_BUDGET=24 cargo test ... -- --ignored --nocapture`.
/// Defaults to 16 (full-occupancy real budget on sm_120).
fn budget() -> usize {
    std::env::var("DISASM_BUDGET")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(16)
}

#[test]
#[ignore = "inspection tool: prints the disassembly; run with --ignored --nocapture"]
fn dump_add_sub_l0() {
    let text = dump("add_sub_lui_auipc_mop_layout_gkr.json", 0, budget());
    println!("\n{text}");
    assert!(!text.is_empty());
}
