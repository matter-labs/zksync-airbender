//! Disassembler driver: build a real GKR circuit, lower it to dag_ir, compile a
//! layer to the forward-eval VM, and print the annotated program via
//! `gkr_eval_isa::fwd::disasm`. Inspection tool — `#[ignore]`d (builds a full
//! circuit; prints only). Run, e.g.:
//!
//!   RUST_MIN_STACK=1073741824 RUSTFLAGS="-Awarnings" \
//!     cargo test -p circuit_prover --release disasm_add_sub_layer0 \
//!     -- --ignored --nocapture
//!
//! The program is a STATIC compilation of the layer's expression DAG — no witness
//! / VM run / storage needed (that machinery lives in `sp2_peek_adapter`'s
//! `build_*_real_data` only for the validation gates).

use super::sp2_peek_adapter::{
    compile_add_sub_circuit, compile_unsigned_mul_div_circuit, ADD_SUB_TRACE_LEN_LOG2,
    MUL_DIV_TRACE_LEN_LOG2,
};
use cs::gkr_compiler::dag_ir::lower_dag;
use cs::gkr_compiler::GKRCircuitArtifact;
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::fwd::disasm::disassemble_layer;

use crate::primitives::field::BF;

/// Compile `layer_idx` of `circuit` and return the annotated disassembly.
fn disasm(title: &str, circuit: &GKRCircuitArtifact<BF>, layer_idx: usize) -> String {
    let dag = lower_dag(circuit).expect("lower_dag failed");
    let cross = build_cross_layer_field_map(&dag);
    const BUDGET: usize = 1024;
    let compiled = compile_layer(
        &dag.layers[layer_idx],
        &circuit.layers[layer_idx],
        &circuit.scratch_space_mapping,
        &cross,
        BUDGET,
    )
    .expect("compile_layer failed");
    disassemble_layer(title, &compiled, Some(&dag.layers[layer_idx]))
}

#[test]
#[ignore = "inspection tool: builds a full circuit and prints; run with --ignored --nocapture"]
fn disasm_add_sub_layer0() {
    let circuit = compile_add_sub_circuit(ADD_SUB_TRACE_LEN_LOG2);
    let text = disasm("add_sub layer-0 forward program", &circuit, 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}

#[test]
#[ignore = "inspection tool: builds a full circuit and prints; run with --ignored --nocapture"]
fn disasm_unsigned_mul_div_layer0() {
    let circuit = compile_unsigned_mul_div_circuit(MUL_DIV_TRACE_LEN_LOG2);
    let text = disasm("unsigned_mul_div layer-0 forward program", &circuit, 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}
