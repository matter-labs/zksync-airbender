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
use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::disasm::disassemble_layer;

use crate::primitives::field::BF;

/// Compile `layer_idx` of `circuit` from its committed b16 schedule (`stem`) and return
/// the annotated disassembly. Post-T3b the forward compiler is schedule-driven, so this
/// loads `cs/compiled_circuits/{stem}_schedule_b16_gkr.json` and compiles the circuit.
fn disasm(title: &str, circuit: &GKRCircuitArtifact<BF>, stem: &str, layer_idx: usize) -> String {
    let dag = lower_dag(circuit).expect("lower_dag failed");
    let sched_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(format!("{stem}_schedule_b16_gkr.json"));
    let sched_bytes = std::fs::read(&sched_path)
        .unwrap_or_else(|e| panic!("read committed schedule {sched_path:?}: {e}"));
    let schedule: cs::gkr_compiler::dag_ir::CircuitSchedule =
        serde_json::from_slice(&sched_bytes)
            .unwrap_or_else(|e| panic!("parse committed schedule {sched_path:?}: {e}"));
    let compiled = compile_circuit(&dag, &schedule, circuit).expect("compile_circuit failed");
    disassemble_layer(title, &compiled.layers[layer_idx], Some(&dag.layers[layer_idx]))
}

#[test]
#[ignore = "inspection tool: builds a full circuit and prints; run with --ignored --nocapture"]
fn disasm_add_sub_layer0() {
    let circuit = compile_add_sub_circuit(ADD_SUB_TRACE_LEN_LOG2);
    let text = disasm("add_sub layer-0 forward program", &circuit, "add_sub_lui_auipc_mop", 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}

#[test]
#[ignore = "inspection tool: builds a full circuit and prints; run with --ignored --nocapture"]
fn disasm_unsigned_mul_div_layer0() {
    let circuit = compile_unsigned_mul_div_circuit(MUL_DIV_TRACE_LEN_LOG2);
    let text = disasm("unsigned_mul_div layer-0 forward program", &circuit, "unsigned_mul_div", 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}
