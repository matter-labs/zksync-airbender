//! Ad-hoc disassembly dump: compile one layer from its committed b16 schedule and
//! print the annotated forward-eval VM program via `gkr_eval_isa::fwd::disasm`.
//! CPU-only (no `circuit_prover` build / no `RUST_MIN_STACK`). Static compile of the
//! layer's expression DAG — no witness/VM run needed.
//!
//! Post-T3b: the self-scheduling residency engine was deleted; this now compiles the
//! committed b16 schedule (`compile_circuit`) and disassembles the chosen layer.
//!
//! Run:
//!   RUSTFLAGS="-Awarnings" cargo test -p gkr_eval_isa --test disasm_dump \
//!     dump_add_sub_l0 -- --ignored --nocapture

mod common;
use common::load_dag_sched;

use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::disasm::disassemble_layer;

/// Compile `fixture`'s `layer_idx` from its committed b16 schedule and return the
/// annotated disassembly. The `_layout_gkr.json` fixtures are the WITH-CACHING variant.
fn dump(fixture: &str, layer_idx: usize) -> String {
    let (dag, sched, artifact) = load_dag_sched(fixture);
    let compiled = compile_circuit(&dag, &sched, &artifact)
        .unwrap_or_else(|e| panic!("compile_circuit({fixture}): {e:?}"));
    disassemble_layer(
        &format!("{fixture}  layer-{layer_idx}  (committed b16 schedule, with caching)"),
        &compiled.layers[layer_idx],
        Some(&dag.layers[layer_idx]),
    )
}

#[test]
#[ignore = "inspection tool: prints the disassembly; run with --ignored --nocapture"]
fn dump_add_sub_l0() {
    let text = dump("add_sub_lui_auipc_mop_layout_gkr.json", 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}
