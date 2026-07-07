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
use gkr_eval_isa::schedule_search::floor::{
    build_cross_layer_field_map, dag_traffic_floor_with_actions,
};

/// Compile `fixture`'s `layer_idx` from its committed b16 schedule and return the
/// annotated disassembly. The `_layout_gkr.json` fixtures are the WITH-CACHING variant.
///
/// The header line reports the DAG-intrinsic traffic floor (the width-weighted
/// lower bound over the roots the emitter actually lowers) against the realized
/// width-weighted `dram_traffic`, so a layer that fails to reach its floor at the
/// committed budget shows the gap directly.
fn dump(fixture: &str, layer_idx: usize) -> String {
    let (dag, sched, artifact) = load_dag_sched(fixture);
    let compiled = compile_circuit(&dag, &sched, &artifact)
        .unwrap_or_else(|e| panic!("compile_circuit({fixture}): {e:?}"));
    let layer = &compiled.layers[layer_idx];
    let cross = build_cross_layer_field_map(&dag);
    let floor = dag_traffic_floor_with_actions(&dag.layers[layer_idx], &cross, &layer.ctx.actions);
    let realized = layer.stats.dram_traffic;
    let text = disassemble_layer(
        &format!("{fixture}  layer-{layer_idx}  (committed b16 schedule, with caching)"),
        layer,
        Some(&dag.layers[layer_idx]),
    );
    format!(
        "floor(claimed) = {floor}  |  realized dram_traffic = {realized} \
         ({:+} over floor)  |  dram_reads = {}\n{text}",
        realized as isize - floor as isize,
        layer.stats.dram_reads,
    )
}

#[test]
#[ignore = "inspection tool: prints the disassembly; run with --ignored --nocapture"]
fn dump_add_sub_l0() {
    let text = dump("add_sub_lui_auipc_mop_layout_gkr.json", 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}

/// shift_binop layer-0 is the sole corpus layer that does NOT reach its floor at
/// budget 16 (committed `predicted_traffic = 35` vs `floor = 33`); this dump is
/// the inspection driver for why its peak working set exceeds 16 cells.
#[test]
#[ignore = "inspection tool: prints the disassembly; run with --ignored --nocapture"]
fn dump_shift_l0() {
    let text = dump("shift_binop_layout_gkr.json", 0);
    println!("\n{text}");
    assert!(!text.is_empty());
}
