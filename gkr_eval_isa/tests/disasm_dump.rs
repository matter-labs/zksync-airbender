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

/// Compile `fixture` once and disassemble every layer, each prefixed by its own
/// floor-vs-realized header. Cheaper than calling `dump` per layer (one
/// `compile_circuit` instead of one-per-layer).
fn dump_all(fixture: &str) -> String {
    let (dag, sched, artifact) = load_dag_sched(fixture);
    let compiled = compile_circuit(&dag, &sched, &artifact)
        .unwrap_or_else(|e| panic!("compile_circuit({fixture}): {e:?}"));
    let cross = build_cross_layer_field_map(&dag);
    let mut out = String::new();
    for (layer_idx, layer) in compiled.layers.iter().enumerate() {
        let floor =
            dag_traffic_floor_with_actions(&dag.layers[layer_idx], &cross, &layer.ctx.actions);
        let realized = layer.stats.dram_traffic;
        let text = disassemble_layer(
            &format!("{fixture}  layer-{layer_idx}  (committed b16 schedule, with caching)"),
            layer,
            Some(&dag.layers[layer_idx]),
        );
        out.push_str(&format!(
            "\n============================== layer {layer_idx} ==============================\n\
             floor(claimed) = {floor}  |  realized dram_traffic = {realized} \
             ({:+} over floor)  |  dram_reads = {}\n{text}\n",
            realized as isize - floor as isize,
            layer.stats.dram_reads,
        ));
    }
    out
}

#[test]
#[ignore = "inspection tool: prints the disassembly; run with --ignored --nocapture"]
fn dump_blake2_ext_all() {
    let text = dump_all("blake2_with_extended_control_layout_gkr.json");
    println!("\n{text}");
    assert!(!text.is_empty());
}

/// The full with-caching corpus (11 circuits).
const CORPUS: &[&str] = &[
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
];

/// Census of compaction relocations (`clear_quad_for_ext`) across the committed-b16
/// corpus, read from the cell allocator's ground-truth `trace.placement_moves`.
///
/// Each relocation is one extra cell-to-cell `MOV` per row on device: a value the
/// allocator parked in a quad that a later overlapping-lifetime Ext then reclaimed.
/// Per move we print the *survival gap* (`moved_last_use - at_instr` — how far past the
/// Ext the relocated Base lives, i.e. why it could not just be dropped) and the *idle
/// span* (`at_instr - moved_def` — how long it had been sitting in the doomed quad
/// before the Ext arrived, i.e. how much opportunity a lifetime-aware placement had to
/// park it elsewhere).
#[test]
#[ignore = "inspection tool: prints the census; run with --ignored --nocapture"]
fn relocation_census() {
    let mut grand = 0usize;
    let mut layers_with_moves = 0usize;
    let mut over_floor = 0usize;
    for fx in CORPUS {
        let (dag, sched, artifact) = load_dag_sched(fx);
        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("compile_circuit({fx}): {e:?}"));
        // Traffic-neutrality guard: two-phase placement must not reduce feasibility (which
        // fill-then-trim would silently absorb as fewer cached values => traffic above the
        // DAG floor). Every committed-b16 layer is at floor; assert it stays there.
        let cross = build_cross_layer_field_map(&dag);
        for (li, layer) in compiled.layers.iter().enumerate() {
            let floor = dag_traffic_floor_with_actions(&dag.layers[li], &cross, &layer.ctx.actions);
            let realized = layer.stats.dram_traffic;
            if realized != floor {
                over_floor += 1;
                println!("  !! {fx} layer {li}: dram_traffic {realized} != floor {floor}");
            }
        }
        let fx_total: usize = compiled.layers.iter().map(|l| l.trace.placement_moves.len()).sum();
        grand += fx_total;
        if fx_total == 0 {
            println!("{fx:52}  0");
            continue;
        }
        println!("{fx:52}  {fx_total}");
        for (li, layer) in compiled.layers.iter().enumerate() {
            let mv = &layer.trace.placement_moves;
            if mv.is_empty() {
                continue;
            }
            layers_with_moves += 1;
            println!(
                "    layer {li}: {} relocation(s)  (budget={}, lanes={}, max_live={})",
                mv.len(),
                layer.budget,
                layer.program.instrs.len(),
                layer.trace.max_live_cells,
            );
            for m in mv {
                println!(
                    "      ext=e{:<5} clears quad@{:<2} <- relocate e{:<5} cell{:>2}->{:<2} \
                     | def@{} lastuse@{} ext@{} | survives ext by {:+}, idle before ext {}",
                    m.ext_value.0,
                    m.cleared_quad,
                    m.moved_value.0,
                    m.from,
                    m.to,
                    m.moved_def,
                    m.moved_last_use,
                    m.at_instr,
                    m.moved_last_use as isize - m.at_instr as isize,
                    m.at_instr.saturating_sub(m.moved_def),
                );
            }
        }
    }
    println!(
        "\n=== corpus total: {grand} compaction relocation(s) across {layers_with_moves} layer(s) ==="
    );
    assert_eq!(over_floor, 0, "{over_floor} layer(s) regressed above the DRAM floor");
}

/// Slot-census guard (v2 Task 4, spec §2 open item): under FIELD-QUALIFIED slot
/// keys (a mixed logical layer/cache output splits into a base slot + an ext
/// slot) every committed corpus layer program must still fit SLOT_BITS=4 —
/// ≤ 16 backing slots. `BackingTable::intern` already hard-fails compilation on
/// the 17th slot, so `compile_circuit` succeeding IS the gate; this census
/// additionally reports the per-corpus maximum so headroom stays visible.
/// NOT `#[ignore]`d: SLOT_BITS is a spec assumption, not a knob — if this
/// fails, STOP and surface it rather than widening the slot field.
#[test]
fn slot_census_b16_under_field_split() {
    let mut max_slots = 0usize;
    let mut max_at = String::new();
    for fx in CORPUS {
        let (dag, sched, artifact) = load_dag_sched(fx);
        let compiled = compile_circuit(&dag, &sched, &artifact).unwrap_or_else(|e| {
            panic!("compile_circuit({fx}) failed under field-qualified slots: {e:?}")
        });
        for (li, layer) in compiled.layers.iter().enumerate() {
            let n = layer.ctx.backings.n_slots();
            assert!(
                n <= 16,
                "{fx} layer {li}: {n} backing slots under the field split (> 16, SLOT_BITS=4)"
            );
            if n > max_slots {
                max_slots = n;
                max_at = format!("{fx} layer {li}");
            }
        }
    }
    println!("=== slot census: corpus max = {max_slots}/16 slots (at {max_at}) ===");
}
