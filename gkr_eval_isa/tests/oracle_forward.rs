//! Stage-1a oracle: the program's gate-input staging values and program-owned
//! outputs equal direct IR evaluation, over random staged leaves. (Native gate
//! semantics are out of scope by the eval-core contract.)

use gkr_design_space::import::load_circuit;
use gkr_eval_isa::compiler::{CompileParams, compile_layer, is_native_output};
use gkr_eval_isa::eval_ref::{self, Bf, Ext, random_row};
use gkr_eval_isa::interp::{StagedSources, execute};
use rand::{SeedableRng, rngs::StdRng};

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../cs/compiled_circuits")
        .join(name)
}

fn base_part(v: Ext) -> Bf {
    use field::{Field, FieldExtension};
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    assert!(
        coeffs[1..].iter().all(|c| c.is_zero()),
        "bf-classified source holds a non-base value"
    );
    coeffs[0]
}

fn check_circuit(path: &std::path::Path, params: CompileParams, seed: u64) {
    let c = load_circuit(path).unwrap_or_else(|e| panic!("{e}"));
    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
        let arena = &layer.arena.nodes;
        let mut rng = StdRng::seed_from_u64(seed ^ ((li as u64) << 32));
        let row = random_row(arena, &mut rng);
        let expected = eval_ref::eval_all(arena, &row);

        let cl = compile_layer(layer, g, params);
        let src = StagedSources {
            bf: cl.source_map.bf.iter().map(|&n| base_part(row.leaf_vals[n].unwrap())).collect(),
            e4: cl.source_map.e4.iter().map(|&n| row.leaf_vals[n].unwrap()).collect(),
        };
        let got = execute(&cl.program, &src);

        // 1. Gate-input staging values — the forward pass's real work.
        for (i, &root) in cl.gate_in_roots.iter().enumerate() {
            assert_eq!(
                got.gate_ins[i].unwrap_or_else(|| panic!("gate_in {i} never written")),
                expected[root],
                "{} layer {li} gate_in {i} (node {root})",
                path.display(),
            );
        }
        // 2. Program-owned output slots (skip native GateOutput stores).
        for (j, out) in g.outputs.iter().enumerate() {
            let native = is_native_output(&arena[out.node]);
            if native {
                assert!(got.outputs[j].is_none(), "program wrote a native slot {j}");
            } else {
                assert_eq!(
                    got.outputs[j].unwrap_or_else(|| panic!("output {j} never written")),
                    expected[out.node],
                    "{} layer {li} output {j} (node {})",
                    path.display(),
                    out.node,
                );
            }
        }
    }
}

#[test]
fn oracle_add_sub_both_layouts() {
    for f in [
        "add_sub_lui_auipc_mop_codegen_ir_gkr.json",
        "add_sub_lui_auipc_mop_codegen_ir_no_caches_gkr.json",
    ] {
        check_circuit(&fixture(f), CompileParams::default(), 0xA5A5);
    }
}

// Blake2 L0 has max_live_cells=3 (all BF), so budget=2 forces spills.
// add_sub L0 has max_live_cells=7, but the minimum feasible spilling budget
// exceeds max_live for that circuit due to remat protect-list constraints;
// blake2 is the correct circuit for verifying the spill/remat path.
#[test]
fn oracle_blake2_tiny_slot_budget_with_spills() {
    let p = CompileParams { budget_cells: 2, ..Default::default() };
    check_circuit(&fixture("blake2_g_function_codegen_ir_gkr.json"), p, 0xBEEF);
}

#[test]
fn oracle_bigint_mid_pressure_budget64() {
    // ~99 evictions + ~99 remats on L0 — the strongest spill-path validation.
    let p = CompileParams { budget_cells: 64, ..Default::default() };
    check_circuit(&fixture("bigint_with_extended_control_codegen_ir_gkr.json"), p, 0xB161);
}

#[test]
fn oracle_blake2_pinned_unbounded() {
    let p = CompileParams { budget_cells: 4096, pinned_cells: 16, ..Default::default() };
    check_circuit(&fixture("blake2_with_extended_control_codegen_ir_gkr.json"), p, 0xF1E);
}

#[test]
fn pin_saturation_absorbs_hub_reads() {
    // Saturated pin (every hub candidate cached): source reads collapse to
    // one per distinct column; the absorbed re-reads show up as pinned_hits.
    let c = load_circuit(&fixture("blake2_with_extended_control_codegen_ir_gkr.json")).unwrap();
    let cl = compile_layer(
        &c.circuit.layers[0],
        &c.graphs[0],
        CompileParams { budget_cells: 4096, pinned_cells: 4096, ..Default::default() },
    );
    assert!(cl.stats.pinned_hits > 1000, "got {}", cl.stats.pinned_hits);
}

#[test]
fn oracle_all_fixtures() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.unwrap().path();
            p.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .contains("codegen_ir")
                .then_some(p)
        })
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 22, "expected 22 IR fixtures");
    for p in &paths {
        check_circuit(p, CompileParams::default(), 7);
        // And once with a realistic GPU-ish budget, half of it pinned.
        check_circuit(
            p,
            CompileParams { budget_cells: 64, pinned_cells: 32, ..Default::default() },
            7 + 1,
        );
    }
}

#[test]
fn tiny_budget_actually_spills() {
    let c = load_circuit(&fixture("blake2_g_function_codegen_ir_gkr.json")).unwrap();
    // Layer 0 is the only layer with instructions; budget=2 < max_live=3 forces spills.
    let cl = compile_layer(
        &c.circuit.layers[0],
        &c.graphs[0],
        CompileParams { budget_cells: 2, ..Default::default() },
    );
    assert!(cl.stats.spill_evictions > 0, "expected spill_evictions > 0 at budget=2, got 0");
    assert!(cl.stats.remat_instrs > 0, "expected remat_instrs > 0 at budget=2, got 0");
}

#[test]
fn oracle_bigint_tight_budget_after_footprint_split() {
    // The arity-only splitter made bigint infeasible below 56 cells (one wide
    // instruction protected ~50 slot-resident operands). Footprint-aware
    // chunking must make 16 cells both feasible and correct.
    let p = CompileParams { budget_cells: 16, ..Default::default() };
    check_circuit(&fixture("bigint_with_extended_control_codegen_ir_gkr.json"), p, 0xB162);
}

#[test]
fn oracle_pinned_slots() {
    // Pinned hub prefix: preloaded, never evicted, read as ordinary cells.
    let p = CompileParams { budget_cells: 32, pinned_cells: 16, ..Default::default() };
    check_circuit(&fixture("blake2_with_extended_control_codegen_ir_gkr.json"), p, 0xF1A5);

    let c = load_circuit(&fixture("blake2_with_extended_control_codegen_ir_gkr.json")).unwrap();
    let cl = compile_layer(&c.circuit.layers[0], &c.graphs[0], p);
    assert!(cl.stats.pinned_cells > 0, "pin assignment empty");
    // Hub fanout is 34-89; 16 pinned cells must absorb >100 reads.
    assert!(cl.stats.pinned_hits > 100, "got {}", cl.stats.pinned_hits);

    // A bigger pin share of the same total budget absorbs more.
    let p2 = CompileParams { budget_cells: 32, pinned_cells: 24, ..Default::default() };
    check_circuit(&fixture("blake2_with_extended_control_codegen_ir_gkr.json"), p2, 0xF1A6);
    let cl2 = compile_layer(&c.circuit.layers[0], &c.graphs[0], p2);
    assert!(cl2.stats.pinned_hits > cl.stats.pinned_hits);
}

#[test]
fn oracle_min_feasible_budget() {
    // The budget-sweep report marks tight cells infeasible via catch_unwind;
    // this verifies the TIGHTEST feasible cell of the sweep grid is not just
    // compilable but CORRECT (max spill/remat stress per circuit).
    use gkr_eval_isa::report::SLOT_GRID;
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.unwrap().path();
            p.file_name().unwrap().to_str().unwrap().contains("codegen_ir").then_some(p)
        })
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 22, "expected 22 IR fixtures");
    for p in &paths {
        let c = load_circuit(p).unwrap_or_else(|e| panic!("{e}"));
        let min = SLOT_GRID
            .iter()
            .copied()
            .find(|&slots| {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    compile_layer(
                        &c.circuit.layers[0],
                        &c.graphs[0],
                        CompileParams { budget_cells: slots, ..Default::default() },
                    )
                }))
                .is_ok()
            })
            .unwrap_or_else(|| panic!("{}: no feasible budget in grid", p.display()));
        check_circuit(p, CompileParams { budget_cells: min, ..Default::default() }, 0x51EE);
    }
}

#[test]
fn oracle_pressure_order() {
    // The report compiles Pressure-order programs for the order-validation
    // comparison; this checks they are also CORRECT (final-review gap).
    use gkr_eval_isa::compiler::OrderKind;
    for f in [
        "bigint_with_extended_control_codegen_ir_gkr.json",
        "blake2_with_extended_control_codegen_ir_gkr.json",
    ] {
        let p = CompileParams { order: OrderKind::Pressure, ..Default::default() };
        check_circuit(&fixture(f), p, 0x9E55);
    }
}
