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
