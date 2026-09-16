use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::{baby_bear::base::BabyBearField, FieldExtension, PrimeField};
use gkr_eval_ir::lower_dag;

use super::common::interp::{interpret_coeff_layer, CoeffResolver};
use super::common::model::{CoefficientRecipeId, SourceId};
use super::common::{Bf, Ext};
use super::continuation::interpret_continuation_program;
use super::r0::interpret_r0_program;
use super::{compile_continuations, compile_r0};

pub(super) const CORPUS: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

#[test]
fn cpu_window_program_selector_retained_corpus() {
    use super::window_manifest::{
        resolve_windowed_r0_dispatch, resolve_windowed_r0_program_dispatch, windowed_r0_bank,
    };
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let bank = windowed_r0_bank();
    let mut coordinates = 0;
    let mut expected_coordinates = 0;
    let mut changes = 0;
    for layout_name in CORPUS {
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&artifact).unwrap();
        expected_coordinates += 1 * dag.layers.len();
        for layer in compile_r0(&dag).unwrap().layers {
            let program = super::lower_window_program(&layer).unwrap();
            let mask = program.shape.bits();
            let bf = program.sections[0];
            let e4 = program.sections[3] - bf;
            let selected = resolve_windowed_r0_program_dispatch(mask, &program.sections).unwrap();
            let baseline = resolve_windowed_r0_dispatch(mask).unwrap();
            let expected = match (*layout_name, layer.layer) {
                ("blake2_with_extended_control_layout_gkr.json", 0) => (0xfff, 3),
                _ => baseline,
            };
            assert_eq!(selected, expected, "{layout_name} L{}", layer.layer);
            assert!(bank.contains(&selected));
            assert_eq!(mask & !selected.0, 0);
            changes += usize::from(selected != baseline);
            coordinates += 1;
            eprintln!("R0_PROGRAM layout={layout_name} layer={} native={mask:03x} bf={bf} e4={e4} compiled={:03x} bound={}",
                layer.layer, selected.0, selected.1);
        }
    }
    assert!(expected_coordinates > 0);
    assert_eq!(coordinates, expected_coordinates);
    assert_eq!(changes, 1);
}

struct Resolver;

fn lift(value: u32) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
}

impl CoeffResolver for Resolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        lift(17 + id.0 * 13)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        let base = 31 + id.0 * 19 + row as u32 * 7;
        (lift(base), lift(base + 5))
    }
}

#[test]
fn retained_corpus_matches_the_cpu_codec_oracle() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for layout_name in CORPUS {
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("{layout_name}: {error}"));
        let r0 = compile_r0(&dag).unwrap_or_else(|error| panic!("{layout_name} R0: {error:?}"));
        let continuations = compile_continuations(&dag)
            .unwrap_or_else(|error| panic!("{layout_name} continuation: {error:?}"));

        for layer in &r0.layers {
            for (row, k) in [(0, 1), (3, 7)] {
                let expected = interpret_coeff_layer(&layer.coefficients, row, &Resolver).unwrap();
                let encoded = interpret_r0_program(layer, row, &Resolver, k).unwrap();
                assert_eq!(encoded, expected, "{layout_name} R0 L{}", layer.layer);
            }
        }
        for layer in &continuations.layers {
            for (row, k) in [(0, 1), (3, 7)] {
                let expected = interpret_coeff_layer(&layer.coefficients, row, &Resolver).unwrap();
                let encoded = interpret_continuation_program(layer, row, &Resolver, k).unwrap();
                assert_eq!(
                    encoded, expected,
                    "{layout_name} continuation L{}",
                    layer.layer
                );
            }
        }
    }
}
