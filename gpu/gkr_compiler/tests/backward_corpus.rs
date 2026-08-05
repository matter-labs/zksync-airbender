use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::{FieldExtension, PrimeField, baby_bear::base::BabyBearField};
use gkr_eval_ir::{Bf, Ext, lower_dag, validate};
use gpu_gkr_compiler::backward::{
    CoeffResolver, CoefficientRecipeId, SourceId, interpret_coefficient_layer,
    interpret_continuation_program, interpret_r0_program,
};
use gpu_gkr_compiler::{GpuResourceProfile, compile_continuations, compile_r0};

const CORPUS: &[&str] = &[
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

struct DeterministicResolver;

fn lift(value: u32) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
}

impl CoeffResolver for DeterministicResolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        lift(17 + id.0 * 13)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        let base = 31 + id.0 * 19 + row as u32 * 7;
        (lift(base), lift(base + 5))
    }
}

#[test]
fn retained_corpus_compiles_and_matches_the_cpu_semantics() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let profile = GpuResourceProfile::production();

    for layout_name in CORPUS {
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("{layout_name}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("{layout_name}: {error}"));

        let r0 = compile_r0(&dag, &profile)
            .unwrap_or_else(|error| panic!("{layout_name} R0: {error:?}"));
        let continuations = compile_continuations(&dag, &profile)
            .unwrap_or_else(|error| panic!("{layout_name} continuation: {error:?}"));
        assert_eq!(r0.layers.len(), dag.layers.len(), "{layout_name} R0");
        assert_eq!(
            continuations.layers.len(),
            dag.layers.len(),
            "{layout_name} continuation"
        );

        for layer in &r0.layers {
            for (row, k) in [(0, 1), (3, 7)] {
                let semantic =
                    interpret_coefficient_layer(&layer.coefficients, row, &DeterministicResolver)
                        .unwrap();
                let encoded = interpret_r0_program(layer, row, &DeterministicResolver, k).unwrap();
                assert_eq!(encoded, semantic, "{layout_name} R0 L{}", layer.layer);
            }
        }
        for layer in &continuations.layers {
            for (row, k) in [(0, 1), (3, 7)] {
                let semantic =
                    interpret_coefficient_layer(&layer.coefficients, row, &DeterministicResolver)
                        .unwrap();
                let encoded =
                    interpret_continuation_program(layer, row, &DeterministicResolver, k).unwrap();
                assert_eq!(
                    encoded, semantic,
                    "{layout_name} continuation L{}",
                    layer.layer
                );
            }
        }
    }
}
