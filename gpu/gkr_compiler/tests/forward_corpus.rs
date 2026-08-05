use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::{lower_dag, validate};
use gpu_gkr_compiler::forward::{encode, validate::validate_compiled};
use gpu_gkr_compiler::{compile_forward, parse_forward_artifact};

const CORPUS: &[(&str, &str)] = &[
    (
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "add_sub_lui_auipc_mop",
    ),
    (
        "bigint_with_extended_control_layout_gkr.json",
        "bigint_with_extended_control",
    ),
    ("blake2_g_function_layout_gkr.json", "blake2_g_function"),
    (
        "blake2_with_extended_control_layout_gkr.json",
        "blake2_with_extended_control",
    ),
    ("inits_and_teardowns_layout_gkr.json", "inits_and_teardowns"),
    ("jump_branch_slt_layout_gkr.json", "jump_branch_slt"),
    ("keccak_special5_layout_gkr.json", "keccak_special5"),
    ("mem_subword_only_layout_gkr.json", "mem_subword_only"),
    ("mem_word_only_layout_gkr.json", "mem_word_only"),
    ("shift_binop_layout_gkr.json", "shift_binop"),
    (
        "unified_reduced_machine_layout_gkr.json",
        "unified_reduced_machine",
    ),
    ("unsigned_mul_div_layout_gkr.json", "unsigned_mul_div"),
];

#[test]
fn every_retained_forward_artifact_validates_compiles_and_encodes() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for &(layout_name, stem) in CORPUS {
        let layout_bytes = std::fs::read(directory.join(layout_name)).unwrap();
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&layout_bytes).unwrap();
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{stem}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("{stem}: {error}"));

        let artifact_name = format!("{stem}_schedule_b16_gkr.json");
        let artifact_bytes = std::fs::read(directory.join(&artifact_name)).unwrap();
        let artifact = parse_forward_artifact(&artifact_bytes, &artifact_name).unwrap();
        let compiled =
            compile_forward(&dag, &artifact).unwrap_or_else(|error| panic!("{stem}: {error:?}"));

        assert_eq!(compiled.layers.len(), dag.layers.len(), "{stem}");
        for (layer_index, (program, layer)) in compiled.layers.iter().zip(&dag.layers).enumerate() {
            validate_compiled(program, layer)
                .unwrap_or_else(|error| panic!("{stem} layer {layer_index}: {error:?}"));
            let encoded = encode::encode(&program.program)
                .unwrap_or_else(|error| panic!("{stem} layer {layer_index}: {error:?}"));
            let decoded = encode::decode(&encoded)
                .unwrap_or_else(|error| panic!("{stem} layer {layer_index}: {error:?}"));
            assert_eq!(decoded, program.program, "{stem} layer {layer_index}");
        }
    }
}
