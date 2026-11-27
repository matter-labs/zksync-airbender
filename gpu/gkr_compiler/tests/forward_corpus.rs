use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::proth120::Proth120;
use field::PrimeField;
use gkr_eval_ir::lower_dag;
use gpu_gkr_compiler::{
    compile_forward, encode_forward_program, encode_forward_runtime_program,
    parse_forward_artifact, ElementModel, FieldTag, ForwardInstr, ForwardOperandField,
    ForwardOperandLine, ForwardSpecialStrategy,
};

const CORPUS: &[(&str, &str)] = &[
    (
        "circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json",
        "add_sub_lui_auipc_mop",
    ),
    (
        "circuit_defs/bigint_with_control/generated/layout.json",
        "bigint_with_extended_control",
    ),
    (
        "circuit_defs/blake2_g_function/generated/layout.json",
        "blake2_g_function",
    ),
    (
        "circuit_defs/blake2_with_compression/generated/layout.json",
        "blake2_with_extended_control",
    ),
    (
        "circuit_defs/unrolled_circuits/inits_and_teardowns/generated/layout.json",
        "inits_and_teardowns",
    ),
    (
        "circuit_defs/unrolled_circuits/jump_branch_slt/generated/layout.json",
        "jump_branch_slt",
    ),
    (
        "circuit_defs/keccak_chi5/generated/layout.json",
        "keccak_chi5",
    ),
    (
        "circuit_defs/keccak_column_parity/generated/layout.json",
        "keccak_column_parity",
    ),
    (
        "circuit_defs/keccak_special5/generated/layout.json",
        "keccak_special5",
    ),
    (
        "circuit_defs/keccak_theta_rho/generated/layout.json",
        "keccak_theta_rho",
    ),
    (
        "circuit_defs/unrolled_circuits/load_store_subword_only/generated/layout.json",
        "mem_subword_only",
    ),
    (
        "circuit_defs/unrolled_circuits/load_store_word_only/generated/layout.json",
        "mem_word_only",
    ),
    (
        "circuit_defs/unrolled_circuits/shift_binary/generated/layout.json",
        "shift_binop",
    ),
    (
        "circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json",
        "unified_reduced_machine",
    ),
    (
        "circuit_defs/unrolled_circuits/mul_div_unsigned/generated/layout.json",
        "unsigned_mul_div",
    ),
];

const PROTH120_CORPUS: &[(&str, &str, usize)] = &[(
    "circuit_defs/unrolled_circuits/unified_reduced_machine_proth120_2_21/generated/layout.json",
    "unified_reduced_machine",
    4,
)];

#[test]
fn proth120_retained_forward_artifacts_compile_and_encode() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = root.join("cs/compiled_circuits");
    for &(layout_path, stem, budget) in PROTH120_CORPUS {
        let layout: GKRCircuitArtifact<Proth120> =
            serde_json::from_slice(&std::fs::read(root.join(layout_path)).unwrap()).unwrap();
        let dag = lower_dag(&layout).unwrap();
        let name = format!("{stem}_schedule_b{budget}_gkr_proth120.json");
        let artifact =
            parse_forward_artifact(&std::fs::read(directory.join(&name)).unwrap(), &name).unwrap();
        assert_eq!(artifact.circuit, stem);
        assert_eq!(artifact.budget_buckets, budget);
        assert_eq!(artifact.field, Some(FieldTag::Proth120));
        let forward = compile_forward(&dag, &artifact).unwrap();
        let mut saw_ext = false;
        let mut wide_encoding = Vec::new();
        for (layer, retained) in forward.layers.iter().zip(&artifact.layers) {
            let words = encode_forward_runtime_program(&layer.program).unwrap();
            assert_eq!(
                words.len(),
                encode_forward_program(&layer.program).unwrap().len()
            );
            for word in words {
                wide_encoding.extend_from_slice(&word.to_le_bytes());
            }
            for &value in layer.consts.values() {
                assert!(value < Proth120::CHARACTERISTICS_U128);
                assert_eq!(
                    ElementModel::PROTH120.constant_width as usize,
                    value.to_le_bytes().len()
                );
                wide_encoding.extend_from_slice(&value.to_le_bytes());
            }
            let mut traffic = 0;
            let mut record = |operand: &ForwardOperandLine, field: ForwardOperandField| {
                saw_ext |= field == ForwardOperandField::Ext;
                traffic += usize::from(matches!(operand, ForwardOperandLine::Source { .. }));
            };
            for instruction in &layer.program.instrs {
                match instruction {
                    ForwardInstr::Add {
                        field, operands, ..
                    }
                    | ForwardInstr::Mul {
                        field, operands, ..
                    } => {
                        for operand in operands {
                            record(operand, *field);
                        }
                    }
                    ForwardInstr::Fma {
                        field_lhs,
                        field_rhs,
                        pairs,
                        ..
                    } => {
                        for (lhs, rhs) in pairs {
                            record(lhs, *field_lhs);
                            record(rhs, *field_rhs);
                        }
                    }
                    ForwardInstr::Mov { field, src, .. } => {
                        if let Some(src) = src {
                            record(src, *field);
                        }
                    }
                }
            }
            assert_eq!(traffic, retained.predicted_traffic);
        }
        assert!(saw_ext);
        assert!(!wide_encoding.is_empty());
    }
}

#[test]
fn every_retained_forward_artifact_validates_compiles_and_encodes() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = root.join("cs/compiled_circuits");
    for &(layout_name, stem) in CORPUS {
        let layout_bytes = std::fs::read(root.join(layout_name)).unwrap();
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&layout_bytes).unwrap();
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{stem}: {error}"));

        let artifact_name = format!("{stem}_schedule_b4_gkr.json");
        let artifact_bytes = std::fs::read(directory.join(&artifact_name)).unwrap();
        let artifact = parse_forward_artifact(&artifact_bytes, &artifact_name).unwrap();
        assert_eq!(artifact.circuit, stem, "{stem}");
        assert_eq!(artifact.budget_buckets, 4, "{stem}");
        let compiled =
            compile_forward(&dag, &artifact).unwrap_or_else(|error| panic!("{stem}: {error:?}"));

        assert_eq!(compiled.layers.len(), dag.layers.len(), "{stem}");
    }
}

#[test]
fn unified_2_22_layout_reuses_the_unified_schedule() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = root.join("cs/compiled_circuits");
    let artifact_name = "unified_reduced_machine_schedule_b4_gkr.json";
    let artifact_bytes = std::fs::read(directory.join(artifact_name)).unwrap();
    let artifact = parse_forward_artifact(&artifact_bytes, artifact_name).unwrap();
    let compile = |layout_name: &str| {
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(root.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{layout_name}: {error}"));
        compile_forward(&dag, &artifact).unwrap_or_else(|error| panic!("{layout_name}: {error:?}"))
    };
    let unified =
        compile("circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json");
    let unified22 = compile(
        "circuit_defs/unrolled_circuits/unified_reduced_machine_2_22/generated/layout.json",
    );

    assert_eq!(unified22.layers.len(), unified.layers.len());
    let mut shifted = 0;
    for (index, (layer, layer22)) in unified.layers.iter().zip(&unified22.layers).enumerate() {
        assert_eq!(
            encode_forward_runtime_program(&layer22.program).unwrap(),
            encode_forward_runtime_program(&layer.program).unwrap(),
            "layer {index}"
        );
        assert_eq!(
            layer22.consts.values(),
            layer.consts.values(),
            "layer {index}"
        );
        assert_eq!(
            layer22.specials.len(),
            layer.specials.len(),
            "layer {index}"
        );
        for (special, special22) in layer.specials.iter().zip(layer22.specials.iter()) {
            match (special, special22) {
                (
                    ForwardSpecialStrategy::InitsAndTeardownsTopBits { reference },
                    ForwardSpecialStrategy::InitsAndTeardownsTopBits {
                        reference: reference22,
                    },
                ) => {
                    assert_eq!(reference22.set_index, reference.set_index, "layer {index}");
                    assert_eq!(reference22.shift + 1, reference.shift, "layer {index}");
                    shifted += 1;
                }
                _ => assert_eq!(special22, special, "layer {index}"),
            }
        }
    }
    assert!(shifted > 0);
}
