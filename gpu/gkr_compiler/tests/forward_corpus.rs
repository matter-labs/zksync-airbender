use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::proth120::Proth120;
use field::PrimeField;
use gkr_eval_ir::lower_dag;
use gpu_gkr_compiler::{
    compile_forward, encode_forward_program, encode_forward_runtime_program,
    parse_forward_artifact, ElementModel, FieldTag, ForwardInstr, ForwardOperandField,
    ForwardOperandLine, ForwardProgramBundle, ForwardSpecialStrategy,
};
use sha3::{Digest, Sha3_256};

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
    ("keccak_chi5_layout_gkr.json", "keccak_chi5"),
    (
        "keccak_column_parity_layout_gkr.json",
        "keccak_column_parity",
    ),
    ("keccak_special5_layout_gkr.json", "keccak_special5"),
    ("keccak_theta_rho_layout_gkr.json", "keccak_theta_rho"),
    ("mem_subword_only_layout_gkr.json", "mem_subword_only"),
    ("mem_word_only_layout_gkr.json", "mem_word_only"),
    ("shift_binop_layout_gkr.json", "shift_binop"),
    (
        "unified_reduced_machine_layout_gkr.json",
        "unified_reduced_machine",
    ),
    ("unsigned_mul_div_layout_gkr.json", "unsigned_mul_div"),
];

const PROTH120_CORPUS: &[(&str, &str, usize)] = &[(
    "unified_reduced_machine_layout_gkr_proth120.json",
    "unified_reduced_machine",
    4,
)];

#[test]
fn proth120_retained_forward_artifacts_compile_and_encode() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for &(layout_name, stem, budget) in PROTH120_CORPUS {
        let layout: GKRCircuitArtifact<Proth120> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
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
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for &(layout_name, stem) in CORPUS {
        let layout_bytes = std::fs::read(directory.join(layout_name)).unwrap();
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
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let artifact_name = "unified_reduced_machine_schedule_b4_gkr.json";
    let artifact_bytes = std::fs::read(directory.join(artifact_name)).unwrap();
    let artifact = parse_forward_artifact(&artifact_bytes, artifact_name).unwrap();
    let compile = |layout_name: &str| {
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{layout_name}: {error}"));
        compile_forward(&dag, &artifact).unwrap_or_else(|error| panic!("{layout_name}: {error:?}"))
    };
    let unified = compile("unified_reduced_machine_layout_gkr.json");
    let unified22 = compile("unified_reduced_machine_2_22_layout_gkr.json");

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

fn push_text(out: &mut Vec<u8>, text: &str) {
    out.extend_from_slice(&(text.len() as u32).to_le_bytes());
    out.extend_from_slice(text.as_bytes());
}

fn stable_forward_program_bytes(bundle: &ForwardProgramBundle) -> Vec<u8> {
    let mut out = Vec::new();
    for (index, layer) in bundle.layers.iter().enumerate() {
        out.extend_from_slice(&(index as u32).to_le_bytes());
        let words = encode_forward_runtime_program(&layer.program).unwrap();
        out.extend_from_slice(&(words.len() as u32).to_le_bytes());
        for word in words {
            out.extend_from_slice(&word.to_le_bytes());
        }
        let consts = layer.consts.values();
        out.extend_from_slice(&(consts.len() as u32).to_le_bytes());
        for &value in consts {
            out.extend_from_slice(&u32::try_from(value).unwrap().to_le_bytes());
        }
        out.extend_from_slice(&(layer.specials.len() as u32).to_le_bytes());
        for special in layer.specials.iter() {
            push_text(&mut out, &format!("{special:?}"));
        }
        out.push(layer.derived_e4.uses_lookup_additive() as u8);
        let arg_refs = layer.derived_e4.arg_refs();
        out.extend_from_slice(&(arg_refs.len() as u32).to_le_bytes());
        for reference in arg_refs {
            push_text(&mut out, &format!("{reference:?}"));
        }
        push_text(&mut out, &format!("{:?}", layer.source_windows));
        push_text(&mut out, &format!("{:?}", layer.backings));
    }
    out
}

#[derive(Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct ForwardProgramIdentity {
    program_sha3_256: String,
    predicted_traffic: Vec<usize>,
}

#[test]
fn babybear_forward_programs_match_committed_hashes() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let directory = manifest.join("../../cs/compiled_circuits");
    let fixture = manifest.join("tests/fixtures/forward_programs.json");
    let mut identities = BTreeMap::new();
    for &(layout_name, stem) in CORPUS {
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{stem}: {error}"));
        let artifact_name = format!("{stem}_schedule_b4_gkr.json");
        let artifact_bytes = std::fs::read(directory.join(&artifact_name)).unwrap();
        let artifact = parse_forward_artifact(&artifact_bytes, &artifact_name).unwrap();
        let compiled =
            compile_forward(&dag, &artifact).unwrap_or_else(|error| panic!("{stem}: {error:?}"));
        let digest = Sha3_256::digest(stable_forward_program_bytes(&compiled));
        identities.insert(
            stem.to_owned(),
            ForwardProgramIdentity {
                program_sha3_256: digest.iter().map(|byte| format!("{byte:02x}")).collect(),
                predicted_traffic: artifact
                    .layers
                    .iter()
                    .map(|layer| layer.predicted_traffic)
                    .collect(),
            },
        );
    }
    if std::env::var_os("AB_RECORD_FORWARD_PROGRAM_HASHES").is_some() {
        let mut text = serde_json::to_string_pretty(&identities).unwrap();
        text.push('\n');
        std::fs::write(&fixture, text).unwrap();
    }
    let committed: BTreeMap<String, ForwardProgramIdentity> =
        serde_json::from_slice(&std::fs::read(&fixture).unwrap()).unwrap();
    assert_eq!(committed.len(), CORPUS.len());
    for (stem, identity) in &identities {
        assert_eq!(committed.get(stem), Some(identity), "{stem}");
    }
}
