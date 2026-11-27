use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::lower_dag;

const RETAINED_LAYOUTS: &[&str] = &[
    "circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json",
    "circuit_defs/bigint_with_control/generated/layout.json",
    "circuit_defs/blake2_g_function/generated/layout.json",
    "circuit_defs/blake2_with_compression/generated/layout.json",
    "circuit_defs/unrolled_circuits/inits_and_teardowns/generated/layout.json",
    "circuit_defs/unrolled_circuits/jump_branch_slt/generated/layout.json",
    "circuit_defs/keccak_special5/generated/layout.json",
    "circuit_defs/unrolled_circuits/load_store_subword_only/generated/layout.json",
    "circuit_defs/unrolled_circuits/load_store_word_only/generated/layout.json",
    "circuit_defs/unrolled_circuits/shift_binary/generated/layout.json",
    "circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json",
    "circuit_defs/unrolled_circuits/mul_div_unsigned/generated/layout.json",
];

#[test]
fn every_retained_layout_lowers_and_validates() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    for fixture in RETAINED_LAYOUTS {
        let path = directory.join(fixture);
        let bytes = std::fs::read(&path).unwrap_or_else(|error| panic!("{fixture}: {error}"));
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&bytes).unwrap_or_else(|error| panic!("{fixture}: {error}"));
        lower_dag(&artifact).unwrap_or_else(|error| panic!("{fixture}: {error}"));
    }
}

#[test]
fn no_cache_layouts_are_rejected() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let fixture = "add_sub_lui_auipc_mop_layout_no_caches_gkr.json";
    let artifact: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_slice(&std::fs::read(directory.join(fixture)).unwrap()).unwrap();

    let error = lower_dag(&artifact).expect_err("GPU no-cache layouts are not supported");
    assert!(
        error.contains("unsupported relation"),
        "unexpected error: {error}"
    );
}

#[test]
fn proth120_unified_lowers() {
    use field::proth120::Proth120;
    use field::PrimeField;
    use gkr_eval_ir::SourceKind;

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120_2_21/generated/layout.json",
    );
    let bytes = std::fs::read(path).unwrap();
    let artifact: GKRCircuitArtifact<Proth120> = serde_json::from_slice(&bytes).unwrap();
    let dag = lower_dag(&artifact).unwrap();
    let modulus = Proth120::CHARACTERISTICS_U128;
    assert_eq!(dag.modulus, modulus);
    let constants: Vec<u128> = dag
        .layers
        .iter()
        .flat_map(|layer| &layer.sources)
        .filter_map(|source| match source {
            SourceKind::Constant { value } => Some(*value),
            _ => None,
        })
        .collect();
    assert!(constants.iter().all(|&value| value < modulus));
    assert!(constants.iter().any(|&value| value >= 1 << 32));
    assert!(constants.contains(&(modulus - 1)));
}
