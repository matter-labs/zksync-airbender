use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::lower_dag;

const RETAINED_LAYOUTS: &[&str] = &[
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
fn every_retained_layout_lowers_and_validates() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
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

    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let bytes =
        std::fs::read(directory.join("unified_reduced_machine_layout_gkr_proth120_2p21.json"))
            .unwrap();
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
