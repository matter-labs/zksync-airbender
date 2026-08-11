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
