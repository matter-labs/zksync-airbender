use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::lower_dag;
use sha3::{Digest, Sha3_256};

const CORPUS: &[&str] = &[
    "add_sub_lui_auipc_mop",
    "bigint_with_extended_control",
    "blake2_g_function",
    "blake2_with_extended_control",
    "inits_and_teardowns",
    "jump_branch_slt",
    "keccak_chi5",
    "keccak_column_parity",
    "keccak_special5",
    "keccak_theta_rho",
    "mem_subword_only",
    "mem_word_only",
    "shift_binop",
    "unified_reduced_machine",
    "unsigned_mul_div",
];

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
fn babybear_lowered_dags_match_committed_hashes() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let layouts = manifest.join("../cs/compiled_circuits");
    let fixture = manifest.join("tests/fixtures/lowering_identity.json");
    let mut hashes = BTreeMap::new();
    for &stem in CORPUS {
        let bytes = std::fs::read(layouts.join(format!("{stem}_layout_gkr.json")))
            .unwrap_or_else(|error| panic!("{stem}: {error}"));
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&bytes).unwrap_or_else(|error| panic!("{stem}: {error}"));
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{stem}: {error}"));
        let encoded = serde_json::to_vec(&dag).unwrap();
        hashes.insert(stem.to_owned(), hex(&Sha3_256::digest(&encoded)));
    }
    if std::env::var_os("AB_RECORD_IR_HASHES").is_some() {
        let mut text = serde_json::to_string_pretty(&hashes).unwrap();
        text.push('\n');
        std::fs::write(&fixture, text).unwrap();
    }
    let committed: BTreeMap<String, String> =
        serde_json::from_slice(&std::fs::read(&fixture).unwrap()).unwrap();
    assert_eq!(committed.len(), CORPUS.len());
    for (stem, hash) in &hashes {
        assert_eq!(committed.get(stem), Some(hash), "{stem}");
    }
}
