#![cfg(feature = "security_80")]

#[macro_use]
mod common;

use common::SecurityLevel;
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;

fn repo_root() -> String {
    format!("{}/..", env!("CARGO_MANIFEST_DIR"))
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(path: &str) -> T {
    let src = std::fs::File::open(path).unwrap();
    serde_json::from_reader(src).unwrap()
}

#[test]
#[ignore]
fn verifier_mop_proof() {
    let path = format!(
        "{}/prover/test_proofs/mop_add_sub_gkr_proof.json",
        repo_root()
    );
    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file(&path);

    let name = "add_sub_lui_auipc_mop";
    let level = SecurityLevel::Sec80;
    let (nds, external_challenges) = common::proof_to_nds(name, level, &proof);

    common::verify_nds(name, level, &external_challenges, nds).unwrap();
}
