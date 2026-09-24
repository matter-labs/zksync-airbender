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
    let level = SecurityLevel::Sec100;
    let (nds, external_challenges) = common::proof_to_nds(name, level, &proof);

    common::verify_nds(name, level, &external_challenges, nds).unwrap();
}

/// `mop_smoke`'s shift/binop proof: its trace carries `mop.r.0` byte-swap rows (funct3 = BSWAP
/// in the shift table), so this exercises the BSWAP lookup rows through the verifier.
#[test]
#[ignore]
fn verifier_mop_shift_binop_proof() {
    let path = format!(
        "{}/prover/test_proofs/mop_shift_binop_gkr_proof.json",
        repo_root()
    );
    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file(&path);

    let name = "shift_binop";
    let level = SecurityLevel::Sec100;
    let (nds, external_challenges) = common::proof_to_nds(name, level, &proof);

    common::verify_nds(name, level, &external_challenges, nds).unwrap();
}
