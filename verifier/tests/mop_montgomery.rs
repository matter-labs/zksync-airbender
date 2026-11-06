#[macro_use]
mod common;

use common::{SecurityLevel, SoundnessMode};
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

// These two fixtures cover MOP/BSWAP rows in the default soundness mode.
fn mop_proof(
    fixture: &str,
    circuit: &str,
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    let path = format!("{}/prover/test_proofs/{fixture}", repo_root());
    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file(&path);
    assert_eq!(
        proof.whir_proof.whir_schedule,
        common::circuit_by_name(circuit)
            .whir_schedule_for(SecurityLevel::Sec100)
            .clone(),
        "{fixture}: stale MOP proof fixture; regenerate it with the current default-mode config"
    );
    proof
}

#[test]
fn verifier_mop_proof() {
    let name = "add_sub_lui_auipc_mop";
    let proof = mop_proof("mop_add_sub_gkr_proof.json", name);
    let level = SecurityLevel::Sec100;
    let (nds, external_challenges) = common::proof_to_nds(name, level, &proof);

    common::verify_nds(
        name,
        level,
        SoundnessMode::DEFAULT,
        &external_challenges,
        nds,
    )
    .unwrap();
}

/// `mop_smoke`'s shift/binop proof: its trace carries `rev8` byte-swap rows (funct3 = BSWAP
/// in the shift table), so this exercises the BSWAP lookup rows through the verifier.
#[test]
fn verifier_mop_shift_binop_proof() {
    let name = "shift_binop";
    let proof = mop_proof("mop_shift_binop_gkr_proof.json", name);
    let level = SecurityLevel::Sec100;
    let (nds, external_challenges) = common::proof_to_nds(name, level, &proof);

    common::verify_nds(
        name,
        level,
        SoundnessMode::DEFAULT,
        &external_challenges,
        nds,
    )
    .unwrap();
}
