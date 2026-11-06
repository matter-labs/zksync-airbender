#[macro_use]
mod common;

use common::{SecurityLevel, SoundnessMode};

fn verify_mop(name: &str) {
    let level = SecurityLevel::Sec100;
    for &mode in SoundnessMode::ALL {
        let proof = common::circuit_by_name(name).proof_for_mode(level, mode);
        let (nds, external_challenges) = common::proof_to_nds(name, level, &proof);
        common::verify_nds(name, level, mode, &external_challenges, nds).unwrap();
    }
}

/// Both canonical add/sub proofs use `mop_smoke`'s MOP rows.
#[test]
fn verifier_mop_proof() {
    verify_mop("add_sub_lui_auipc_mop");
}

/// Both canonical shift/binop proofs use `mop_smoke`'s `rev8` byte-swap rows.
#[test]
fn verifier_mop_shift_binop_proof() {
    verify_mop("shift_binop");
}
