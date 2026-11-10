use super::*;

#[test]
#[ignore = "GPU cap validation rejects a different committed circuit proof"]
#[should_panic(expected = "GPU memory cap differs from committed proof")]
fn rejects_mismatched_committed_memory_cap() {
    let fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::AddSubLuiAuipcMop,
        circuit_common::SoundnessMode::DEFAULT,
    );
    let other = load_committed_proof(
        CanonicalCircuit::ShiftBinop,
        circuit_common::SoundnessMode::DEFAULT,
    );
    assert_memory_caps_match_committed(&fixture.base.memory_tree_caps, &other.proof);
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn add_sub_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::AddSubLuiAuipcMop,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn jump_branch_slt_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::JumpBranchSlt,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn shift_binop_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::ShiftBinop,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn unsigned_mul_div_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::UnsignedMulDiv,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn mem_word_only_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::MemWordOnly,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn mem_subword_only_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::MemSubwordOnly,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn inits_and_teardowns_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::InitsAndTeardowns,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn unified_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::UnifiedReducedMachine,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn bigint_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::BigintWithExtendedControl,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn blake2_with_compression_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::Blake2WithExtendedControl,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn keccak_special5_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::KeccakSpecial5,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn keccak_column_parity_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::KeccakColumnParity,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn keccak_theta_rho_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::KeccakThetaRho,
        circuit_common::SoundnessMode::DEFAULT,
    );
}

#[test]
#[ignore = "GPU memory commitment compared with committed canonical bytes"]
fn keccak_chi5_memory_cap_matches_committed() {
    let _fixture = prepare_canonical_proof_fixture(
        CanonicalCircuit::KeccakChi5,
        circuit_common::SoundnessMode::DEFAULT,
    );
}
