use super::*;
use crate::proof::memory_policy::{GkrMemoryPolicy, WitnessMemoryPolicy, WitnessPostCommitStorage};
use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;

fn check_policies(base: &BasicUnrolledFixture) {
    let baseline = base.context.get_used_mem_current();
    let (expected, _) = base
        .schedule_prove_with_memory_policy(ProofMemoryPolicy::default())
        .unwrap()
        .finish()
        .unwrap();
    let expected_bytes = serde_json::to_vec(&expected).unwrap();
    assert_eq!(base.context.get_used_mem_current(), baseline);
    let presets =
        [21usize << 30, 30usize << 30].map(|arena| presets::policy(base.circuit_type, arena));
    let mut policies = ProofMemoryPolicy::candidates()
        .chain(GkrMemoryPolicy::candidates().map(|gkr| ProofMemoryPolicy {
            gkr,
            ..Default::default()
        }))
        .chain(presets);
    while let Some(first) = policies.next() {
        let second = policies.next().unwrap_or(first);
        let jobs =
            [first, second].map(|policy| base.schedule_prove_with_memory_policy(policy).unwrap());
        for job in jobs {
            let (proof, _) = job.finish().unwrap();
            assert_gkr_proof_eq_for_test(&proof, &expected);
            assert_eq!(serde_json::to_vec(&proof).unwrap(), expected_bytes);
        }
        assert_eq!(base.context.get_used_mem_current(), baseline);
    }
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_separate_with_setup() {
    check_policies(&prepare_basic_unrolled_profiling_fixture());
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_separate_without_setup() {
    check_policies(
        &inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(
            false,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .0,
    );
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_virtual_k0() {
    let config = delegation_prover_config(DelegationCircuitType::KeccakSpecial5);
    check_policies(&proof_matrix::prepare_keccak_special5_fixture_for_config(config, false).0);
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_virtual_k2() {
    let config = delegation_prover_config(DelegationCircuitType::Blake2WithCompression);
    check_policies(
        &proof_matrix::prepare_blake2_with_compression_fixture_for_config(config, false).0,
    );
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_physical_k4() {
    let config = packed_config(20, 4, SecurityLevel::Sec100);
    check_policies(
        &proof_matrix::prepare_blake2_with_compression_fixture_for_config(config, false).0,
    );
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_merged_fold1() {
    let mut config = packed_config(20, 4, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    check_policies(
        &proof_matrix::prepare_blake2_with_compression_fixture_for_config(config, false).0,
    );
}

#[test]
#[ignore = "GPU policy candidates and presets against the default-policy proof"]
fn policies_merged_fold0() {
    let mut config = delegation_prover_config(DelegationCircuitType::KeccakSpecial5);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    check_policies(&proof_matrix::prepare_keccak_special5_fixture_for_config(config, false).0);
}

#[test]
#[should_panic(expected = "invalid witness memory policy")]
fn invalid_witness_policy_is_refused() {
    let base = prepare_basic_unrolled_profiling_fixture();
    let _ = base.schedule_prove_with_memory_policy(ProofMemoryPolicy {
        witness: WitnessMemoryPolicy {
            post_commitment: WitnessPostCommitStorage::RawEvaluations,
            ..Default::default()
        },
        ..Default::default()
    });
}
