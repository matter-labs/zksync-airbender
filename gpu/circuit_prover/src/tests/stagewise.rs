use super::*;
use prover::gkr::prover::transcript_utils::draw_random_field_els_with_pow;
#[path = "stagewise_replay.rs"]
mod replay;

fn replay_expected_snapshots(
    fixture: &BasicUnrolledProofFixture,
) -> Vec<replay::ExpectedStageSnapshot<E4>> {
    let proof = &fixture.committed_proof;
    let mut transcript_input = proof.inits_and_teardowns_top_bits.clone();
    proof
        .external_challenges
        .flatten_into_buffer(&mut transcript_input);
    for commitment in [
        &proof.whir_proof.setup_commitment,
        &proof.whir_proof.memory_commitment,
        &proof.whir_proof.witness_commitment,
    ] {
        if commitment.num_columns != 0 {
            flatten_merkle_caps_iter_into(
                Some(commitment.commitment.cap.clone()).into_iter(),
                &mut transcript_input,
            );
        }
    }

    let mut seed = <Blake2sTranscript as Transcript<BF, E4>>::commit_initial_u32(&transcript_input);
    let worker = Worker::new();
    let compiled_circuit = fixture.base.gkr_programs.compiled_circuit();
    let lookup_pow_bits = crate::upstream::pow_bits::lookup_challenges_pow_bits::<BF, E4>(
        fixture.base.prover_config.security_level.security_bits(),
        crate::upstream::pow_bits::lookup_identity_degree(compiled_circuit),
    );
    let (lookup_nonce, _) = draw_random_field_els_with_pow::<BF, E4, Blake2sTranscript>(
        &mut seed,
        2,
        lookup_pow_bits,
        &worker,
    );
    assert_eq!(lookup_nonce, proof.lookup_challenges_pow_nonce);

    replay::replay_expected_snapshots::<BF, E4, Blake2sTranscript, _>(
        proof,
        seed,
        compiled_circuit.layers.len(),
    )
}

fn run_stagewise_parity(fixture: &BasicUnrolledProofFixture) {
    let preparation_peak = fixture.base.context.get_used_mem_peak();
    let baseline = fixture.base.context.get_used_mem_current();
    fixture.base.context.reset_used_mem_peak();
    let mut transfers = fixture.base.create_transfers().unwrap();
    transfers.schedule(&fixture.base.context).unwrap();
    let job = crate::proof::prove_stagewise(
        crate::proof::BabyBearProofRequest::new(
            &fixture.base.gkr_programs,
            &fixture.base.prover_config,
            fixture.base.final_trace_size_log_2,
            transfers,
            ProofMemoryPolicy::default(),
            crate::proof::memory_policy::PartialTreePolicy::DEFAULT,
        ),
        &fixture.base.context,
    )
    .unwrap();
    let (gpu_proof, actual_snapshots, _) = job.finish_stagewise().unwrap();

    for (name, actual, expected) in [
        (
            "setup",
            &gpu_proof.whir_proof.setup_commitment,
            &fixture.committed_proof.whir_proof.setup_commitment,
        ),
        (
            "memory",
            &gpu_proof.whir_proof.memory_commitment,
            &fixture.committed_proof.whir_proof.memory_commitment,
        ),
        (
            "witness",
            &gpu_proof.whir_proof.witness_commitment,
            &fixture.committed_proof.whir_proof.witness_commitment,
        ),
    ] {
        assert_eq!(
            actual.commitment.cap, expected.commitment.cap,
            "stage 1 {name} cap diverged",
        );
    }
    assert_eq!(
        gpu_proof.final_explicit_evaluations, fixture.committed_proof.final_explicit_evaluations,
        "forward output evaluations diverged",
    );

    let expected_snapshots = replay_expected_snapshots(fixture);
    replay::assert_stage_snapshots(&actual_snapshots, &expected_snapshots);
    fixture.assert_proof(&gpu_proof);
    assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
    record_test_resources(&fixture.base, preparation_peak, 1);
}

#[test]
#[ignore]
fn add_sub_stagewise_pessimistic_conjecture() {
    run_stagewise_parity(&prepare_canonical_proof_fixture(
        CanonicalCircuit::AddSubLuiAuipcMop,
        circuit_common::SoundnessMode::PessimisticConjecture,
    ));
}

#[test]
#[ignore]
fn add_sub_stagewise_ethproofs_soundcalc() {
    run_stagewise_parity(&prepare_canonical_proof_fixture(
        CanonicalCircuit::AddSubLuiAuipcMop,
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    ));
}

#[test]
#[ignore]
fn unified_stagewise_pessimistic_conjecture() {
    run_stagewise_parity(&prepare_canonical_proof_fixture(
        CanonicalCircuit::UnifiedReducedMachine,
        circuit_common::SoundnessMode::PessimisticConjecture,
    ));
}

#[test]
#[ignore]
fn unified_stagewise_ethproofs_soundcalc() {
    run_stagewise_parity(&prepare_canonical_proof_fixture(
        CanonicalCircuit::UnifiedReducedMachine,
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    ));
}
