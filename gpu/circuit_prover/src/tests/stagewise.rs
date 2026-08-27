use std::collections::BTreeMap;

use super::*;
use cs::definitions::GKRAddress;
use prover::gkr::prover::transcript_utils::{
    commit_field_els, draw_random_field_els, draw_random_field_els_with_pow,
};
use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full_lsb;

enum ExpectedClaims {
    Ordered(Vec<E4>),
    ByAddress(BTreeMap<GKRAddress, E4>),
}

struct ExpectedStageSnapshot {
    layer_idx: usize,
    claim_point: Vec<E4>,
    batching_challenge: E4,
    claims: ExpectedClaims,
}

fn evaluate_output(values: &[E4], eq: &[E4]) -> E4 {
    values
        .iter()
        .zip(eq)
        .fold(E4::ZERO, |mut acc, (&value, &weight)| {
            let mut term = value;
            term.mul_assign(&weight);
            acc.add_assign(&term);
            acc
        })
}

fn interpolate(a: E4, b: E4, at: E4) -> E4 {
    let mut result = b;
    result.sub_assign(&a);
    result.mul_assign(&at);
    result.add_assign(&a);
    result
}

fn replay_expected_snapshots(fixture: &BasicUnrolledProofFixture) -> Vec<ExpectedStageSnapshot> {
    let proof = &fixture.expected_cpu_proof;
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
    let lookup_pow_bits =
        crate::config::lookup_challenges_pow_bits(&fixture.base.prover_config, compiled_circuit);
    let (lookup_nonce, _) = draw_random_field_els_with_pow::<BF, E4, Blake2sTranscript>(
        &mut seed,
        2,
        lookup_pow_bits,
        &worker,
    );
    assert_eq!(lookup_nonce, proof.lookup_challenges_pow_nonce);

    let explicit_evaluations = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|pair| pair.iter().flat_map(|values| values.iter().copied()))
        .collect::<Vec<_>>();
    commit_field_els::<BF, E4, Blake2sTranscript>(&mut seed, &explicit_evaluations);
    let final_trace_size_log_2 = proof
        .final_explicit_evaluations
        .values()
        .next()
        .expect("proof must contain an explicit output")[0]
        .len()
        .trailing_zeros() as usize;
    let mut initial_challenges =
        draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, final_trace_size_log_2 + 1);
    let batching_challenge = initial_challenges.pop().unwrap();
    let eq = make_eq_poly_in_full_lsb::<E4>(&initial_challenges, &worker)
        .pop()
        .unwrap();
    let initial_claims = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|pair| pair.iter().map(|values| evaluate_output(values, &eq)))
        .collect::<Vec<_>>();
    let initial_layer_idx = proof
        .sumcheck_intermediate_values
        .keys()
        .next_back()
        .copied()
        .expect("proof must contain a backward layer")
        + 1;
    let mut expected = vec![ExpectedStageSnapshot {
        layer_idx: initial_layer_idx,
        claim_point: initial_challenges,
        batching_challenge,
        claims: ExpectedClaims::Ordered(initial_claims),
    }];

    let main_layers = compiled_circuit.layers.len();
    for (&layer_idx, layer) in proof.sumcheck_intermediate_values.iter().rev() {
        let mut round_challenges = Vec::with_capacity(layer.sumcheck_num_rounds);
        for coefficients in &layer.internal_round_coefficients {
            commit_field_els::<BF, E4, Blake2sTranscript>(&mut seed, coefficients.as_multilinear());
            round_challenges
                .push(draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 1)[0]);
        }
        let mut claim_point = Vec::with_capacity(layer.sumcheck_num_rounds + 1);

        let (batching_challenge, claims) = if layer_idx >= main_layers {
            let transcript_values = layer
                .final_step_evaluations
                .values()
                .flatten()
                .copied()
                .collect::<Vec<_>>();
            commit_field_els::<BF, E4, Blake2sTranscript>(&mut seed, &transcript_values);
            let challenges = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 2);
            // Plain variable order: the end-of-layer challenge binds the gate
            // bit, which is coordinate 0 of the polys the next layer reads, so
            // it LEADS the point.
            claim_point.push(challenges[0]);
            claim_point.extend_from_slice(&round_challenges);
            let claims = layer
                .final_step_evaluations
                .iter()
                .map(|(&address, values)| {
                    (address, interpolate(values[0], values[1], challenges[0]))
                })
                .collect();
            (challenges[1], claims)
        } else {
            let transcript_values = layer
                .final_step_evaluations
                .values()
                .flatten()
                .copied()
                .chain(
                    layer
                        .extra_evaluations_from_caching_relations
                        .values()
                        .copied(),
                )
                .collect::<Vec<_>>();
            let mut claims = layer
                .final_step_evaluations
                .iter()
                .map(|(&address, values)| (address, values[0]))
                .collect::<BTreeMap<_, _>>();
            claims.extend(
                layer
                    .extra_evaluations_from_caching_relations
                    .iter()
                    .map(|(&address, &value)| (address, value)),
            );
            commit_field_els::<BF, E4, Blake2sTranscript>(&mut seed, &transcript_values);
            let batching_challenge =
                draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 1)[0];
            claim_point.extend_from_slice(&round_challenges);
            (batching_challenge, claims)
        };
        expected.push(ExpectedStageSnapshot {
            layer_idx,
            claim_point,
            batching_challenge,
            claims: ExpectedClaims::ByAddress(claims),
        });
    }
    expected
}

fn run_stagewise_parity(fixture: &BasicUnrolledProofFixture) {
    let mut transfers = fixture.base.create_transfers().unwrap();
    transfers.schedule(&fixture.base.context).unwrap();
    let job = crate::proof::prove_stagewise(
        &fixture.base.gkr_programs,
        &fixture.base.prover_config,
        fixture.base.final_trace_size_log_2,
        transfers,
        &fixture.base.context,
    )
    .unwrap();
    let (gpu_proof, actual_snapshots, _) = job.finish_stagewise().unwrap();

    for (name, actual, expected) in [
        (
            "setup",
            &gpu_proof.whir_proof.setup_commitment,
            &fixture.expected_cpu_proof.whir_proof.setup_commitment,
        ),
        (
            "memory",
            &gpu_proof.whir_proof.memory_commitment,
            &fixture.expected_cpu_proof.whir_proof.memory_commitment,
        ),
        (
            "witness",
            &gpu_proof.whir_proof.witness_commitment,
            &fixture.expected_cpu_proof.whir_proof.witness_commitment,
        ),
    ] {
        assert_eq!(
            actual.commitment.cap, expected.commitment.cap,
            "stage 1 {name} cap diverged",
        );
    }
    assert_eq!(
        gpu_proof.final_explicit_evaluations, fixture.expected_cpu_proof.final_explicit_evaluations,
        "forward output evaluations diverged",
    );

    let expected_snapshots = replay_expected_snapshots(fixture);
    assert_eq!(actual_snapshots.len(), expected_snapshots.len());
    for (actual, expected) in actual_snapshots.iter().zip(&expected_snapshots) {
        assert_eq!(actual.layer_idx, expected.layer_idx);
        assert_eq!(
            actual.claim_point, expected.claim_point,
            "claim point diverged after layer {}",
            actual.layer_idx,
        );
        assert_eq!(
            actual.batching_challenge, expected.batching_challenge,
            "batching challenge diverged after layer {}",
            actual.layer_idx,
        );
        match &expected.claims {
            ExpectedClaims::Ordered(expected) => assert_eq!(
                actual.claims.values().copied().collect::<Vec<_>>(),
                *expected,
                "claims diverged at the forward/backward handoff",
            ),
            ExpectedClaims::ByAddress(expected) => assert_eq!(
                &actual.claims, expected,
                "claims diverged after layer {}",
                actual.layer_idx,
            ),
        }
    }
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

#[test]
#[ignore]
fn run_add_sub_stagewise_parity_test() {
    run_stagewise_parity(&prepare_basic_unrolled_proof_fixture());
}

#[test]
#[ignore]
fn run_unified_stagewise_parity_test() {
    run_stagewise_parity(&prepare_unified_proof_fixture());
}
