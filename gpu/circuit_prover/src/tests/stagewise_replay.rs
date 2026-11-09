//! Shared transcript replay for BabyBear and Proth120 stagewise tests.
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};
use gpu_gkr::backward::GKRBackwardStageSnapshot;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::GKRProof;
use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full_lsb;
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
use prover::transcript::Transcript;
use std::collections::BTreeMap;
use worker::Worker;

enum ExpectedClaims<E> {
    Ordered(Vec<E>),
    ByAddress(BTreeMap<GKRAddress, E>),
}

pub struct ExpectedStageSnapshot<E> {
    layer_idx: usize,
    claim_point: Vec<E>,
    batching_challenge: E,
    claims: ExpectedClaims<E>,
}

fn evaluate_output<E: Field>(values: &[E], eq: &[E]) -> E {
    values
        .iter()
        .zip(eq)
        .fold(E::ZERO, |mut acc, (&value, &weight)| {
            let mut term = value;
            term.mul_assign(&weight);
            acc.add_assign(&term);
            acc
        })
}

fn interpolate<E: Field>(a: E, b: E, at: E) -> E {
    let mut result = b;
    result.sub_assign(&a);
    result.mul_assign(&at);
    result.add_assign(&a);
    result
}

pub fn replay_expected_snapshots<F, E, T, H>(
    proof: &GKRProof<F, E, H>,
    mut seed: T::Seed,
    main_layers: usize,
) -> Vec<ExpectedStageSnapshot<E>>
where
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: Transcript<F, E>,
    H: ColumnMajorMerkleTreeConstructor<F>,
{
    let worker = Worker::new();
    let explicit_evaluations = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|pair| pair.iter().flat_map(|values| values.iter().copied()))
        .collect::<Vec<_>>();
    commit_field_els::<F, E, T>(&mut seed, &explicit_evaluations);
    let final_trace_size_log_2 = proof
        .final_explicit_evaluations
        .values()
        .next()
        .expect("proof must contain an explicit output")[0]
        .len()
        .trailing_zeros() as usize;
    let mut initial_challenges =
        draw_random_field_els::<F, E, T>(&mut seed, final_trace_size_log_2 + 1);
    let batching_challenge = initial_challenges.pop().unwrap();
    let eq = make_eq_poly_in_full_lsb::<E>(&initial_challenges, &worker)
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

    for (&layer_idx, layer) in proof.sumcheck_intermediate_values.iter().rev() {
        let mut round_challenges = Vec::with_capacity(layer.sumcheck_num_rounds);
        for coefficients in &layer.internal_round_coefficients {
            commit_field_els::<F, E, T>(&mut seed, coefficients.as_multilinear());
            round_challenges.push(draw_random_field_els::<F, E, T>(&mut seed, 1)[0]);
        }
        let mut claim_point = Vec::with_capacity(layer.sumcheck_num_rounds + 1);

        let (batching_challenge, claims) = if layer_idx >= main_layers {
            let transcript_values = layer
                .final_step_evaluations
                .values()
                .flatten()
                .copied()
                .collect::<Vec<_>>();
            commit_field_els::<F, E, T>(&mut seed, &transcript_values);
            let challenges = draw_random_field_els::<F, E, T>(&mut seed, 2);
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
            commit_field_els::<F, E, T>(&mut seed, &transcript_values);
            let batching_challenge = draw_random_field_els::<F, E, T>(&mut seed, 1)[0];
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

pub fn assert_stage_snapshots<E: Field>(
    actual_snapshots: &[GKRBackwardStageSnapshot<E>],
    expected_snapshots: &[ExpectedStageSnapshot<E>],
) {
    assert_eq!(actual_snapshots.len(), expected_snapshots.len());
    for (actual, expected) in actual_snapshots.iter().zip(expected_snapshots) {
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
}
