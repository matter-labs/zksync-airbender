use std::collections::BTreeMap;
use std::mem::MaybeUninit;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, GateArtifacts, NoFieldGKRRelation};
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};
use transcript::Seed;
use worker::Worker;

use super::utils::*;
use crate::gkr::prover::sumcheck_loop::evaluate_sumcheck_for_layer;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::eq_poly::*;

type F = Mersenne31Field;
type E = Mersenne31Quartic;

/// Test the full sumcheck loop with a simple product gate.
#[test]
fn test_sumcheck_loop_product() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let worker = Worker::new_with_num_threads(1);

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let output = compute_product::<F, E>(&a, &b);

    let addr_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let mut storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output.clone())],
    );

    let layer = GKRLayerDescription {
        layer: 0,
        gates: vec![GateArtifacts {
            output_layer: 1,
            enforced_relation: NoFieldGKRRelation::TrivialProduct {
                input: [addr_a, addr_b],
                output: addr_out,
            },
        }],
        gates_with_external_connections: vec![],
        cached_relations: BTreeMap::new(),
        additional_base_layer_openings: vec![],
    };

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<E>(&prev_challenges, &worker);
    let eq_last = eq_precomputed.last().unwrap();

    let output_claim = evaluate_with_precomputed_eq_ext::<E>(&output, eq_last);

    let mut claims_storage: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_out, output_claim);
    claims_storage.insert(1, output_claims);

    let mut claim_points: BTreeMap<usize, Vec<E>> = BTreeMap::new();
    claim_points.insert(1, prev_challenges.clone());

    let lookup_multiplicative_part = E::from_base(F::from_u64_with_reduction(0xff));
    let lookup_additive_part = E::from_base(F::from_u64_with_reduction(42));
    let constraints_batch_challenge = E::from_base(F::from_u64_with_reduction(127));

    let mut batching_challenge = E::from_base(F::from_u64_with_reduction(0xff));
    let mut seed = Seed::default();

    evaluate_sumcheck_for_layer::<F, E>(
        0,
        &layer,
        &mut claim_points,
        &mut claims_storage,
        &mut storage,
        &mut batching_challenge,
        unsafe { MaybeUninit::uninit().assume_init_ref() }, // unused
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge,
        &GKRExternalChallenges::default(),
        &mut seed,
        &worker,
    );

    assert!(
        claims_storage.contains_key(&0),
        "Claims for layer 0 should exist"
    );
    assert!(
        claim_points.contains_key(&0),
        "Claim points for layer 0 should exist"
    );

    let layer_0_claims = claims_storage.get(&0).unwrap();
    let layer_0_challenges = claim_points.get(&0).unwrap();

    // Verify that we have claims for the input addresses
    assert!(
        layer_0_claims.contains_key(&addr_a),
        "Claim for input A should exist"
    );
    assert!(
        layer_0_claims.contains_key(&addr_b),
        "Claim for input B should exist"
    );

    assert_eq!(
        layer_0_challenges.len(),
        FOLDING_STEPS,
        "Should have correct number of challenges"
    );

    let eq_for_claims = make_eq_poly_in_full::<E>(layer_0_challenges, &worker);
    let eq_claims_last = eq_for_claims.last().unwrap();

    let expected_a = evaluate_with_precomputed_eq_ext::<E>(&a, eq_claims_last);
    let expected_b = evaluate_with_precomputed_eq_ext::<E>(&b, eq_claims_last);

    assert_eq!(
        layer_0_claims.get(&addr_a).unwrap(),
        &expected_a,
        "Claim for A should match expected value"
    );
    assert_eq!(
        layer_0_claims.get(&addr_b).unwrap(),
        &expected_b,
        "Claim for B should match expected value"
    );
}

#[test]
fn test_sumcheck_loop_multiple_gates() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let worker = Worker::new_with_num_threads(1);

    let copy_in = random_poly_in_ext::<F, E>(POLY_SIZE);
    let prod_a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let prod_b = random_poly_in_ext::<F, E>(POLY_SIZE);

    let copy_out = copy_in.clone();
    let prod_out = compute_product::<F, E>(&prod_a, &prod_b);

    let addr_copy_in = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_prod_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let addr_prod_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 2,
    };
    let addr_copy_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_prod_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };

    let mut storage = setup_storage::<F, E>(
        vec![
            (addr_copy_in, copy_in.clone()),
            (addr_prod_a, prod_a.clone()),
            (addr_prod_b, prod_b.clone()),
        ],
        vec![
            (addr_copy_out, copy_out.clone()),
            (addr_prod_out, prod_out.clone()),
        ],
    );

    let layer = GKRLayerDescription {
        layer: 0,
        gates: vec![
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::Copy {
                    input: addr_copy_in,
                    output: addr_copy_out,
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::TrivialProduct {
                    input: [addr_prod_a, addr_prod_b],
                    output: addr_prod_out,
                },
            },
        ],
        gates_with_external_connections: vec![],
        cached_relations: BTreeMap::new(),
        additional_base_layer_openings: vec![],
    };

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<E>(&prev_challenges, &worker);
    let eq_last = eq_precomputed.last().unwrap();

    let copy_claim = evaluate_with_precomputed_eq_ext::<E>(&copy_out, eq_last);
    let prod_claim = evaluate_with_precomputed_eq_ext::<E>(&prod_out, eq_last);

    let mut claims_storage: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_copy_out, copy_claim);
    output_claims.insert(addr_prod_out, prod_claim);
    claims_storage.insert(1, output_claims);

    let mut claim_points: BTreeMap<usize, Vec<E>> = BTreeMap::new();
    claim_points.insert(1, prev_challenges.clone());

    let lookup_multiplicative_part = E::from_base(F::from_u64_with_reduction(0xff));
    let lookup_additive_part = E::from_base(F::from_u64_with_reduction(42));
    let constraints_batch_challenge = E::from_base(F::from_u64_with_reduction(127));

    let mut batching_challenge = E::from_base(F::from_u64_with_reduction(0xff));
    let mut seed = Seed::default();

    evaluate_sumcheck_for_layer::<F, E>(
        0,
        &layer,
        &mut claim_points,
        &mut claims_storage,
        &mut storage,
        &mut batching_challenge,
        unsafe { MaybeUninit::uninit().assume_init_ref() }, // unused
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge,
        &GKRExternalChallenges::default(),
        &mut seed,
        &worker,
    );

    assert!(claims_storage.contains_key(&0));
    let layer_0_claims = claims_storage.get(&0).unwrap();
    let layer_0_challenges = claim_points.get(&0).unwrap();

    assert!(layer_0_claims.contains_key(&addr_copy_in));
    assert!(layer_0_claims.contains_key(&addr_prod_a));
    assert!(layer_0_claims.contains_key(&addr_prod_b));

    let eq_for_claims = make_eq_poly_in_full::<E>(layer_0_challenges, &worker);
    let eq_claims_last = eq_for_claims.last().unwrap();

    let expected_copy = evaluate_with_precomputed_eq_ext::<E>(&copy_in, eq_claims_last);
    let expected_a = evaluate_with_precomputed_eq_ext::<E>(&prod_a, eq_claims_last);
    let expected_b = evaluate_with_precomputed_eq_ext::<E>(&prod_b, eq_claims_last);

    assert_eq!(layer_0_claims.get(&addr_copy_in).unwrap(), &expected_copy);
    assert_eq!(layer_0_claims.get(&addr_prod_a).unwrap(), &expected_a);
    assert_eq!(layer_0_claims.get(&addr_prod_b).unwrap(), &expected_b);
}
