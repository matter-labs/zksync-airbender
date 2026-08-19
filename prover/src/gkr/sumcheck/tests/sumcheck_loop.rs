use crate::gkr::prover_config;
use std::collections::BTreeMap;
use std::mem::MaybeUninit;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, GateArtifacts, NoFieldGKRRelation};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};
use transcript::{
    commit_base_field_elements_impl, commit_extension_field_elements_impl,
    draw_random_field_elements_impl, Blake2sTranscript, Seed, Transcript,
};
use worker::Worker;

use super::utils::*;
use crate::gkr::prover::sumcheck_loop::evaluate_sumcheck_for_layer;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::eq_poly::*;

type F = BabyBearField;
type E = BabyBearExt4;

/// Minimal all-naive config for driving `evaluate_sumcheck_for_layer`
/// directly (the WHIR fields are never read by the sumcheck path).
fn test_prover_config() -> prover_config::ProverConfig {
    prover_config::ProverConfig {
        lde_factor: 2,
        cap_size: 64,
        base_oracles_values_per_leaf: 2,
        sumcheck_explicit_output_size_log_2: 4,
        security_level: crate::definitions::SecurityLevel::Sec100,
        whir_schedule: crate::gkr::prover::WhirSchedule {
            base_lde_factor: 2,
            cap_size: 64,
            whir_steps_schedule: vec![],
            whir_queries_schedule: vec![],
            whir_steps_lde_factors: vec![],
            whir_pow_schedule: vec![],
        },
        same_size_sumcheck_schedule: prover_config::naive_same_size_schedule(),
        dimension_reducing_sumcheck_schedule: Default::default(),
    }
}

/// Test-only transcript implementing `Transcript<BabyBearField, BabyBearExt4>`.
///
/// The production `Blake2sTranscript` only implements `Transcript<BabyBearField,
/// BabyBearExt4>`; the orphan rule forbids adding a Mersenne impl for it outside
/// the `transcript` crate, so we wrap it in this local type for the Mersenne-based
/// sumcheck tests. It delegates everything to `Blake2sTranscript`, reusing the
/// shared (field-generic) serialization helpers.
#[derive(Clone, Copy, Debug, Default)]
struct TestTranscript;

type TestBlake2s = Blake2sTranscript<true>;

impl Transcript<F, E> for TestTranscript {
    type Seed = Seed;
    type Hasher = blake2s_u32::DelegatedBlake2sState;

    fn commit_initial_u32(input: &[u32]) -> Seed {
        TestBlake2s::commit_initial(input)
    }
    fn commit_u32_with_seed(seed: &mut Seed, input: &[u32]) {
        TestBlake2s::commit_with_seed(seed, input);
    }
    fn commit_initial_u32_using_hasher(h: &mut Self::Hasher, input: &[u32]) -> Seed {
        TestBlake2s::commit_initial_using_hasher(h, input)
    }
    fn commit_u32_with_seed_using_hasher(h: &mut Self::Hasher, seed: &mut Seed, input: &[u32]) {
        TestBlake2s::commit_with_seed_using_hasher(h, seed, input);
    }
    fn draw_randomness(seed: &mut Seed, dst: &mut [u32]) {
        TestBlake2s::draw_randomness(seed, dst);
    }
    fn draw_randomness_using_hasher(h: &mut Self::Hasher, seed: &mut Seed, dst: &mut [u32]) {
        TestBlake2s::draw_randomness_using_hasher(h, seed, dst);
    }
    fn pow_threshold(pow_bits: u32) -> u32 {
        TestBlake2s::pow_threshold(pow_bits)
    }
    fn verify_pow(seed: &mut Seed, nonce: u64, pow_bits: u32) {
        TestBlake2s::verify_pow(seed, nonce, pow_bits);
    }
    fn verify_pow_using_hasher(h: &mut Self::Hasher, seed: &mut Seed, nonce: u64, pow_bits: u32) {
        TestBlake2s::verify_pow_using_hasher(h, seed, nonce, pow_bits);
    }
    fn search_pow(seed: &Seed, pow_bits: u32, worker: &worker::Worker) -> (Seed, u64) {
        TestBlake2s::search_pow(seed, pow_bits, worker)
    }
    fn commit_base_field_elements(seed: &mut Seed, els: &[F]) {
        commit_base_field_elements_impl::<true, F>(seed, els);
    }
    fn commit_extension_field_elements(seed: &mut Seed, els: &[E]) {
        commit_extension_field_elements_impl::<true, F, E>(seed, els);
    }
    fn draw_random_field_elements(seed: &mut Seed, buffer: &mut [E]) {
        draw_random_field_elements_impl::<true, F, E>(seed, buffer);
    }
    fn draw_random_field_elements_with_pow(
        seed: &Self::Seed,
        pow_bits: u32,
        buffer: &mut [E],
        worker: &worker::Worker,
    ) -> (Self::Seed, u64) {
        todo!();
    }
}

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
        intermediate_layer_width: None,
    };

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full_lsb::<E>(&prev_challenges, &worker);
    let eq_last = eq_precomputed.last().unwrap();

    let output_claim = evaluate_with_precomputed_eq_ext::<E>(&output, eq_last);

    let mut claims_storage: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_out, output_claim);
    claims_storage.insert(1, output_claims);

    let mut claim_points: BTreeMap<usize, Vec<E>> = BTreeMap::new();
    let mut claim_point_entries: std::collections::BTreeMap<
        usize,
        Vec<crate::gkr::prover::EvaluationPointEntry<E>>,
    > = Default::default();
    claim_points.insert(1, prev_challenges.clone());
    claim_point_entries.insert(
        1,
        prev_challenges
            .iter()
            .map(|point| crate::gkr::prover::EvaluationPointEntry::Coordinate { point: *point })
            .collect(),
    );

    let lookup_multiplicative_part = E::from_base(F::from_u32_with_reduction(0xff));
    let lookup_additive_part = E::from_base(F::from_u32_with_reduction(42));

    let mut batching_challenge = E::from_base(F::from_u32_with_reduction(0xff));
    let mut seed = Seed::default();

    evaluate_sumcheck_for_layer::<F, E, TestTranscript, _>(
        0,
        &layer,
        &mut claim_point_entries,
        &mut claims_storage,
        &mut storage,
        &mut batching_challenge,
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        &[],
        0,
        &GKRExternalChallenges::default(),
        &test_prover_config(),
        &mut seed,
        &worker,
        |_, _, _, _| Vec::new(),
        |_, _, _, _| Vec::new(),
        |prog| {
            crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::GenericSameSizeChain::<
                F,
                E,
            >::new(prog)
        },
    );

    assert!(
        claims_storage.contains_key(&0),
        "Claims for layer 0 should exist"
    );
    assert!(
        claim_point_entries.contains_key(&0),
        "Claim points for layer 0 should exist"
    );

    let layer_0_claims = claims_storage.get(&0).unwrap();
    let layer_0_challenges = claim_point_entries.get(&0).unwrap();

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

    let layer_0_scalar_point: Vec<E> = layer_0_challenges
        .iter()
        .map(|e| match e {
            crate::gkr::prover::EvaluationPointEntry::Coordinate { point } => *point,
            other => panic!("naive schedule emits scalar coordinates, got {other:?}"),
        })
        .collect();
    let eq_for_claims = make_eq_poly_in_full_lsb::<E>(&layer_0_scalar_point, &worker);
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
                enforced_relation: NoFieldGKRRelation::CopyInExtensionField {
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
        intermediate_layer_width: None,
    };

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full_lsb::<E>(&prev_challenges, &worker);
    let eq_last = eq_precomputed.last().unwrap();

    let copy_claim = evaluate_with_precomputed_eq_ext::<E>(&copy_out, eq_last);
    let prod_claim = evaluate_with_precomputed_eq_ext::<E>(&prod_out, eq_last);

    let mut claims_storage: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_copy_out, copy_claim);
    output_claims.insert(addr_prod_out, prod_claim);
    claims_storage.insert(1, output_claims);

    let mut claim_points: BTreeMap<usize, Vec<E>> = BTreeMap::new();
    let mut claim_point_entries: std::collections::BTreeMap<
        usize,
        Vec<crate::gkr::prover::EvaluationPointEntry<E>>,
    > = Default::default();
    claim_points.insert(1, prev_challenges.clone());
    claim_point_entries.insert(
        1,
        prev_challenges
            .iter()
            .map(|point| crate::gkr::prover::EvaluationPointEntry::Coordinate { point: *point })
            .collect(),
    );

    let lookup_multiplicative_part = E::from_base(F::from_u32_with_reduction(0xff));
    let lookup_additive_part = E::from_base(F::from_u32_with_reduction(42));

    let mut batching_challenge = E::from_base(F::from_u32_with_reduction(0xff));
    let mut seed = Seed::default();

    evaluate_sumcheck_for_layer::<F, E, TestTranscript, _>(
        0,
        &layer,
        &mut claim_point_entries,
        &mut claims_storage,
        &mut storage,
        &mut batching_challenge,
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        &[],
        0,
        &GKRExternalChallenges::default(),
        &test_prover_config(),
        &mut seed,
        &worker,
        |_, _, _, _| Vec::new(),
        |_, _, _, _| Vec::new(),
        |prog| {
            crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::GenericSameSizeChain::<
                F,
                E,
            >::new(prog)
        },
    );

    assert!(claims_storage.contains_key(&0));
    let layer_0_claims = claims_storage.get(&0).unwrap();
    let layer_0_challenges = claim_point_entries.get(&0).unwrap();

    assert!(layer_0_claims.contains_key(&addr_copy_in));
    assert!(layer_0_claims.contains_key(&addr_prod_a));
    assert!(layer_0_claims.contains_key(&addr_prod_b));

    let layer_0_scalar_point: Vec<E> = layer_0_challenges
        .iter()
        .map(|e| match e {
            crate::gkr::prover::EvaluationPointEntry::Coordinate { point } => *point,
            other => panic!("naive schedule emits scalar coordinates, got {other:?}"),
        })
        .collect();
    let eq_for_claims = make_eq_poly_in_full_lsb::<E>(&layer_0_scalar_point, &worker);
    let eq_claims_last = eq_for_claims.last().unwrap();

    let expected_copy = evaluate_with_precomputed_eq_ext::<E>(&copy_in, eq_claims_last);
    let expected_a = evaluate_with_precomputed_eq_ext::<E>(&prod_a, eq_claims_last);
    let expected_b = evaluate_with_precomputed_eq_ext::<E>(&prod_b, eq_claims_last);

    assert_eq!(layer_0_claims.get(&addr_copy_in).unwrap(), &expected_copy);
    assert_eq!(layer_0_claims.get(&addr_prod_a).unwrap(), &expected_a);
    assert_eq!(layer_0_claims.get(&addr_prod_b).unwrap(), &expected_b);
}
