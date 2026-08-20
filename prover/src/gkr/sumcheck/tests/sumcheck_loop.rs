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
        security_level: crate::definitions::SecurityLevel::Sec80,
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

// ---------------------------------------------------------------------------
// P0 characterization: the windowed same-size schedule against the plain-LSB
// (all-naive) schedule on the SAME layer, comparing the transcript EVENT
// STREAM (every commit and every draw, in order) and every derived output.
// ---------------------------------------------------------------------------

/// One transcript interaction, holding the raw `u32` words that reach the
/// hasher so the comparison is on committed bytes rather than on field values.
#[derive(Clone, Debug, PartialEq, Eq)]
enum TranscriptEvent {
    CommitBase(Vec<u32>),
    CommitExt(Vec<u32>),
    Draw(Vec<u32>),
}

thread_local! {
    static P0_EVENTS: std::cell::RefCell<Vec<TranscriptEvent>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

fn p0_events_reset() {
    P0_EVENTS.with(|log| log.borrow_mut().clear());
}

fn p0_events_take() -> Vec<TranscriptEvent> {
    P0_EVENTS.with(|log| core::mem::take(&mut *log.borrow_mut()))
}

fn p0_events_push(event: TranscriptEvent) {
    P0_EVENTS.with(|log| log.borrow_mut().push(event));
}

fn p0_flatten_ext(els: &[E]) -> Vec<u32> {
    let mut out = Vec::with_capacity(els.len() * <E as FieldExtension<F>>::DEGREE);
    crate::gkr::prover::transcript_utils::flatten_field_els_into::<F, E>(els, &mut out);
    out
}

fn p0_flatten_base(els: &[F]) -> Vec<u32> {
    els.iter().map(|el| el.as_u32_raw_repr_reduced()).collect()
}

/// [`TestTranscript`] plus an event log: the hashing is delegated unchanged, so
/// the seed evolution is the production one and the log is a pure observation.
#[derive(Clone, Copy, Debug, Default)]
struct RecordingTranscript;

impl Transcript<F, E> for RecordingTranscript {
    type Seed = Seed;
    type Hasher = blake2s_u32::DelegatedBlake2sState;

    fn commit_initial_u32(input: &[u32]) -> Seed {
        <TestTranscript as Transcript<F, E>>::commit_initial_u32(input)
    }
    fn commit_u32_with_seed(seed: &mut Seed, input: &[u32]) {
        <TestTranscript as Transcript<F, E>>::commit_u32_with_seed(seed, input);
    }
    fn commit_initial_u32_using_hasher(h: &mut Self::Hasher, input: &[u32]) -> Seed {
        <TestTranscript as Transcript<F, E>>::commit_initial_u32_using_hasher(h, input)
    }
    fn commit_u32_with_seed_using_hasher(h: &mut Self::Hasher, seed: &mut Seed, input: &[u32]) {
        <TestTranscript as Transcript<F, E>>::commit_u32_with_seed_using_hasher(h, seed, input);
    }
    fn draw_randomness(seed: &mut Seed, dst: &mut [u32]) {
        <TestTranscript as Transcript<F, E>>::draw_randomness(seed, dst);
    }
    fn draw_randomness_using_hasher(h: &mut Self::Hasher, seed: &mut Seed, dst: &mut [u32]) {
        <TestTranscript as Transcript<F, E>>::draw_randomness_using_hasher(h, seed, dst);
    }
    fn pow_threshold(pow_bits: u32) -> u32 {
        <TestTranscript as Transcript<F, E>>::pow_threshold(pow_bits)
    }
    fn verify_pow(seed: &mut Seed, nonce: u64, pow_bits: u32) {
        <TestTranscript as Transcript<F, E>>::verify_pow(seed, nonce, pow_bits);
    }
    fn verify_pow_using_hasher(h: &mut Self::Hasher, seed: &mut Seed, nonce: u64, pow_bits: u32) {
        <TestTranscript as Transcript<F, E>>::verify_pow_using_hasher(h, seed, nonce, pow_bits);
    }
    fn search_pow(seed: &Seed, pow_bits: u32, worker: &worker::Worker) -> (Seed, u64) {
        <TestTranscript as Transcript<F, E>>::search_pow(seed, pow_bits, worker)
    }
    fn commit_base_field_elements(seed: &mut Seed, els: &[F]) {
        p0_events_push(TranscriptEvent::CommitBase(p0_flatten_base(els)));
        <TestTranscript as Transcript<F, E>>::commit_base_field_elements(seed, els);
    }
    fn commit_extension_field_elements(seed: &mut Seed, els: &[E]) {
        p0_events_push(TranscriptEvent::CommitExt(p0_flatten_ext(els)));
        <TestTranscript as Transcript<F, E>>::commit_extension_field_elements(seed, els);
    }
    fn draw_random_field_elements(seed: &mut Seed, buffer: &mut [E]) {
        <TestTranscript as Transcript<F, E>>::draw_random_field_elements(seed, buffer);
        p0_events_push(TranscriptEvent::Draw(p0_flatten_ext(buffer)));
    }
    fn draw_random_field_elements_with_pow(
        seed: &Self::Seed,
        pow_bits: u32,
        buffer: &mut [E],
        worker: &worker::Worker,
    ) -> (Self::Seed, u64) {
        <TestTranscript as Transcript<F, E>>::draw_random_field_elements_with_pow(
            seed, pow_bits, buffer, worker,
        )
    }
}

const P0_INITIAL_SEED: Seed = Seed([
    0x0000_0001,
    0x0000_0002,
    0x0000_0003,
    0x0000_0004,
    0x0000_0005,
    0x0000_0006,
    0x0000_0007,
    0x0000_0008,
]);

fn p0_random_base(rng: &mut rand::rngs::StdRng) -> F {
    use rand::RngCore;
    F::from_u32_with_reduction(rng.next_u32())
}

fn p0_random_ext(rng: &mut rand::rngs::StdRng) -> E {
    use field::FixedArrayConvertible;
    let coeffs: [F; 4] = core::array::from_fn(|_| p0_random_base(rng));
    <E as FieldExtension<F>>::from_coeffs(<E as FieldExtension<F>>::Coeffs::from_array(coeffs))
}

/// A same-size layer mixing every accumulator path the batched relation can
/// take: a max-quadratic gate (base products, base linear terms, an additive
/// constant), an extension-by-extension product, a base copy, an extension
/// copy, and a logup pair over base inputs.
struct P0MixedLayer {
    layer: GKRLayerDescription<F>,
    base_inputs: Vec<(GKRAddress, Vec<F>)>,
    ext_inputs: Vec<(GKRAddress, Vec<E>)>,
    base_outputs: Vec<(GKRAddress, Vec<F>)>,
    ext_outputs: Vec<(GKRAddress, Vec<E>)>,
    prev_point: Vec<E>,
    batching_challenge: E,
    lookup_multiplicative_part: E,
    lookup_additive_part: E,
}

fn p0_mixed_layer(folding_steps: usize) -> P0MixedLayer {
    use rand::SeedableRng;

    let size = 1usize << folding_steps;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x5000_0000 + folding_steps as u64);

    let base: Vec<Vec<F>> = (0..4)
        .map(|_| (0..size).map(|_| p0_random_base(&mut rng)).collect())
        .collect();
    let ext: Vec<Vec<E>> = (0..3)
        .map(|_| (0..size).map(|_| p0_random_ext(&mut rng)).collect())
        .collect();

    let addr_base: [GKRAddress; 4] = core::array::from_fn(|i| GKRAddress::InnerLayer {
        layer: 0,
        offset: i,
    });
    let addr_ext: [GKRAddress; 3] = core::array::from_fn(|i| GKRAddress::InnerLayer {
        layer: 0,
        offset: 4 + i,
    });
    let addr_out: [GKRAddress; 7] = core::array::from_fn(|i| GKRAddress::InnerLayer {
        layer: 1,
        offset: i,
    });

    let lookup_additive_part = E::from_base(F::from_u32_with_reduction(42));
    let lookup_multiplicative_part = E::from_base(F::from_u32_with_reduction(0xff));

    let c3 = F::from_u32_with_reduction(3);
    let c5 = F::from_u32_with_reduction(5);
    let c7 = F::from_u32_with_reduction(7);
    let c2 = F::from_u32_with_reduction(2);
    let c11 = F::from_u32_with_reduction(11);

    let max_quadratic = cs::gkr_compiler::NoFieldMaxQuadraticGKRRelation::<F> {
        quadratic_terms: vec![
            (
                addr_base[0],
                vec![(c3, addr_base[1]), (F::ONE, addr_base[0])].into_boxed_slice(),
            ),
            (addr_base[2], vec![(c5, addr_base[2])].into_boxed_slice()),
        ]
        .into_boxed_slice(),
        linear_terms: vec![
            (c7, addr_base[1]),
            (F::MINUS_ONE, addr_base[2]),
            (c2, addr_base[3]),
        ]
        .into_boxed_slice(),
        constant: c11,
    };
    // the SAME polynomial as a structured tree: the windowed chain compiles
    // this form directly, the naive loop consumes the relation above, so the
    // two must agree term for term
    let expression = {
        use cs::gkr_compiler::NoFieldStructuredExpression as X;
        X::Sum(vec![
            X::Constant(c11),
            X::Product(vec![
                X::Constant(c3),
                X::Place(addr_base[0]),
                X::Place(addr_base[1]),
            ]),
            X::Product(vec![X::Place(addr_base[0]), X::Place(addr_base[0])]),
            X::Product(vec![
                X::Constant(c5),
                X::Place(addr_base[2]),
                X::Place(addr_base[2]),
            ]),
            X::Product(vec![X::Constant(c7), X::Place(addr_base[1])]),
            X::Product(vec![X::Constant(F::MINUS_ONE), X::Place(addr_base[2])]),
            X::Product(vec![X::Constant(c2), X::Place(addr_base[3])]),
        ])
    };

    let mut out_max_quadratic = Vec::with_capacity(size);
    for i in 0..size {
        let mut value = c11;

        let mut term = base[0][i];
        term.mul_assign(&base[1][i]);
        term.mul_assign(&c3);
        value.add_assign(&term);

        let mut term = base[0][i];
        term.square();
        value.add_assign(&term);

        let mut term = base[2][i];
        term.square();
        term.mul_assign(&c5);
        value.add_assign(&term);

        let mut term = base[1][i];
        term.mul_assign(&c7);
        value.add_assign(&term);

        value.sub_assign(&base[2][i]);

        let mut term = base[3][i];
        term.mul_assign(&c2);
        value.add_assign(&term);

        out_max_quadratic.push(value);
    }

    let out_base_copy = base[3].clone();
    let out_product = compute_product::<F, E>(&ext[0], &ext[1]);
    let out_ext_copy = ext[2].clone();

    let mut out_mask = Vec::with_capacity(size);
    for i in 0..size {
        let mut value = ext[2][i];
        value.mul_assign_by_base(&base[3][i]);
        value.sub_assign(&E::from_base(base[3][i]));
        value.add_assign(&E::ONE);
        out_mask.push(value);
    }

    let mut out_lookup_num = Vec::with_capacity(size);
    let mut out_lookup_den = Vec::with_capacity(size);
    for i in 0..size {
        let mut first = lookup_additive_part;
        first.add_assign(&E::from_base(base[0][i]));
        let mut second = lookup_additive_part;
        second.add_assign(&E::from_base(base[1][i]));

        let mut num = first;
        num.add_assign(&second);
        out_lookup_num.push(num);

        let mut den = first;
        den.mul_assign(&second);
        out_lookup_den.push(den);
    }

    let layer = GKRLayerDescription {
        layer: 0,
        gates: vec![
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::MaxQuadratic {
                    input: max_quadratic,
                    expression,
                    output: addr_out[0],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::TrivialProduct {
                    input: [addr_ext[0], addr_ext[1]],
                    output: addr_out[2],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::CopyInBaseField {
                    input: addr_base[3],
                    output: addr_out[1],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::CopyInExtensionField {
                    input: addr_ext[2],
                    output: addr_out[3],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
                    input: [addr_base[0], addr_base[1]],
                    output: [addr_out[4], addr_out[5]],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::MaskIntoIdentityProduct {
                    input: addr_ext[2],
                    mask: addr_base[3],
                    output: addr_out[6],
                },
            },
        ],
        gates_with_external_connections: vec![],
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
    };

    let prev_point: Vec<E> = (0..folding_steps)
        .map(|_| p0_random_ext(&mut rng))
        .collect();
    let batching_challenge = p0_random_ext(&mut rng);

    P0MixedLayer {
        layer,
        base_inputs: addr_base.into_iter().zip(base).collect(),
        ext_inputs: addr_ext.into_iter().zip(ext).collect(),
        base_outputs: vec![
            (addr_out[0], out_max_quadratic),
            (addr_out[1], out_base_copy),
        ],
        ext_outputs: vec![
            (addr_out[2], out_product),
            (addr_out[3], out_ext_copy),
            (addr_out[4], out_lookup_num),
            (addr_out[5], out_lookup_den),
            (addr_out[6], out_mask),
        ],
        prev_point,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
    }
}

impl P0MixedLayer {
    fn storage(&self) -> crate::gkr::sumcheck::access_and_fold::GKRStorage<F, E> {
        use crate::gkr::sumcheck::access_and_fold::{
            BaseFieldPoly, ExtensionFieldPoly, GKRLayerSource, GKRStorage,
        };

        let mut storage = GKRStorage::<F, E>::default();
        let mut inputs = GKRLayerSource::default();
        inputs.layer_idx = 0;
        for (addr, poly) in self.base_inputs.iter() {
            inputs
                .base_field_inputs
                .insert(*addr, BaseFieldPoly::new(poly.clone().into_boxed_slice()));
        }
        for (addr, poly) in self.ext_inputs.iter() {
            inputs.extension_field_inputs.insert(
                *addr,
                ExtensionFieldPoly::new(poly.clone().into_boxed_slice()),
            );
        }
        storage.layers.push(inputs);

        let mut outputs = GKRLayerSource::default();
        outputs.layer_idx = 1;
        for (addr, poly) in self.base_outputs.iter() {
            outputs
                .base_field_inputs
                .insert(*addr, BaseFieldPoly::new(poly.clone().into_boxed_slice()));
        }
        for (addr, poly) in self.ext_outputs.iter() {
            outputs.extension_field_inputs.insert(
                *addr,
                ExtensionFieldPoly::new(poly.clone().into_boxed_slice()),
            );
        }
        storage.layers.push(outputs);

        storage
    }

    fn output_claims(&self, worker: &Worker) -> BTreeMap<GKRAddress, E> {
        let eq = make_eq_poly_in_full_lsb::<E>(&self.prev_point, worker);
        let eq = eq.last().expect("full table");
        let mut claims = BTreeMap::new();
        for (addr, poly) in self.base_outputs.iter() {
            claims.insert(*addr, evaluate_base_with_precomputed_eq::<F, E>(poly, eq));
        }
        for (addr, poly) in self.ext_outputs.iter() {
            claims.insert(*addr, evaluate_with_precomputed_eq_ext::<E>(poly, eq));
        }
        claims
    }
}

struct P0LegOutcome {
    events: Vec<TranscriptEvent>,
    rounds: Vec<[E; 4]>,
    point: Vec<E>,
    claims: BTreeMap<GKRAddress, E>,
    final_step_evaluations: BTreeMap<GKRAddress, Vec<E>>,
    next_batching_challenge: E,
    seed: Seed,
}

fn p0_prover_config(schedule: Vec<prover_config::SumcheckStep>) -> prover_config::ProverConfig {
    let mut config = test_prover_config();
    config.same_size_sumcheck_schedule = schedule;
    config
}

fn p0_run_leg<B: crate::gkr::prover::gkr_backend::GKRBackend<F, E>>(
    backend: &B,
    fixture: &P0MixedLayer,
    schedule: Vec<prover_config::SumcheckStep>,
    worker: &Worker,
) -> P0LegOutcome {
    use crate::gkr::prover::EvaluationPointEntry;

    let folding_steps = fixture.prev_point.len();
    let trace_len = 1usize << folding_steps;

    let mut storage = fixture.storage();
    let mut claims_storage = BTreeMap::new();
    claims_storage.insert(1, fixture.output_claims(worker));
    let mut claim_point_entries: BTreeMap<usize, Vec<EvaluationPointEntry<E>>> = BTreeMap::new();
    claim_point_entries.insert(
        1,
        fixture
            .prev_point
            .iter()
            .map(|point| EvaluationPointEntry::Coordinate { point: *point })
            .collect(),
    );
    let mut batching_challenge = fixture.batching_challenge;
    let mut seed = P0_INITIAL_SEED;

    p0_events_reset();
    let values = backend.evaluate_same_size_sumcheck_for_layer::<RecordingTranscript>(
        0,
        &fixture.layer,
        &mut claim_point_entries,
        &mut claims_storage,
        &mut storage,
        &mut batching_challenge,
        trace_len,
        fixture.lookup_multiplicative_part,
        fixture.lookup_additive_part,
        &[],
        0,
        &GKRExternalChallenges::default(),
        &p0_prover_config(schedule),
        &mut seed,
        worker,
    );
    let events = p0_events_take();

    let point = claim_point_entries
        .get(&0)
        .expect("the layer emits a claim point")
        .iter()
        .map(|entry| match entry {
            EvaluationPointEntry::Coordinate { point } => *point,
            other => panic!("both schedules emit scalar coordinates, got {other:?}"),
        })
        .collect();

    P0LegOutcome {
        events,
        rounds: values
            .internal_round_coefficients
            .iter()
            .map(|round| *round.as_multilinear())
            .collect(),
        point,
        claims: claims_storage
            .get(&0)
            .expect("the layer emits claims")
            .clone(),
        final_step_evaluations: values.final_step_evaluations,
        next_batching_challenge: batching_challenge,
        seed,
    }
}

/// Pins the reference leg's event ORDER: one round-coefficient commit followed
/// by one challenge draw per variable, then the claim commit and the next
/// batching-challenge draw.
fn p0_assert_event_shape(outcome: &P0LegOutcome, folding_steps: usize) {
    assert_eq!(
        outcome.rounds.len(),
        folding_steps,
        "one round message per variable"
    );
    assert_eq!(
        outcome.events.len(),
        2 * folding_steps + 2,
        "commit+draw per round, plus the claim commit and batching draw"
    );
    for round in 0..folding_steps {
        assert_eq!(
            outcome.events[2 * round],
            TranscriptEvent::CommitExt(p0_flatten_ext(&outcome.rounds[round])),
            "event {} must commit round {round}'s coefficients",
            2 * round
        );
        match &outcome.events[2 * round + 1] {
            TranscriptEvent::Draw(words) => assert_eq!(
                words.len(),
                4,
                "event {} must draw one challenge",
                2 * round + 1
            ),
            other => panic!("event {} must be a draw, got {other:?}", 2 * round + 1),
        }
    }
    match &outcome.events[2 * folding_steps] {
        TranscriptEvent::CommitExt(words) => {
            assert_eq!(
                words.len(),
                4 * outcome.claims.len(),
                "the postlude commits every claim"
            )
        }
        other => panic!("the postlude must commit the claims, got {other:?}"),
    }
    match &outcome.events[2 * folding_steps + 1] {
        TranscriptEvent::Draw(words) => {
            assert_eq!(words.len(), 4, "the postlude draws one batching challenge")
        }
        other => panic!("the postlude must draw the batching challenge, got {other:?}"),
    }
}

fn p0_assert_legs_equal(label: &str, reference: &P0LegOutcome, other: &P0LegOutcome) {
    assert_eq!(
        reference.events.len(),
        other.events.len(),
        "{label}: transcript event count diverged"
    );
    for (idx, (a, b)) in reference.events.iter().zip(other.events.iter()).enumerate() {
        assert_eq!(a, b, "{label}: transcript event {idx} diverged");
    }
    assert_eq!(
        reference.rounds.len(),
        other.rounds.len(),
        "{label}: round count diverged"
    );
    for (round, (a, b)) in reference.rounds.iter().zip(other.rounds.iter()).enumerate() {
        for coeff in 0..4 {
            assert_eq!(
                a[coeff], b[coeff],
                "{label}: round {round} coefficient {coeff} diverged"
            );
        }
    }
    assert_eq!(
        reference.point, other.point,
        "{label}: folding point diverged"
    );
    assert_eq!(reference.claims, other.claims, "{label}: claims diverged");
    assert_eq!(
        reference.final_step_evaluations, other.final_step_evaluations,
        "{label}: final evaluations diverged"
    );
    assert_eq!(
        reference.next_batching_challenge, other.next_batching_challenge,
        "{label}: next batching challenge diverged"
    );
    assert_eq!(
        reference.seed, other.seed,
        "{label}: final transcript seed diverged"
    );
}

fn p0_windowed_vs_naive_transcript(folding_steps: usize) {
    let worker = Worker::new_with_num_threads(1);
    let fixture = p0_mixed_layer(folding_steps);

    let naive_schedule = vec![prover_config::SumcheckStep::NaiveSumcheck; folding_steps];
    let windowed_schedule = prover_config::windowed_same_size_schedule(folding_steps);

    let naive = p0_run_leg(
        &crate::gkr::prover::gkr_backend::NaiveGKRBackend,
        &fixture,
        naive_schedule,
        &worker,
    );
    p0_assert_event_shape(&naive, folding_steps);

    let windowed = p0_run_leg(
        &crate::gkr::prover::gkr_backend::NaiveGKRBackend,
        &fixture,
        windowed_schedule.clone(),
        &worker,
    );
    p0_assert_legs_equal("naive backend, window schedule", &naive, &windowed);

    // On aarch64 this alias is the NEON backend; on x86 it resolves back to
    // NaiveGKRBackend, so the NEON chain needs its own aarch64 run.
    let default_backend = p0_run_leg(
        &crate::gkr::prover::gkr_backend::DefaultBabyBearGKRBackend::default(),
        &fixture,
        windowed_schedule,
        &worker,
    );
    p0_assert_legs_equal("default backend, window schedule", &naive, &default_backend);
}

#[test]
fn p0_windowed_vs_naive_transcript_n6() {
    p0_windowed_vs_naive_transcript(6);
}

#[test]
fn p0_windowed_vs_naive_transcript_n7() {
    p0_windowed_vs_naive_transcript(7);
}

#[test]
fn p0_windowed_vs_naive_transcript_n8() {
    p0_windowed_vs_naive_transcript(8);
}

/// Independent oracle for the plain-LSB round 0: a hand-rolled fold over the
/// hypercube with straight arithmetic (no eq tables, no monomial helper, no
/// evaluator from the prover) on a layer built from two basis vectors and one
/// random vector.
#[test]
fn p0_plain_lsb_round0_oracle() {
    use crate::gkr::prover::EvaluationPointEntry;
    use rand::SeedableRng;

    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let worker = Worker::new_with_num_threads(1);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x0A11_C1E0);

    let mut basis_a = vec![E::ZERO; POLY_SIZE];
    basis_a[3] = E::ONE;
    let random_b: Vec<E> = (0..POLY_SIZE).map(|_| p0_random_ext(&mut rng)).collect();
    let mut basis_c = vec![E::ZERO; POLY_SIZE];
    basis_c[5] = E::ONE;

    let addr_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let addr_c = GKRAddress::InnerLayer {
        layer: 0,
        offset: 2,
    };
    let addr_product = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_copy = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };

    let out_product = compute_product::<F, E>(&basis_a, &random_b);
    let out_copy = basis_c.clone();

    let tau: Vec<E> = (0..FOLDING_STEPS)
        .map(|_| p0_random_ext(&mut rng))
        .collect();
    let beta = p0_random_ext(&mut rng);

    // ---- the oracle: local eq, local fold, local cubic interpolation ----
    let eq_bit = |t: &E, bit: usize| -> E {
        if bit == 0 {
            let mut value = E::ONE;
            value.sub_assign(t);
            value
        } else {
            *t
        }
    };
    let eq_row = |row: usize| -> E {
        let mut weight = E::ONE;
        for (variable, t) in tau.iter().enumerate() {
            weight.mul_assign(&eq_bit(t, (row >> variable) & 1));
        }
        weight
    };
    let claim_of = |poly: &[E]| -> E {
        let mut total = E::ZERO;
        for (row, value) in poly.iter().enumerate() {
            let mut term = eq_row(row);
            term.mul_assign(value);
            total.add_assign(&term);
        }
        total
    };
    let fold_at = |poly: &[E], pair: usize, x: &E| -> E {
        let mut value = poly[2 * pair + 1];
        value.sub_assign(&poly[2 * pair]);
        value.mul_assign(x);
        value.add_assign(&poly[2 * pair]);
        value
    };

    let mut oracle_values = [E::ZERO; 4];
    for (index, value) in oracle_values.iter_mut().enumerate() {
        let x = E::from_base(F::from_u32_with_reduction(index as u32));
        let mut partial_sum = E::ZERO;
        for pair in 0..POLY_SIZE / 2 {
            let mut weight = E::ONE;
            for (variable, t) in tau.iter().enumerate().skip(1) {
                weight.mul_assign(&eq_bit(t, (pair >> (variable - 1)) & 1));
            }
            let folded_a = fold_at(&basis_a, pair, &x);
            let folded_b = fold_at(&random_b, pair, &x);
            let folded_c = fold_at(&basis_c, pair, &x);

            let mut gate = folded_a;
            gate.mul_assign(&folded_b);
            let mut copy_term = beta;
            copy_term.mul_assign(&folded_c);
            gate.add_assign(&copy_term);

            weight.mul_assign(&gate);
            partial_sum.add_assign(&weight);
        }
        // the round message carries the local eq factor of the bound variable
        let mut eq_factor = E::ONE;
        eq_factor.sub_assign(&tau[0]);
        let mut high = tau[0];
        high.mul_assign(&x);
        let mut low = E::ONE;
        low.sub_assign(&x);
        eq_factor.mul_assign(&low);
        eq_factor.add_assign(&high);

        *value = eq_factor;
        value.mul_assign(&partial_sum);
    }

    let oracle_coefficients = {
        let [y0, y1, y2, y3] = oracle_values;
        let inverse_of = |k: u32| -> E {
            E::from_base(F::from_u32_with_reduction(k))
                .inverse()
                .expect("non-zero")
        };
        let inv2 = inverse_of(2);
        let inv3 = inverse_of(3);
        let inv6 = inverse_of(6);

        let mut d1 = y1;
        d1.sub_assign(&y0);

        let mut d2 = y2;
        let mut twice_y1 = y1;
        twice_y1.double();
        d2.sub_assign(&twice_y1);
        d2.add_assign(&y0);

        let mut d3 = y3;
        let mut thrice_y2 = y2;
        thrice_y2.mul_assign(&E::from_base(F::from_u32_with_reduction(3)));
        d3.sub_assign(&thrice_y2);
        let mut thrice_y1 = y1;
        thrice_y1.mul_assign(&E::from_base(F::from_u32_with_reduction(3)));
        d3.add_assign(&thrice_y1);
        d3.sub_assign(&y0);

        let mut half_d2 = d2;
        half_d2.mul_assign(&inv2);
        let mut third_d3 = d3;
        third_d3.mul_assign(&inv3);
        let mut half_d3 = d3;
        half_d3.mul_assign(&inv2);
        let mut sixth_d3 = d3;
        sixth_d3.mul_assign(&inv6);

        let mut c1 = d1;
        c1.sub_assign(&half_d2);
        c1.add_assign(&third_d3);

        let mut c2 = half_d2;
        c2.sub_assign(&half_d3);

        [y0, c1, c2, sixth_d3]
    };

    // ---- the naive schedule over the same layer ----
    let layer = GKRLayerDescription {
        layer: 0,
        gates: vec![
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::TrivialProduct {
                    input: [addr_a, addr_b],
                    output: addr_product,
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::CopyInExtensionField {
                    input: addr_c,
                    output: addr_copy,
                },
            },
        ],
        gates_with_external_connections: vec![],
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
    };

    let mut storage = setup_storage::<F, E>(
        vec![
            (addr_a, basis_a.clone()),
            (addr_b, random_b.clone()),
            (addr_c, basis_c.clone()),
        ],
        vec![
            (addr_product, out_product.clone()),
            (addr_copy, out_copy.clone()),
        ],
    );

    let mut claims_storage = BTreeMap::new();
    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_product, claim_of(&out_product));
    output_claims.insert(addr_copy, claim_of(&out_copy));
    claims_storage.insert(1, output_claims);

    let mut claim_point_entries: BTreeMap<usize, Vec<EvaluationPointEntry<E>>> = BTreeMap::new();
    claim_point_entries.insert(
        1,
        tau.iter()
            .map(|point| EvaluationPointEntry::Coordinate { point: *point })
            .collect(),
    );

    let mut batching_challenge = beta;
    let mut seed = P0_INITIAL_SEED;

    p0_events_reset();
    let values =
        crate::gkr::prover::gkr_backend::GKRBackend::<F, E>::evaluate_same_size_sumcheck_for_layer::<
            RecordingTranscript,
        >(
            &crate::gkr::prover::gkr_backend::NaiveGKRBackend,
            0,
            &layer,
            &mut claim_point_entries,
            &mut claims_storage,
            &mut storage,
            &mut batching_challenge,
            POLY_SIZE,
            E::from_base(F::from_u32_with_reduction(0xff)),
            E::from_base(F::from_u32_with_reduction(42)),
            &[],
            0,
            &GKRExternalChallenges::default(),
            &p0_prover_config(vec![
                prover_config::SumcheckStep::NaiveSumcheck;
                FOLDING_STEPS
            ]),
            &mut seed,
            &worker,
        );
    let events = p0_events_take();

    let round_0 = *values.internal_round_coefficients[0].as_multilinear();
    for coeff in 0..4 {
        assert_eq!(
            round_0[coeff], oracle_coefficients[coeff],
            "round 0 coefficient {coeff} disagrees with the hand-rolled LSB fold"
        );
    }
    assert_eq!(
        events[0],
        TranscriptEvent::CommitExt(p0_flatten_ext(&oracle_coefficients)),
        "round 0 commits coefficients other than the hand-rolled ones"
    );
}
