//! Task 9 smoke tests for the layer-oracle harness.
//!
//! 1. Twin-run gate: `run_layer_oracle` on an identical (cloned) setup + same
//!    seed reproduces the production `evaluate_sumcheck_for_layer` transcript
//!    byte-for-byte (`folding_challenges`, `round_coeffs`), proving the capture
//!    is transcript-inert.
//! 2. `recover_and_emit` self-consistency: fed the round-polynomial evaluations
//!    `(g(0), g(2))` derived from a captured round, it reproduces that round's
//!    committed `[E; 4]` and the production linear coefficient `d`.

use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, GateArtifacts, NoFieldGKRRelation};
use field::{Field, FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};
use transcript::Seed;
use worker::Worker;

use super::utils::*;
use crate::gkr::prover::sumcheck_loop::evaluate_sumcheck_for_layer;
use crate::gkr::prover::sumcheck_loop::test_harness::{recover_and_emit, run_layer_oracle};
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::eq_poly::*;

type F = Mersenne31Field;
type E = Mersenne31Quartic;

/// Build the `test_sumcheck_loop_product` fixture: a single trivial-product gate
/// over two random extension-field inputs. Returns the inputs so callers can
/// rebuild identical storage twice (`GKRStorage` is not `Clone`).
fn product_fixture() -> (
    Vec<E>,
    Vec<E>,
    Vec<E>,
    GKRAddress,
    GKRAddress,
    GKRAddress,
    GKRLayerDescription,
) {
    const POLY_SIZE: usize = 1 << 4;

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

    (a, b, output, addr_a, addr_b, addr_out, layer)
}

/// Twin-run: harness capture must not perturb the transcript.
#[test]
fn layer_oracle_twin_run_matches_production_transcript() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let worker = Worker::new_with_num_threads(1);
    let (a, b, output, addr_a, addr_b, addr_out, layer) = product_fixture();

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<E>(&prev_challenges, &worker);
    let eq_last = eq_precomputed.last().unwrap();
    let output_claim = evaluate_with_precomputed_eq_ext::<E>(&output, eq_last);

    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_out, output_claim);

    let lookup_multiplicative_part = E::from_base(F::from_u64_with_reduction(0xff));
    let lookup_additive_part = E::from_base(F::from_u64_with_reduction(42));
    let batch_challenge_base = E::from_base(F::from_u64_with_reduction(0xff));

    // --- Production path on its own storage + seed ------------------------
    let mut prod_storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output.clone())],
    );
    let mut prod_claims_storage: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    prod_claims_storage.insert(1, output_claims.clone());
    let mut prod_claim_points: BTreeMap<usize, Vec<E>> = BTreeMap::new();
    prod_claim_points.insert(1, prev_challenges.clone());
    let mut prod_batching = batch_challenge_base;
    let mut prod_seed = Seed::default();

    let prod = evaluate_sumcheck_for_layer::<F, E, ()>(
        0,
        &layer,
        &mut prod_claim_points,
        &mut prod_claims_storage,
        &mut prod_storage,
        &mut prod_batching,
        &super::empty_circuit_artifact::<F>(), // unused compiled circuit (non-evaluator route)
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        &[],
        0,
        &GKRExternalChallenges::default(),
        None,
        &mut prod_seed,
        &worker,
    );
    let prod_folding_challenges = prod_claim_points.get(&0).unwrap().clone();
    let prod_round_coeffs = prod.internal_round_coefficients.clone();

    // --- Harness path on a fresh identical storage + fresh identical seed --
    let mut oracle_storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output.clone())],
    );
    let mut oracle_seed = Seed::default();

    let run = run_layer_oracle::<F, E>(
        0,
        &layer,
        &output_claims,
        &prev_challenges,
        &mut oracle_storage,
        batch_challenge_base,
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        &[],
        0,
        &GKRExternalChallenges::default(),
        &mut oracle_seed,
        &worker,
    );

    assert_eq!(
        run.folding_challenges, prod_folding_challenges,
        "harness folding challenges diverged from production transcript"
    );
    assert_eq!(
        run.round_coeffs, prod_round_coeffs,
        "harness round coefficients diverged from production transcript"
    );

    // Sanity on captured shapes.
    assert_eq!(run.round_coeffs.len(), FOLDING_STEPS);
    assert_eq!(run.per_round_reduced.len(), FOLDING_STEPS);
    assert_eq!(run.per_round_claims.len(), FOLDING_STEPS);
    assert_eq!(run.per_round_eq_prefactor.len(), FOLDING_STEPS);
    assert_eq!(run.per_round_claims[0], run.initial_combined_claim);
    assert_eq!(run.per_relation_weights.len(), 1); // single-challenge product kernel
}

/// `recover_and_emit` round-trips a captured round back into the committed
/// monomial form and the production linear coefficient.
#[test]
fn recover_and_emit_reproduces_committed_round() {
    const FOLDING_STEPS: usize = 4;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let worker = Worker::new_with_num_threads(1);
    let (a, b, output, addr_a, addr_b, addr_out, layer) = product_fixture();

    let prev_challenges: Vec<E> = random_poly_in_ext::<F, E>(FOLDING_STEPS);
    let eq_precomputed = make_eq_poly_in_full::<E>(&prev_challenges, &worker);
    let eq_last = eq_precomputed.last().unwrap();
    let output_claim = evaluate_with_precomputed_eq_ext::<E>(&output, eq_last);

    let mut output_claims = BTreeMap::new();
    output_claims.insert(addr_out, output_claim);

    let lookup_multiplicative_part = E::from_base(F::from_u64_with_reduction(0xff));
    let lookup_additive_part = E::from_base(F::from_u64_with_reduction(42));
    let batch_challenge_base = E::from_base(F::from_u64_with_reduction(0xff));

    let mut storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output.clone())],
    );
    let mut seed = Seed::default();

    let run = run_layer_oracle::<F, E>(
        0,
        &layer,
        &output_claims,
        &prev_challenges,
        &mut storage,
        batch_challenge_base,
        POLY_SIZE,
        lookup_multiplicative_part,
        lookup_additive_part,
        &[],
        0,
        &GKRExternalChallenges::default(),
        &mut seed,
        &worker,
    );

    let _ = (addr_a, addr_b, addr_out);

    for step in 0..FOLDING_STEPS {
        let z = prev_challenges[step];
        let claim = run.per_round_claims[step];
        let eq_prefactor = run.per_round_eq_prefactor[step];
        let [c0, c2] = run.per_round_reduced[step];

        // `[c0, c2]` are monomial coefficients (constant, quadratic); `recover_and_emit`
        // consumes round-poly EVALUATIONS `g(0), g(2)`. `g(0) == c0` exactly, while
        // `g(2)` must be reconstructed via the production linear coefficient `d`.
        //   C  = claim / eq_prefactor
        //   b  = 1 - z
        //   g(1) = q1 = (C - b*c0)/z   (sum-constraint-pinned)
        //   d    = q1 - c2 - c0        (production's linear coefficient)
        //   g(2) = 4*c2 + 2*d + c0
        let mut big_c = claim;
        big_c.mul_assign(&eq_prefactor.inverse().unwrap());
        let mut b = E::ONE;
        b.sub_assign(&z);
        let mut bc0 = b;
        bc0.mul_assign(&c0);
        let mut q1 = big_c;
        q1.sub_assign(&bc0);
        q1.mul_assign(&z.inverse().unwrap());
        // d_prod = q1 - c2 - c0
        let mut d_prod = q1;
        d_prod.sub_assign(&c2);
        d_prod.sub_assign(&c0);
        // g2 = 4*c2 + 2*d_prod + c0
        let mut g2 = c2;
        g2.double();
        g2.double(); // 4*c2
        let mut two_d = d_prod;
        two_d.double();
        g2.add_assign(&two_d);
        g2.add_assign(&c0);

        let (coeffs, d) = recover_and_emit::<F, E>(z, claim, eq_prefactor, c0, g2);

        assert_eq!(
            coeffs, run.round_coeffs[step],
            "recover_and_emit diverged from committed round {step}"
        );
        assert_eq!(d, d_prod, "recovered linear coefficient diverged at round {step}");
    }
}
