use std::collections::BTreeMap;

use field::{PrimeField, FieldExtension, Field};
use crate::gkr::sumcheck::{
    access_and_fold::GKRStorage,
    eq_poly::{
        evaluate_constant_and_quadratic_coeffs_with_precomputed_eq, make_eq_poly_in_full,
    },
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use crate::worker::Worker;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRLayerDescription;
use transcript::Seed;
use crate::gkr::prover::transcript_utils::{draw_random_field_els, commit_field_els};
use kernel_collector::KernelCollector;

mod kernel_collector;


pub fn evaluate_sumcheck_for_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<F>,
    _external_challenges: &crate::gkr::prover::GKRExternalChallenges<F, E>,
    trace_len: usize,
    lookup_challenges_additive_part: E,
    constraints_batch_challenge: E,
    worker: &Worker,
    seed: &mut Seed
)
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized,
{
    println!("Running sum-check for layer {}", layer_idx);

    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    debug_assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps >= 4, "need at least 4 folding steps");

    let eq_polys = make_eq_poly_in_full::<E>(prev_challenges);

    let challenges: Vec<E> = draw_random_field_els(seed, 1);
    let batch_challenge_base: E = challenges[0];

    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        batch_challenge_base,
        gkr_storage,
        lookup_challenges_additive_part,
        constraints_batch_challenge,
        compiled_circuit.memory_layout.total_width,
        compiled_circuit.witness_layout.total_width,
    );

    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    let (folding_challenges, last_evaluations) = run_sumcheck_loop(
        &collector,
        claim,
        prev_challenges,
        &eq_polys,
        gkr_storage,
        folding_steps,
        worker,
        seed
    );

    // After sumcheck completes, extract claims for the input layer
    let last_r = folding_challenges
        .last()
        .expect("must have at least one folding challenge");

    let new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, &[f0, f1])| (*addr, interpolate_linear::<F, E>(f0, f1, last_r)))
        .collect();

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    // and we can purge the storage
    gkr_storage.purge_up_to_layer(layer_idx);
}

fn run_sumcheck_loop<F: PrimeField, E: FieldExtension<F> + Field>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut Seed
) -> (Vec<E>, BTreeMap<GKRAddress, [E; 2]>) 
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized
{
    let mut claim = initial_claim;
    let mut folding_challenges = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; 2]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let max_acc_size = 1 << (folding_steps - 1);
    let mut accumulator_buffer = vec![[E::ZERO; 2]; max_acc_size];

    for step in 0..folding_steps - 1 {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        accumulator.fill([E::ZERO; 2]);

        collector.evaluate_kernels_over_storage(
            gkr_storage,
            step,
            &folding_challenges,
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        let eq = &eq_poly[folding_steps - step - 1];

        debug_assert_eq!(eq.len(), acc_size);

        let [c0, c2] =
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(&accumulator, eq);

        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

        let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
            prev_challenges[step],
            normalized_claim,
            c0,
            c2,
        );

        #[cfg(feature = "gkr_self_checks")]
        {
            let s0 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ONE);
            let mut sum = s0;
            sum.add_assign(&s1);
            sum.mul_assign(&eq_prefactor);
            assert_eq!(sum, claim, "s(0) + s(1) != claim / eq_prefactor");
        }

        commit_field_els(seed, &coeffs);
        let folding_challenge = unsafe { *draw_random_field_els(seed, 1).get_unchecked(0) };
        
        let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

        claim = new_claim;
        eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

        folding_challenges.push(folding_challenge);
    }

    // Final step
    {
        let step = folding_steps - 1;
        let accumulator = &mut accumulator_buffer[..1];
        accumulator.fill([E::ZERO; 2]);

        collector.evaluate_kernels_over_storage(
            gkr_storage,
            step,
            &folding_challenges,
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        let [f0, f1] = accumulator[0];

        commit_field_els(seed, &[f0, f1]);
        let folding_challenge = unsafe { *draw_random_field_els(seed, 1).get_unchecked(0)};
        
        let [eq0, eq1]: [E; 2] = eq_poly[1].to_vec().try_into().unwrap();

        let mut t0 = eq0;
        t0.mul_assign(&f0);
        let mut t1 = eq1;
        t1.mul_assign(&f1);
        let mut claim_inner = t0;
        claim_inner.add_assign(&t1);

        #[cfg(feature = "gkr_self_checks")]
        {
            let mut recomputed_claim = claim_inner;
            recomputed_claim.mul_assign(&eq_prefactor);
            assert_eq!(recomputed_claim, claim);
        }

        folding_challenges.push(folding_challenge);
    }

    (folding_challenges, last_evaluations)
}


#[inline(always)]
fn interpolate_linear<F: PrimeField, E: FieldExtension<F> + Field>(f0: E, f1: E, r: &E) -> E {
    let mut result = f1;
    result.sub_assign(&f0);
    result.mul_assign(r);
    result.add_assign(&f0);
    result
}