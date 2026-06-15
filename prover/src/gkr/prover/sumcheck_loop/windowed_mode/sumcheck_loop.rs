use std::mem::MaybeUninit;

use super::*;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::ExtensionOnlyRoundImplementation;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::initial_round::*;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::produce_descriptions_from_batched_description;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::transition_round::TransitionRoundImplementation;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::transition_round::evaluate_transition_with_full_sized_scratch_parallel;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::transition_round::in_3_out_1::TransitionRoundWindowIn3Out1;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::in_1_out_1::ExtensionOnlyRoundWindowIn1Out1;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::evaluate_extension_only_rounds_with_full_sized_scratch_parallel;

pub(crate) fn windowed_sumcheck_loop<F: PrimeField, E: FieldExtension<F> + Field, const N: usize>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut Seed,
    // ) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, [E; 2])
) where
    [(); E::DEGREE]: Sized,
{
    println!("Running sumcheck loop in windowed batched mode");

    let mut claim = initial_claim;
    let mut folding_challenges: Vec<E> = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; N]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let mut intermediate_coeffs: Vec<[E; 4]> = Vec::with_capacity(folding_steps);

    let batched_description =
        collector.make_batched_description(challenge_constants, collector.layer);
    let (windowed_description, base_field_polys, ext_field_polys) =
        produce_descriptions_from_batched_description(&batched_description);

    assert!(folding_steps >= 6);

    let mut unfolded_input_size: usize = 1 << folding_steps;

    let now = std::time::Instant::now();
    {
        // initial windows of 3
        let base_sources: Vec<_> = base_field_polys
            .iter()
            .map(|el| {
                let slice = gkr_storage
                    .try_get_base_poly(*el)
                    .expect(&format!("must get an base field poly for address {:?}", el));
                DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
            })
            .collect();
        let ext_sources: Vec<_> = ext_field_polys
            .iter()
            .map(|el| {
                let slice = gkr_storage.try_get_ext_poly(*el).expect(&format!(
                    "must get an extension field poly for address {:?}",
                    el
                ));
                DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
            })
            .collect();

        let unfolded_input_size_log_2 = unfolded_input_size.trailing_zeros() as usize;
        let work_size = unfolded_input_size / 8;
        let mut found_eq = None;
        for eq_matrix in eq_poly.iter() {
            if eq_matrix.len() == work_size {
                found_eq = Some(eq_matrix);
                break;
            }
        }
        let eq_matrix = found_eq.expect("precomputed eq suffix");
        let acc = evaluate_initial_with_full_sized_scratch_parallel(
            base_sources,
            ext_sources,
            &windowed_description,
            eq_matrix,
            unfolded_input_size_log_2,
            worker,
        );
    }
    println!("Initial 3 rounds took {:?}", now.elapsed());
    let buffer_sizes = unfolded_input_size / 8;

    let mut base_folding_buffers: Vec<Box<[MaybeUninit<E>]>> = base_field_polys
        .iter()
        .map(|_| Box::new_uninit_slice(buffer_sizes))
        .collect();
    let mut ext_folding_buffers: Vec<Box<[MaybeUninit<E>]>> = ext_field_polys
        .iter()
        .map(|_| Box::new_uninit_slice(buffer_sizes))
        .collect();

    folding_challenges.push(E::TWO);
    folding_challenges.push(E::TWO);
    folding_challenges.push(E::TWO);

    {
        let now = std::time::Instant::now();

        type I = TransitionRoundWindowIn3Out1;

        let unfolded_input_size_log_2 = unfolded_input_size.trailing_zeros() as usize;
        let folded_poly_size =
            <I as TransitionRoundImplementation<F, E>>::folded_buffer_size_for_unfolded_input_size(
                folding_steps,
            );
        assert_eq!(buffer_sizes, folded_poly_size);
        let work_size =
            <I as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                folding_steps,
            );
        let mut found_eq = None;
        for eq_matrix in eq_poly.iter() {
            if eq_matrix.len() == work_size {
                found_eq = Some(eq_matrix);
                break;
            }
        }
        let precomputed_prefix =
            I::make_prefix_from_all_folding_challenges(&folding_challenges, worker);
        let eq_matrix = found_eq.expect("precomputed eq suffix");

        let base_sources: Vec<_> = base_field_polys
            .iter()
            .map(|el| {
                let slice = gkr_storage
                    .try_get_base_poly(*el)
                    .expect(&format!("must get an base field poly for address {:?}", el));
                DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
            })
            .collect();
        let ext_sources: Vec<_> = ext_field_polys
            .iter()
            .map(|el| {
                let slice = gkr_storage.try_get_ext_poly(*el).expect(&format!(
                    "must get an extension field poly for address {:?}",
                    el
                ));
                DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
            })
            .collect();

        let base_buffers: Vec<_> = base_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();
        let ext_buffers: Vec<_> = ext_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();

        let acc = evaluate_transition_with_full_sized_scratch_parallel::<
            F,
            E,
            TransitionRoundWindowIn3Out1,
        >(
            base_sources,
            ext_sources,
            base_buffers,
            ext_buffers,
            &windowed_description,
            &precomputed_prefix,
            eq_matrix,
            unfolded_input_size_log_2,
            worker,
        );

        unfolded_input_size = folded_poly_size;
        for _ in 0..<I as TransitionRoundImplementation<F, E>>::OUTPUT_WINDOW_SIZE {
            folding_challenges.push(E::TWO);
        }

        let in_size = <I as TransitionRoundImplementation<F, E>>::INPUT_WINDOW_SIZE;
        let out_size = <I as TransitionRoundImplementation<F, E>>::OUTPUT_WINDOW_SIZE;
        println!(
            "Transition {} in {} out took {:?}",
            in_size,
            out_size,
            now.elapsed()
        );
    }

    {
        let now = std::time::Instant::now();
        type I = ExtensionOnlyRoundWindowIn1Out1;

        let unfolded_input_size_log_2 = unfolded_input_size.trailing_zeros() as usize;
        let folded_poly_size = <I as ExtensionOnlyRoundImplementation<F, E>>::folded_buffer_size_for_unfolded_input_size(unfolded_input_size_log_2);
        let work_size =
            <I as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                unfolded_input_size_log_2,
            );
        let mut found_eq = None;
        for eq_matrix in eq_poly.iter() {
            if eq_matrix.len() == work_size {
                found_eq = Some(eq_matrix);
                break;
            }
        }
        let precomputed_prefix =
            I::make_prefix_from_all_folding_challenges(&folding_challenges, worker);
        let eq_matrix = found_eq.expect("precomputed eq suffix");

        let base_buffers: Vec<_> = base_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
            .collect();
        let ext_buffers: Vec<_> = ext_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
            .collect();

        let acc = evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, I>(
            base_buffers,
            ext_buffers,
            &windowed_description,
            &precomputed_prefix,
            eq_matrix,
            unfolded_input_size_log_2,
            worker,
        );

        unfolded_input_size = folded_poly_size;
        for _ in 0..<I as ExtensionOnlyRoundImplementation<F, E>>::OUTPUT_WINDOW_SIZE {
            folding_challenges.push(E::TWO);
        }

        let in_size = <I as ExtensionOnlyRoundImplementation<F, E>>::INPUT_WINDOW_SIZE;
        let out_size = <I as ExtensionOnlyRoundImplementation<F, E>>::OUTPUT_WINDOW_SIZE;
        println!(
            "Extension {} in {} out took {:?}",
            in_size,
            out_size,
            now.elapsed()
        );
    }

    // // now all the way using window of size 3 or 2

    // for step in 0..folding_steps - 1 {
    //     let acc_size = 1 << (folding_steps - step - 1);
    //     let accumulator = &mut accumulator_buffer[..acc_size];
    //     if step > 0 {
    //         accumulator.fill([E::ZERO; 2]);
    //     }

    //     if USE_BATCHING {
    //         use crate::gkr::prover::sumcheck_loop::batch_evaluation::evaluate_batched_gkr_description;
    //         evaluate_batched_gkr_description(
    //             &batched_description,
    //             gkr_storage,
    //             step,
    //             &folding_challenges,
    //             accumulator,
    //             folding_steps,
    //             &mut last_evaluations,
    //             worker,
    //         );
    //     } else {
    //         collector.evaluate_kernels_over_storage(
    //             gkr_storage,
    //             step,
    //             &folding_challenges,
    //             accumulator,
    //             folding_steps,
    //             &mut last_evaluations,
    //             worker,
    //         );
    //     }

    //     let eq = &eq_poly[folding_steps - step - 1];

    //     assert_eq!(eq.len(), acc_size);

    //     let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
    //         &accumulator,
    //         eq,
    //         worker,
    //     );

    //     let mut normalized_claim = claim;
    //     normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

    //     let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
    //         prev_challenges[step],
    //         normalized_claim,
    //         c0,
    //         c2,
    //     );

    //     #[cfg(feature = "gkr_self_checks")]
    //     {
    //         let s0 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ZERO);
    //         let s1 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ONE);
    //         let mut sum = s0;
    //         sum.add_assign(&s1);
    //         sum.mul_assign(&eq_prefactor);
    //         assert_eq!(
    //             sum, claim,
    //             "s(0) + s(1) != claim / eq_prefactor at folding step {}",
    //             step
    //         );
    //     }

    //     commit_field_els(seed, &coeffs);
    //     intermediate_coeffs.push(coeffs);
    //     let folding_challenge = draw_random_field_els(seed, 1)[0];

    //     let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

    //     claim = new_claim;
    //     eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

    //     folding_challenges.push(folding_challenge);
    // }

    // // Final step - we do not make a new claim, and do not update the transcript yet
    // {
    //     let step = folding_steps - 1;
    //     let accumulator = &mut accumulator_buffer[..1];
    //     accumulator.fill([E::ZERO; 2]);

    //     if USE_BATCHING {
    //         use crate::gkr::prover::sumcheck_loop::batch_evaluation::evaluate_batched_gkr_description;
    //         evaluate_batched_gkr_description(
    //             &batched_description,
    //             gkr_storage,
    //             step,
    //             &folding_challenges,
    //             accumulator,
    //             folding_steps,
    //             &mut last_evaluations,
    //             worker,
    //         );
    //     } else {
    //         collector.evaluate_kernels_over_storage(
    //             gkr_storage,
    //             step,
    //             &folding_challenges,
    //             accumulator,
    //             folding_steps,
    //             &mut last_evaluations,
    //             worker,
    //         );
    //     }

    //     #[cfg(feature = "gkr_self_checks")]
    //     {
    //         let [f0, f1] = accumulator[0];
    //         let [eq0, eq1]: [E; 2] = eq_poly[1].to_vec().try_into().unwrap();

    //         let mut t0 = eq0;
    //         t0.mul_assign(&f0);
    //         let mut t1 = eq1;
    //         t1.mul_assign(&f1);
    //         let mut claim_inner = t0;
    //         claim_inner.add_assign(&t1);

    //         let mut recomputed_claim = claim_inner;
    //         recomputed_claim.mul_assign(&eq_prefactor);

    //         assert_eq!(
    //             recomputed_claim, claim,
    //             "s(0) + s(1) != claim / eq_prefactor at explicit sumcheck verification"
    //         );
    //     }
    // }

    // (
    //     folding_challenges,
    //     intermediate_coeffs,
    //     last_evaluations,
    //     accumulator_buffer[0],
    // )
}
