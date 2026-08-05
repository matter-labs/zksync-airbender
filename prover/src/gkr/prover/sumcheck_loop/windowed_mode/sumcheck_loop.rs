//! Production windowed sumcheck loop: the NEON + SoA + bracket-preserving
//! engine (validated in `windowed_mode::bench`) driving the real transcript.
//!
//! Chain: window-3 initial (rounds 0..3) -> transition in3out1 (round 3, folds
//! everything to ext buffers) -> in1out3 bridge (rounds 4..7) -> in3out3 chain
//! -> in3out1 bridge -> in1out1 tail. Multi-round windows are protocol-valid
//! because each accumulator is bound at the freshly drawn challenge before the
//! next round's univariate is extracted. Per-round `[c0, c2]` coefficients are
//! bit-identical to the per-round batched evaluator's (see the bench
//! validations), so the emitted transcript is unchanged.
//!
//! The fast path applies on aarch64 for BabyBear/Ext4 with `folding_steps >= 10`
//! and window-1 (`N == 2`) last evaluations; anything else returns `None` and
//! the caller falls back to the per-round loop.

use std::mem::MaybeUninit;

use super::*;
use crate::gkr::prover::sumcheck_loop::windowed_mode::bench::{
    build_soa_program, evaluate_ext_window3_soa_parallel, evaluate_initial_soa_parallel,
    evaluate_transition_soa_parallel, find_eq_with_len,
};
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::evaluate_extension_only_rounds_with_full_sized_scratch_parallel;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::in_1_out_1::ExtensionOnlyRoundWindowIn1Out1;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::in_3_out_1::ExtensionOnlyRoundWindowIn3Out1;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::extension_only_round::ExtensionOnlyRoundImplementation;
use crate::gkr::prover::sumcheck_loop::windowed_mode::full_size_scratch::produce_descriptions_from_batched_description;

/// Runs the windowed engine if applicable; `None` means the caller must use
/// the per-round path.
pub(crate) fn windowed_sumcheck_loop<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    const N: usize,
>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut TR::Seed,
) -> Option<(Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, E)>
where
    [(); E::DEGREE]: Sized,
{
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = (
            collector,
            initial_claim,
            prev_challenges,
            eq_poly,
            gkr_storage,
            challenge_constants,
            folding_steps,
            worker,
            seed,
        );
        None
    }

    #[cfg(target_arch = "aarch64")]
    {
        if const { !neon::is_bb_pair::<F, E>() } {
            return None;
        }
        if N != 2 || folding_steps < 10 {
            return None;
        }

        println!("Running sumcheck loop in windowed batched mode");

        let description = collector.make_batched_description(challenge_constants, collector.layer);
        let (_compact, base_addrs, ext_addrs) =
            produce_descriptions_from_batched_description(&description);

        // all sources must be present in storage as their expected kind
        let mut base_sources = Vec::with_capacity(base_addrs.len());
        for addr in base_addrs.iter() {
            base_sources.push(DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                gkr_storage.try_get_base_poly(*addr)?,
            ));
        }
        let mut ext_sources = Vec::with_capacity(ext_addrs.len());
        for addr in ext_addrs.iter() {
            ext_sources.push(DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                gkr_storage.try_get_ext_poly(*addr)?,
            ));
        }

        let prog = build_soa_program(&description, collector, &base_addrs, &ext_addrs);

        let buffer_size = (1usize << folding_steps) / 8;
        let mut base_buffers: Vec<Box<[MaybeUninit<E>]>> = base_addrs
            .iter()
            .map(|_| Box::new_uninit_slice(buffer_size))
            .collect();
        let mut ext_buffers: Vec<Box<[MaybeUninit<E>]>> = ext_addrs
            .iter()
            .map(|_| Box::new_uninit_slice(buffer_size))
            .collect();

        let one_table = [E::ONE];
        let find_eq = |len: usize| -> &[E] {
            if len == 1 {
                &one_table[..]
            } else {
                find_eq_with_len(eq_poly, len)
            }
        };

        let mut claim = initial_claim;
        let mut eq_prefactor = E::ONE;
        let mut folding_challenges: Vec<E> = Vec::with_capacity(folding_steps);
        let mut intermediate_coeffs: Vec<[E; 4]> = Vec::with_capacity(folding_steps);

        macro_rules! emit_round {
            ($step:expr, $c0:expr, $c2:expr) => {{
                let mut normalized_claim = claim;
                normalized_claim
                    .mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));
                let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
                    prev_challenges[$step],
                    normalized_claim,
                    $c0,
                    $c2,
                );
                #[cfg(feature = "gkr_self_checks")]
                {
                    let s0 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ZERO);
                    let s1 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ONE);
                    let mut sum = s0;
                    sum.add_assign(&s1);
                    sum.mul_assign(&eq_prefactor);
                    assert_eq!(
                        sum, claim,
                        "windowed: s(0) + s(1) != claim / eq_prefactor at folding step {}",
                        $step
                    );
                }
                commit_field_els::<F, E, TR>(seed, &coeffs);
                intermediate_coeffs.push(coeffs);
                let folding_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];
                claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);
                eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[$step]);
                folding_challenges.push(folding_challenge);
                folding_challenge
            }};
        }

        // emit the three rounds of a window-3 accumulator, binding at the
        // freshly drawn challenges in between
        macro_rules! emit_window3 {
            ($acc:expr, $s:expr) => {{
                let eq4: [E; 4] = make_eq_poly_in_full::<E>(
                    &prev_challenges[$s + 1..$s + 3],
                    worker,
                )
                .pop()
                .unwrap()
                .to_vec()
                .try_into()
                .unwrap();
                let eq2: [E; 2] = make_eq_poly_in_full::<E>(
                    &prev_challenges[$s + 2..$s + 3],
                    worker,
                )
                .pop()
                .unwrap()
                .to_vec()
                .try_into()
                .unwrap();
                let r = evaluate_claim_from_intermediate_matrix_27(&eq4, &$acc);
                let w = emit_round!($s, r[0], r[2]);
                let acc_9 = bind_accumulator_27(&$acc, &w);
                let r = evaluate_claim_from_intermediate_matrix_9(&eq2, &acc_9);
                let w = emit_round!($s + 1, r[0], r[2]);
                let acc_3 = bind_accumulator_9(&acc_9, &w);
                emit_round!($s + 2, acc_3[0], acc_3[2]);
            }};
        }

        // rounds 0-2: initial window over the original polys
        let acc27 = evaluate_initial_soa_parallel(
            &base_sources,
            &ext_sources,
            &prog.base_interp,
            &prog.ext_interp,
            &prog.forms,
            &prog.products,
            &prog.rest_steps,
            &prog.additive_constant,
            find_eq(1 << (folding_steps - 3)),
            folding_steps,
            worker,
        );
        emit_window3!(acc27, 0);

        // round 3: transition, folds everything into the ext buffers
        {
            let prefix: [E; 8] = make_eq_poly_in_full::<E>(&folding_challenges[..3], worker)
                .pop()
                .unwrap()
                .to_vec()
                .try_into()
                .unwrap();
            let base_ptrs: Vec<usize> = base_buffers
                .iter_mut()
                .map(|el| el.as_mut_ptr() as usize)
                .collect();
            let ext_ptrs: Vec<usize> = ext_buffers
                .iter_mut()
                .map(|el| el.as_mut_ptr() as usize)
                .collect();
            let acc2 = evaluate_transition_soa_parallel(
                &base_sources,
                &ext_sources,
                &base_ptrs,
                &ext_ptrs,
                &prog.forms,
                &prog.products,
                &prog.folded_quad,
                &prog.folded_lin,
                &prog.additive_constant,
                &prefix,
                find_eq(1 << (folding_steps - 4)),
                folding_steps,
                worker,
            );
            emit_round!(3, acc2[0], acc2[1]);
        }

        let mut cur_log2 = folding_steps - 3;
        let mut next_round = 4;

        // window-3 ext pass over the folded buffers (SoA), used while the pass
        // is large enough for 4-row blocking
        macro_rules! soa_window3 {
            ($fold2:expr, $fold8:expr, $work:expr) => {{
                let ptrs: Vec<usize> = base_buffers
                    .iter_mut()
                    .chain(ext_buffers.iter_mut())
                    .map(|el| el.as_mut_ptr() as usize)
                    .collect();
                let fold2: Option<&E> = $fold2;
                let fold8: Option<&[E; 8]> = $fold8;
                evaluate_ext_window3_soa_parallel::<F, E>(
                    &ptrs,
                    fold2,
                    fold8,
                    &prog.forms,
                    &prog.products,
                    &prog.folded_quad,
                    &prog.folded_lin,
                    &prog.additive_constant,
                    find_eq($work),
                    cur_log2,
                    worker,
                )
            }};
        }

        // generic (AoS trait) ext pass fallback for the tail
        macro_rules! aos_ext_pass {
            ($impl:ty) => {{
                let work = <$impl as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(cur_log2);
                let prefix = <$impl as ExtensionOnlyRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                    &folding_challenges,
                    worker,
                );
                let base_b: Vec<_> = base_buffers
                    .iter_mut()
                    .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                    .collect();
                let ext_b: Vec<_> = ext_buffers
                    .iter_mut()
                    .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                    .collect();
                evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, $impl>(
                    base_b,
                    ext_b,
                    &_compact,
                    &prefix,
                    find_eq(work),
                    cur_log2,
                    worker,
                )
            }};
        }

        // rounds 4-6: bridge with one pending challenge
        {
            let work = (1usize << cur_log2) / 16;
            let w3 = folding_challenges[next_round - 1];
            let acc = soa_window3!(Some(&w3), None, work);
            emit_window3!(acc, next_round);
            cur_log2 -= 1;
            next_round += 3;
        }

        // in3out3 chain; stop early enough that the tail (in3out1 bridge +
        // in1out1 rounds) always ends on a 2-element line for any n
        while folding_steps - next_round >= 5 {
            let work = (1usize << cur_log2) / 64;
            if work >= 4 && work % 4 == 0 {
                let prefix: [E; 8] = make_eq_poly_in_full::<E>(
                    &folding_challenges[next_round - 3..next_round],
                    worker,
                )
                .pop()
                .unwrap()
                .to_vec()
                .try_into()
                .unwrap();
                let acc = soa_window3!(None, Some(&prefix), work);
                emit_window3!(acc, next_round);
            } else {
                let acc = aos_ext_pass!(
                    super::full_size_scratch::extension_only_round::in_3_out_3::ExtensionOnlyRoundWindowIn3Out3
                );
                emit_window3!(acc, next_round);
            }
            cur_log2 -= 3;
            next_round += 3;
        }

        // three challenges pending; bridge out with a window of 1
        if next_round < folding_steps {
            let acc = aos_ext_pass!(ExtensionOnlyRoundWindowIn3Out1);
            emit_round!(next_round, acc[0], acc[1]);
            cur_log2 -= 3;
            next_round += 1;
        }

        // in1out1 tail
        while next_round < folding_steps {
            let acc = aos_ext_pass!(ExtensionOnlyRoundWindowIn1Out1);
            emit_round!(next_round, acc[0], acc[1]);
            cur_log2 -= 1;
            next_round += 1;
        }

        assert_eq!(folding_challenges.len(), folding_steps);
        assert_eq!(cur_log2, 1);

        // the buffers now hold each poly folded by w_0..w_{n-2}: a 2-element
        // line, which is exactly the classic loop's `last_evaluations`
        let mut last_evaluations: BTreeMap<GKRAddress, [E; N]> = BTreeMap::new();
        for (addr, buf) in base_addrs.iter().zip(base_buffers.iter()) {
            let f0 = unsafe { buf[0].assume_init() };
            let f1 = unsafe { buf[1].assume_init() };
            let line = [f0, f1];
            last_evaluations.insert(*addr, core::array::from_fn(|i| line[i.min(1)]));
        }
        for (addr, buf) in ext_addrs.iter().zip(ext_buffers.iter()) {
            let f0 = unsafe { buf[0].assume_init() };
            let f1 = unsafe { buf[1].assume_init() };
            let line = [f0, f1];
            last_evaluations.insert(*addr, core::array::from_fn(|i| line[i.min(1)]));
        }

        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

        Some((
            folding_challenges,
            intermediate_coeffs,
            last_evaluations,
            normalized_claim,
        ))
    }
}
