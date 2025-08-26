#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![feature(array_chunks)]
#![feature(ptr_as_ref_unchecked)]
#![feature(slice_from_ptr_range)]
#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

extern crate alloc;

use core::mem::MaybeUninit;

use field::{
    batch_inverse_checked, Field, FieldExtension, Mersenne31Complex, Mersenne31Field,
    Mersenne31Quartic,
};
use verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use verifier_common::cs::definitions::*;
use verifier_common::fri_folding::fri_fold_by_log_n;
use verifier_common::fri_folding::fri_fold_by_log_n_with_fma;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::prover::definitions::*;
use verifier_common::transcript::Blake2sTranscript;
use verifier_common::DefaultLeafInclusionVerifier;
use verifier_common::DefaultNonDeterminismSource;
use verifier_common::ProofOutput;

pub mod concrete;
pub mod skeleton;
pub mod utils;
pub use verifier_common::structs::*;

pub use verifier_common::ProofPublicInputs;

pub use field;
pub use verifier_common;
pub use verifier_common::blake2s_u32;
pub use verifier_common::prover;
pub use verifier_common::transcript;

use self::concrete::*;
use self::utils::*;

pub type ConcreteProofOutput =
    ProofOutput<TREE_CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, NUM_AUX_BOUNDARY_VALUES>;
pub type ConcreteProofPublicInputs = ProofPublicInputs<NUM_STATE_ELEMENTS>;

#[cfg(test)]
mod tests;

#[allow(invalid_value)]
#[allow(unreachable_code)]
#[inline(always)]
pub unsafe fn verify(
    proof_state_dst: &mut ProofOutput<
        TREE_CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
    >,
    proof_input_dst: &mut ProofPublicInputs<NUM_STATE_ELEMENTS>,
) {
    verify_with_configuration::<DefaultNonDeterminismSource, DefaultLeafInclusionVerifier>(
        proof_state_dst,
        proof_input_dst,
    )
}

/// This function effectively asserts existence of the valid(!) proof for some fixed
/// geometry + constraints (but not setup), and returns the values needed to verify chunking
/// of the statement being proven if needed. Internally if `proof_state_dst` is Some, then
/// the function assumes that it runs as a part of the chain of proofs of the same "flavour", and enforces some invariants.
/// It is designed to be run within riscV environment (it loads the proofs from the CSR).
// If you want to run it outside of riscV environment, make sure to set `verifier_in_rust` feature flag.
#[allow(invalid_value)]
#[allow(unreachable_code)]
#[inline(never)]
pub unsafe fn verify_with_configuration<I: NonDeterminismSource, V: LeafInclusionVerifier>(
    proof_state_dst: &mut ProofOutput<
        TREE_CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
    >,
    proof_input_dst: &mut ProofPublicInputs<NUM_STATE_ELEMENTS>,
) {
    // #[cfg(test)]
    // panic!();

    Mersenne31Quartic::init_ext4_fma_ops();

    let mut leaf_inclusion_verifier = V::new();

    let mut skeleton = MaybeUninit::<ProofSkeletonInstance>::uninit().assume_init();
    ProofSkeletonInstance::fill::<I>((&mut skeleton) as *mut _);
    // let skeleton = skeleton.assume_init();

    let mut queries = MaybeUninit::<[QueryValuesInstance; NUM_QUERIES]>::uninit().assume_init();
    QueryValuesInstance::fill_array::<I, V, NUM_QUERIES>(
        (&mut queries) as *mut _,
        &skeleton,
        &mut leaf_inclusion_verifier,
    );
    // let queries = queries.assume_init();

    // now drive the transcript and continue
    let mut transcript_hasher = blake2s_u32::DelegatedBlake2sState::new();
    let mut seed = Blake2sTranscript::commit_initial_using_hasher(
        &mut transcript_hasher,
        skeleton.transcript_elements_before_stage2(),
    );

    // draw local lookup argument challenges
    let mut transcript_challenges = MaybeUninit::<
        [u32; ((NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4)
            .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)],
    >::uninit()
    .assume_init();
    Transcript::draw_randomness_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        &mut transcript_challenges,
    );

    let mut it = transcript_challenges.array_chunks::<4>();
    let lookup_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES] = core::array::from_fn(|_| {
        Mersenne31Quartic::from_array_of_base(
            it.next()
                .unwrap_unchecked()
                .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
        )
    });
    let lookup_argument_gamma = Mersenne31Quartic::from_array_of_base(
        it.next()
            .unwrap_unchecked()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    // commit stage 2 artifacts - tree and memory grand product / delegation set accumulator
    Blake2sTranscript::commit_with_seed_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        skeleton.transcript_elements_stage2_to_stage3(),
    );

    // draw quotient linearization challenges
    let mut transcript_challenges = MaybeUninit::<
        [u32; (2usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)],
    >::uninit()
    .assume_init();
    Transcript::draw_randomness_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        &mut transcript_challenges,
    );

    let mut it = transcript_challenges.array_chunks::<4>();
    let quotient_alpha = Mersenne31Quartic::from_array_of_base(
        it.next()
            .unwrap_unchecked()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    let quotient_beta = Mersenne31Quartic::from_array_of_base(
        it.next()
            .unwrap_unchecked()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    // commit quotient tree
    Blake2sTranscript::commit_with_seed_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        skeleton.transcript_elements_stage3_to_stage4(),
    );

    // draw DEEP poly linearization challenge
    let mut transcript_challenges = MaybeUninit::<
        [u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)],
    >::uninit()
    .assume_init();
    Transcript::draw_randomness_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        &mut transcript_challenges,
    );

    let mut it = transcript_challenges.array_chunks::<4>();
    let z = Mersenne31Quartic::from_array_of_base(
        it.next()
            .unwrap_unchecked()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    // commit evaluations
    Blake2sTranscript::commit_with_seed_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        skeleton.transcript_elements_evaluations_at_z(),
    );

    // draw initial challenge for DEEP-poly
    let mut transcript_challenges = MaybeUninit::<
        [u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)],
    >::uninit()
    .assume_init();
    Transcript::draw_randomness_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        &mut transcript_challenges,
    );

    let mut it = transcript_challenges.array_chunks::<4>();
    let deep_poly_alpha = Mersenne31Quartic::from_array_of_base(
        it.next()
            .unwrap_unchecked()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    // now we should draw challenges and commit FRI oracles
    #[allow(invalid_value)]
    let mut fri_folding_challenges: [Mersenne31Quartic; NUM_FRI_STEPS] =
        [MaybeUninit::uninit().assume_init(); NUM_FRI_STEPS];

    for (caps, challenge) in skeleton
        .transcript_elements_fri_intermediate_oracles()
        .into_iter()
        .zip(fri_folding_challenges.iter_mut())
    {
        Blake2sTranscript::commit_with_seed_using_hasher(&mut transcript_hasher, &mut seed, caps);

        let mut transcript_challenges = MaybeUninit::<
            [u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)],
        >::uninit()
        .assume_init();
        Transcript::draw_randomness_using_hasher(
            &mut transcript_hasher,
            &mut seed,
            &mut transcript_challenges,
        );

        let mut it = transcript_challenges.array_chunks::<4>();
        *challenge = Mersenne31Quartic::from_array_of_base(
            it.next()
                .unwrap_unchecked()
                .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
        );
    }

    if LAST_FRI_STEP_EXPOSE_LEAFS {
        let dst = &mut fri_folding_challenges[NUM_FRI_STEPS - 1];
        Blake2sTranscript::commit_with_seed_using_hasher(
            &mut transcript_hasher,
            &mut seed,
            skeleton.transcript_elements_last_fri_step_leaf_values(),
        );

        let mut transcript_challenges = MaybeUninit::<
            [u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)],
        >::uninit()
        .assume_init();
        Transcript::draw_randomness_using_hasher(
            &mut transcript_hasher,
            &mut seed,
            &mut transcript_challenges,
        );

        let mut it = transcript_challenges.array_chunks::<4>();
        *dst = Mersenne31Quartic::from_array_of_base(
            it.next()
                .unwrap_unchecked()
                .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
        );
    }

    // commit monomial coefficients before drawing queries
    Blake2sTranscript::commit_with_seed_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        skeleton.transcript_elements_monomial_coefficients(),
    );

    // now we can verify PoW
    Blake2sTranscript::verify_pow_using_hasher(
        &mut transcript_hasher,
        &mut seed,
        skeleton.pow_nonce,
        POW_BITS as u32,
    );

    // now we need to draw enough bits to form query indexes
    let mut indexes_bits: [u32; NUM_REQUIRED_WORDS_FOR_QUERY_INDEXES] =
        MaybeUninit::<[u32; NUM_REQUIRED_WORDS_FOR_QUERY_INDEXES]>::uninit().assume_init();
    Transcript::draw_randomness_using_hasher(&mut transcript_hasher, &mut seed, &mut indexes_bits);

    // NOTE: when we will use queries below, we MUST check that query set's index is exactly the index we draw from transcript.
    // Indexes in `queries` are already checked to be included in merkle tree caps declared in `skeleton`

    // And NOW we can check algebraic properties of the proof:
    // - quotient evaluation at z
    // - consistency check for DEEP poly
    // - correct folding in FRI

    // quotient evaluation at z

    let omega = Mersenne31Complex::TWO_ADICITY_GENERATORS[TRACE_LEN_LOG2];
    let omega_inv = Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED[TRACE_LEN_LOG2];

    let mut z_omega = z;
    z_omega.mul_assign_by_base(&omega);

    {
        // setup, then witness, then memory, then stage 2 base, then stage 2 ext, then quotient
        let (setup, rest) = skeleton.openings_at_z.split_at(NUM_SETUP_OPENINGS);
        let (witness, rest) = rest.split_at(NUM_WITNESS_OPENINGS);
        let (memory, rest) = rest.split_at(NUM_MEMORY_OPENINGS);
        let (stage_2, rest) = rest.split_at(NUM_STAGE2_OPENINGS);
        assert_eq!(rest.len(), 1);
        let quotient_opening = rest[0];

        let mut witness_next_row: [_; NUM_WITNESS_OPENINGS] = MaybeUninit::uninit().assume_init();
        let mut memory_next_row: [_; NUM_MEMORY_OPENINGS] = MaybeUninit::uninit().assume_init();
        let mut stage_2_next_row: [_; NUM_STAGE2_OPENINGS] = MaybeUninit::uninit().assume_init();

        // we only need to update very few places here, so we will overwrite them below

        let mut lookup_argument_two_gamma = lookup_argument_gamma;
        lookup_argument_two_gamma.double();

        let (witness_next_row_set, rest) = skeleton
            .openings_at_z_omega
            .split_at(NUM_WITNESS_OPENING_NEXT_ROW);
        let (memory_next_row_set, rest) = rest.split_at(NUM_MEMORY_OPENING_NEXT_ROW);
        assert_eq!(rest.len(), 1);
        let stage_2_next_row_set = rest;

        debug_assert_eq!(
            witness_next_row_set.len(),
            WITNESS_NEXT_ROW_OPENING_INDEXES.len()
        );
        debug_assert_eq!(
            memory_next_row_set.len(),
            MEMORY_NEXT_ROW_OPENING_INDEXES.len()
        );

        for (index, element) in WITNESS_NEXT_ROW_OPENING_INDEXES
            .iter()
            .zip(witness_next_row_set.iter())
        {
            witness_next_row[*index] = *element;
        }
        for (index, element) in MEMORY_NEXT_ROW_OPENING_INDEXES
            .iter()
            .zip(memory_next_row_set.iter())
        {
            memory_next_row[*index] = *element;
        }

        stage_2_next_row[MEMORY_GRAND_PRODUCT_ACCUMULATOR_POLY_INDEX] = stage_2_next_row_set[0];

        let mut vanishing = z;
        vanishing.exp_power_of_2(TRACE_LEN_LOG2);
        vanishing.sub_assign_base(&Mersenne31Field::ONE);

        let omega_inv_squared =
            Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED[TRACE_LEN_LOG2 - 1];

        let mut z_minus_omega_inv = z;
        z_minus_omega_inv.sub_assign_base(&omega_inv);

        let mut z_minus_omega_inv_squared = z;
        z_minus_omega_inv_squared.sub_assign_base(&omega_inv_squared);

        // now we should assemble candidates for batch inversion

        // first row is 1 / (x - omega^0)
        let mut first_row_to_inverse = z;
        first_row_to_inverse.sub_assign_base(&Mersenne31Field::ONE);

        // one before last row is 1/(x - omega^-2)
        let mut one_before_last_row_to_inverse = z;
        one_before_last_row_to_inverse.sub_assign_base(&omega_inv_squared);

        // last row is 1/(x - omega^-1)
        let mut last_row_to_inverse = z;
        last_row_to_inverse.sub_assign_base(&omega_inv);

        let mut to_batch_inverse = [
            z,
            vanishing,
            first_row_to_inverse,
            one_before_last_row_to_inverse,
            last_row_to_inverse,
        ];

        let mut buffer = to_batch_inverse;

        let all_non_zero = field::batch_inverse_checked(&mut to_batch_inverse, &mut buffer);
        // low probability here
        assert!(all_non_zero);

        let [z_inv, vanishing_inv, first_row, one_before_last_row, last_row] = to_batch_inverse;

        // everywhere except last row (x - omega^-1) / (x^n - 1)
        let mut everywhere_except_last = z_minus_omega_inv;
        everywhere_except_last.mul_assign(&vanishing_inv);

        // everywhere except last two rows
        let mut everywhere_except_last_two_rows = everywhere_except_last;
        everywhere_except_last_two_rows.mul_assign(&z_minus_omega_inv_squared);

        let mut last_row_and_zero = last_row;
        last_row_and_zero.mul_assign(&z_inv);

        let divisors = [
            everywhere_except_last,
            everywhere_except_last_two_rows,
            first_row,
            one_before_last_row,
            last_row,
            last_row_and_zero,
        ];

        let delegation_argument_accumulator_sum =
            if skeleton.delegation_argument_accumulator.len() > 0 {
                *skeleton.delegation_argument_accumulator.get_unchecked(0)
            } else {
                // will be unused, but we do not want to deal with Option
                Mersenne31Quartic::ZERO
            };

        let aux_proof_values = ProofAuxValues {
            memory_grand_product_accumulator_final_value: skeleton.memory_grand_product_accumulator,
            delegation_argument_accumulator_sum,
        };

        let delegation_argument_linearization_challenges =
            if skeleton.delegation_argument_challenges.len() > 0 {
                *skeleton.delegation_argument_challenges.get_unchecked(0)
            } else {
                ExternalDelegationArgumentChallenges::default()
            };

        let aux_boundary_values = if skeleton.aux_boundary_values.len() > 0 {
            *skeleton.aux_boundary_values.get_unchecked(0)
        } else {
            AuxArgumentsBoundaryValues::default()
        };

        assert!((u32::MAX >> CIRCUIT_SEQUENCE_BITS_SHIFT) >= skeleton.circuit_sequence_idx);

        let memory_timestamp_high_from_circuit_sequence =
            Mersenne31Field::new(skeleton.circuit_sequence_idx << CIRCUIT_SEQUENCE_BITS_SHIFT);

        let delegation_type = Mersenne31Field::new(skeleton.delegation_type);

        // we need to show the sum of the values everywhere except the last row,
        // so we show that intermediate poly - interpolant((0, 0), (omega^-1, `value``)) is divisible
        // by our selected divisor, where "value" == negate(our sum over all other domain), and we also require that sum over
        // all the domain is 0

        // interpolant is literally 1/omega^-1 * value * X (as one can see it's 0 at 0 and `value` at omega^-1)
        let mut delegation_argument_interpolant_linear_coeff = delegation_argument_accumulator_sum;
        delegation_argument_interpolant_linear_coeff.mul_assign_by_base(&omega);
        delegation_argument_interpolant_linear_coeff.negate();

        use crate::concrete::evaluate_quotient;
        let quotient_recomputed_value = evaluate_quotient(
            z,
            witness,
            memory,
            setup,
            stage_2,
            &witness_next_row,
            &memory_next_row,
            &stage_2_next_row,
            quotient_alpha,
            quotient_beta,
            &divisors,
            lookup_argument_linearization_challenges,
            lookup_argument_gamma,
            lookup_argument_two_gamma,
            skeleton
                .memory_argument_challenges
                .memory_argument_linearization_challenges,
            skeleton.memory_argument_challenges.memory_argument_gamma,
            delegation_argument_linearization_challenges
                .delegation_argument_linearization_challenges,
            delegation_argument_linearization_challenges.delegation_argument_gamma,
            &skeleton.public_inputs,
            &aux_proof_values,
            aux_boundary_values,
            memory_timestamp_high_from_circuit_sequence,
            delegation_type,
            delegation_argument_interpolant_linear_coeff,
        );

        assert_eq!(
            quotient_recomputed_value, quotient_opening,
            "quotient evaluation diverged"
        );
    }

    // DEEP poly consistency

    {
        // For the purposes of FRI below we consider query index as indexing into coset (highest bits) and domain (lowest bits).
        // Both indexes are bitreversed. When we will perform FRI folding we will need to perform an operation like (a - b)/eval_point(a).
        // Since our lowest bits are bitreversed, it means that lowest 3 bits correspond to element arising from 8th root of unity, and at
        // the end of the day we would to precompute 4 elements - 0..=3 powers of 8th root, and every time when our evaluation point is mapped
        // as x -> x^2, we only start to ignore

        assert_eq!(FRI_FACTOR_LOG2, 1);

        // below we will use consistency checks for oracles, where we compute just \sum alpha^i (f(z) - f(x))/(z - x) for few values of x.
        // So we can precompute \sum_i alpha^i f(z) that doesn't change

        let mut powers_of_deep_quotient_challenge =
            [MaybeUninit::uninit().assume_init(); NUM_OPENINGS_AT_Z + NUM_OPENINGS_AT_Z_OMEGA];
        let mut extra_factor_for_accumulation_at_z_omega = MaybeUninit::uninit().assume_init();

        let (precompute_with_evals_at_z, precompute_with_evals_at_z_omega) =
            if Mersenne31Quartic::PREFER_FMA {
                precompute_for_consistency_checks_with_fma(
                    &skeleton,
                    &deep_poly_alpha,
                    &mut extra_factor_for_accumulation_at_z_omega,
                )
            } else {
                precompute_for_consistency_checks(
                    &skeleton,
                    &deep_poly_alpha,
                    &mut powers_of_deep_quotient_challenge,
                )
            };

        let omega = Mersenne31Complex::TWO_ADICITY_GENERATORS[TRACE_LEN_LOG2];
        let tau = Mersenne31Complex::TWO_ADICITY_GENERATORS[TRACE_LEN_LOG2 + FRI_FACTOR_LOG2];
        let tau_inv =
            Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED[TRACE_LEN_LOG2 + FRI_FACTOR_LOG2];

        let mut taus = [MaybeUninit::uninit().assume_init(); 1 << FRI_FACTOR_LOG2];
        taus[0] = Mersenne31Complex::ONE;
        taus[1] = tau;

        let mut taus_inversed = [MaybeUninit::uninit().assume_init(); 1 << FRI_FACTOR_LOG2];
        taus_inversed[0] = Mersenne31Complex::ONE;
        taus_inversed[1] = tau_inv;

        let mut taus_in_domain_by_half =
            [MaybeUninit::uninit().assume_init(); 1 << FRI_FACTOR_LOG2];
        taus_in_domain_by_half[0] = Mersenne31Complex::ONE;
        taus_in_domain_by_half[1] = Mersenne31Complex::TWO_ADICITY_GENERATORS
            [TRACE_LEN_LOG2 + FRI_FACTOR_LOG2 - (TRACE_LEN_LOG2 - 1)];

        let mut taus_in_domain_by_half_inversed =
            [MaybeUninit::uninit().assume_init(); 1 << FRI_FACTOR_LOG2];
        taus_in_domain_by_half_inversed[0] = Mersenne31Complex::ONE;
        taus_in_domain_by_half_inversed[1] = Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED
            [TRACE_LEN_LOG2 + FRI_FACTOR_LOG2 - (TRACE_LEN_LOG2 - 1)];

        // here we will precompute max powers even needed
        let fri_folding_challenges_powers = if Mersenne31Quartic::PREFER_FMA
            && Mersenne31Quartic::USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF
            && Mersenne31Quartic::CAN_PROJECT_FROM_BASE
        {
            // it'll be unused
            MaybeUninit::uninit().assume_init()
        } else {
            fri_folding_challenges.map(|el| {
                let mut squared = el;
                squared.square();
                let mut quad = squared;
                quad.square();
                let mut eigths = quad;
                eigths.square();
                let mut sixteens = eigths;
                sixteens.square();

                [el, squared, quad, eigths, sixteens]
            })
        };

        // NOTE: here we skip 1 word because PoW is checked over it
        let mut bit_iterator = BitSource::new(&indexes_bits[1..]);
        let mut inversion_buffer = [Mersenne31Quartic::ZERO; 2];
        for query_round in 0..NUM_QUERIES {
            let query = &queries[query_round];
            let query_index: u32 =
                assemble_query_index(BITS_FOR_QUERY_INDEX, &mut bit_iterator) as u32;

            // assert that our query is at the proper index
            assert_eq!(query.query_index, query_index);

            let tree_index = query_index & TREE_INDEX_MASK;
            let domain_index = bitreverse_for_bitlength(tree_index, TRACE_LEN_LOG2 as u32);
            let coset_index = query_index >> TRACE_LEN_LOG2;

            core::hint::assert_unchecked(coset_index < 1 << FRI_FACTOR_LOG2);

            let mut evaluation_point = omega.pow(domain_index);
            evaluation_point.mul_assign(&taus[coset_index as usize]);

            let mut to_inverse = [z, z_omega];

            to_inverse[0].sub_assign_base(&evaluation_point);
            to_inverse[1].sub_assign_base(&evaluation_point);

            let all_nonzero = batch_inverse_checked(&mut to_inverse, &mut inversion_buffer);
            assert!(all_nonzero);

            let [divisor_for_z, divisor_for_z_omega] = to_inverse;

            // and can verify FRI. Note that FRI oracle initial leaf is true RS code word, without any adjustments by tau^H/2,
            // and so all next intermediate oracles

            let expected_value = if Mersenne31Quartic::PREFER_FMA {
                accumulate_over_row_for_consistency_check_with_fma(
                    precompute_with_evals_at_z,
                    precompute_with_evals_at_z_omega,
                    query,
                    &deep_poly_alpha,
                    &extra_factor_for_accumulation_at_z_omega,
                    &divisor_for_z,
                    &divisor_for_z_omega,
                    &taus_in_domain_by_half[coset_index as usize],
                    &taus_in_domain_by_half_inversed[coset_index as usize],
                )
            } else {
                accumulate_over_row_for_consistency_check(
                    precompute_with_evals_at_z,
                    precompute_with_evals_at_z_omega,
                    query,
                    &powers_of_deep_quotient_challenge,
                    &divisor_for_z,
                    &divisor_for_z_omega,
                    &taus_in_domain_by_half[coset_index as usize],
                    &taus_in_domain_by_half_inversed[coset_index as usize],
                )
            };

            let mut expected_value = expected_value;
            let mut evaluation_point = evaluation_point;

            let mut domain_size_log_2 = TRACE_LEN_LOG2;
            let mut domain_index = domain_index as usize;
            let mut tree_index = tree_index as usize;
            let mut offset_inv = taus_inversed[coset_index as usize];
            let mut leaf_src = query.fri_oracles_leafs.as_ptr();

            // NOTE: all our LDEs that "start" on the main domain are additionally multiplied by the compression factor
            // tau^-H/2, so we need to adjust our "true" value by such compression factor

            expected_value
                .mul_assign_by_base(&taus_in_domain_by_half_inversed[coset_index as usize]);

            for (step, folding_degree_log_2) in FRI_FOLDING_SCHEDULE.iter().enumerate() {
                let leaf_size = (1 << *folding_degree_log_2) * 4;
                let leaf_projection = if LAST_FRI_STEP_EXPOSE_LEAFS && (step == NUM_FRI_STEPS - 1) {
                    let leaf_size_in_ext4_elements = leaf_size / 4;
                    // we should peek into the skeleton for all leaf values
                    let all_leaf_values_in_coset = skeleton
                        .fri_final_step_leafs
                        .get_unchecked(coset_index as usize);
                    let leaf_index = tree_index / leaf_size_in_ext4_elements;
                    let src = all_leaf_values_in_coset
                        .as_ptr()
                        .add(leaf_index * leaf_size_in_ext4_elements);
                    let leaf_projection =
                        core::slice::from_raw_parts(src.cast::<Mersenne31Field>(), leaf_size);

                    leaf_projection
                } else {
                    let leaf_projection = core::slice::from_raw_parts(leaf_src, leaf_size);
                    leaf_src = leaf_src.add(leaf_size);

                    leaf_projection
                };

                if Mersenne31Quartic::PREFER_FMA
                    && Mersenne31Quartic::USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF
                    && Mersenne31Quartic::CAN_PROJECT_FROM_BASE
                {
                    // we use specialized procedure
                    let challenge = fri_folding_challenges.get_unchecked(step);

                    match *folding_degree_log_2 {
                        1 => {
                            fri_fold_by_log_n_with_fma::<1>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenge,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        2 => {
                            fri_fold_by_log_n_with_fma::<2>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenge,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        3 => {
                            fri_fold_by_log_n_with_fma::<3>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenge,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        4 => {
                            fri_fold_by_log_n_with_fma::<4>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenge,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        5 => {
                            fri_fold_by_log_n_with_fma::<5>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenge,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        _ => {
                            unreachable!("too high folding degree");
                        }
                    }
                } else {
                    let challenges = fri_folding_challenges_powers.get_unchecked(step);

                    // NOTE: routine below will check that our expected value is indeed in the leaf at the expected position

                    match *folding_degree_log_2 {
                        1 => {
                            fri_fold_by_log_n::<1>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenges,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        2 => {
                            fri_fold_by_log_n::<2>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenges,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        3 => {
                            fri_fold_by_log_n::<3>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenges,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        4 => {
                            fri_fold_by_log_n::<4>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenges,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        5 => {
                            fri_fold_by_log_n::<5>(
                                &mut expected_value,
                                &mut evaluation_point,
                                &mut domain_size_log_2,
                                &mut domain_index,
                                &mut tree_index,
                                &mut offset_inv,
                                leaf_projection,
                                challenges,
                                &SHARED_FACTORS_FOR_FOLDING,
                            );
                        }
                        _ => {
                            unreachable!("too high folding degree");
                        }
                    }
                }
            }

            fn evaluate_monomial_form(
                monomial_coeffs: &[Mersenne31Quartic; FRI_FINAL_DEGREE],
                evaluation_point: &Mersenne31Complex,
            ) -> Mersenne31Quartic {
                // now we have our evaluation point, and we can evaluate a result from the monomial form
                if Mersenne31Quartic::PREFER_FMA
                    && Mersenne31Quartic::USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF
                {
                    // here Horner rule is a little more involved
                    unsafe {
                        // we want to multiply previous by evaluation point, and add to the new one
                        let bound = monomial_coeffs.len();
                        let mut i = bound - 1;
                        let mut value_from_monomial_form = *monomial_coeffs.get_unchecked(i);
                        let evaluation_point = Mersenne31Quartic::from_base(*evaluation_point);
                        while i > 0 {
                            i -= 1;
                            let monomial_coeff = monomial_coeffs.get_unchecked(i);
                            Mersenne31Quartic::fused_mul_add_assign(
                                &mut value_from_monomial_form,
                                &evaluation_point,
                                &monomial_coeff,
                            );
                        }

                        value_from_monomial_form
                    }
                } else {
                    unsafe {
                        let mut i = monomial_coeffs.len() - 1;
                        let mut value_from_monomial_form = Mersenne31Quartic::ZERO;
                        while i > 0 {
                            value_from_monomial_form.add_assign(monomial_coeffs.get_unchecked(i));
                            value_from_monomial_form.mul_assign_by_base(evaluation_point);
                            i -= 1;
                        }
                        value_from_monomial_form.add_assign(&monomial_coeffs.get_unchecked(0));

                        value_from_monomial_form
                    }
                }
            }

            let value_from_monomial_form =
                evaluate_monomial_form(&skeleton.monomial_coeffs, &evaluation_point);

            // NOTE: above we applied compression factor for FRI-related values, but our evaluation from monomial form
            // is "true" value, so we need to adjust it back

            expected_value.mul_assign_by_base(&taus_in_domain_by_half[coset_index as usize]);

            assert_eq!(value_from_monomial_form, expected_value);
        }
    }

    // NOTE: we will NOT perform any logic about comparison here, and instead we will just write the result back to callee

    // setup caps
    proof_state_dst.setup_caps = skeleton.setup_caps;
    // memory caps
    proof_state_dst.memory_caps = skeleton.memory_caps;
    // - memory challenges
    proof_state_dst.memory_challenges = skeleton.memory_argument_challenges;
    // - delegation challenges
    if NUM_DELEGATION_CHALLENGES > 0 {
        proof_state_dst.delegation_challenges = skeleton.delegation_argument_challenges;
    }
    // - shuffle RAM lazy init first and last values
    if NUM_AUX_BOUNDARY_VALUES > 0 {
        proof_state_dst.lazy_init_boundary_values = skeleton.aux_boundary_values;
    }
    // - memory grand product and delegation accumulators
    proof_state_dst.memory_grand_product_accumulator = skeleton.memory_grand_product_accumulator;
    if NUM_DELEGATION_CHALLENGES > 0 {
        proof_state_dst.delegation_argument_accumulator = skeleton.delegation_argument_accumulator;
    }
    // sequence and delegation types
    proof_state_dst.circuit_sequence = skeleton.circuit_sequence_idx;
    proof_state_dst.delegation_type = skeleton.delegation_type;
    // - input and output state variables
    if NUM_STATE_ELEMENTS > 0 {
        let mut it = skeleton.public_inputs.array_chunks::<NUM_STATE_ELEMENTS>();
        proof_input_dst.input_state_variables = *it.next().unwrap_unchecked();
        proof_input_dst.output_state_variables = *it.next().unwrap_unchecked();
    }
}
