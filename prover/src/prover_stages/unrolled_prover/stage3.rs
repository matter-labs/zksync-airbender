use std::alloc::Global;

use super::prover_stages::stage1::FirstStageOutput;
use super::prover_stages::stage2::SecondStageOutput;
use super::*;
use crate::prover_stages::cached_data::ProverCachedData;
use crate::prover_stages::stage1::compute_wide_ldes;
use crate::prover_stages::stage3::AlphaPowersLayout;
use crate::prover_stages::unrolled_prover::quotient_parts::*;
use cs::one_row_compiler::ColumnAddress;
use field_utils::materialize_powers_serial_starting_with_one;

pub fn prover_stage_3_for_unrolled_circuit<
    const N: usize,
    A: GoodAllocator,
    T: MerkleTreeConstructor,
>(
    seed: &mut Seed,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cached_data: &ProverCachedData,
    compiled_constraints: &CompiledConstraintsForDomain,
    public_inputs: &[Mersenne31Field],
    stage_1_output: &FirstStageOutput<N, A, T>,
    stage_2_output: &SecondStageOutput<N, A, T>,
    setup_precomputations: &SetupPrecomputations<N, A, T>,
    first_row_boundary_constraints: Vec<(ColumnAddress, Mersenne31Field)>,
    one_before_last_row_boundary_constraints: Vec<(ColumnAddress, Mersenne31Field)>,
    aux_boundary_values: &[AuxArgumentsBoundaryValues],
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
    folding_description: &FoldingDescription,
    worker: &Worker,
) -> ThirdStageOutput<N, A, T> {
    assert!(lde_factor.is_power_of_two());

    assert_eq!(
        aux_boundary_values.len(),
        compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .len()
    );

    let mut transcript_challenges =
        [0u32; (2usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    let mut it = transcript_challenges.as_chunks::<4>().0.into_iter();
    let quotient_alpha = Mersenne31Quartic::from_coeffs_in_base(
        &it.next()
            .unwrap()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );
    let quotient_beta = Mersenne31Quartic::from_coeffs_in_base(
        &it.next()
            .unwrap()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    #[cfg(feature = "debug_logs")]
    {
        dbg!(quotient_alpha);
        dbg!(quotient_beta);
    }

    let ProverCachedData {
        trace_len,
        memory_timestamp_high_from_circuit_idx,
        memory_argument_challenges,
        machine_state_argument_challenges,
        delegation_challenges,
        process_shuffle_ram_init,
        handle_delegation_requests,
        delegation_request_layout,
        process_batch_ram_access,
        process_registers_and_indirect_access,
        delegation_processor_layout,
        process_delegations,
        delegation_processing_aux_poly,
        range_check_16_multiplicities_src,
        range_check_16_setup_column,

        timestamp_range_check_multiplicities_src,
        timestamp_range_check_setup_column,

        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,

        timestamp_range_check_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,

        num_stage_3_quotient_terms,
        ..
    } = cached_data.clone();

    assert!(public_inputs.is_empty());
    assert!(compiled_circuit.state_linkage_constraints.is_empty());

    let grand_product_accumulator = stage_2_output.grand_product_accumulator;

    assert!(lde_factor == 2);
    let (domain_index, tau, divisors_precomputation) = if DEBUG_QUOTIENT {
        let domain_index = 0;
        let precomputations = lde_precomputations.domain_bound_precomputations[domain_index]
            .as_ref()
            .unwrap();
        let tau = precomputations.coset_offset;
        let divisors_precomputation = compute_divisors_trace::<A>(
            trace_len,
            lde_precomputations.domain_bound_precomputations[1]
                .as_ref()
                .unwrap()
                .coset_offset,
            worker,
        );

        (domain_index, tau, divisors_precomputation)
    } else {
        let domain_index = 1;
        let precomputations = lde_precomputations.domain_bound_precomputations[domain_index]
            .as_ref()
            .unwrap();
        let tau = precomputations.coset_offset;
        let divisors_precomputation = compute_divisors_trace::<A>(trace_len, tau, worker);

        (domain_index, tau, divisors_precomputation)
    };

    assert_eq!(tau, compiled_constraints.tau);
    let omega = domain_generator_for_size::<Mersenne31Complex>(trace_len as u64);

    // we should count how many powers we need

    // compute number of different challenges
    let (mut b5, mut b4, mut b3, mut b2, mut b1) = (vec![], vec![], vec![], vec![], vec![]);
    let verifier_compiled =
        compiled_circuit.as_verifier_compiled_artifact(&mut b5, &mut b4, &mut b3, &mut b2, &mut b1);

    let num_quotient_terms_every_rows_except_last =
        verifier_compiled.num_quotient_terms_every_row_except_last();
    let num_quotient_terms_every_row_except_last_two =
        verifier_compiled.num_quotient_terms_every_row_except_last_two();
    let num_quotient_terms_first_row = verifier_compiled.num_quotient_terms_first_row();
    let num_quotient_terms_one_before_last_row =
        verifier_compiled.num_quotient_terms_one_before_last_row();
    let num_quotient_terms_last_row = verifier_compiled.num_quotient_terms_last_row();
    let num_quotient_terms_last_row_and_at_zero =
        verifier_compiled.num_quotient_terms_last_row_and_at_zero();
    let num_quotient_terms = verifier_compiled.num_quotient_terms();

    #[allow(dropping_copy_types)]
    drop(verifier_compiled);

    // double-check number of terms, can't hurt
    assert_eq!(
        num_quotient_terms_every_rows_except_last
            + num_quotient_terms_every_row_except_last_two
            + num_quotient_terms_first_row
            + num_quotient_terms_one_before_last_row
            + num_quotient_terms_last_row
            + num_quotient_terms_last_row_and_at_zero,
        num_quotient_terms
    );
    assert_eq!(num_quotient_terms, num_stage_3_quotient_terms);

    let AlphaPowersLayout {
        num_quotient_terms_every_row_except_last,
        num_quotient_terms_every_row_except_last_two,
        num_quotient_terms_first_row,
        num_quotient_terms_one_before_last_row,
        num_quotient_terms_last_row,
        num_quotient_terms_last_row_and_at_zero,
        precomputation_size,
    } = AlphaPowersLayout::new(&compiled_circuit, num_stage_3_quotient_terms);

    // For verifier it's beneficial to use Horner rule, but in prover we want to do (F4 * base_field) + F4 evaluations instead,
    // so we need to precompute and reverse
    let mut alphas = materialize_powers_serial_starting_with_one::<_, Global>(
        quotient_alpha,
        precomputation_size,
    );
    alphas.reverse();

    let alphas_for_every_row_except_last =
        &alphas[(precomputation_size - num_quotient_terms_every_row_except_last)..];
    let alphas_for_every_row_except_last_two =
        &alphas[(precomputation_size - num_quotient_terms_every_row_except_last_two)..];
    let alphas_for_first_row = &alphas[(precomputation_size - num_quotient_terms_first_row)..];
    let alphas_for_one_before_last_row =
        &alphas[(precomputation_size - num_quotient_terms_one_before_last_row)..];
    let alphas_for_last_row = &alphas[(precomputation_size - num_quotient_terms_last_row)..];
    let alphas_for_last_row_and_at_zero =
        &alphas[(precomputation_size - num_quotient_terms_last_row_and_at_zero)..];

    let tau_in_domain_by_half = tau.pow((trace_len / 2) as u32);
    let mut tau_in_domain = tau_in_domain_by_half;
    tau_in_domain.square();

    let tau_in_domain_by_half_inv = tau_in_domain_by_half.inverse().unwrap();

    // contribution coming from challenge * literal constant timestamp offset
    let mut delegation_requests_timestamp_low_extra_contribution = delegation_challenges
        .delegation_argument_linearization_challenges
        [DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW];
    delegation_requests_timestamp_low_extra_contribution.mul_assign_by_base(&Mersenne31Field(
        delegation_request_layout.in_cycle_write_index as u32,
    ));

    let mut delegation_requests_timestamp_high_extra_contribution = delegation_challenges
        .delegation_argument_linearization_challenges
        [DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH];
    delegation_requests_timestamp_high_extra_contribution
        .mul_assign_by_base(&memory_timestamp_high_from_circuit_idx);

    let mut delegation_requests_timestamp_extra_contribution =
        delegation_requests_timestamp_low_extra_contribution;
    delegation_requests_timestamp_extra_contribution
        .add_assign(&delegation_requests_timestamp_high_extra_contribution);

    let mut extra_write_timestamp_high = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    extra_write_timestamp_high.mul_assign_by_base(&memory_timestamp_high_from_circuit_idx);

    // we need to show the sum of the values everywhere except the last row,
    // so we show that intermediate poly - interpolant((0, 0), (omega^-1, `value``)) is divisible
    // by our selected divisor, where "value" == negate(our sum over all other domain), and we also require that sum over
    // all the domain is 0

    // interpolant is literaly 1/omega^-1 * value * X (as one can see it's 0 at 0 and `value` at omega^-1)
    let mut delegation_accumulator_interpolant_prefactor = stage_2_output.sum_over_delegation_poly;
    delegation_accumulator_interpolant_prefactor.mul_assign_by_base(&omega);
    delegation_accumulator_interpolant_prefactor.negate();

    // NOTE: all traces that are expected to be FFT inputs must be wide
    let result =
        RowMajorTrace::<Mersenne31Field, N, A>::new_zeroed_for_size(trace_len, 4, A::default());
    let (quadratic_terms_challenges, rest) =
        alphas_for_every_row_except_last.split_at(compiled_circuit.degree_2_constraints.len());
    let (linear_terms_challenges, other_challenges) =
        rest.split_at(compiled_circuit.degree_1_constraints.len());

    assert_eq!(
        quadratic_terms_challenges.len(),
        compiled_constraints.quadratic_terms.len()
    );
    assert_eq!(
        linear_terms_challenges.len(),
        compiled_constraints.linear_terms.len()
    );

    let lookup_argument_linearization_challenges =
        stage_2_output.lookup_argument_linearization_challenges;
    let lookup_argument_linearization_challenges_without_table_id: [Mersenne31Quartic;
        NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES - 1] =
        lookup_argument_linearization_challenges
            [..(NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES - 1)]
            .try_into()
            .unwrap();
    let lookup_argument_gamma = stage_2_output.lookup_argument_gamma;

    let mut lookup_argument_two_gamma = lookup_argument_gamma;
    lookup_argument_two_gamma.double();

    let first_row_boundary_constraints_ref = &first_row_boundary_constraints;
    let one_before_last_row_boundary_constraints_ref = &one_before_last_row_boundary_constraints;

    let range_check_16_width_1_lookups_access_ref = &range_check_16_width_1_lookups_access;
    let range_check_16_width_1_lookups_access_via_expressions_ref =
        &range_check_16_width_1_lookups_access_via_expressions;

    let timestamp_range_check_width_1_lookups_access_via_expressions_ref =
        &timestamp_range_check_width_1_lookups_access_via_expressions;
    let timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref =
        &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram;

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    assert!(
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.is_empty()
    );

    let offset_for_grand_product_poly = compiled_circuit
        .stage_2_layout
        .intermediate_poly_for_grand_product
        .start();

    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut exec_trace_view = stage_1_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut stage_2_trace_view = stage_2_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut setup_trace_view = setup_precomputations.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut divisors_trace_view = divisors_precomputation.row_view(range.clone());

                let mut quotient_view = result.row_view(range.clone());

                Worker::smart_spawn(
                    scope,
                    thread_idx == geometry.len() - 1,
                    move |_| {
                    let tau_in_domain_by_half = tau_in_domain_by_half;
                    let tau_in_domain = tau_in_domain;
                    let omega = omega;
                    let tau = tau;

                    let mut x = omega.pow(chunk_start as u32);
                    x.mul_assign(&tau);

                    for _i in 0..chunk_size {
                        let absolute_row_idx = chunk_start + _i;
                        let is_last_row = absolute_row_idx == trace_len - 1;
                        let is_one_before_last_row = absolute_row_idx == trace_len - 2;
                        let is_last_two_rows = is_last_row || is_one_before_last_row;
                        let is_first_row = absolute_row_idx == 0;

                        let (exec_trace_view_row, exec_trace_view_next_row) =
                            exec_trace_view.current_and_next_row_ref();
                        let (witness_trace_view_row, memory_trace_view_row)
                            = exec_trace_view_row.split_at_unchecked(stage_1_output.num_witness_columns);
                        let (_witness_trace_view_next_row, memory_trace_view_next_row)
                            = exec_trace_view_next_row.split_at_unchecked(stage_1_output.num_witness_columns);

                        let (stage_2_trace_view_row, stage_2_trace_view_next_row) =
                            stage_2_trace_view.current_and_next_row_ref();
                        let setup_trace_view_row = setup_trace_view.current_row_ref();
                        let divisors_trace_view_row = divisors_trace_view.current_row_ref();

                        let quotient_view_row = quotient_view.current_row();
                        let quotient_dst =
                            quotient_view_row.as_mut_ptr().cast::<Mersenne31Quartic>();
                        debug_assert!(quotient_dst.is_aligned());

                        let mut quotient_term = evaluate_generic_constraints(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            quadratic_terms_challenges,
                            linear_terms_challenges,
                            absolute_row_idx,
                            is_last_row
                        );

                        // NOTE: since we actually do not provide a code to the poly, but to
                        // (p(x) − c0) / tau^H/2, even though we do not benefit from it for polys that are in 4th extension,
                        // we should multiply the terms below by either tau^H/2 or tau^H where needed

                        let mut other_challenges_ptr = other_challenges.as_ptr();

                        // if we handle delegation, but have multiplicity == 0, then we must enforce
                        // that incoming values are trivial, timestamps are zeroes, etc
                        if process_delegations {
                            evaluate_delegation_processing_conventions(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &delegation_processor_layout
                            );
                        }

                        // now lookup width 1

                        // range 16, that consists of 2 cases
                        evaluate_range_check_16_over_variables(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut other_challenges_ptr,
                            &lookup_argument_gamma,
                            &lookup_argument_two_gamma,
                            &range_check_16_width_1_lookups_access_ref[..]
                        );

                        // then range check 16 using lookup expressions
                        evaluate_range_check_16_over_expressions(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut other_challenges_ptr,
                            &lookup_argument_gamma,
                            &lookup_argument_two_gamma,
                            &range_check_16_width_1_lookups_access_via_expressions_ref[..]
                        );

                        // special case for range check over lazy init address columns
                        if process_shuffle_ram_init {
                            evaluate_memory_init_teardown_range_checks(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &lookup_argument_gamma,
                                &lookup_argument_two_gamma,
                            );
                        }

                        // now remainders
                        // Acc(x) * (witness(x) + gamma) - 1
                        if let Some(_remainder_for_range_check_16) =
                            compiled_circuit.stage_2_layout.remainder_for_range_check_16
                        {
                            todo!();
                        }

                        // then timestamp related range checks. We do them together, but in some cases we add extra contribution from
                        // circuit index

                        evaluate_timestamp_range_check_expressions(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut other_challenges_ptr,
                            &lookup_argument_gamma,
                            &lookup_argument_two_gamma,
                            &timestamp_range_check_width_1_lookups_access_via_expressions_ref[..],
                            &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref[..],
                            &memory_timestamp_high_from_circuit_idx,
                        );

                        if compiled_circuit
                            .memory_layout
                            .intermediate_state_layout.is_some() {

                            evaluate_decoder_table_access(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &stage_2_output.decoder_table_linearization_challenges,
                                &stage_2_output.decoder_table_gamma,
                            );
                        }

                        // width-3 generic lookup
                        evaluate_width_3_lookups(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut other_challenges_ptr,
                            &lookup_argument_linearization_challenges,
                            &lookup_argument_linearization_challenges_without_table_id,
                            &lookup_argument_gamma,
                        );

                        // now multiplicities
                        if compiled_circuit.stage_2_layout
                            .intermediate_poly_for_range_check_16_multiplicity.num_elements() > 0 {
                                evaluate_width_1_range_check_multiplicity(
                                    compiled_circuit,
                                    witness_trace_view_row,
                                    memory_trace_view_row,
                                    setup_trace_view_row,
                                    stage_2_trace_view_row,
                                    &tau_in_domain,
                                    &tau_in_domain_by_half,
                                    absolute_row_idx,
                                    is_last_row,
                                    &mut quotient_term,
                                    &mut other_challenges_ptr,
                                    &lookup_argument_gamma,
                                    compiled_circuit.stage_2_layout
                                        .intermediate_poly_for_range_check_16_multiplicity
                                        .start(),
                                        range_check_16_multiplicities_src,
                                        range_check_16_setup_column,
                                );
                        }

                        if compiled_circuit.stage_2_layout
                            .intermediate_poly_for_timestamp_range_check_multiplicity.num_elements() > 0 {
                            evaluate_width_1_range_check_multiplicity(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &lookup_argument_gamma,
                                compiled_circuit.stage_2_layout
                                    .intermediate_poly_for_timestamp_range_check_multiplicity
                                    .start(),
                                timestamp_range_check_multiplicities_src,
                                timestamp_range_check_setup_column,
                            );
                        }

                        if compiled_circuit.witness_layout
                            .multiplicities_columns_for_decoder_in_executor_families.num_elements() > 0 {
                                evaluate_decoder_lookup_multiplicity(
                                    compiled_circuit,
                                    witness_trace_view_row,
                                    memory_trace_view_row,
                                    setup_trace_view_row,
                                    stage_2_trace_view_row,
                                    &tau_in_domain,
                                    &tau_in_domain_by_half,
                                    absolute_row_idx,
                                    is_last_row,
                                    &mut quotient_term,
                                    &mut other_challenges_ptr,
                                    &stage_2_output.decoder_table_linearization_challenges,
                                    &stage_2_output.decoder_table_gamma,
                                );
                        }

                        // generic lookup
                        evaluate_width_3_lookups_multiplicity(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut other_challenges_ptr,
                            &lookup_argument_linearization_challenges,
                            &lookup_argument_gamma,
                        );

                        // write timestamps come from cycle itself, and are used for multiple things below
                        let (write_timestamp_low, write_timestamp_high) = if let Some(intermediate_state_layout) = compiled_circuit.memory_layout.intermediate_state_layout.as_ref() {
                            let write_timestamp_low = *memory_trace_view_row
                                .get_unchecked(intermediate_state_layout.timestamp.start());
                            let write_timestamp_high = *memory_trace_view_row
                                .get_unchecked(
                                    intermediate_state_layout.timestamp.start() + 1,
                                );

                            (write_timestamp_low, write_timestamp_high)
                        } else {
                            (Mersenne31Field::ZERO, Mersenne31Field::ZERO)
                        };

                        // either process set equality for delegation requests or processings
                        if handle_delegation_requests {
                            evaluate_delegation_requests(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &delegation_request_layout,
                                &delegation_challenges,
                                write_timestamp_low,
                                write_timestamp_high,
                                &delegation_requests_timestamp_extra_contribution,
                            );
                        }

                        if process_delegations {
                            panic!("Please use another prover function for such circuit types");
                        }

                        if process_shuffle_ram_init {
                            evaluate_memory_init_teardown_padding(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                            );
                        }

                        // and now we work with memory multiplicative accumulators
                        // Numerator is write set, denom is read set

                        // NOTE: it'll be multiplied by tau^H/2 eventually, so we must give an inverse instead of one
                        let initial = Mersenne31Quartic::from_base(tau_in_domain_by_half_inv);
                        let mut permutation_argument_src = &initial as *const Mersenne31Quartic;

                        // first lazy init from read set / lazy teardown

                        // and memory grand product accumulation identities

                        // sequence of keys is in general is_reg || address_low || address_high || timestamp low || timestamp_high || value_low || value_high

                        // Note on multiplication by tau^H/2: numerator and denominator are degree 1

                        if process_shuffle_ram_init {
                            evaluate_memory_init_teardown_accumulation(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &memory_argument_challenges,
                                &mut permutation_argument_src,
                            )
                        }

                        // we assembled P(x) = write init set / read teardown set

                        // now we can continue to accumulate either for shuffle RAM, or for batched RAM accesses

                        evaluate_memory_queries_accumulation(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut other_challenges_ptr,
                            &memory_argument_challenges,
                            &tau_in_domain_by_half_inv,
                            &mut permutation_argument_src,
                            &Mersenne31Quartic::ZERO,
                            write_timestamp_low,
                            write_timestamp_high,
                        );

                        // Same for batched RAM accesses
                        if process_batch_ram_access {
                            unreachable!("deprecated");
                        }

                        // Same for registers and indirects
                        if process_registers_and_indirect_access {
                            panic!("Please use another prover function for such circuit types");
                        }

                        if compiled_circuit.stage_2_layout.intermediate_polys_for_state_permutation.num_elements() > 0 {
                            evaluate_machine_state_permutation_assuming_no_decoder(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &machine_state_argument_challenges,
                                &mut permutation_argument_src,
                            );
                        }

                        // maybe we should mask
                        if compiled_circuit.stage_2_layout.intermediate_polys_for_permutation_masking.num_elements() > 0 {
                            evaluate_permutation_masking(
                                compiled_circuit,
                                witness_trace_view_row,
                                memory_trace_view_row,
                                setup_trace_view_row,
                                stage_2_trace_view_row,
                                &tau_in_domain,
                                &tau_in_domain_by_half,
                                absolute_row_idx,
                                is_last_row,
                                &mut quotient_term,
                                &mut other_challenges_ptr,
                                &mut permutation_argument_src,
                            );
                        }

                        // and now we need to make Z(next_row) = Z(this_row) * previous(this_row)
                        {
                            let mut previous = permutation_argument_src.read();
                            previous.mul_assign_by_base(&tau_in_domain_by_half);

                            let accumulator_this_row = stage_2_trace_view_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>()
                                .read();
                            let accumulator_next_row = stage_2_trace_view_next_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>()
                                .read();

                            let mut term_contribution = accumulator_next_row;
                            let mut t = accumulator_this_row;
                            t.mul_assign(&previous);
                            term_contribution.sub_assign(&t);
                            // we are linear over accumulators
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at memory accumulation grand product at row {}",
                                        absolute_row_idx,
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        let divisor = divisors_trace_view_row
                            .as_ptr()
                            .add(DIVISOR_EVERYWHERE_EXCEPT_LAST_ROW_OFFSET)
                            .cast::<Mersenne31Complex>()
                            .read();
                        let mut every_row_except_last_contribution =
                            quotient_term;
                        every_row_except_last_contribution.mul_assign_by_base(&divisor);

                        assert_eq!(
                            other_challenges_ptr,
                            other_challenges.as_ptr_range().end,
                            "challenges for other terms at every row except last have a size of {}, but {} were used",
                            other_challenges.len(),
                            other_challenges_ptr.offset_from_unsigned(other_challenges.as_ptr()),
                        );

                        // now all constraints have less places to be encountered

                        // Constraints that happen everywhere except last two rows
                        let mut quotient_term = Mersenne31Quartic::ZERO;
                        let mut every_row_except_last_two_challenges_ptr = alphas_for_every_row_except_last_two.as_ptr();

                        // then linking constraints - None

                        // two constraints to compare sorting of lazy init
                        evaluate_memory_init_teardown_ordering(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            memory_trace_view_next_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_two_rows,
                            &mut quotient_term,
                            &mut every_row_except_last_two_challenges_ptr,
                        );

                        let divisor = divisors_trace_view_row
                            .as_ptr()
                            .add(DIVISOR_EVERYWHERE_EXCEPT_LAST_TWO_ROWS_OFFSET)
                            .cast::<Mersenne31Complex>()
                            .read();
                        let mut every_row_except_last_two_contribution =
                            quotient_term;
                        every_row_except_last_two_contribution.mul_assign_by_base(&divisor);

                        assert_eq!(every_row_except_last_two_challenges_ptr, alphas_for_every_row_except_last_two.as_ptr_range().end);

                        // Constraints that happen at first row
                        let mut quotient_term = Mersenne31Quartic::ZERO;
                        let mut first_row_challenges_ptr = alphas_for_first_row.as_ptr();

                        // first row

                        // Note on multiplication by tau^H/2 - only terms containing polynomials should be scaled

                        for (_i, (place, expected_value)) in first_row_boundary_constraints_ref.iter().enumerate() {
                            let value = read_value(*place, witness_trace_view_row, memory_trace_view_row);
                            let mut term_contribution = tau_in_domain_by_half;
                            term_contribution.mul_assign_by_base(&value);
                            term_contribution.sub_assign_base(expected_value);
                            if DEBUG_QUOTIENT {
                                if is_first_row {
                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied at boundary constraint {}: {:?} = {:?} at first row", _i, place, expected_value);
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut first_row_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // 1 constraint for memory accumulator initial value == 1
                        {
                            let memory_accumulators_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(memory_accumulators_ptr.is_aligned());
                            let accumulator = memory_accumulators_ptr.read();

                            let mut term_contribution = accumulator;
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                            if DEBUG_QUOTIENT {
                                if is_first_row {
                                    assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at grand product accumulator first value == 1");
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut first_row_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        let divisor = divisors_trace_view_row
                            .as_ptr()
                            .add(DIVISOR_FIRST_ROW_OFFSET)
                            .cast::<Mersenne31Complex>()
                            .read();
                        let mut first_row_contribution = quotient_term;
                        first_row_contribution.mul_assign_by_base(&divisor);

                        assert_eq!(first_row_challenges_ptr, alphas_for_first_row.as_ptr_range().end);

                        // Constraints that happen at one before last row
                        let mut quotient_term = Mersenne31Quartic::ZERO;
                        let mut one_before_last_row_challenges_ptr = alphas_for_one_before_last_row.as_ptr();

                        for (_i, (place, expected_value)) in one_before_last_row_boundary_constraints_ref.iter().enumerate() {
                            let value = read_value(*place, witness_trace_view_row, memory_trace_view_row);

                            let mut term_contribution = tau_in_domain_by_half;
                            term_contribution.mul_assign_by_base(&value);
                            term_contribution.sub_assign_base(expected_value);
                            if DEBUG_QUOTIENT {
                                if is_one_before_last_row {
                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied at boundary constraint {}: {:?} = {:?} at one row before last", _i, place, expected_value);
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut one_before_last_row_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        let divisor = divisors_trace_view_row
                            .as_ptr()
                            .add(DIVISOR_ONE_BEFORE_LAST_ROW_OFFSET)
                            .cast::<Mersenne31Complex>()
                            .read();
                        let mut one_before_last_row_contribution = quotient_term;
                        one_before_last_row_contribution.mul_assign_by_base(&divisor);

                        assert_eq!(one_before_last_row_challenges_ptr, alphas_for_one_before_last_row.as_ptr_range().end);

                        // last row - only grand product accumulator
                        let mut quotient_term = Mersenne31Quartic::ZERO;
                        let mut last_row_challenges_ptr = alphas_for_last_row.as_ptr();

                        {
                            let memory_accumulators_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(memory_accumulators_ptr.is_aligned());
                            let accumulator = memory_accumulators_ptr.read();

                            let mut term_contribution = accumulator;
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            term_contribution.sub_assign(&grand_product_accumulator);
                            if DEBUG_QUOTIENT {
                                if is_last_row {
                                    assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at grand product accumulator last value");
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut last_row_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        let divisor = divisors_trace_view_row
                            .as_ptr()
                            .add(DIVISOR_LAST_ROW_OFFSET)
                            .cast::<Mersenne31Complex>()
                            .read();
                        let mut last_row_contribution = quotient_term;
                        last_row_contribution.mul_assign_by_base(&divisor);

                        assert_eq!(last_row_challenges_ptr, alphas_for_last_row.as_ptr_range().end);

                        // and last two rows - sums equality for lookup arguments

                        let mut quotient_term = Mersenne31Quartic::ZERO;
                        let mut last_row_and_at_zero_challenges_ptr = alphas_for_last_row_and_at_zero.as_ptr();

                        // generic approach is \sum multiplicities aux - \sum witness_aux

                        evaluate_lookup_arguments_consistency(
                            compiled_circuit,
                            witness_trace_view_row,
                            memory_trace_view_row,
                            setup_trace_view_row,
                            stage_2_trace_view_row,
                            &tau_in_domain,
                            &tau_in_domain_by_half,
                            absolute_row_idx,
                            is_last_row,
                            &mut quotient_term,
                            &mut last_row_and_at_zero_challenges_ptr,
                        );

                        if handle_delegation_requests || process_delegations {
                            // we need to show the sum of the values everywhere except the last row,
                            // so we show that intermediate poly - interpolant((0, 0), (omega^-1, `value``)) is divisible
                            // by our selected divisor

                            // interpolant is literally 1/omega^-1 * value * X (as one can see it's 0 at 0 and `value` at omega^-1)
                            let mut interpolant_value = delegation_accumulator_interpolant_prefactor;
                            interpolant_value.mul_assign_by_base(&x);
                            let mut term_contribution = stage_2_trace_view_row.as_ptr().add(delegation_processing_aux_poly.start()).cast::<Mersenne31Quartic>().read();
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            term_contribution.sub_assign(&interpolant_value);

                            if DEBUG_QUOTIENT {
                                if is_last_row {
                                    assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at delegation argument set equality at last row");
                                }
                            }

                            add_quotient_term_contribution_in_ext4(
                                &mut last_row_and_at_zero_challenges_ptr,
                                term_contribution,
                                &mut quotient_term
                            );
                        }

                        let divisor = divisors_trace_view_row
                            .as_ptr()
                            .add(DIVISOR_LAST_ROW_AND_ZERO_OFFSET)
                            .cast::<Mersenne31Complex>()
                            .read();
                        let mut last_row_and_zero_contribution = quotient_term;
                        last_row_and_zero_contribution.mul_assign_by_base(&divisor);

                        assert_eq!(
                            last_row_and_at_zero_challenges_ptr,
                            alphas_for_last_row_and_at_zero.as_ptr_range().end,
                            "challenges for terms at last row and 0 have a size of {}, but {} were used",
                            alphas_for_last_row_and_at_zero.len(),
                            last_row_and_at_zero_challenges_ptr.offset_from_unsigned(alphas_for_last_row_and_at_zero.as_ptr()),
                        );

                        // Horner rule for separation of divisors
                        let mut quotient_term = every_row_except_last_contribution;
                        quotient_term.mul_assign(&quotient_beta);
                        quotient_term.add_assign(&every_row_except_last_two_contribution);
                        quotient_term.mul_assign(&quotient_beta);
                        quotient_term.add_assign(&first_row_contribution);
                        quotient_term.mul_assign(&quotient_beta);
                        quotient_term.add_assign(&one_before_last_row_contribution);
                        quotient_term.mul_assign(&quotient_beta);
                        quotient_term.add_assign(&last_row_contribution);
                        quotient_term.mul_assign(&quotient_beta);
                        quotient_term.add_assign(&last_row_and_zero_contribution);

                        quotient_dst.write(quotient_term);

                        // and go to the next row
                        exec_trace_view.advance_row();
                        stage_2_trace_view.advance_row();
                        setup_trace_view.advance_row();
                        divisors_trace_view.advance_row();

                        quotient_view.advance_row();

                        x.mul_assign(&omega);
                    }
                });
            }
        });
    }

    #[cfg(feature = "timing_logs")]
    println!("Quotient evaluation time = {:?}", now.elapsed());

    // We interpolate from non-main domain, and extraloate to all other domains

    // now we can LDE and make oracles
    let ldes = compute_wide_ldes(
        result,
        &twiddles,
        &lde_precomputations,
        domain_index,
        lde_factor,
        worker,
    );
    assert_eq!(ldes.len(), lde_factor);

    let subtree_cap_size = (1 << folding_description.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut trees = Vec::with_capacity(lde_factor);
    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    for domain in ldes.iter() {
        let witness_tree = T::construct_for_coset(&domain.trace, subtree_cap_size, true, worker);
        trees.push(witness_tree);
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    let output = ThirdStageOutput {
        quotient_alpha,
        quotient_beta,
        ldes,
        trees,
    };

    output
}
