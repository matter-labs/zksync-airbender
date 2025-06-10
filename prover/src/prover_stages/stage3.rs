use std::alloc::Global;

use super::prover_stages::stage1::FirstStageOutput;
use super::prover_stages::stage2::SecondStageOutput;
use super::*;
use crate::prover_stages::cached_data::ProverCachedData;
use crate::prover_stages::stage1::compute_wide_ldes;
use cs::one_row_compiler::BoundaryConstraintLocation;
use cs::one_row_compiler::ColumnAddress;
use cs::one_row_compiler::ShuffleRamAuxComparisonSet;
use cs::one_row_compiler::ShuffleRamQueryColumns;
use cs::one_row_compiler::TableIndex;
use field_utils::materialize_powers_serial_starting_with_one;

pub struct ThirdStageOutput<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> {
    pub quotient_alpha: Mersenne31Quartic,
    pub quotient_beta: Mersenne31Quartic,
    pub ldes: Vec<CosetBoundTracePart<N, A>>,
    pub trees: Vec<T>,
}

#[derive(Clone)]
pub struct AlphaPowersLayout {
    pub num_quotient_terms_every_row_except_last: usize,
    pub num_quotient_terms_every_row_except_last_two: usize,
    pub num_quotient_terms_first_row: usize,
    pub num_quotient_terms_one_before_last_row: usize,
    pub num_quotient_terms_last_row: usize,
    pub num_quotient_terms_last_row_and_at_zero: usize,
    pub precomputation_size: usize,
}
// TODO: Maybe this belongs in ProverCachedData
impl AlphaPowersLayout {
    pub fn new(
        compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        num_stage_3_quotient_terms: usize,
    ) -> Self {
        // compute number of different challenges
        let (mut b5, mut b4, mut b3, mut b2, mut b1) = (vec![], vec![], vec![], vec![], vec![]);
        let verifier_compiled = compiled_circuit
            .as_verifier_compiled_artifact(&mut b5, &mut b4, &mut b3, &mut b2, &mut b1);

        let num_quotient_terms_every_row_except_last =
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
            num_quotient_terms_every_row_except_last
                + num_quotient_terms_every_row_except_last_two
                + num_quotient_terms_first_row
                + num_quotient_terms_one_before_last_row
                + num_quotient_terms_last_row
                + num_quotient_terms_last_row_and_at_zero,
            num_quotient_terms
        );
        assert_eq!(num_quotient_terms, num_stage_3_quotient_terms);

        let precomputation_size = [
            num_quotient_terms_every_row_except_last,
            num_quotient_terms_every_row_except_last_two,
            num_quotient_terms_first_row,
            num_quotient_terms_one_before_last_row,
            num_quotient_terms_last_row,
            num_quotient_terms_last_row_and_at_zero,
        ]
        .iter()
        .max()
        .copied()
        .unwrap();

        #[cfg(feature = "debug_logs")]
        {
            dbg!(num_quotient_terms);
            dbg!(precomputation_size);
        }

        Self {
            num_quotient_terms_every_row_except_last,
            num_quotient_terms_every_row_except_last_two,
            num_quotient_terms_first_row,
            num_quotient_terms_one_before_last_row,
            num_quotient_terms_last_row,
            num_quotient_terms_last_row_and_at_zero,
            precomputation_size,
        }
    }
}

pub fn prover_stage_3<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor>(
    seed: &mut Seed,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cached_data: &ProverCachedData,
    compiled_constraints: &CompiledConstraintsForDomain,
    public_inputs: &[Mersenne31Field],
    stage_1_output: &FirstStageOutput<N, A, T>,
    stage_2_output: &SecondStageOutput<N, A, T>,
    setup_precomputations: &SetupPrecomputations<N, A, T>,
    external_values: &ExternalValues,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
    folding_description: &FoldingDescription,
    worker: &Worker,
) -> ThirdStageOutput<N, A, T> {
    assert!(lde_factor.is_power_of_two());

    let mut transcript_challenges =
        [0u32; (2usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    let mut it = transcript_challenges.array_chunks::<4>();
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
        delegation_type,
        memory_argument_challenges,
        //execute_delegation_argument,
        delegation_challenges,
        process_shuffle_ram_init,
        shuffle_ram_inits_and_teardowns,
        lazy_init_address_range_check_16,
        handle_delegation_requests,
        delegation_request_layout,
        process_batch_ram_access,
        process_registers_and_indirect_access,
        delegation_processor_layout,
        process_delegations,
        delegation_processing_aux_poly,
        offset_for_grand_product_accumulation_poly,

        range_check_16_multiplicities_src,
        range_check_16_setup_column,

        timestamp_range_check_multiplicities_src,
        timestamp_range_check_setup_column,

        generic_lookup_multiplicities_src_start,

        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,

        timestamp_range_check_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,

        generic_lookup_setup_columns_start,
        memory_accumulator_dst_start,
        num_stage_3_quotient_terms,
        ..
    } = cached_data.clone();

    let mut first_row_boundary_constraints = vec![];
    let mut one_before_last_row_boundary_constraints = vec![];

    // first lazy init, then public inputs

    if process_shuffle_ram_init {
        // first row
        {
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_init_addresses_columns
                        .start(),
                ),
                external_values.aux_boundary_values.lazy_init_first_row[0],
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_init_addresses_columns
                        .start()
                        + 1,
                ),
                external_values.aux_boundary_values.lazy_init_first_row[1],
            ));

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_values_columns
                        .start(),
                ),
                external_values.aux_boundary_values.teardown_value_first_row[0],
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_values_columns
                        .start()
                        + 1,
                ),
                external_values.aux_boundary_values.teardown_value_first_row[1],
            ));

            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_timestamps_columns
                        .start(),
                ),
                external_values
                    .aux_boundary_values
                    .teardown_timestamp_first_row[0],
            ));
            first_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_timestamps_columns
                        .start()
                        + 1,
                ),
                external_values
                    .aux_boundary_values
                    .teardown_timestamp_first_row[1],
            ));
        }

        // one before last row
        {
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_init_addresses_columns
                        .start(),
                ),
                external_values
                    .aux_boundary_values
                    .lazy_init_one_before_last_row[0],
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_init_addresses_columns
                        .start()
                        + 1,
                ),
                external_values
                    .aux_boundary_values
                    .lazy_init_one_before_last_row[1],
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_values_columns
                        .start(),
                ),
                external_values
                    .aux_boundary_values
                    .teardown_value_one_before_last_row[0],
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_values_columns
                        .start()
                        + 1,
                ),
                external_values
                    .aux_boundary_values
                    .teardown_value_one_before_last_row[1],
            ));

            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_timestamps_columns
                        .start(),
                ),
                external_values
                    .aux_boundary_values
                    .teardown_timestamp_one_before_last_row[0],
            ));
            one_before_last_row_boundary_constraints.push((
                ColumnAddress::MemorySubtree(
                    shuffle_ram_inits_and_teardowns
                        .lazy_teardown_timestamps_columns
                        .start()
                        + 1,
                ),
                external_values
                    .aux_boundary_values
                    .teardown_timestamp_one_before_last_row[1],
            ));
        }
    }

    for ((location, column_address), value) in compiled_circuit
        .public_inputs
        .iter()
        .zip(public_inputs.iter())
    {
        match location {
            BoundaryConstraintLocation::FirstRow => {
                first_row_boundary_constraints.push((*column_address, *value));
            }
            BoundaryConstraintLocation::OneBeforeLastRow => {
                one_before_last_row_boundary_constraints.push((*column_address, *value));
            }
            BoundaryConstraintLocation::LastRow => {
                panic!("public inputs on the last row are not supported");
            }
        }
    }

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

    let num_boolean_constraints = compiled_circuit
        .witness_layout
        .boolean_vars_columns_range
        .num_elements();

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

    // interpolant is literally 1/omega^-1 * value * X (as one can see it's 0 at 0 and `value` at omega^-1)
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

    #[cfg(feature = "debug_logs")]
    {
        dbg!(quadratic_terms_challenges.len());
        dbg!(linear_terms_challenges.len());
        dbg!(other_challenges.len());
    }

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

    const SHIFT_16: Mersenne31Field = Mersenne31Field(1u32 << 16);

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
                        let (witness_trace_view_next_row, memory_trace_view_next_row)
                            = exec_trace_view_next_row.split_at_unchecked(stage_1_output.num_witness_columns);

                        let (stage_2_trace_view_row, stage_2_trace_view_next_row) =
                            stage_2_trace_view.current_and_next_row_ref();
                        let setup_trace_view_row = setup_trace_view.current_row_ref();
                        let divisors_trace_view_row = divisors_trace_view.current_row_ref();

                        let quotient_view_row = quotient_view.current_row();
                        let quotient_dst =
                            quotient_view_row.as_mut_ptr().cast::<Mersenne31Quartic>();
                        debug_assert!(quotient_dst.is_aligned());

                        let mut quotient_quadratic_accumulator = Mersenne31Quartic::ZERO;
                        let mut quotient_linear_accumulator = Mersenne31Quartic::ZERO;
                        let mut quotient_constant_accumulator = Mersenne31Quartic::ZERO;

                        //  Quadratic terms
                        let bound = compiled_circuit.degree_2_constraints.len();

                        // special case for boolean constraints
                        let start = compiled_circuit.witness_layout.boolean_vars_columns_range.start();
                        for i in 0..num_boolean_constraints {
                            // a^2 - a
                            let challenge = *quadratic_terms_challenges.get_unchecked(i);
                            let value = *witness_trace_view_row.get_unchecked(start + i);
                            let mut t = value;
                            t.square();

                            let mut quadratic = challenge;
                            quadratic.mul_assign_by_base(&t);
                            quotient_quadratic_accumulator.add_assign(&quadratic);

                            let mut linear = challenge;
                            linear.mul_assign_by_base(&value);
                            quotient_linear_accumulator.sub_assign(&linear);

                            if DEBUG_QUOTIENT {
                                assert!(compiled_circuit.degree_2_constraints.get_unchecked(i).is_boolean_constraint());

                                let mut term_contribution = value;
                                term_contribution.square();
                                term_contribution.sub_assign(&value);

                                if is_last_row == false {
                                    assert!(value == Mersenne31Field::ZERO || value == Mersenne31Field::ONE);
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Field::ZERO,
                                        "unsatisfied at row {} boolean constraint {}: {:?}",
                                        absolute_row_idx,
                                        i,
                                        compiled_circuit.degree_2_constraints.get_unchecked(i),
                                    );
                                }
                            }
                        }
                        for i in num_boolean_constraints..bound {
                            let challenge = *quadratic_terms_challenges.get_unchecked(i);
                            let term = compiled_circuit.degree_2_constraints.get_unchecked(i);
                            term
                                .evaluate_at_row_with_accumulation(
                                    &*witness_trace_view_row,
                                    &*memory_trace_view_row,
                                    &challenge,
                                    &mut quotient_quadratic_accumulator,
                                    &mut quotient_linear_accumulator,
                                    &mut quotient_constant_accumulator,
                                );

                            if DEBUG_QUOTIENT {
                                let term_contribution = term.evaluate_at_row_on_main_domain(witness_trace_view_row, memory_trace_view_row);
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Field::ZERO,
                                        "unsatisfied at row {} at degree-2 constraint {}: {:?}",
                                        absolute_row_idx,
                                        i,
                                        compiled_circuit.degree_2_constraints.get_unchecked(i),
                                    );
                                }
                            }
                        }

                        quotient_quadratic_accumulator.mul_assign_by_base(&tau_in_domain);

                        // Linear terms
                        let bound = compiled_circuit.degree_1_constraints.len();
                        for i in 0..bound {
                            let challenge = *linear_terms_challenges.get_unchecked(i);
                            let term = compiled_circuit.degree_1_constraints.get_unchecked(i);
                            term
                                .evaluate_at_row_with_accumulation(
                                    &*witness_trace_view_row,
                                    &*memory_trace_view_row,
                                    &challenge,
                                    &mut quotient_linear_accumulator,
                                    &mut quotient_constant_accumulator,
                                );

                            if DEBUG_QUOTIENT {
                                let term_contribution = term.evaluate_at_row_on_main_domain_ext(witness_trace_view_row, memory_trace_view_row, setup_trace_view_row);

                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Field::ZERO,
                                        "unsatisfied at row {} degree-1 constraint {}: {:?}",
                                        absolute_row_idx,
                                        i,
                                        compiled_circuit.degree_1_constraints.get_unchecked(i),
                                    );
                                }
                            }
                        }
                        quotient_linear_accumulator.mul_assign_by_base(&tau_in_domain_by_half);

                        let mut quotient_term = quotient_constant_accumulator;
                        quotient_term.add_assign(&quotient_quadratic_accumulator);
                        quotient_term.add_assign(&quotient_linear_accumulator);

                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(quotient_term, Mersenne31Quartic::ZERO, "unsatisfied over user constraints at row {}", absolute_row_idx);
                            }
                        }

                        // NOTE: since we actually do not provide a code to the poly, but to
                        // (p(x) − c0) / tau^H/2, even though we do not benefit from it for polys that are in 4th extension,
                        // we should multiply the terms below by either tau^H/2 or tau^H where needed

                        let mut other_challenges_ptr = other_challenges.as_ptr();
                        // if we handle delegation, but have multiplicity == 0, then we must enforce
                        // that incoming values are trivial, timestamps are zeroes, etc
                        if process_delegations {
                            let predicate = *memory_trace_view_row.get_unchecked(delegation_processor_layout.multiplicity.start());
                            let mut t = tau_in_domain_by_half;
                            t.mul_assign_by_base(&predicate);
                            let mut t_minus_one = t;
                            t_minus_one.sub_assign_base(&Mersenne31Field::ONE);

                            // predicate is 0/1
                            let mut term_contribution = t;
                            term_contribution.mul_assign(&t_minus_one);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: predicate is 0/1 at row {}", absolute_row_idx);
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            // now the rest of the values have to be 0s
                            // we want a constraint of (predicate - 1) * value == 0

                            let mut t_minus_one_adjusted = t_minus_one;
                            t_minus_one_adjusted.mul_assign(&tau_in_domain_by_half);

                            // - mem abi offset == 0
                            let mut term_contribution = t_minus_one_adjusted;
                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(delegation_processor_layout.abi_mem_offset_high.start()));
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: mem offset high is 0 if predicate is 0 at row {}", absolute_row_idx);
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            // - write timestamp == 0
                            let mut term_contribution = t_minus_one_adjusted;
                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(delegation_processor_layout.write_timestamp.start()));
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: write timestamp low is 0 if predicate is 0 at row {}", absolute_row_idx);
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            let mut term_contribution = t_minus_one_adjusted;
                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(delegation_processor_layout.write_timestamp.start() + 1));
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: write timestamp high is 0 if predicate is 0 at row {}", absolute_row_idx);
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            // for every value we check that read timestamp == 0
                            // for every read value we check that value == 0
                            // for every written value value we check that value == 0

                            let bound = compiled_circuit.memory_layout.batched_ram_accesses.len();
                            for access_idx in 0..bound {
                                let access = *compiled_circuit.memory_layout.batched_ram_accesses.get_unchecked(access_idx);
                                match access {
                                    BatchedRamAccessColumns::ReadAccess { read_timestamp, read_value } => {
                                        for set in [read_timestamp, read_value].into_iter() {
                                            // low and high
                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {}", absolute_row_idx);
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {}", absolute_row_idx);
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                        }
                                    },
                                    BatchedRamAccessColumns::WriteAccess { read_timestamp, read_value, write_value } => {
                                        for set in [read_timestamp, read_value, write_value].into_iter() {
                                            // low and high
                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {}", absolute_row_idx);
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {}", absolute_row_idx);
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                        }
                                    }
                                }
                            }

                            // for every register and indirect access
                            let bound = compiled_circuit.memory_layout.register_and_indirect_accesses.len();
                            for access_idx in 0..bound {
                                let access = compiled_circuit.memory_layout.register_and_indirect_accesses.get_unchecked(access_idx);
                                match access.register_access {
                                    RegisterAccessColumns::ReadAccess { read_timestamp, read_value, .. } => {
                                        for set in [read_timestamp, read_value].into_iter() {
                                            // low and high
                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                        }
                                    },
                                    RegisterAccessColumns::WriteAccess { read_timestamp, read_value, write_value, .. } => {
                                        for set in [read_timestamp, read_value, write_value].into_iter() {
                                            // low and high
                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                                            let mut term_contribution = t_minus_one_adjusted;
                                            term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                        }
                                    }
                                }

                                let subbound = access.indirect_accesses.len();
                                for indirect_access_idx in 0..subbound {
                                    let indirect_access = access.indirect_accesses.get_unchecked(indirect_access_idx);
                                    match indirect_access {
                                        IndirectAccessColumns::ReadAccess { read_timestamp, read_value, address_derivation_carry_bit, .. } => {
                                            for set in [read_timestamp, read_value].into_iter() {
                                                // low and high
                                                let mut term_contribution = t_minus_one_adjusted;
                                                term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                                                if DEBUG_QUOTIENT {
                                                    if is_last_row == false {
                                                        assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                                                    }
                                                }
                                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                                                let mut term_contribution = t_minus_one_adjusted;
                                                term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                                                if DEBUG_QUOTIENT {
                                                    if is_last_row == false {
                                                        assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                                                    }
                                                }
                                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                            }

                                            // We only derive with non-trivial addition if it's not-first access, or unaligned access
                                            if indirect_access_idx > 0 && address_derivation_carry_bit.num_elements() > 0{
                                                let carry_bit = *memory_trace_view_row.get_unchecked(address_derivation_carry_bit.start());
                                                let mut term_contribution = tau_in_domain_by_half;
                                                term_contribution.mul_assign_by_base(&carry_bit);
                                                term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                                                term_contribution.mul_assign_by_base(&carry_bit);
                                                term_contribution.mul_assign(&tau_in_domain_by_half);
                                                if DEBUG_QUOTIENT {
                                                    if is_last_row == false {
                                                        assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: carry bit is not boolean at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                                                    }
                                                }
                                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                            } else {
                                                debug_assert_eq!(address_derivation_carry_bit.num_elements(), 0);
                                            }
                                        },
                                        IndirectAccessColumns::WriteAccess { read_timestamp, read_value, write_value, address_derivation_carry_bit, .. } => {
                                            for set in [read_timestamp, read_value, write_value].into_iter() {
                                                // low and high
                                                let mut term_contribution = t_minus_one_adjusted;
                                                term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                                                if DEBUG_QUOTIENT {
                                                    if is_last_row == false {
                                                        assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                                                    }
                                                }
                                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                                                let mut term_contribution = t_minus_one_adjusted;
                                                term_contribution.mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                                                if DEBUG_QUOTIENT {
                                                    if is_last_row == false {
                                                        assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                                                    }
                                                }
                                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                            }

                                            // We only derive with non-trivial addition if it's not-first access, or unaligned access
                                            if indirect_access_idx > 0 && address_derivation_carry_bit.num_elements() > 0 {
                                                let carry_bit = *memory_trace_view_row.get_unchecked(address_derivation_carry_bit.start());
                                                let mut term_contribution = tau_in_domain_by_half;
                                                term_contribution.mul_assign_by_base(&carry_bit);
                                                term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                                                term_contribution.mul_assign_by_base(&carry_bit);
                                                term_contribution.mul_assign(&tau_in_domain_by_half);
                                                if DEBUG_QUOTIENT {
                                                    if is_last_row == false {
                                                        assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: carry bit is not boolean at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                                                    }
                                                }
                                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                            } else {
                                                debug_assert_eq!(address_derivation_carry_bit.num_elements(), 0);
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // now lookup width 1

                        // range 16, that consists of 2 cases

                        // trivial case where range check is just over 1 variable
                        for (i, lookup_set) in range_check_16_width_1_lookups_access_ref.iter().enumerate() {
                            let c_offset = lookup_set.base_field_quadratic_oracle_col;
                            let c = *stage_2_trace_view_row.get_unchecked(c_offset);
                            let a = lookup_set.a_col;
                            let b = lookup_set.b_col;
                            let a_place = ColumnAddress::WitnessSubtree(a);
                            let b_place = ColumnAddress::WitnessSubtree(b);
                            let a =
                                read_value(a_place, witness_trace_view_row, memory_trace_view_row);
                            let b =
                                read_value(b_place, witness_trace_view_row, memory_trace_view_row);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert!(
                                        a.to_reduced_u32() < 1u32<<16,
                                        "unsatisfied at range check 16: value is {}",
                                        a,
                                    );

                                    assert!(
                                        b.to_reduced_u32() < 1u32<<16,
                                        "unsatisfied at range check 16: value is {}",
                                        b,
                                    );
                                }
                            }

                            let mut a_mul_by_b = a;
                            a_mul_by_b.mul_assign(&b);

                            let mut term_contribution = tau_in_domain_by_half;
                            term_contribution.mul_assign_by_base(&a_mul_by_b);
                            term_contribution.sub_assign_base(&c);
                            term_contribution.mul_assign(&tau_in_domain_by_half);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Complex::ZERO,
                                        "unsatisfied at range check lookup base field oracle {}",
                                        i
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            // now accumulator * denom - numerator == 0
                            let acc = lookup_set.ext4_field_inverses_columns_start;
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());

                            let mut acc_value = acc_ptr.read();
                            acc_value.mul_assign_by_base(&tau_in_domain_by_half);

                            let mut t = a;
                            t.add_assign(&b);
                            let mut a_plus_b_contribution = tau_in_domain_by_half;
                            a_plus_b_contribution.mul_assign_by_base(&t);

                            let mut c_contribution = tau_in_domain_by_half;
                            c_contribution.mul_assign_by_base(&c);

                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&a_plus_b_contribution);
                            denom.mul_assign(&lookup_argument_gamma);
                            denom.add_assign_base(&c_contribution);
                            // C(x) + gamma * (a(x) + b(x)) + gamma^2

                            // a(x) + b(x) + 2 * gamma
                            let mut numerator = lookup_argument_two_gamma;
                            numerator.add_assign_base(&a_plus_b_contribution);

                            // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign(&numerator);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at range check lookup ext field oracle {}",
                                        i
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // then range check 16 using lookup expressions
                        for (i, lookup_set) in range_check_16_width_1_lookups_access_via_expressions_ref.iter().enumerate() {
                            let c_offset = lookup_set.base_field_quadratic_oracle_col;
                            let c = *stage_2_trace_view_row.get_unchecked(c_offset);
                            let LookupExpression::Expression(a) = &lookup_set.a_expr else {
                                unreachable!()
                            };
                            let LookupExpression::Expression(b) = &lookup_set.b_expr else {
                                unreachable!()
                            };
                            let a = a.evaluate_at_row_ext(witness_trace_view_row, memory_trace_view_row, setup_trace_view_row, &tau_in_domain_by_half);
                            let b = b.evaluate_at_row_ext(witness_trace_view_row, memory_trace_view_row, setup_trace_view_row, &tau_in_domain_by_half);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert!(
                                        a.c0.to_reduced_u32() < 1u32<<16,
                                        "unsatisfied at range check 16: value is {}",
                                        a,
                                    );

                                    assert!(
                                        b.c0.to_reduced_u32() < 1u32<<16,
                                        "unsatisfied at range check 16: value is {}",
                                        b,
                                    );
                                }
                            }

                            let mut a_mul_by_b = a;
                            a_mul_by_b.mul_assign(&b);

                            let mut c_ext = tau_in_domain_by_half;
                            c_ext.mul_assign_by_base(&c);

                            let mut term_contribution = a_mul_by_b;
                            term_contribution.sub_assign_base(&c_ext);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Complex::ZERO,
                                        "unsatisfied at range check lookup base field oracle {}",
                                        i
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            // now accumulator * denom - numerator == 0
                            let acc = lookup_set.ext4_field_inverses_columns_start;
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());

                            let mut acc_value = acc_ptr.read();
                            acc_value.mul_assign_by_base(&tau_in_domain_by_half);

                            let mut a_plus_b_contribution = a;
                            a_plus_b_contribution.add_assign(&b);

                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&a_plus_b_contribution);
                            denom.mul_assign(&lookup_argument_gamma);
                            denom.add_assign_base(&c_ext);
                            // C(x) + gamma * (a(x) + b(x)) + gamma^2

                            // a(x) + b(x) + 2 * gamma
                            let mut numerator = lookup_argument_two_gamma;
                            numerator.add_assign_base(&a_plus_b_contribution);

                            // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign(&numerator);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at range check lookup ext field oracle {}",
                                        i
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // special case for range check over lazy init address columns
                        if process_shuffle_ram_init {
                            let c = lazy_init_address_range_check_16
                                .base_field_oracles
                                .get_range(0)
                                .start;
                            let c = *stage_2_trace_view_row.get_unchecked(c);
                            let a = shuffle_ram_inits_and_teardowns
                                .lazy_init_addresses_columns
                                .start();
                            let b = a + 1;
                            let a_place = ColumnAddress::MemorySubtree(a);
                            let b_place = ColumnAddress::MemorySubtree(b);
                            let a =
                                read_value(a_place, witness_trace_view_row, memory_trace_view_row);
                            let b =
                                read_value(b_place, witness_trace_view_row, memory_trace_view_row);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert!(
                                        a.to_reduced_u32() < 1u32<<16,
                                        "unsatisfied at range check 16 for lazy init addresses: value is {}",
                                        a,
                                    );

                                    assert!(
                                        b.to_reduced_u32() < 1u32<<16,
                                        "unsatisfied at range check 16 for lazy init addresses: value is {}",
                                        b,
                                    );
                                }
                            }

                            let mut a_mul_by_b = a;
                            a_mul_by_b.mul_assign(&b);

                            let mut term_contribution = tau_in_domain_by_half;
                            term_contribution.mul_assign_by_base(&a_mul_by_b);
                            term_contribution.sub_assign_base(&c);
                            term_contribution.mul_assign(&tau_in_domain_by_half);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Complex::ZERO,
                                        "unsatisfied at range check 16 lookup base field oracle for lazy init addresses",
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            let acc = lazy_init_address_range_check_16
                                .ext_4_field_oracles
                                .get_range(0)
                                .start;
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());

                            let mut acc_value = acc_ptr.read();
                            acc_value.mul_assign_by_base(&tau_in_domain_by_half);

                            let mut t = a;
                            t.add_assign(&b);
                            let mut a_plus_b_contribution = tau_in_domain_by_half;
                            a_plus_b_contribution.mul_assign_by_base(&t);

                            let mut c_contribution = tau_in_domain_by_half;
                            c_contribution.mul_assign_by_base(&c);

                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&a_plus_b_contribution);
                            denom.mul_assign(&lookup_argument_gamma);
                            denom.add_assign_base(&c_contribution);
                            // C(x) + gamma * (a(x) + b(x)) + gamma^2

                            // a(x) + b(x) + 2 * gamma
                            let mut numerator = lookup_argument_two_gamma;
                            numerator.add_assign_base(&a_plus_b_contribution);

                            // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign(&numerator);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at range check 16 lookup ext field oracle for lazy init addresses",
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
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
                        let bound = timestamp_range_check_width_1_lookups_access_via_expressions_ref.len() + timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref.len();
                        let offset = timestamp_range_check_width_1_lookups_access_via_expressions_ref.len();
                        // second part is where we have expressions as part of the range check, but do not need extra contribution from the timestamp
                        // and the last part, where we also account for the circuit sequence in the write timestamp
                        for i in 0..bound {
                            let lookup_set = if i < offset {
                                timestamp_range_check_width_1_lookups_access_via_expressions_ref.get_unchecked(i)
                            } else {
                                timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref.get_unchecked(i - offset)
                            };
                            let c_offset = lookup_set.base_field_quadratic_oracle_col;
                            let c = *stage_2_trace_view_row.get_unchecked(c_offset);
                            let LookupExpression::Expression(a) = &lookup_set.a_expr else {
                                unreachable!()
                            };
                            let LookupExpression::Expression(b) = &lookup_set.b_expr else {
                                unreachable!()
                            };
                            let a = a.evaluate_at_row_ext(witness_trace_view_row, memory_trace_view_row, setup_trace_view_row, &tau_in_domain_by_half);
                            let mut b = b.evaluate_at_row_ext(witness_trace_view_row, memory_trace_view_row, setup_trace_view_row, &tau_in_domain_by_half);
                            if i >= offset {
                                // width_1_lookups_access_via_expressions_for_shuffle_ram_ref need to account for extra contribution for timestamp high
                                b.sub_assign_base(&memory_timestamp_high_from_circuit_idx); // literal constant
                            }

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert!(
                                        a.c0.to_reduced_u32() < 1u32<<TIMESTAMP_COLUMNS_NUM_BITS,
                                        "unsatisfied at timestamp range check: value is {}",
                                        a,
                                    );

                                    assert!(
                                        b.c0.to_reduced_u32() < 1u32<<TIMESTAMP_COLUMNS_NUM_BITS,
                                        "unsatisfied at timestamp range check: value is {}",
                                        b,
                                    );
                                }
                            }

                            let mut a_mul_by_b = a;
                            a_mul_by_b.mul_assign(&b);

                            let mut c_ext = tau_in_domain_by_half;
                            c_ext.mul_assign_by_base(&c);

                            let mut term_contribution = a_mul_by_b;
                            term_contribution.sub_assign_base(&c_ext);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Complex::ZERO,
                                        "unsatisfied at range check lookup base field oracle {}",
                                        i
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution, &mut quotient_term);

                            // now accumulator * denom - numerator == 0
                            let acc = lookup_set.ext4_field_inverses_columns_start;
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());

                            let mut acc_value = acc_ptr.read();
                            acc_value.mul_assign_by_base(&tau_in_domain_by_half);

                            let mut a_plus_b_contribution = a;
                            a_plus_b_contribution.add_assign(&b);

                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&a_plus_b_contribution);
                            denom.mul_assign(&lookup_argument_gamma);
                            denom.add_assign_base(&c_ext);
                            // C(x) + gamma * (a(x) + b(x)) + gamma^2

                            // a(x) + b(x) + 2 * gamma
                            let mut numerator = lookup_argument_two_gamma;
                            numerator.add_assign_base(&a_plus_b_contribution);

                            // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign(&numerator);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at range check lookup ext field oracle {}",
                                        i
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // width-3 generic lookup
                        for (i, lookup_set) in compiled_circuit.witness_layout.width_3_lookups.iter().enumerate() {
                            let mut table_id_contribution = lookup_argument_linearization_challenges[NUM_LOOKUP_ARGUMENT_KEY_PARTS - 2];
                            match lookup_set.table_index {
                                TableIndex::Constant(table_type) => {
                                    let table_id = Mersenne31Field(table_type.to_table_id());
                                    table_id_contribution.mul_assign_by_base(&table_id);
                                },
                                TableIndex::Variable(place) => {
                                    let mut t = tau_in_domain_by_half;
                                    let table_id = read_value(place, &*witness_trace_view_row, &*memory_trace_view_row);
                                    t.mul_assign_by_base(&table_id);
                                    table_id_contribution.mul_assign_by_base(&t);
                                }
                            }

                            let acc = compiled_circuit.stage_2_layout
                                    .intermediate_polys_for_generic_lookup
                                    .get_range(i)
                                    .start;
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            assert!(acc_ptr.is_aligned());
                            let mut acc_value = acc_ptr.read();
                            acc_value.mul_assign_by_base(&tau_in_domain_by_half);

                            let input_values = std::array::from_fn(|i| {
                                match &lookup_set.input_columns[i] {
                                    LookupExpression::Variable(place) => {
                                        let mut t = tau_in_domain_by_half;
                                        t.mul_assign_by_base(&read_value(*place, &*witness_trace_view_row, &*memory_trace_view_row));

                                        t
                                    },
                                    LookupExpression::Expression(constraint) => {
                                        // as we allow constant to be non-zero, we have to evaluate as on non-main domain in general
                                        // instead of once amortizing multiplication by tau in domain by half
                                        constraint.evaluate_at_row(&*witness_trace_view_row, &*memory_trace_view_row, &tau_in_domain_by_half)
                                    }
                                }
                            });

                            let [input0, input1, input2] = input_values;
                            let mut denom = quotient_compute_aggregated_key_value_in_ext2(
                                input0,
                                [
                                    input1,
                                    input2,
                                ],
                                lookup_argument_linearization_challenges_without_table_id,
                                lookup_argument_gamma,
                            );

                            denom.add_assign(&table_id_contribution);

                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign_base(&Mersenne31Field::ONE);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    let input = input_values.map(|el| {
                                        assert!(el.c1.is_zero());
                                        el.c0
                                    });

                                    let table_id = match lookup_set.table_index {
                                        TableIndex::Constant(table_type) => {
                                            table_type.to_table_id()
                                        },
                                        TableIndex::Variable(place) => {
                                            let table_id = read_value(place, &*witness_trace_view_row, &*memory_trace_view_row);
                                            assert!(table_id.to_reduced_u32() as usize <= TABLE_TYPES_UPPER_BOUNDS, "table ID is the integer between 0 and {}, but got {}", TABLE_TYPES_UPPER_BOUNDS, table_id);

                                            table_id.to_reduced_u32()
                                        }
                                    };

                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at width 3 lookup set {} with table type {:?} at row {} with tuple {:?} and ID = {}",
                                        i,
                                        lookup_set.table_index,
                                        absolute_row_idx,
                                        input,
                                        table_id,
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // now multiplicities
                        if compiled_circuit.stage_2_layout
                            .intermediate_poly_for_range_check_16_multiplicity.num_elements() > 0 {
                            let acc = compiled_circuit.stage_2_layout
                                .intermediate_poly_for_range_check_16_multiplicity
                                .start;

                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());
                            let acc_value = acc_ptr.read();

                            let m = *witness_trace_view_row
                                .get_unchecked(range_check_16_multiplicities_src);

                            let mut t = tau_in_domain_by_half;
                            t.mul_assign_by_base(setup_trace_view_row.get_unchecked(range_check_16_setup_column));

                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&t);

                            // extra power to scale accumulator and multiplicity
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign_base(&m);
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    if term_contribution.is_zero() == false {
                                        dbg!(m);
                                        dbg!(t);
                                        dbg!(denom);
                                        dbg!(acc_value);
                                    }
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at range check 16 multiplicities column at row {}",
                                        absolute_row_idx,
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        if compiled_circuit.stage_2_layout
                            .intermediate_poly_for_timestamp_range_check_multiplicity.num_elements() > 0 {
                            let acc = compiled_circuit.stage_2_layout
                                .intermediate_poly_for_timestamp_range_check_multiplicity
                                .start;

                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());
                            let acc_value = acc_ptr.read();

                            let m = *witness_trace_view_row
                                .get_unchecked(timestamp_range_check_multiplicities_src);

                            let mut t = tau_in_domain_by_half;
                            t.mul_assign_by_base(setup_trace_view_row.get_unchecked(timestamp_range_check_setup_column));

                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&t);

                            // extra power to scale accumulator and multiplicity
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign_base(&m);
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at timestamp range check multiplicities column at row {}",
                                        absolute_row_idx,
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // generic lookup
                        for i in 0..compiled_circuit.witness_layout.multiplicities_columns_for_generic_lookup.num_elements() {
                            let acc = compiled_circuit.stage_2_layout
                                .intermediate_polys_for_generic_multiplicities
                                .get_range(i)
                                .start;
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());
                            let acc_value = acc_ptr.read();

                            let m = *witness_trace_view_row
                                .get_unchecked(generic_lookup_multiplicities_src_start + i);

                            let start = generic_lookup_setup_columns_start + i * (COMMON_TABLE_WIDTH + 1);
                            let [src0, src1, src2, src3] = setup_trace_view_row.as_ptr().add(start).cast::<[Mersenne31Field; COMMON_TABLE_WIDTH + 1]>().read();

                            let denom = quotient_compute_aggregated_key_value(
                                src0,
                                [
                                    src1,
                                    src2,
                                    src3,
                                ],
                                lookup_argument_linearization_challenges,
                                lookup_argument_gamma,
                                tau_in_domain_by_half
                            );

                            // extra power to scale accumulator and multiplicity
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign_base(&m);
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at generic lookup multiplicities column",
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(
                                &mut other_challenges_ptr,
                                term_contribution,
                                &mut quotient_term
                            );
                        }

                        // either process set equality for delegation requests or processings
                        if handle_delegation_requests {
                            // memory write timestamp's low part comes from the setup and constant offset
                            let acc = delegation_processing_aux_poly
                                .start();
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());
                            let acc_value = acc_ptr.read();

                            let m = *memory_trace_view_row
                                .get_unchecked(delegation_request_layout.multiplicity.start());

                            // we will add contribution from literal offset afterwards
                            let mut denom = quotient_compute_aggregated_key_value(
                                *memory_trace_view_row.get_unchecked(delegation_request_layout.delegation_type.start()),
                                [
                                    *memory_trace_view_row.get_unchecked(delegation_request_layout.abi_mem_offset_high.start()),
                                    *setup_trace_view_row.get_unchecked(compiled_circuit.setup_layout.timestamp_setup_columns.start()),
                                    *setup_trace_view_row.get_unchecked(compiled_circuit.setup_layout.timestamp_setup_columns.start() + 1),
                                ],
                                delegation_challenges.delegation_argument_linearization_challenges,
                                delegation_challenges.delegation_argument_gamma,
                                tau_in_domain_by_half
                            );
                            denom.add_assign(&delegation_requests_timestamp_extra_contribution);

                            // extra power to scale accumulator and multiplicity
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign_base(&m);
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert!(m == Mersenne31Field::ZERO || m == Mersenne31Field::ONE, "multiplicity must be 0 or 1, but got {}", m);
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at delegation argument aux column",
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(
                                &mut other_challenges_ptr,
                                term_contribution,
                                &mut quotient_term
                            );
                        }

                        if process_delegations {
                            // memory write timestamp's low part comes from the delegation request itself,
                            // but delegation type is literal constant
                            let acc = delegation_processing_aux_poly
                                .start();
                            let acc_ptr = stage_2_trace_view_row
                                .as_ptr()
                                .add(acc)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(acc_ptr.is_aligned());
                            let acc_value = acc_ptr.read();

                            let m = *memory_trace_view_row
                                .get_unchecked(delegation_processor_layout.multiplicity.start());

                            let mut denom = delegation_challenges.delegation_argument_linearization_challenges[DELEGATION_ARGUMENT_CHALLENGED_IDX_ABI_MEM_OFFSET_HIGH];
                            denom.mul_assign_by_base(
                                memory_trace_view_row.get_unchecked(delegation_processor_layout.abi_mem_offset_high.start())
                            );

                            let mut t = delegation_challenges.delegation_argument_linearization_challenges[DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW];
                            t.mul_assign_by_base(
                                memory_trace_view_row.get_unchecked(delegation_processor_layout.write_timestamp.start())
                            );
                            denom.add_assign(&t);

                            let mut t = delegation_challenges.delegation_argument_linearization_challenges[DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH];
                            t.mul_assign_by_base(
                                memory_trace_view_row.get_unchecked(delegation_processor_layout.write_timestamp.start() + 1)
                            );
                            denom.add_assign(&t);

                            denom.mul_assign_by_base(&tau_in_domain_by_half);
                            denom.add_assign_base(&delegation_type);
                            denom.add_assign(&delegation_challenges.delegation_argument_gamma);

                            // extra power to scale accumulator and multiplicity
                            let mut term_contribution = denom;
                            term_contribution.mul_assign(&acc_value);
                            term_contribution.sub_assign_base(&m);
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert!(m == Mersenne31Field::ZERO || m == Mersenne31Field::ONE, "multiplicity must be 0 or 1, but got {}", m);
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at delegation argument aux column",
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(
                                &mut other_challenges_ptr,
                                term_contribution,
                                &mut quotient_term
                            );
                        }

                        // NOTE: very special trick here - this constraint makes sense on every row except last two, but it's quadratic,
                        // and unless we actually make it on every row except last only(!) we can not get a quotient of degree 1. The good thing
                        // is that a constraint about final borrow in the lazy init sorting is on every row except last two, so we can just place
                        // an artificial borrow value for our needs
                        if let Some(lazy_init_address_aux_vars) = compiled_circuit.lazy_init_address_aux_vars {
                            debug_assert!(process_shuffle_ram_init);
                            let ShuffleRamAuxComparisonSet { final_borrow, .. } = lazy_init_address_aux_vars;

                            // then if we do NOT have borrow-high, then we require that init address, teardown final value and timestamps are all zeroes

                            let final_borrow_value = read_value(final_borrow, witness_trace_view_row, memory_trace_view_row);

                            let lazy_init_address_start = shuffle_ram_inits_and_teardowns.lazy_init_addresses_columns.start();
                            let lazy_init_address_low = lazy_init_address_start;
                            let lazy_init_address_high = lazy_init_address_start + 1;

                            let lazy_init_address_low = memory_trace_view_row[lazy_init_address_low];
                            let lazy_init_address_high = memory_trace_view_row[lazy_init_address_high];

                            let teardown_value_start = shuffle_ram_inits_and_teardowns.lazy_teardown_values_columns.start();
                            let teardown_value_low = teardown_value_start;
                            let teardown_value_high = teardown_value_start + 1;

                            let teardown_value_low = memory_trace_view_row[teardown_value_low];
                            let teardown_value_high = memory_trace_view_row[teardown_value_high];

                            let teardown_timestamp_start = shuffle_ram_inits_and_teardowns.lazy_teardown_timestamps_columns.start();
                            let teardown_timestamp_low = teardown_timestamp_start;
                            let teardown_timestamp_high = teardown_timestamp_start + 1;

                            let teardown_timestamp_low = memory_trace_view_row[teardown_timestamp_low];
                            let teardown_timestamp_high = memory_trace_view_row[teardown_timestamp_high];

                            // if borrow is 1 (strict comparison), then values can be any,
                            // otherwise address, value and timestamp are 0
                            let mut final_borrow_minus_one = tau_in_domain_by_half;
                            final_borrow_minus_one.mul_assign_by_base(&final_borrow_value);
                            final_borrow_minus_one.sub_assign_base(&Mersenne31Field::ONE);

                            // pre-multiply by another tau^H/2
                            let mut final_borrow_minus_one_term = final_borrow_minus_one;
                            final_borrow_minus_one_term.mul_assign(&tau_in_domain_by_half);

                            for value in [lazy_init_address_low, lazy_init_address_high, teardown_value_low, teardown_value_high, teardown_timestamp_low, teardown_timestamp_high].into_iter() {
                                let mut term_contribution_ext2 = final_borrow_minus_one_term;
                                term_contribution_ext2.mul_assign_by_base(&value);

                                if DEBUG_QUOTIENT {
                                    if is_last_row == false {
                                        assert_eq!(term_contribution_ext2, Mersenne31Complex::ZERO, "unsatisfied at lazy init padding constraint at row {}", absolute_row_idx);
                                        if final_borrow_value.is_zero() {
                                            assert_eq!(value, Mersenne31Field::ZERO, "unsatisfied at lazy init padding constraint at row {}", absolute_row_idx);
                                        } else {
                                            assert_eq!(final_borrow_value, Mersenne31Field::ONE);
                                        }
                                    }
                                }

                                add_quotient_term_contribution_in_ext2(&mut other_challenges_ptr, term_contribution_ext2, &mut quotient_term);
                            }
                        }

                        // and now we work with memory multiplicative accumulators
                        // Numerator is write set, denom is read set

                        // first lazy init from read set / lazy teardown

                        let mut memory_argument_src = stage_2_trace_view_row
                            .as_ptr()
                            .add(memory_accumulator_dst_start)
                            .cast::<Mersenne31Quartic>();
                        debug_assert!(memory_argument_src.is_aligned());

                        // and memory grand product accumulation identities

                        // sequence of keys is in general is_reg || address_low || address_high || timestamp low || timestamp_high || value_low || value_high

                        // Note on multiplication by tau^H/2: numerator and denominator are degree 1

                        if process_shuffle_ram_init {
                            let mut numerator = Mersenne31Quartic::ZERO;

                            let address_low =
                                *memory_trace_view_row.get_unchecked(shuffle_ram_inits_and_teardowns.lazy_init_addresses_columns.start());
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                            t.mul_assign_by_base(&address_low);
                            numerator.add_assign(&t);

                            let address_high =
                                *memory_trace_view_row.get_unchecked(shuffle_ram_inits_and_teardowns.lazy_init_addresses_columns.start() + 1);
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                            t.mul_assign_by_base(&address_high);
                            numerator.add_assign(&t);

                            // lazy init and teardown sets have same addresses
                            let mut denom = numerator;

                            let value_low =
                                *memory_trace_view_row.get_unchecked(shuffle_ram_inits_and_teardowns.lazy_teardown_values_columns.start());
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            t.mul_assign_by_base(&value_low);
                            denom.add_assign(&t);

                            let value_high =
                                *memory_trace_view_row.get_unchecked(shuffle_ram_inits_and_teardowns.lazy_teardown_values_columns.start() + 1);
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign_by_base(&value_high);
                            denom.add_assign(&t);

                            let timestamp_low =
                                *memory_trace_view_row.get_unchecked(shuffle_ram_inits_and_teardowns.lazy_teardown_timestamps_columns.start());
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            t.mul_assign_by_base(&timestamp_low);
                            denom.add_assign(&t);

                            let timestamp_high = *memory_trace_view_row
                                .get_unchecked(shuffle_ram_inits_and_teardowns.lazy_teardown_timestamps_columns.start() + 1);
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign_by_base(&timestamp_high);
                            denom.add_assign(&t);

                            numerator.mul_assign_by_base(&tau_in_domain_by_half);
                            denom.mul_assign_by_base(&tau_in_domain_by_half);

                            numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                            denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                            let mut accumulator = memory_argument_src.read();
                            accumulator.mul_assign_by_base(&tau_in_domain_by_half);

                            let mut term_contribution = accumulator;
                            term_contribution.mul_assign(&denom);
                            term_contribution.sub_assign(&numerator);
                            if DEBUG_QUOTIENT {
                                if is_last_row == false {
                                    assert_eq!(
                                        term_contribution,
                                        Mersenne31Quartic::ZERO,
                                        "unsatisfied at memory accumulation for lazy init/teardown",
                                    );
                                }
                            }
                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // we assembled P(x) = write init set / read teardown set

                        // now we can continue to accumulate either for shuffle RAM, or for batched RAM accesses

                        for (access_idx, memory_access_columns) in compiled_circuit
                            .memory_layout
                            .shuffle_ram_access_sets
                            .iter()
                            .enumerate()
                        {
                            let read_value_columns = memory_access_columns.get_read_value_columns();
                            let read_timestamp_columns = memory_access_columns.get_read_timestamp_columns();

                            let address_contribution = match memory_access_columns.get_address() {
                                ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index }) => {
                                    let address_low = *memory_trace_view_row
                                        .get_unchecked(register_index.start());
                                    let mut address_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                    address_contribution.mul_assign_by_base(&address_low);

                                    // considered is register always
                                    // to we need to add literal 1, so we cancel multiplication by tau^H/2 below
                                    address_contribution.add_assign_base(&tau_in_domain_by_half_inv);

                                    address_contribution
                                },

                                ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress { is_register, address }) => {
                                    debug_assert_eq!(address.width(), 2);

                                    let address_low = *memory_trace_view_row
                                        .get_unchecked(address.start());
                                    let mut address_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                    address_contribution.mul_assign_by_base(&address_low);

                                    let address_high = *memory_trace_view_row
                                        .get_unchecked(address.start() + 1);
                                    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                                    t.mul_assign_by_base(&address_high);
                                    address_contribution.add_assign(&t);

                                    debug_assert_eq!(is_register.width(), 1);
                                    let is_reg =
                                        *memory_trace_view_row.get_unchecked(is_register.start());
                                    address_contribution.add_assign_base(&is_reg);

                                    address_contribution
                                },
                            };

                            debug_assert_eq!(read_value_columns.width(), 2);

                            let read_value_low = *memory_trace_view_row
                                .get_unchecked(read_value_columns.start());
                            let mut read_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            read_value_contribution.mul_assign_by_base(&read_value_low);

                            let read_value_high = *memory_trace_view_row
                                .get_unchecked(read_value_columns.start() + 1);
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign_by_base(&read_value_high);
                            read_value_contribution.add_assign(&t);

                            debug_assert_eq!(read_timestamp_columns.width(), 2);

                            let read_timestamp_low = *memory_trace_view_row
                                .get_unchecked(read_timestamp_columns.start());
                            let mut read_timestamp_contribution =
                                memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            read_timestamp_contribution
                                .mul_assign_by_base(&read_timestamp_low);

                            let read_timestamp_high = *memory_trace_view_row
                                .get_unchecked(read_timestamp_columns.start() + 1);
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign_by_base(&read_timestamp_high);
                            read_timestamp_contribution.add_assign(&t);

                            // timestamp high is STATIC from the index of access, and setup value
                            debug_assert_eq!(compiled_circuit.setup_layout.timestamp_setup_columns.width(), 2);

                            // NOTE on write timestamp: it has literal constants in contribution, so we add it AFTER
                            // scaling by tau^H/2
                            let write_timestamp_low = *setup_trace_view_row
                                .get_unchecked(compiled_circuit.setup_layout.timestamp_setup_columns.start());
                            let mut write_timestamp_contribution =
                                memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            write_timestamp_contribution
                                .mul_assign_by_base(&write_timestamp_low);

                            let write_timestamp_high = *setup_trace_view_row
                                .get_unchecked(
                                    compiled_circuit.setup_layout.timestamp_setup_columns.start() + 1,
                                );
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign_by_base(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            let mut extra_write_timestamp_low = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            extra_write_timestamp_low.mul_assign_by_base(
                                &Mersenne31Field::from_u64_unchecked(access_idx as u64),
                            );

                            let previous = memory_argument_src.read();
                            memory_argument_src = memory_argument_src.add(1);

                            match memory_access_columns {
                                ShuffleRamQueryColumns::Readonly(_) => {
                                    let mut numerator = address_contribution;
                                    numerator.add_assign(&read_value_contribution);

                                    let mut denom = numerator;

                                    // read and write set only differ in timestamp contribution
                                    numerator.add_assign(&write_timestamp_contribution);
                                    denom.add_assign(&read_timestamp_contribution);

                                    // scale all previous terms that are linear in witness
                                    numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                    denom.mul_assign_by_base(&tau_in_domain_by_half);

                                    // add missing contribution from literal constants
                                    numerator.add_assign(&extra_write_timestamp_low);
                                    numerator.add_assign(&extra_write_timestamp_high);

                                    numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                    denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                                    // this * demon - previous * numerator
                                    let accumulator = memory_argument_src.read();

                                    let mut term_contribution = accumulator;
                                    term_contribution.mul_assign(&denom);
                                    let mut t = previous;
                                    t.mul_assign(&numerator);
                                    term_contribution.sub_assign(&t);
                                    // only accumulators are not restored, but we are linear over them
                                    // or just this * denom - numerator
                                    term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                    if DEBUG_QUOTIENT {
                                        if is_last_row == false {
                                            assert_eq!(
                                                term_contribution,
                                                Mersenne31Quartic::ZERO,
                                                "unsatisfied at shuffle RAM memory accumulation for access idx {} at readonly access",
                                                access_idx,
                                            );
                                        }
                                    }
                                    add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                }
                                ShuffleRamQueryColumns::Write(columns) => {
                                    debug_assert_eq!(columns.write_value.width(), 2);

                                    let write_value_low = *memory_trace_view_row
                                        .get_unchecked(columns.write_value.start());
                                    let mut write_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                    write_value_contribution.mul_assign_by_base(&write_value_low);

                                    let write_value_high = *memory_trace_view_row
                                        .get_unchecked(columns.write_value.start() + 1);
                                    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                    t.mul_assign_by_base(&write_value_high);
                                    write_value_contribution.add_assign(&t);

                                    let mut numerator = address_contribution;
                                    let mut denom = numerator;

                                    // read and write set differ in timestamp and value
                                    numerator.add_assign(&write_value_contribution);
                                    denom.add_assign(&read_value_contribution);

                                    numerator.add_assign(&write_timestamp_contribution);
                                    denom.add_assign(&read_timestamp_contribution);

                                    // scale all previous terms that are linear in witness
                                    numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                    denom.mul_assign_by_base(&tau_in_domain_by_half);

                                    // add missing contribution from literal constants
                                    numerator.add_assign(&extra_write_timestamp_low);
                                    numerator.add_assign(&extra_write_timestamp_high);

                                    numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                    denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                                    // this * demon - previous * numerator,
                                    let accumulator = memory_argument_src.read();

                                    let mut term_contribution = accumulator;
                                    term_contribution.mul_assign(&denom);
                                    let mut t = previous;
                                    t.mul_assign(&numerator);
                                    term_contribution.sub_assign(&t);
                                    // only accumulators are not restored, but we are linear over them
                                    term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                    if DEBUG_QUOTIENT {
                                        if is_last_row == false {
                                            assert_eq!(
                                                term_contribution,
                                                Mersenne31Quartic::ZERO,
                                                "unsatisfied at shuffle RAM memory accumulation for access idx {} at write access",
                                                access_idx,
                                            );
                                        }
                                    }
                                    add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                }
                            }
                        }

                        let delegation_write_timestamp_contribution = if process_batch_ram_access || process_registers_and_indirect_access {
                            let write_timestamp_low = *memory_trace_view_row
                                .get_unchecked(
                                    delegation_processor_layout.write_timestamp.start(),
                                );
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            t.mul_assign_by_base(&write_timestamp_low);
                            let mut write_timestamp_contribution = t;

                            let write_timestamp_high = *memory_trace_view_row
                                .get_unchecked(
                                    delegation_processor_layout.write_timestamp.start() + 1,
                                );
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign_by_base(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            write_timestamp_contribution
                        } else {
                            Mersenne31Quartic::ZERO
                        };

                        // Same for batched RAM accesses
                        if process_batch_ram_access {
                            // we only process RAM permutation itself here, and extra constraints related to convention of
                            // read timestamps/values and write timestamps/values is enforced above

                            // all common contributions involve witness values, and need to be added before scalign by tau^H/2
                            let mut common_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                            let address_high = *memory_trace_view_row.get_unchecked(delegation_processor_layout.abi_mem_offset_high.start());
                            common_contribution.mul_assign_by_base(&address_high);

                            for (access_idx, memory_access_columns) in compiled_circuit
                                .memory_layout
                                .batched_ram_accesses
                                .iter()
                                .enumerate()
                            {
                                let read_value_columns = memory_access_columns.get_read_value_columns();
                                let read_timestamp_columns = memory_access_columns.get_read_timestamp_columns();
                                // memory address low is literal constant
                                let mem_offset_low = Mersenne31Field((access_idx * std::mem::size_of::<u32>()) as u32);
                                let mut address_low_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                address_low_contribution.mul_assign_by_base(&mem_offset_low);

                                // we access RAM and not registers
                                debug_assert_eq!(read_value_columns.width(), 2);

                                let read_value_low = *memory_trace_view_row
                                    .get_unchecked(read_value_columns.start());
                                let mut read_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                read_value_contribution.mul_assign_by_base(&read_value_low);

                                let read_value_high = *memory_trace_view_row
                                    .get_unchecked(read_value_columns.start() + 1);
                                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                t.mul_assign_by_base(&read_value_high);
                                read_value_contribution.add_assign(&t);

                                debug_assert_eq!(read_timestamp_columns.width(), 2);

                                let read_timestamp_low = *memory_trace_view_row
                                    .get_unchecked(read_timestamp_columns.start());
                                let mut read_timestamp_contribution =
                                    memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                                read_timestamp_contribution
                                    .mul_assign_by_base(&read_timestamp_low);

                                let read_timestamp_high = *memory_trace_view_row
                                    .get_unchecked(read_timestamp_columns.start() + 1);
                                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                                t.mul_assign_by_base(&read_timestamp_high);
                                read_timestamp_contribution.add_assign(&t);

                                // this is "address high"
                                let mut numerator = common_contribution;

                                let previous = if access_idx == 0 {
                                    let mut previous = Mersenne31Quartic::ONE;
                                    // NOTE: we will multiply it by tau^H/2 below, so not distinguishing between
                                    // this case and other, so we need to multiply by inverse here
                                    previous.mul_assign_by_base(&tau_in_domain_by_half_inv);

                                    previous
                                } else {
                                    let previous = memory_argument_src.read();
                                    memory_argument_src = memory_argument_src.add(1);

                                    previous
                                };

                                match memory_access_columns {
                                    BatchedRamAccessColumns::ReadAccess { ..} => {
                                        numerator.add_assign(&read_value_contribution);

                                        let mut denom = numerator;

                                        numerator.add_assign(&delegation_write_timestamp_contribution);
                                        denom.add_assign(&read_timestamp_contribution);

                                        numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                        numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        // literal constant
                                        numerator.add_assign(&address_low_contribution);

                                        denom.mul_assign_by_base(&tau_in_domain_by_half);
                                        denom.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        // literal constant
                                        denom.add_assign(&address_low_contribution);

                                        // this * demon - previous * numerator
                                        // or just this * denom - numerator
                                        let accumulator = memory_argument_src.read();

                                        let mut term_contribution = accumulator;
                                        term_contribution.mul_assign(&denom);
                                        let mut t = previous;
                                        t.mul_assign(&numerator);
                                        term_contribution.sub_assign(&t);
                                        // only accumulators are not restored, but we are linear over them
                                        term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                        if DEBUG_QUOTIENT {
                                            if is_last_row == false {
                                                assert_eq!(
                                                    term_contribution,
                                                    Mersenne31Quartic::ZERO,
                                                    "unsatisfied at batch RAM memory accumulation for access idx {} at readonly access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. Previous * numerator = {}",
                                                    access_idx,
                                                    previous,
                                                    numerator,
                                                    denom,
                                                    accumulator,
                                                    t,
                                                );
                                            }
                                        }
                                        add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                    }
                                    BatchedRamAccessColumns::WriteAccess { write_value, .. } => {
                                        let write_value_low = *memory_trace_view_row
                                            .get_unchecked(write_value.start());
                                        let mut write_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                        write_value_contribution.mul_assign_by_base(&write_value_low);

                                        let write_value_high = *memory_trace_view_row
                                            .get_unchecked(write_value.start() + 1);
                                        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                        t.mul_assign_by_base(&write_value_high);
                                        write_value_contribution.add_assign(&t);

                                        let mut denom = numerator;

                                        numerator.add_assign(&write_value_contribution);
                                        denom.add_assign(&read_value_contribution);

                                        numerator.add_assign(&delegation_write_timestamp_contribution);
                                        denom.add_assign(&read_timestamp_contribution);

                                        numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                        numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        numerator.add_assign(&address_low_contribution);

                                        denom.mul_assign_by_base(&tau_in_domain_by_half);
                                        denom.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        denom.add_assign(&address_low_contribution);

                                        // this * demon - previous * numerator
                                        // or just this * denom - numerator
                                        let accumulator = memory_argument_src.read();

                                        let mut term_contribution = accumulator;
                                        term_contribution.mul_assign(&denom);
                                        let mut t = previous;
                                        t.mul_assign(&numerator);
                                        term_contribution.sub_assign(&t);
                                        // only accumulators are not restored, but we are linear over them
                                        term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                        if DEBUG_QUOTIENT {
                                            if is_last_row == false {
                                                let mut ttt = accumulator;
                                                ttt.mul_assign(&denom);
                                                assert_eq!(
                                                    term_contribution,
                                                    Mersenne31Quartic::ZERO,
                                                    "unsatisfied at batch RAM memory accumulation for access idx {} at write access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. previous * numerator = {}, current * denom = {}",
                                                    access_idx,
                                                    previous,
                                                    numerator,
                                                    denom,
                                                    accumulator,
                                                    t,
                                                    ttt,
                                                );
                                            }
                                        }
                                        add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                    }
                                }
                            }
                        }

                        // Same for registers and indirects
                        if process_registers_and_indirect_access {
                            // we only process RAM permutation itself here, and extra constraints related to convention of
                            // read timestamps/values and write timestamps/values is enforced above

                            // commong contribution here will come from the fact that we access register, but it's a literal constant and will be added last

                            for (access_idx, register_access_columns) in compiled_circuit
                                .memory_layout
                                .register_and_indirect_accesses
                                .iter()
                                .enumerate()
                            {
                                let read_value_columns = register_access_columns.register_access.get_read_value_columns();
                                let read_timestamp_columns = register_access_columns.register_access.get_read_timestamp_columns();
                                let register_index = register_access_columns.register_access.get_register_index();
                                debug_assert!(register_index > 0);
                                debug_assert!(register_index < 32);

                                // address contribution is literal constant
                                let mem_offset_low = Mersenne31Field(register_index);
                                let mut address_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                address_contribution.mul_assign_by_base(&mem_offset_low);
                                // also a fact that it's a register. There is no challenge here
                                address_contribution.add_assign_base(&Mersenne31Field::ONE);

                                debug_assert_eq!(read_value_columns.width(), 2);

                                let register_read_value_low = *memory_trace_view_row
                                    .get_unchecked(read_value_columns.start());
                                let mut read_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                read_value_contribution.mul_assign_by_base(&register_read_value_low);

                                let register_read_value_high = *memory_trace_view_row
                                    .get_unchecked(read_value_columns.start() + 1);
                                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                t.mul_assign_by_base(&register_read_value_high);
                                read_value_contribution.add_assign(&t);

                                debug_assert_eq!(read_timestamp_columns.width(), 2);

                                let read_timestamp_low = *memory_trace_view_row
                                    .get_unchecked(read_timestamp_columns.start());
                                let mut read_timestamp_contribution =
                                    memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                                read_timestamp_contribution
                                    .mul_assign_by_base(&read_timestamp_low);

                                let read_timestamp_high = *memory_trace_view_row
                                    .get_unchecked(read_timestamp_columns.start() + 1);
                                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                                t.mul_assign_by_base(&read_timestamp_high);
                                read_timestamp_contribution.add_assign(&t);

                                let previous = if access_idx == 0 && process_batch_ram_access == false {
                                    debug_assert_eq!(
                                        stage_2_trace_view_row
                                            .as_ptr()
                                            .add(memory_accumulator_dst_start)
                                            .cast::<Mersenne31Quartic>(),
                                        memory_argument_src
                                    );

                                    let mut previous = Mersenne31Quartic::ONE;
                                    // NOTE: we will multiply it by tau^H/2 below, so not distinguishing between
                                    // this case and other, so we need to multiply by inverse here
                                    previous.mul_assign_by_base(&tau_in_domain_by_half_inv);

                                    previous
                                } else {
                                    let previous = memory_argument_src.read();
                                    memory_argument_src = memory_argument_src.add(1);

                                    previous
                                };

                                match register_access_columns.register_access {
                                    RegisterAccessColumns::ReadAccess { .. } => {
                                        let mut numerator = read_value_contribution;

                                        let mut denom = numerator;

                                        numerator.add_assign(&delegation_write_timestamp_contribution);
                                        denom.add_assign(&read_timestamp_contribution);

                                        numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                        numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        // literal constant
                                        numerator.add_assign(&address_contribution);

                                        denom.mul_assign_by_base(&tau_in_domain_by_half);
                                        denom.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        // literal constant
                                        denom.add_assign(&address_contribution);

                                        // this * demon - previous * numerator
                                        // or just this * denom - numerator
                                        let accumulator = memory_argument_src.read();

                                        let mut term_contribution = accumulator;
                                        term_contribution.mul_assign(&denom);
                                        let mut t = previous;
                                        t.mul_assign(&numerator);
                                        term_contribution.sub_assign(&t);
                                        // only accumulators are not restored, but we are linear over them
                                        term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                        if DEBUG_QUOTIENT {
                                            if is_last_row == false {
                                                assert_eq!(
                                                    term_contribution,
                                                    Mersenne31Quartic::ZERO,
                                                    "unsatisfied at register RAM memory accumulation for access idx {} at readonly access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. Previous * numerator = {}",
                                                    access_idx,
                                                    previous,
                                                    numerator,
                                                    denom,
                                                    accumulator,
                                                    t,
                                                );
                                            }
                                        }
                                        add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                    }
                                    RegisterAccessColumns::WriteAccess { write_value, .. } => {
                                        let write_value_low = *memory_trace_view_row
                                            .get_unchecked(write_value.start());
                                        let mut write_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                        write_value_contribution.mul_assign_by_base(&write_value_low);

                                        let write_value_high = *memory_trace_view_row
                                            .get_unchecked(write_value.start() + 1);
                                        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                        t.mul_assign_by_base(&write_value_high);
                                        write_value_contribution.add_assign(&t);

                                        let mut numerator = write_value_contribution;
                                        let mut denom = read_value_contribution;

                                        numerator.add_assign(&delegation_write_timestamp_contribution);
                                        denom.add_assign(&read_timestamp_contribution);

                                        numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                        numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        // literal constant
                                        numerator.add_assign(&address_contribution);

                                        denom.mul_assign_by_base(&tau_in_domain_by_half);
                                        denom.add_assign(&memory_argument_challenges.memory_argument_gamma);
                                        // literal constant
                                        denom.add_assign(&address_contribution);

                                        // this * demon - previous * numerator
                                        // or just this * denom - numerator
                                        let accumulator = memory_argument_src.read();

                                        let mut term_contribution = accumulator;
                                        term_contribution.mul_assign(&denom);
                                        let mut t = previous;
                                        t.mul_assign(&numerator);
                                        term_contribution.sub_assign(&t);
                                        // only accumulators are not restored, but we are linear over them
                                        term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                        if DEBUG_QUOTIENT {
                                            if is_last_row == false {
                                                assert_eq!(
                                                    term_contribution,
                                                    Mersenne31Quartic::ZERO,
                                                    "unsatisfied at register RAM memory accumulation for access idx {} at write access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. previous * numerator = {}",
                                                    access_idx,
                                                    previous,
                                                    numerator,
                                                    denom,
                                                    accumulator,
                                                    t,
                                                );
                                            }
                                        }
                                        add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                    }
                                }

                                // and now if we have indirects - must process those
                                for (indirect_access_idx, indirect_access_columns) in register_access_columns.indirect_accesses
                                    .iter()
                                    .enumerate()
                                {
                                    let read_value_columns = indirect_access_columns.get_read_value_columns();
                                    let read_timestamp_columns = indirect_access_columns.get_read_timestamp_columns();
                                    let carry_bit_column = indirect_access_columns.get_address_derivation_carry_bit_column();
                                    let offset = indirect_access_columns.get_offset();
                                    assert!(offset < 1<<16, "offset {} is too large and not supported", offset);
                                    // we expect offset == 0 for the first indirect access and offset > 0 for others
                                    assert_eq!(indirect_access_idx == 0, offset == 0);
                                    // address contribution is literal constant common, but a little convoluated

                                    // let will multiply offset by inverse of tau in domain by half to make our live simpler below
                                    let mut offset_adjusted = tau_in_domain_by_half_inv;
                                    offset_adjusted.mul_assign_by_base(&Mersenne31Field(offset));

                                    let address_contribution = if indirect_access_idx == 0 || carry_bit_column.num_elements() == 0 {
                                        let mem_offset_low = register_read_value_low;
                                        let mut mem_offset_low = Mersenne31Complex::from_base(mem_offset_low);
                                        mem_offset_low.add_assign_base(&offset_adjusted);

                                        let mut address_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                        address_contribution.mul_assign_by_base(&mem_offset_low);

                                        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                                        t.mul_assign_by_base(&register_read_value_high);
                                        address_contribution.add_assign(&t);

                                        address_contribution
                                    } else {
                                        // we compute an absolute address as read value + offset, so low part is register_low + offset - 2^16 * carry_bit
                                        let carry_bit = *memory_trace_view_row
                                            .get_unchecked(carry_bit_column.start());
                                        let mut carry_bit_shifted = SHIFT_16;
                                        carry_bit_shifted.mul_assign(&carry_bit);

                                        let mut mem_offset_low = register_read_value_low;
                                        mem_offset_low.sub_assign(&carry_bit_shifted);
                                        let mut mem_offset_low = Mersenne31Complex::from_base(mem_offset_low);
                                        mem_offset_low.add_assign(&offset_adjusted);

                                        let mut address_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                        address_contribution.mul_assign_by_base(&mem_offset_low);

                                        let mut mem_offset_high = register_read_value_high;
                                        mem_offset_high.add_assign(&carry_bit);

                                        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                                        t.mul_assign_by_base(&mem_offset_high);
                                        address_contribution.add_assign(&t);

                                        address_contribution
                                    };

                                    // we access RAM and not registers
                                    debug_assert_eq!(read_value_columns.width(), 2);

                                    let read_value_low = *memory_trace_view_row
                                        .get_unchecked(read_value_columns.start());
                                    let mut read_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                    read_value_contribution.mul_assign_by_base(&read_value_low);

                                    let read_value_high = *memory_trace_view_row
                                        .get_unchecked(read_value_columns.start() + 1);
                                    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                    t.mul_assign_by_base(&read_value_high);
                                    read_value_contribution.add_assign(&t);

                                    debug_assert_eq!(read_timestamp_columns.width(), 2);

                                    let read_timestamp_low = *memory_trace_view_row
                                        .get_unchecked(read_timestamp_columns.start());
                                    let mut read_timestamp_contribution =
                                        memory_argument_challenges.memory_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                                    read_timestamp_contribution
                                        .mul_assign_by_base(&read_timestamp_low);

                                    let read_timestamp_high = *memory_trace_view_row
                                        .get_unchecked(read_timestamp_columns.start() + 1);
                                    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                                    t.mul_assign_by_base(&read_timestamp_high);
                                    read_timestamp_contribution.add_assign(&t);

                                    let previous = memory_argument_src.read();
                                    memory_argument_src = memory_argument_src.add(1);

                                    let mut numerator = address_contribution;

                                    match indirect_access_columns {
                                        IndirectAccessColumns::ReadAccess { .. } => {
                                            numerator.add_assign(&read_value_contribution);

                                            let mut denom = numerator;

                                            numerator.add_assign(&delegation_write_timestamp_contribution);
                                            denom.add_assign(&read_timestamp_contribution);

                                            numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                            numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);

                                            denom.mul_assign_by_base(&tau_in_domain_by_half);
                                            denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                                            // this * demon - previous * numerator
                                            // or just this * denom - numerator
                                            let accumulator = memory_argument_src.read();

                                            let mut term_contribution = accumulator;
                                            term_contribution.mul_assign(&denom);
                                            let mut t = previous;
                                            t.mul_assign(&numerator);
                                            term_contribution.sub_assign(&t);
                                            // only accumulators are not restored, but we are linear over them
                                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(
                                                        term_contribution,
                                                        Mersenne31Quartic::ZERO,
                                                        "row {}: unsatisfied at indirect RAM memory accumulation for register access idx {} indirect access {} at readonly access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. Previous * numerator = {}",
                                                        absolute_row_idx,
                                                        access_idx,
                                                        indirect_access_idx,
                                                        previous,
                                                        numerator,
                                                        denom,
                                                        accumulator,
                                                        t,
                                                    );
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                        }
                                        IndirectAccessColumns::WriteAccess { write_value, .. } => {
                                            let write_value_low = *memory_trace_view_row
                                                .get_unchecked(write_value.start());
                                            let mut write_value_contribution = memory_argument_challenges.memory_argument_linearization_challenges
                                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                                            write_value_contribution.mul_assign_by_base(&write_value_low);

                                            let write_value_high = *memory_trace_view_row
                                                .get_unchecked(write_value.start() + 1);
                                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                                            t.mul_assign_by_base(&write_value_high);
                                            write_value_contribution.add_assign(&t);

                                            let mut denom = numerator;

                                            numerator.add_assign(&write_value_contribution);
                                            denom.add_assign(&read_value_contribution);

                                            numerator.add_assign(&delegation_write_timestamp_contribution);
                                            denom.add_assign(&read_timestamp_contribution);

                                            numerator.mul_assign_by_base(&tau_in_domain_by_half);
                                            numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);

                                            denom.mul_assign_by_base(&tau_in_domain_by_half);
                                            denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                                            // this * demon - previous * numerator
                                            // or just this * denom - numerator
                                            let accumulator = memory_argument_src.read();

                                            let mut term_contribution = accumulator;
                                            term_contribution.mul_assign(&denom);
                                            let mut t = previous;
                                            t.mul_assign(&numerator);
                                            term_contribution.sub_assign(&t);
                                            // only accumulators are not restored, but we are linear over them
                                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);

                                            if DEBUG_QUOTIENT {
                                                if is_last_row == false {
                                                    assert_eq!(
                                                        term_contribution,
                                                        Mersenne31Quartic::ZERO,
                                                        "row {}: unsatisfied at indirect RAM memory accumulation for access idx {} indirect access {} at write access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. previous * numerator = {}",
                                                        absolute_row_idx,
                                                        access_idx,
                                                        indirect_access_idx,
                                                        previous,
                                                        numerator,
                                                        denom,
                                                        accumulator,
                                                        t,
                                                    );
                                                }
                                            }
                                            add_quotient_term_contribution_in_ext4(&mut other_challenges_ptr, term_contribution, &mut quotient_term);
                                        }
                                    }
                                }
                            }
                        }

                        // and now we need to make Z(next) = Z(this) * previous(this)
                        {
                            let mut previous = memory_argument_src.read();
                            previous.mul_assign_by_base(&tau_in_domain_by_half);
                            memory_argument_src = memory_argument_src.add(1);
                            let accumulator_this_row = memory_argument_src.read();
                            let accumulator_next_row = stage_2_trace_view_next_row
                                .as_ptr()
                                .add(memory_accumulator_dst_start)
                                .cast::<Mersenne31Quartic>()
                                .add(offset_for_grand_product_accumulation_poly)
                                .read();
                            debug_assert!(memory_argument_src.is_aligned());

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
                                        "unsatisfied at memory accumulation grand product",
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

                        // then linking constraints
                        for (src, dst) in compiled_circuit.state_linkage_constraints.iter() {
                            // src - dst == 0;
                            let mut diff =
                                read_value(*src, witness_trace_view_row, memory_trace_view_row);
                            let dst_value = read_value(
                                *dst,
                                witness_trace_view_next_row,
                                memory_trace_view_next_row,
                            );
                            diff.sub_assign(&dst_value);
                            if DEBUG_QUOTIENT {
                                if is_last_two_rows == false {
                                    assert_eq!(
                                        diff,
                                        Mersenne31Field::ZERO,
                                        "unsatisfied at link {:?} -> {:?}",
                                        src,
                                        dst
                                    );
                                }
                            }
                            let mut term_contribution = tau_in_domain_by_half;
                            term_contribution.mul_assign_by_base(&diff);
                            add_quotient_term_contribution_in_ext2(&mut every_row_except_last_two_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // two constraints to compare sorting of lazy init
                        if let Some(lazy_init_address_aux_vars) = compiled_circuit.lazy_init_address_aux_vars {
                            debug_assert!(process_shuffle_ram_init);
                            let lazy_init_address_start = shuffle_ram_inits_and_teardowns.lazy_init_addresses_columns.start();
                            let lazy_init_address_low = lazy_init_address_start;
                            let lazy_init_address_high = lazy_init_address_start + 1;
                            let lazy_init_address_low_place = ColumnAddress::MemorySubtree(lazy_init_address_low);
                            let lazy_init_address_high_place = ColumnAddress::MemorySubtree(lazy_init_address_high);

                            let ShuffleRamAuxComparisonSet { aux_low_high: [address_aux_low, address_aux_high], intermediate_borrow, final_borrow } = lazy_init_address_aux_vars;
                            // first we do low: this - next with borrow
                            let this_low = read_value(lazy_init_address_low_place, witness_trace_view_row, memory_trace_view_row);
                            let next_low = read_value(lazy_init_address_low_place, witness_trace_view_next_row, memory_trace_view_next_row);
                            let aux_low = read_value(address_aux_low, witness_trace_view_row, memory_trace_view_row);
                            let intermediate_borrow_value = read_value(intermediate_borrow, witness_trace_view_row, memory_trace_view_row);
                            let final_borrow_value = read_value(final_borrow, witness_trace_view_row, memory_trace_view_row);

                            let mut term_contribution = SHIFT_16;
                            term_contribution.mul_assign(&intermediate_borrow_value);
                            term_contribution.add_assign(&this_low);
                            term_contribution.sub_assign(&next_low);
                            term_contribution.sub_assign(&aux_low);
                            if DEBUG_QUOTIENT {
                                if is_last_two_rows == false {
                                    assert_eq!(term_contribution, Mersenne31Field::ZERO, "unsatisfied at lazy init address sorting low at row idx {}", absolute_row_idx);
                                }
                            }
                            let mut term_contribution_ext2 = tau_in_domain_by_half;
                            term_contribution_ext2.mul_assign_by_base(&term_contribution);
                            add_quotient_term_contribution_in_ext2(&mut every_row_except_last_two_challenges_ptr, term_contribution_ext2, &mut quotient_term);

                            // then we do high: this - next with borrow
                            let this_high = read_value(lazy_init_address_high_place, witness_trace_view_row, memory_trace_view_row);
                            let next_high = read_value(lazy_init_address_high_place, witness_trace_view_next_row, memory_trace_view_next_row);
                            let aux_high = read_value(address_aux_high, witness_trace_view_row, memory_trace_view_row);

                            let mut term_contribution = SHIFT_16;
                            term_contribution.mul_assign(&final_borrow_value);
                            term_contribution.add_assign(&this_high);
                            term_contribution.sub_assign(&intermediate_borrow_value);
                            term_contribution.sub_assign(&next_high);
                            term_contribution.sub_assign(&aux_high);
                            if DEBUG_QUOTIENT {
                                if is_last_two_rows == false {
                                    assert_eq!(term_contribution, Mersenne31Field::ZERO, "unsatisfied at lazy init address sorting highat row idx {}", absolute_row_idx);
                                }
                            }

                            let mut term_contribution_ext2 = tau_in_domain_by_half;
                            term_contribution_ext2.mul_assign_by_base(&term_contribution);
                            add_quotient_term_contribution_in_ext2(&mut every_row_except_last_two_challenges_ptr, term_contribution_ext2, &mut quotient_term);
                        }

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
                                .add(memory_accumulator_dst_start)
                                .cast::<Mersenne31Quartic>();
                            let accumulator = memory_accumulators_ptr.add(offset_for_grand_product_accumulation_poly).read();

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
                                .add(memory_accumulator_dst_start)
                                .cast::<Mersenne31Quartic>();
                            let accumulator = memory_accumulators_ptr.add(offset_for_grand_product_accumulation_poly).read();

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

                        // range check 16
                        if compiled_circuit.witness_layout.multiplicities_columns_for_range_check_16.num_elements() > 0 {
                            let multiplicity_aux = stage_2_trace_view_row.as_ptr().add(compiled_circuit.stage_2_layout.intermediate_poly_for_range_check_16_multiplicity.start()).cast::<Mersenne31Quartic>().read();
                            let mut term_contribution = multiplicity_aux;

                            for i in 0..compiled_circuit.stage_2_layout.intermediate_polys_for_range_check_16.num_pairs {
                                let el = stage_2_trace_view_row.as_ptr().add(compiled_circuit.stage_2_layout.intermediate_polys_for_range_check_16.ext_4_field_oracles.get_range(i).start).cast::<Mersenne31Quartic>().read();
                                term_contribution.sub_assign(&el);
                            }
                            // add lazy init value
                            if process_shuffle_ram_init {
                                let el = stage_2_trace_view_row.as_ptr().add(lazy_init_address_range_check_16.ext_4_field_oracles.get_range(0).start).cast::<Mersenne31Quartic>().read();
                                term_contribution.sub_assign(&el);
                            }
                            if let Some(_remainder) = compiled_circuit.stage_2_layout.remainder_for_range_check_16 {
                                todo!();
                            }
                            if DEBUG_QUOTIENT {
                                if  is_last_row {
                                    assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at lookups aux polys difference for range check 16 at last row");
                                }
                            }
                            // linear
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            add_quotient_term_contribution_in_ext4(&mut last_row_and_at_zero_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // timestamp range check
                        if compiled_circuit.witness_layout.multiplicities_columns_for_timestamp_range_check.num_elements() > 0 {
                            let multiplicity_aux = stage_2_trace_view_row.as_ptr().add(compiled_circuit.stage_2_layout.intermediate_poly_for_timestamp_range_check_multiplicity.start()).cast::<Mersenne31Quartic>().read();
                            let mut term_contribution = multiplicity_aux;

                            for i in 0..compiled_circuit.stage_2_layout.intermediate_polys_for_timestamp_range_checks.num_pairs {
                                let el = stage_2_trace_view_row.as_ptr().add(compiled_circuit.stage_2_layout.intermediate_polys_for_timestamp_range_checks.ext_4_field_oracles.get_range(i).start).cast::<Mersenne31Quartic>().read();
                                term_contribution.sub_assign(&el);
                            }
                            if DEBUG_QUOTIENT {
                                if  is_last_row {
                                    assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at lookups aux polys difference for timestamp range check at last row");
                                }
                            }
                            // linear
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            add_quotient_term_contribution_in_ext4(&mut last_row_and_at_zero_challenges_ptr, term_contribution, &mut quotient_term);
                        }

                        // generic lookup
                        if compiled_circuit.witness_layout.multiplicities_columns_for_generic_lookup.num_elements() > 0 {
                            assert!(compiled_circuit.stage_2_layout.intermediate_polys_for_generic_lookup.num_elements() > 0);
                            let mut term_contribution = Mersenne31Quartic::ZERO;
                            for i in 0..compiled_circuit.witness_layout.multiplicities_columns_for_generic_lookup.num_elements() {
                                let ptr = stage_2_trace_view_row.as_ptr()
                                    .add(compiled_circuit.stage_2_layout.intermediate_polys_for_generic_multiplicities
                                    .get_range(i).start)
                                    .cast::<Mersenne31Quartic>();
                                assert!(ptr.is_aligned());
                                let multiplicity_aux = ptr.read();
                                term_contribution.add_assign(&multiplicity_aux);
                            }

                            for i in 0..compiled_circuit.stage_2_layout.intermediate_polys_for_generic_lookup.num_elements() {
                                let ptr = stage_2_trace_view_row.as_ptr()
                                    .add(compiled_circuit.stage_2_layout.intermediate_polys_for_generic_lookup
                                    .get_range(i).start)
                                    .cast::<Mersenne31Quartic>();
                                assert!(ptr.is_aligned());
                                let el = ptr.read();
                                term_contribution.sub_assign(&el);
                            }
                            if DEBUG_QUOTIENT {
                                if is_last_row {
                                    assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at lookups aux polys difference for generic lookup at last row");
                                }
                            }
                            // linear
                            term_contribution.mul_assign_by_base(&tau_in_domain_by_half);
                            add_quotient_term_contribution_in_ext4(&mut last_row_and_at_zero_challenges_ptr, term_contribution, &mut quotient_term);
                        }

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

                        assert_eq!(last_row_and_at_zero_challenges_ptr, alphas_for_last_row_and_at_zero.as_ptr_range().end);

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
