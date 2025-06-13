// In stage 2 we work with randomized arguments. Main optimization point here:
// we want to evaluate \sum_i 1/(witness_i + gamma), where witness_i is in base field, while
// gamma is in the extension. If we would naively create auxiliary polys then we would have to commit to those in the extension,
// that is a blowup. Let's try to do better
//
// naively for every column we would need 1 aux poly in 4th extension, but for width=1 columns we can do better (if we will spend separate multiplicities columns for them)
//
// we can add up 1/a + 1/b (if we have separate access as a/b) in projective coordinates as a + b, a * b
// now unroll
// 1 / a + gamma + 1/b + gamma = a + b + 2 * gamma, gamma^2 + a*b + gamma * (a + b)
// note that in the numerator we have just degree 1 poly, so we can forget it, and only
// provide C(x) = a(X)*b(X) elementwise on the domain, that is BASE FIELD
// then we still need to compute a sum of those "pairwise sums" on the domain, and we will do it as
// B(X) = (a(x) + b(x) + 2 * gamma) / (C(x) + gamma * (a(x) + b(x)) + gamma^2) elementwise on the domain
// that is extension field, but one per two witness columns in the lookup,
// so our total cost is
// - baseline: 4 * num witness polys
// - optimized: (num witnees polys / 2) + (num witnees polys / 2) * 4 = num witnees polys * 2.5

use super::stage1::*;
use super::*;
use crate::{prover_stages::stage2_utils::*, utils::*};
use cached_data::ProverCachedData;
use cs::one_row_compiler::{ColumnAddress, ShuffleRamQueryColumns};
use fft::field_utils::batch_inverse_with_buffer;

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct LookupWidth1SourceDestInformation {
    pub a_col: usize,
    pub b_col: usize,
    pub base_field_quadratic_oracle_col: usize,
    pub ext4_field_inverses_columns_start: usize,
}

pub struct SecondStageOutput<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> {
    pub ldes: Vec<CosetBoundTracePart<N, A>>,
    pub trees: Vec<T>,
    pub lookup_argument_linearization_challenges:
        [Mersenne31Quartic; NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1],
    pub lookup_argument_gamma: Mersenne31Quartic,
    pub grand_product_accumulator: Mersenne31Quartic,
    pub sum_over_delegation_poly: Mersenne31Quartic,
}

pub fn prover_stage_2<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor>(
    seed: &mut Seed,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cached_data: &ProverCachedData,
    stage_1_output: &FirstStageOutput<N, A, T>,
    setup_precomputations: &SetupPrecomputations<N, A, T>,
    lookup_mapping: RowMajorTrace<u32, N, A>,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
    folding_description: &FoldingDescription,
    worker: &Worker,
) -> SecondStageOutput<N, A, T> {
    assert!(lde_factor.is_power_of_two());

    assert_eq!(
        compiled_circuit.witness_layout.width_3_lookups.len(),
        lookup_mapping.width(),
    );

    let exec_trace = &stage_1_output.ldes[0].trace;
    let setup_trace = &setup_precomputations.ldes[0].trace;

    let mut transcript_challenges = [0u32;
        ((NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4)
            .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    let mut it = transcript_challenges.array_chunks::<4>();
    let lookup_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES] = std::array::from_fn(|_| {
        Mersenne31Quartic::from_coeffs_in_base(
            &it.next()
                .unwrap()
                .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
        )
    });
    let lookup_argument_gamma = Mersenne31Quartic::from_coeffs_in_base(
        &it.next()
            .unwrap()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    #[cfg(feature = "debug_logs")]
    {
        dbg!(lookup_argument_linearization_challenges);
        dbg!(lookup_argument_gamma);
    }

    let mut lookup_argument_two_gamma = lookup_argument_gamma;
    lookup_argument_two_gamma.double();

    let ProverCachedData {
        trace_len,
        memory_timestamp_high_from_circuit_idx,
        delegation_type,
        memory_argument_challenges,
        #[cfg(feature = "debug_logs")]
        execute_delegation_argument,
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
        range_check_16_multiplicities_dst,

        timestamp_range_check_multiplicities_src,
        timestamp_range_check_multiplicities_dst,

        generic_lookup_multiplicities_src_start,
        generic_lookup_multiplicities_dst_start,
        generic_lookup_setup_columns_start,

        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,

        timestamp_range_check_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,

        memory_accumulator_dst_start,
        ..
    } = cached_data.clone();

    #[cfg(feature = "debug_logs")]
    {
        dbg!(process_shuffle_ram_init);
        dbg!(handle_delegation_requests);
        dbg!(process_delegations);
        dbg!(execute_delegation_argument);
    }

    assert_eq!(
        compiled_circuit
            .setup_layout
            .generic_lookup_setup_columns
            .num_elements(),
        compiled_circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .num_elements()
    );
    assert_eq!(
        generic_lookup_setup_columns_start,
        compiled_circuit
            .setup_layout
            .generic_lookup_setup_columns
            .start()
    );

    #[cfg(feature = "debug_logs")]
    println!("Evaluating lookup tables preprocessing");
    let now = std::time::Instant::now();

    // we will preprocess everything as a single vector for generic lookup tables,
    // and a separate short vector for range-check 16 table and timestamp range check table

    let lookup_encoding_capacity = trace_len - 1;
    let generic_lookup_tables_size = compiled_circuit.total_tables_size;
    let mut generic_lookup_preprocessing =
        Vec::with_capacity_in(generic_lookup_tables_size, A::default());
    let mut dst =
        &mut generic_lookup_preprocessing.spare_capacity_mut()[..generic_lookup_tables_size];

    unsafe {
        worker.scope(generic_lookup_tables_size, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let (chunk, rest) = dst.split_at_mut(chunk_size);
                dst = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut batch_inverse_buffer = vec![Mersenne31Quartic::ZERO; chunk.len()];
                    for i in 0..chunk_size {
                        let absolute_table_idx = chunk_start + i;

                        let (column, row_idx) = lookup_index_into_encoding_tuple(
                            absolute_table_idx,
                            lookup_encoding_capacity,
                        );
                        let row = setup_trace.get_row(row_idx as usize);
                        let src = row.get_unchecked(
                            compiled_circuit
                                .setup_layout
                                .generic_lookup_setup_columns
                                .get_range(column as usize),
                        );
                        assert_eq!(src.len(), COMMON_TABLE_WIDTH + 1);

                        let [el0, el1, el2, el3] = std::array::from_fn(|j| {
                            let value = src[j];

                            value
                        });
                        let denom = compute_aggregated_key_value(
                            el0,
                            [el1, el2, el3],
                            lookup_argument_linearization_challenges,
                            lookup_argument_gamma,
                        );

                        chunk[i].write(denom);
                    }

                    // batch inverse
                    let buffer = chunk.assume_init_mut();
                    let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                    assert!(all_nonzero);
                });
            }

            assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), generic_lookup_tables_size, worker.get_num_cores());
        });
    }

    unsafe {
        generic_lookup_preprocessing.set_len(generic_lookup_tables_size);
    }

    // same for range check 16

    assert!(trace_len > 1 << 16);

    let mut range_check_16_preprocessing: Vec<Mersenne31Quartic, A> =
        Vec::with_capacity_in(1 << 16, A::default());
    let mut dst = &mut range_check_16_preprocessing.spare_capacity_mut()[..(1 << 16)];

    unsafe {
        worker.scope(1 << 16, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let (chunk, rest) = dst.split_at_mut(chunk_size);
                dst = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut batch_inverse_buffer = vec![Mersenne31Quartic::ZERO; chunk.len()];
                    for i in 0..chunk_size {
                        let absolute_table_idx = chunk_start + i;

                        // range check 16
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign_base(&Mersenne31Field(absolute_table_idx as u32));

                        chunk[i].write(denom);
                    }

                    // batch inverse
                    let buffer = chunk.assume_init_mut();
                    let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                    assert!(all_nonzero);
                });
            }

            assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << 16, worker.get_num_cores());
        });
    }

    unsafe {
        range_check_16_preprocessing.set_len(1 << 16);
    }

    // and timestamp range checks
    assert!(trace_len > 1 << TIMESTAMP_COLUMNS_NUM_BITS);

    let mut timestamp_range_check_preprocessing: Vec<Mersenne31Quartic, A> =
        Vec::with_capacity_in(1 << TIMESTAMP_COLUMNS_NUM_BITS, A::default());
    let mut dst = &mut timestamp_range_check_preprocessing.spare_capacity_mut()
        [..(1 << TIMESTAMP_COLUMNS_NUM_BITS)];

    unsafe {
        worker.scope(1 << TIMESTAMP_COLUMNS_NUM_BITS, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let (chunk, rest) = dst.split_at_mut(chunk_size);
                dst = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut batch_inverse_buffer = vec![Mersenne31Quartic::ZERO; chunk.len()];
                    for i in 0..chunk_size {
                        let absolute_table_idx = chunk_start + i;

                        // range check
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign_base(&Mersenne31Field(absolute_table_idx as u32));

                        chunk[i].write(denom);
                    }

                    // batch inverse
                    let buffer = chunk.assume_init_mut();
                    let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                    assert!(all_nonzero);
                });
            }

            assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << TIMESTAMP_COLUMNS_NUM_BITS, worker.get_num_cores());
        });
    }

    unsafe {
        timestamp_range_check_preprocessing.set_len(1 << TIMESTAMP_COLUMNS_NUM_BITS);
    }

    println!("Lookup preprocessing took {:?}", now.elapsed());

    // now we can make stage 2 trace on the main domain. We will still have some batch inverses along the way,
    // but a small value

    let mut stage_2_trace = RowMajorTrace::<Mersenne31Field, N, A>::new_zeroed_for_size(
        trace_len,
        compiled_circuit.stage_2_layout.total_width,
        A::default(),
    );

    // NOTE: we will preprocess lookup setup polynomials to more quickly generate values of lookup
    // multiplicities aux polys and aux polys for rational expressions

    // Also we will need to do batch inverses for memory argument, and we need to count how many we will need

    // now for self-check we should compute how many batch inverses we will want,
    // and define ranges when numerators that are part of batch inverses are 1, so we can skip those

    let offset_for_continuous_batch_inverses_write = if let Some(delegation_processing_aux_poly) =
        compiled_circuit
            .stage_2_layout
            .delegation_processing_aux_poly
    {
        assert_eq!(
            delegation_processing_aux_poly.full_range().end,
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_memory_argument
                .start()
        );

        delegation_processing_aux_poly.start()
    } else {
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .start()
    };
    assert!(
        offset_for_continuous_batch_inverses_write < compiled_circuit.stage_2_layout.total_width
    );

    if let Some(el) = compiled_circuit
        .stage_2_layout
        .lazy_init_address_range_check_16
    {
        assert!(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_range_check_16
                .ext_4_field_oracles
                .start()
                <= el.ext_4_field_oracles.start()
        );
        assert_eq!(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_range_check_16
                .ext_4_field_oracles
                .full_range()
                .end,
            el.ext_4_field_oracles.start()
        );
    }

    if let Some(delegation_processing_aux_poly) = compiled_circuit
        .stage_2_layout
        .delegation_processing_aux_poly
        .as_ref()
    {
        assert!(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_range_check_16
                .ext_4_field_oracles
                .start()
                <= delegation_processing_aux_poly.start()
        );
    }

    assert_eq!(
        compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_range_check_16_multiplicity
            .full_range()
            .end,
        compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_timestamp_range_check_multiplicity
            .start()
    );
    assert_eq!(
        compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_timestamp_range_check_multiplicity
            .full_range()
            .end,
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .start()
    );

    // small assert over continuous range
    if compiled_circuit
        .memory_layout
        .delegation_processor_layout
        .is_none()
        && compiled_circuit
            .memory_layout
            .delegation_request_layout
            .is_none()
    {
        assert_eq!(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_generic_multiplicities
                .full_range()
                .end,
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_memory_argument
                .start()
        );
    } else {
        assert!(delegation_challenges.delegation_argument_gamma.is_zero() == false);
        assert!(compiled_circuit
            .stage_2_layout
            .delegation_processing_aux_poly
            .is_some());
    }

    // batch inverses are only required for delegation linkage poly and memory grand product accumulators
    let mut num_batch_inverses = 0;

    if let Some(el) = compiled_circuit
        .stage_2_layout
        .delegation_processing_aux_poly
    {
        assert_eq!(
            el.full_range().end,
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_memory_argument
                .start()
        );
        num_batch_inverses += el.num_elements();
    }
    num_batch_inverses += compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .num_elements()
        - 1; // we do not need last inverse where we only accumulate grand product

    let range_check_16_width_1_lookups_access_ref = &range_check_16_width_1_lookups_access;
    let range_check_16_width_1_lookups_access_via_expressions_ref =
        &range_check_16_width_1_lookups_access_via_expressions;

    let timestamp_range_check_width_1_lookups_access_via_expressions_ref =
        &timestamp_range_check_width_1_lookups_access_via_expressions;
    let timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref =
        &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram;

    #[cfg(feature = "debug_logs")]
    println!("Evaluating main stage 2 logic");
    let mut grand_product_accumulators = vec![Mersenne31Quartic::ZERO; worker.num_cores];

    // NOTE on trace_len - 1 below: because we work with grand products, we want to stop accumulating them when our meaningful
    // trace ends, so we should skip last row entirely

    let generic_lookup_preprocessing_ref = &generic_lookup_preprocessing;
    let timestamp_range_check_preprocessing_ref = &timestamp_range_check_preprocessing;
    let range_check_16_preprocessing_ref = &range_check_16_preprocessing;

    let now = std::time::Instant::now();

    assert!(exec_trace.width() >= stage_1_output.num_witness_columns);

    let width_3_intermediate_polys_offset = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_generic_lookup
        .start();

    unsafe {
        worker.scope(trace_len - 1, |scope, geometry| {
            let mut accumulators_dsts = grand_product_accumulators.chunks_mut(1);
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut exec_trace_view = exec_trace.row_view(range.clone());
                let mut setup_trace_view = setup_trace.row_view(range.clone());
                let mut stage_2_trace_view = stage_2_trace.row_view(range.clone());
                let mut lookup_indexes_view = lookup_mapping.row_view(range.clone());

                let grand_product_accumulator = accumulators_dsts.next().unwrap();

                Worker::smart_spawn(
                    scope,
                    thread_idx == geometry.len() - 1,
                    move |_|
                {
                    let mut batch_inverses_input = Vec::with_capacity(num_batch_inverses);
                    let mut batch_inverses_buffer = Vec::with_capacity(num_batch_inverses);
                    // we will accumulate our write set/read set grand products in this global value
                    let mut total_accumulated = Mersenne31Quartic::ONE;

                    for _i in 0..chunk_size {
                        let absolute_row_idx = chunk_start + _i;

                        batch_inverses_input.clear();

                        let (witness_trace_row, memory_trace_row) = exec_trace_view
                            .current_row_ref()
                            .split_at_unchecked(stage_1_output.num_witness_columns);
                        let setup_row = setup_trace_view.current_row_ref();
                        let stage_2_trace = stage_2_trace_view.current_row();
                        let lookup_indexes_view_row = lookup_indexes_view.current_row_ref();

                        // range check 16 are special as those are width-1
                        for lookup_set in range_check_16_width_1_lookups_access_ref.iter() {
                            let a = *witness_trace_row.get_unchecked(lookup_set.a_col);
                            let b = *witness_trace_row.get_unchecked(lookup_set.b_col);
                            if DEBUG_QUOTIENT {
                                assert!(a.to_reduced_u32() < 1 << 16);
                                assert!(b.to_reduced_u32() < 1 << 16);
                            }

                            let mut quad = a;
                            quad.mul_assign(&b);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.base_field_quadratic_oracle_col)
                                .write(quad);

                            // we made a * b = some temporary variable,
                            // and now would use this temporary variable to more efficiently prove
                            // that the final value is just
                            // 1 / (a + gamma) + 1 / (b + gamma)

                            // And we can compute final value by just taking a sum of range check 16 preprocessing

                            let a_idx = a.to_reduced_u32() as usize;
                            let b_idx = b.to_reduced_u32() as usize;
                            let mut final_value = *range_check_16_preprocessing_ref.get_unchecked(a_idx);
                            final_value.add_assign(range_check_16_preprocessing_ref.get_unchecked(b_idx));

                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.ext4_field_inverses_columns_start)
                                .cast::<Mersenne31Quartic>()
                                .write(final_value);
                        }

                        // then we have some non-trivial expressions too
                        for lookup_set in range_check_16_width_1_lookups_access_via_expressions_ref.iter() {
                            let LookupExpression::Expression(a) = &lookup_set.a_expr else {
                                unreachable!()
                            };
                            let LookupExpression::Expression(b) = &lookup_set.b_expr else {
                                unreachable!()
                            };
                            let a = a.evaluate_at_row_on_main_domain(
                                witness_trace_row,
                                memory_trace_row,
                            );
                            let b = b.evaluate_at_row_on_main_domain(
                                witness_trace_row,
                                memory_trace_row,
                            );
                            if DEBUG_QUOTIENT {
                                assert!(a.to_reduced_u32() < 1 << 16);
                                assert!(b.to_reduced_u32() < 1 << 16);
                            }

                            let mut quad = a;
                            quad.mul_assign(&b);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.base_field_quadratic_oracle_col)
                                .write(quad);

                            let a_idx = a.to_reduced_u32() as usize;
                            let b_idx = b.to_reduced_u32() as usize;
                            let mut final_value = *range_check_16_preprocessing_ref.get_unchecked(a_idx);
                            final_value.add_assign(range_check_16_preprocessing_ref.get_unchecked(b_idx));

                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.ext4_field_inverses_columns_start)
                                .cast::<Mersenne31Quartic>()
                                .write(final_value);
                        }

                        // special case for range check 16 for lazy init address
                        if process_shuffle_ram_init {
                            let lookup_set = &lazy_init_address_range_check_16;
                            let a_col = shuffle_ram_inits_and_teardowns
                                .lazy_init_addresses_columns
                                .start();
                            let b_col = a_col + 1;
                            let a = *memory_trace_row.get_unchecked(a_col);
                            let b = *memory_trace_row.get_unchecked(b_col);
                            if DEBUG_QUOTIENT {
                                assert!(a.to_reduced_u32() < 1 << 16);
                                assert!(b.to_reduced_u32() < 1 << 16);
                            }
                            let mut quad = a;
                            quad.mul_assign(&b);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.base_field_oracles.start())
                                .write(quad);

                            let a_idx = a.to_reduced_u32() as usize;
                            let b_idx = b.to_reduced_u32() as usize;
                            let mut final_value = *range_check_16_preprocessing_ref.get_unchecked(a_idx);
                            final_value.add_assign(range_check_16_preprocessing_ref.get_unchecked(b_idx));

                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.ext_4_field_oracles.start())
                                .cast::<Mersenne31Quartic>()
                                .write(final_value);
                        }

                        // // remainders for width 1
                        // for (src, _dst) in remainder_for_width_1_lookups_ref.iter() {
                        //     todo!();

                        //     // // we do not care about numerator as it's 1

                        //     // let a = *witness_trace_row.get_unchecked(*src);
                        //     // let mut denom = lookup_argument_gamma;
                        //     // denom.add_assign_base(&a);

                        //     // batch_inverses_input.push(denom);
                        // }

                        // then expressions for the timestamps
                        for lookup_set in timestamp_range_check_width_1_lookups_access_via_expressions_ref.iter() {
                            let LookupExpression::Expression(a) = &lookup_set.a_expr else {
                                unreachable!()
                            };
                            let LookupExpression::Expression(b) = &lookup_set.b_expr else {
                                unreachable!()
                            };
                            let a = a.evaluate_at_row_on_main_domain(
                                witness_trace_row,
                                memory_trace_row,
                            );
                            let b = b.evaluate_at_row_on_main_domain(
                                witness_trace_row,
                                memory_trace_row,
                            );
                            if DEBUG_QUOTIENT {
                                assert!(a.to_reduced_u32() < 1 << TIMESTAMP_COLUMNS_NUM_BITS);
                                assert!(b.to_reduced_u32() < 1 << TIMESTAMP_COLUMNS_NUM_BITS);
                            }

                            let mut quad = a;
                            quad.mul_assign(&b);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.base_field_quadratic_oracle_col)
                                .write(quad);

                            let a_idx = a.to_reduced_u32() as usize;
                            let b_idx = b.to_reduced_u32() as usize;
                            let mut final_value = *timestamp_range_check_preprocessing_ref.get_unchecked(a_idx);
                            final_value.add_assign(timestamp_range_check_preprocessing_ref.get_unchecked(b_idx));

                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.ext4_field_inverses_columns_start)
                                .cast::<Mersenne31Quartic>()
                                .write(final_value);
                        }

                        // and finish with those that also have shuffle ram part and extra contribution in timestamp
                        for lookup_set in
                            timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref.iter()
                        {
                            let LookupExpression::Expression(a_expr) = &lookup_set.a_expr else {
                                unreachable!()
                            };
                            let LookupExpression::Expression(b_expr) = &lookup_set.b_expr else {
                                unreachable!()
                            };
                            let a = a_expr.evaluate_at_row_on_main_domain_ext(
                                witness_trace_row,
                                memory_trace_row,
                                setup_row,
                            );
                            // only "high" (that is always second) needs an adjustment
                            let mut b = b_expr.evaluate_at_row_on_main_domain_ext(
                                witness_trace_row,
                                memory_trace_row,
                                setup_row,
                            );
                            b.sub_assign(&memory_timestamp_high_from_circuit_idx);

                            if DEBUG_QUOTIENT {
                                assert!(a.to_reduced_u32() < 1 << TIMESTAMP_COLUMNS_NUM_BITS);
                                assert!(b.to_reduced_u32() < 1 << TIMESTAMP_COLUMNS_NUM_BITS);
                            }

                            let mut quad = a;
                            quad.mul_assign(&b);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.base_field_quadratic_oracle_col)
                                .write(quad);

                            let a_idx = a.to_reduced_u32() as usize;
                            let b_idx = b.to_reduced_u32() as usize;
                            let mut final_value = *timestamp_range_check_preprocessing_ref.get_unchecked(a_idx);
                            final_value.add_assign(timestamp_range_check_preprocessing_ref.get_unchecked(b_idx));

                            stage_2_trace
                                .as_mut_ptr()
                                .add(lookup_set.ext4_field_inverses_columns_start)
                                .cast::<Mersenne31Quartic>()
                                .write(final_value);
                        }

                        // now generic lookups

                        // NOTE: as we have preprocessed the lookup setup, we can just pick a value by index
                        {
                            let mut dst_ptr = stage_2_trace
                                .as_mut_ptr()
                                .add(width_3_intermediate_polys_offset)
                                .cast::<Mersenne31Quartic>();
                            assert!(dst_ptr.is_aligned());

                            for (i, _lookup_set) in compiled_circuit
                                .witness_layout
                                .width_3_lookups
                                .iter()
                                .enumerate()
                            {
                                let absolute_table_idx = *lookup_indexes_view_row.get_unchecked(i);

                                if DEBUG_QUOTIENT {
                                    assert!((absolute_table_idx as usize) < generic_lookup_tables_size);
                                }

                                let preprocessed_value = *generic_lookup_preprocessing_ref.get_unchecked(absolute_table_idx as usize);
                                dst_ptr.write(preprocessed_value);

                                dst_ptr = dst_ptr.add(1);
                            }
                        }

                        // now we can do the same with multiplicities

                        // range check 16
                        {
                            let value = if absolute_row_idx < 1<<16 {
                                let m =
                                    *witness_trace_row.get_unchecked(range_check_16_multiplicities_src);

                                // Read preprocessed column and read rational value 1/(table(alpha) + gammma)
                                let mut value = range_check_16_preprocessing_ref[absolute_row_idx];
                                // it's enough just to multiply by multiplicity
                                value.mul_assign_by_base(&m);

                                value
                            } else {
                                if DEBUG_QUOTIENT {
                                    assert_eq!(
                                        *witness_trace_row.get_unchecked(range_check_16_multiplicities_src),
                                        Mersenne31Field::ZERO,
                                        "multiplicity for range check 16 is not zero for row {}",
                                        absolute_row_idx
                                    );
                                }
                                Mersenne31Quartic::ZERO
                            };

                            stage_2_trace
                                .as_mut_ptr()
                                .add(range_check_16_multiplicities_dst)
                                .cast::<Mersenne31Quartic>()
                                .write(value);
                        }

                        // timestamp
                        {
                            let value = if absolute_row_idx < 1<<TIMESTAMP_COLUMNS_NUM_BITS {
                                let m =
                                    *witness_trace_row.get_unchecked(timestamp_range_check_multiplicities_src);

                                // Read preprocessed column and read rational value 1/(table(alpha) + gammma)
                                let mut value = timestamp_range_check_preprocessing_ref[absolute_row_idx];
                                // it's enough just to multiply by multiplicity
                                value.mul_assign_by_base(&m);

                                value
                            } else {
                                if DEBUG_QUOTIENT {
                                    assert_eq!(
                                        *witness_trace_row.get_unchecked(timestamp_range_check_multiplicities_src),
                                        Mersenne31Field::ZERO,
                                        "multiplicity for timestamp range check is not zero for row {}",
                                        absolute_row_idx
                                    );
                                }

                                Mersenne31Quartic::ZERO
                            };

                            stage_2_trace
                                .as_mut_ptr()
                                .add(timestamp_range_check_multiplicities_dst)
                                .cast::<Mersenne31Quartic>()
                                .write(value);
                        }

                        // generic lookup
                        for i in 0..compiled_circuit
                            .stage_2_layout
                            .intermediate_polys_for_generic_multiplicities
                            .num_elements()
                        {
                            let absolute_table_idx = encoding_tuple_into_lookup_index(
                                i as u32,
                                absolute_row_idx as u32,
                                lookup_encoding_capacity,
                            );

                            let value = if absolute_table_idx < generic_lookup_tables_size {
                                let m = *witness_trace_row
                                    .get_unchecked(generic_lookup_multiplicities_src_start + i);
                                let mut value = generic_lookup_preprocessing_ref[absolute_table_idx];
                                value.mul_assign_by_base(&m);

                                value
                            } else {
                                Mersenne31Quartic::ZERO
                            };

                            stage_2_trace
                                .as_mut_ptr()
                                .add(generic_lookup_multiplicities_dst_start)
                                .cast::<Mersenne31Quartic>()
                                .add(i)
                                .write(value);
                        }

                        // now we process set-equality argument for either delegation requests or processing
                        // in all the cases we have 0 or 1 in the numerator, and need to assemble denominator
                        if handle_delegation_requests {
                            let m = *memory_trace_row
                                .get_unchecked(delegation_request_layout.multiplicity.start());
                            assert!(m == Mersenne31Field::ZERO || m == Mersenne31Field::ONE);

                            let numerator = Mersenne31Quartic::from_base(m);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(delegation_processing_aux_poly.start())
                                .cast::<Mersenne31Quartic>()
                                .write(numerator);

                            let mut timestamp_low = *setup_row.get_unchecked(
                                compiled_circuit
                                    .setup_layout
                                    .timestamp_setup_columns
                                    .start(),
                            );
                            // offset by access number
                            timestamp_low.add_assign(&Mersenne31Field(
                                delegation_request_layout.in_cycle_write_index as u32,
                            ));

                            let mut timestamp_high = *setup_row.get_unchecked(
                                compiled_circuit
                                    .setup_layout
                                    .timestamp_setup_columns
                                    .start()
                                    + 1,
                            );
                            timestamp_high.add_assign(&memory_timestamp_high_from_circuit_idx);

                            let denom = compute_aggregated_key_value(
                                *memory_trace_row.get_unchecked(
                                    delegation_request_layout.delegation_type.start(),
                                ),
                                [
                                    *memory_trace_row.get_unchecked(
                                        delegation_request_layout.abi_mem_offset_high.start(),
                                    ),
                                    timestamp_low,
                                    timestamp_high,
                                ],
                                delegation_challenges.delegation_argument_linearization_challenges,
                                delegation_challenges.delegation_argument_gamma,
                            );

                            batch_inverses_input.push(denom);

                            if DEBUG_QUOTIENT {
                                if m == Mersenne31Field::ZERO {
                                    let valid_convention = memory_trace_row.get_unchecked(
                                        delegation_request_layout.delegation_type.start(),
                                    ).is_zero() && memory_trace_row.get_unchecked(
                                        delegation_request_layout.abi_mem_offset_high.start(),
                                    ).is_zero();
                                    assert!(
                                        valid_convention,
                                        "Delegation request violates convention with inputs: delegation type = {:?}, abi offset = {:?}, timestamp {:?}|{:?}",
                                        memory_trace_row.get_unchecked(
                                            delegation_request_layout.delegation_type.start(),
                                        ),
                                        memory_trace_row.get_unchecked(
                                            delegation_request_layout.abi_mem_offset_high.start(),
                                        ),
                                        timestamp_low,
                                        timestamp_high,
                                    );
                                } else {
                                    println!(
                                        "Delegation request with inputs: delegation type = {:?}, abi offset = {:?}, timestamp {:?}|{:?}",
                                        memory_trace_row.get_unchecked(
                                            delegation_request_layout.delegation_type.start(),
                                        ),
                                        memory_trace_row.get_unchecked(
                                            delegation_request_layout.abi_mem_offset_high.start(),
                                        ),
                                        timestamp_low,
                                        timestamp_high,
                                    );
                                    println!("Contribution = {:?}", denom);
                                }
                            }
                        }

                        if process_delegations {
                            let m = *memory_trace_row
                                .get_unchecked(delegation_processor_layout.multiplicity.start());
                            assert!(m == Mersenne31Field::ZERO || m == Mersenne31Field::ONE);

                            let numerator = Mersenne31Quartic::from_base(m);
                            stage_2_trace
                                .as_mut_ptr()
                                .add(delegation_processing_aux_poly.start())
                                .cast::<Mersenne31Quartic>()
                                .write(numerator);

                            let denom = compute_aggregated_key_value(
                                delegation_type,
                                [
                                    *memory_trace_row.get_unchecked(
                                        delegation_processor_layout.abi_mem_offset_high.start(),
                                    ),
                                    *memory_trace_row.get_unchecked(
                                        delegation_processor_layout.write_timestamp.start(),
                                    ),
                                    *memory_trace_row.get_unchecked(
                                        delegation_processor_layout.write_timestamp.start() + 1,
                                    ),
                                ],
                                delegation_challenges.delegation_argument_linearization_challenges,
                                delegation_challenges.delegation_argument_gamma,
                            );

                            batch_inverses_input.push(denom);

                            if DEBUG_QUOTIENT {
                                if m == Mersenne31Field::ZERO {
                                    let valid_convention = memory_trace_row.get_unchecked(
                                        delegation_processor_layout.abi_mem_offset_high.start(),
                                    ).is_zero() && memory_trace_row.get_unchecked(
                                        delegation_processor_layout.write_timestamp.start(),
                                    ).is_zero() && memory_trace_row.get_unchecked(
                                        delegation_processor_layout.write_timestamp.start() + 1,
                                    ).is_zero();
                                    assert!(
                                        valid_convention,
                                        "Delegation processing violates convention with inputs: delegation type = {:?}, abi offset = {:?}, timestamp {:?}|{:?}",
                                        delegation_type,
                                        memory_trace_row.get_unchecked(
                                            delegation_processor_layout.abi_mem_offset_high.start(),
                                        ),
                                        memory_trace_row.get_unchecked(
                                            delegation_processor_layout.write_timestamp.start(),
                                        ),
                                        memory_trace_row.get_unchecked(
                                            delegation_processor_layout.write_timestamp.start() + 1,
                                        ),
                                    );
                                } else {
                                    println!(
                                        "Delegation processing with inputs: delegation type = {:?}, abi offset = {:?}, timestamp {:?}|{:?}",
                                        delegation_type,
                                        memory_trace_row.get_unchecked(
                                            delegation_processor_layout.abi_mem_offset_high.start(),
                                        ),
                                        memory_trace_row.get_unchecked(
                                            delegation_processor_layout.write_timestamp.start(),
                                        ),
                                        memory_trace_row.get_unchecked(
                                            delegation_processor_layout.write_timestamp.start() + 1,
                                        ),
                                    );
                                    println!("Contribution = {:?}", denom);
                                }
                            }
                        }

                        // Now handle RAM

                        // Numerator is write set, denom is read set

                        // first we write total accumulated from all previous rows
                        let mut memory_argument_dst = stage_2_trace
                            .as_mut_ptr()
                            .add(memory_accumulator_dst_start)
                            .cast::<Mersenne31Quartic>();
                        debug_assert!(memory_argument_dst.is_aligned());

                        // NOTE: we want to accumulate our grand products, but in practice we want to write full running accumulator to the NEXT row,
                        // so we first write a value here, and below we accumulate, to eventually write to the next row

                        memory_argument_dst
                            .add(offset_for_grand_product_accumulation_poly)
                            .write(total_accumulated);

                        // first lazy init from read set / lazy teardown

                        // and memory grand product accumulation identities
                        let mut numerator_acc_value;
                        let mut denom_acc_value;

                        // sequence of keys is in general is_reg || address_low || address_high || timestamp low || timestamp_high || value_low || value_high
                        if process_shuffle_ram_init {
                            assert!(
                                compiled_circuit.memory_layout.shuffle_ram_access_sets.len() > 0
                            );
                            let mut numerator = memory_argument_challenges.memory_argument_gamma;

                            let address_low = *memory_trace_row.get_unchecked(
                                shuffle_ram_inits_and_teardowns
                                    .lazy_init_addresses_columns
                                    .start(),
                            );
                            let mut t = memory_argument_challenges
                                .memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                            t.mul_assign_by_base(&address_low);
                            numerator.add_assign(&t);

                            let address_high = *memory_trace_row.get_unchecked(
                                shuffle_ram_inits_and_teardowns
                                    .lazy_init_addresses_columns
                                    .start()
                                    + 1,
                            );
                            let mut t = memory_argument_challenges
                                .memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                            t.mul_assign_by_base(&address_high);
                            numerator.add_assign(&t);

                            numerator_acc_value = numerator;

                            // NOTE: we write accumulators
                            memory_argument_dst.write(numerator_acc_value);
                            memory_argument_dst = memory_argument_dst.add(1);

                            // lazy init and teardown sets have same addresses
                            let mut denom = numerator;

                            let value_low = *memory_trace_row.get_unchecked(
                                shuffle_ram_inits_and_teardowns
                                    .lazy_teardown_values_columns
                                    .start(),
                            );
                            let mut t = memory_argument_challenges
                                .memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                            t.mul_assign_by_base(&value_low);
                            denom.add_assign(&t);

                            let value_high = *memory_trace_row.get_unchecked(
                                shuffle_ram_inits_and_teardowns
                                    .lazy_teardown_values_columns
                                    .start()
                                    + 1,
                            );
                            let mut t = memory_argument_challenges
                                .memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                            t.mul_assign_by_base(&value_high);
                            denom.add_assign(&t);

                            let timestamp_low = *memory_trace_row.get_unchecked(
                                shuffle_ram_inits_and_teardowns
                                    .lazy_teardown_timestamps_columns
                                    .start(),
                            );
                            let mut t = memory_argument_challenges
                                .memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            t.mul_assign_by_base(&timestamp_low);
                            denom.add_assign(&t);

                            let timestamp_high = *memory_trace_row.get_unchecked(
                                shuffle_ram_inits_and_teardowns
                                    .lazy_teardown_timestamps_columns
                                    .start()
                                    + 1,
                            );
                            let mut t = memory_argument_challenges
                                .memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign_by_base(&timestamp_high);
                            denom.add_assign(&t);

                            denom_acc_value = denom;

                            batch_inverses_input.push(denom_acc_value);
                        } else {
                            // we do not have any logic and only have to initialize products
                            numerator_acc_value = Mersenne31Quartic::ONE;
                            denom_acc_value = Mersenne31Quartic::ONE;
                        }

                        // we assembled P(x) = write init set / read teardown set, or trivial init. Now we add contributions fro
                        // either individual or batched RAM accesses

                        // timestamp high is STATIC from the index of access, and setup value
                        assert_eq!(
                            compiled_circuit
                                .setup_layout
                                .timestamp_setup_columns
                                .width(),
                            2
                        );

                        // now we can continue to accumulate
                        for (access_idx, memory_access_columns) in compiled_circuit
                            .memory_layout
                            .shuffle_ram_access_sets
                            .iter()
                            .enumerate()
                        {
                            match memory_access_columns {
                                ShuffleRamQueryColumns::Readonly(columns) => {
                                    let address_contribution =
                                        stage_2_shuffle_ram_assemble_address_contribution(
                                            memory_trace_row,
                                            memory_access_columns,
                                            &memory_argument_challenges,
                                        );

                                    debug_assert_eq!(columns.read_value.width(), 2);

                                    stage_2_shuffle_ram_assemble_read_contribution(
                                        memory_trace_row,
                                        setup_row,
                                        &address_contribution,
                                        &columns,
                                        compiled_circuit.setup_layout.timestamp_setup_columns,
                                        &memory_argument_challenges,
                                        access_idx,
                                        memory_timestamp_high_from_circuit_idx,
                                        &mut numerator_acc_value,
                                        &mut denom_acc_value,
                                    );

                                    // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                    memory_argument_dst.write(numerator_acc_value);
                                    memory_argument_dst = memory_argument_dst.add(1);

                                    // and keep denominators for batch inverse
                                    batch_inverses_input.push(denom_acc_value);
                                }
                                ShuffleRamQueryColumns::Write(columns) => {
                                    let address_contribution =
                                        stage_2_shuffle_ram_assemble_address_contribution(
                                            memory_trace_row,
                                            memory_access_columns,
                                            &memory_argument_challenges,
                                        );

                                    stage_2_shuffle_ram_assemble_write_contribution(
                                        memory_trace_row,
                                        setup_row,
                                        &address_contribution,
                                        &columns,
                                        compiled_circuit.setup_layout.timestamp_setup_columns,
                                        &memory_argument_challenges,
                                        access_idx,
                                        memory_timestamp_high_from_circuit_idx,
                                        &mut numerator_acc_value,
                                        &mut denom_acc_value,
                                    );

                                    // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                    memory_argument_dst.write(numerator_acc_value);
                                    memory_argument_dst = memory_argument_dst.add(1);

                                    // and keep denominators for batch inverse
                                    batch_inverses_input.push(denom_acc_value);
                                }
                            }
                        }

                        let delegation_write_timestamp_contribution = if process_batch_ram_access || process_registers_and_indirect_access {
                            let write_timestamp = delegation_processor_layout.write_timestamp;

                            let write_timestamp_low = *memory_trace_row.get_unchecked(write_timestamp.start());
                            let mut write_timestamp_contribution = memory_argument_challenges
                                .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            write_timestamp_contribution.mul_assign_by_base(&write_timestamp_low);

                            let write_timestamp_high = *memory_trace_row.get_unchecked(write_timestamp.start() + 1);
                            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            t.mul_assign_by_base(&write_timestamp_high);
                            write_timestamp_contribution.add_assign(&t);

                            write_timestamp_contribution
                        } else {
                            Mersenne31Quartic::ZERO
                        };

                        if process_batch_ram_access {
                            assert!(process_delegations);

                            let abi_mem_offset_high =
                                delegation_processor_layout.abi_mem_offset_high;

                            // alternatively we may have batch RAM access
                            for (offset, memory_access_columns) in compiled_circuit
                                .memory_layout
                                .batched_ram_accesses
                                .iter()
                                .enumerate()
                            {
                                // we must compute offsets in u32 words
                                let offset = offset * std::mem::size_of::<u32>();

                                match memory_access_columns {
                                    BatchedRamAccessColumns::ReadAccess {
                                        read_timestamp,
                                        read_value,
                                    } => {
                                        stage_2_batched_ram_assemble_read_contribution(
                                            memory_trace_row,
                                            *read_value,
                                            *read_timestamp,
                                            &delegation_write_timestamp_contribution,
                                            abi_mem_offset_high,
                                            offset,
                                            &memory_argument_challenges,
                                            &mut numerator_acc_value,
                                            &mut denom_acc_value,
                                        );

                                        // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                        memory_argument_dst.write(numerator_acc_value);
                                        memory_argument_dst = memory_argument_dst.add(1);

                                        // and keep denominators for batch inverse
                                        batch_inverses_input.push(denom_acc_value);
                                    }
                                    BatchedRamAccessColumns::WriteAccess {
                                        read_timestamp,
                                        read_value,
                                        write_value,
                                    } => {
                                        stage_2_batched_ram_assemble_write_contribution(
                                            memory_trace_row,
                                            *read_value,
                                            *write_value,
                                            *read_timestamp,
                                            &delegation_write_timestamp_contribution,
                                            abi_mem_offset_high,
                                            offset,
                                            &memory_argument_challenges,
                                            &mut numerator_acc_value,
                                            &mut denom_acc_value,
                                        );

                                        // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                        memory_argument_dst.write(numerator_acc_value);
                                        memory_argument_dst = memory_argument_dst.add(1);

                                        // and keep denominators for batch inverse
                                        batch_inverses_input.push(denom_acc_value);
                                    }
                                }
                            }
                        }

                        if process_registers_and_indirect_access {
                            assert!(process_delegations);

                            // alternatively we may have batch RAM access
                            for register_access_columns in compiled_circuit
                                .memory_layout
                                .register_and_indirect_accesses
                                .iter()
                            {
                                let base_value = match &register_access_columns.register_access {
                                    RegisterAccessColumns::ReadAccess {
                                        read_timestamp,
                                        read_value,
                                        register_index,
                                    } => {
                                        let base_value = stage_2_register_access_assemble_read_contribution(
                                            memory_trace_row,
                                            *read_value,
                                            *read_timestamp,
                                            &delegation_write_timestamp_contribution,
                                            *register_index,
                                            &memory_argument_challenges,
                                            &mut numerator_acc_value,
                                            &mut denom_acc_value,
                                        );

                                        // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                        memory_argument_dst.write(numerator_acc_value);
                                        memory_argument_dst = memory_argument_dst.add(1);

                                        // and keep denominators for batch inverse
                                        batch_inverses_input.push(denom_acc_value);

                                        base_value
                                    }
                                    RegisterAccessColumns::WriteAccess {
                                        read_timestamp,
                                        read_value,
                                        write_value,
                                        register_index,
                                    } => {
                                        let base_value = stage_2_register_access_assemble_write_contribution(
                                            memory_trace_row,
                                            *read_value,
                                            *write_value,
                                            *read_timestamp,
                                            &delegation_write_timestamp_contribution,
                                            *register_index,
                                            &memory_argument_challenges,
                                            &mut numerator_acc_value,
                                            &mut denom_acc_value,
                                        );

                                        // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                        memory_argument_dst.write(numerator_acc_value);
                                        memory_argument_dst = memory_argument_dst.add(1);

                                        // and keep denominators for batch inverse
                                        batch_inverses_input.push(denom_acc_value);

                                        base_value
                                    }
                                };

                                for indirect_access_columns in register_access_columns.indirect_accesses
                                    .iter()
                                {
                                    match indirect_access_columns {
                                        IndirectAccessColumns::ReadAccess {
                                            read_timestamp,
                                            read_value,
                                            offset,
                                            ..
                                        } => {
                                            debug_assert!(*offset < 1<<16);
                                            stage_2_indirect_access_assemble_read_contribution(
                                                memory_trace_row,
                                                *read_value,
                                                *read_timestamp,
                                                &delegation_write_timestamp_contribution,
                                                base_value,
                                                *offset as u16,
                                                &memory_argument_challenges,
                                                &mut numerator_acc_value,
                                                &mut denom_acc_value,
                                            );

                                            // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                            memory_argument_dst.write(numerator_acc_value);
                                            memory_argument_dst = memory_argument_dst.add(1);

                                            // and keep denominators for batch inverse
                                            batch_inverses_input.push(denom_acc_value);
                                        }
                                        IndirectAccessColumns::WriteAccess {
                                            read_timestamp,
                                            read_value,
                                            write_value,
                                            offset,
                                            ..
                                        } => {
                                            debug_assert!(*offset < 1<<16);
                                            stage_2_indirect_access_assemble_write_contribution(
                                                memory_trace_row,
                                                *read_value,
                                                *write_value,
                                                *read_timestamp,
                                                &delegation_write_timestamp_contribution,
                                                base_value,
                                                *offset as u16,
                                                &memory_argument_challenges,
                                                &mut numerator_acc_value,
                                                &mut denom_acc_value,
                                            );

                                            // NOTE: here we write a chain of accumulator values, and not numerators themselves
                                            memory_argument_dst.write(numerator_acc_value);
                                            memory_argument_dst = memory_argument_dst.add(1);

                                            // and keep denominators for batch inverse
                                            batch_inverses_input.push(denom_acc_value);
                                        }
                                    };
                                }
                            }
                        }

                        assert_eq!(num_batch_inverses, batch_inverses_input.len());
                        batch_inverse_with_buffer(
                            &mut batch_inverses_input,
                            &mut batch_inverses_buffer,
                        );

                        total_accumulated.mul_assign(&numerator_acc_value);
                        let total_accumulated_denom =
                            batch_inverses_input.last().copied().unwrap_unchecked();
                        total_accumulated.mul_assign(&total_accumulated_denom);

                        assert_eq!(
                            memory_argument_dst,
                            stage_2_trace
                                .as_mut_ptr()
                                .add(memory_accumulator_dst_start)
                                .cast::<Mersenne31Quartic>()
                                .add(offset_for_grand_product_accumulation_poly)
                        );

                        // now we save total accumulated for the next step, and write down batch inverses

                        // write batch inversed range check 16 elements
                        let mut dst = stage_2_trace
                            .as_mut_ptr()
                            .add(offset_for_continuous_batch_inverses_write)
                            .cast::<Mersenne31Quartic>();
                        assert!(dst.is_aligned());
                        for denom_value in batch_inverses_input.iter() {
                            let mut numerator = dst.read();
                            numerator.mul_assign(&denom_value);
                            dst.write(numerator);
                            dst = dst.add(1);
                        }

                        exec_trace_view.advance_row();
                        setup_trace_view.advance_row();
                        stage_2_trace_view.advance_row();
                        lookup_indexes_view.advance_row();
                    }

                    // since we skip last row in global boundary over trace length,
                    // we should still write it if we are working on the very last chunk
                    if chunk_start + chunk_size == trace_len - 1 {
                        // we will be at the very last row here
                        let stage_2_trace = stage_2_trace_view.current_row();
                        let dst_ptr = stage_2_trace.as_mut_ptr();

                        let memory_argument_dst = dst_ptr
                            .add(memory_accumulator_dst_start)
                            .cast::<Mersenne31Quartic>();
                        assert!(memory_argument_dst.is_aligned());

                        memory_argument_dst
                            .add(offset_for_grand_product_accumulation_poly)
                            .write(total_accumulated);
                    }

                    // this is a full running grand product over our chunk of rows
                    grand_product_accumulator[0] = total_accumulated;
                });
            }
        });
    }

    println!("Generation of stage 2 trace took {:?}", now.elapsed());
    drop(lookup_mapping);

    let offset_for_grand_product_poly = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .get_range(offset_for_grand_product_accumulation_poly)
        .start;

    // unfortunately we have to go over it again, to finish grand product accumulation
    // here we should wait for all threads to finish and go over them again in maybe not too cache convenient manner
    if worker.num_cores > 1 {
        let mut products = vec![Mersenne31Quartic::ONE; worker.num_cores];
        let mut running_product = Mersenne31Quartic::ONE;
        for (dst, src) in products.iter_mut().zip(grand_product_accumulators.iter()) {
            dst.mul_assign(&running_product);
            running_product.mul_assign(&src);
        }

        // NOTE on length here - our final accumulated value is at the last row, so we do full trace len, without skipping last one

        unsafe {
            worker.scope(trace_len - 1, |scope, geometry| {
                let mut accumulators_srcs = products.chunks(1);
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let range = chunk_start..(chunk_start + chunk_size);
                    let mut stage_2_trace_view = stage_2_trace.row_view(range.clone());
                    let accumulator_value = accumulators_srcs.next().unwrap()[0];

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for _i in 0..chunk_size {
                            let stage_2_trace = stage_2_trace_view.current_row();
                            let dst_ptr = stage_2_trace
                                .as_mut_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(dst_ptr.is_aligned());
                            let mut value = dst_ptr.read();
                            value.mul_assign(&accumulator_value);
                            dst_ptr.write(value);

                            stage_2_trace_view.advance_row();
                        }
                    });
                }
            });

            // The last element is processed separately to guarantee ranges correctness
            let accumulator_value = products.last().unwrap();
            let mut stage_2_trace_view = stage_2_trace.row_view(trace_len - 1..trace_len);
            let last_row = stage_2_trace_view.current_row();
            let dst_ptr = last_row
                .as_mut_ptr()
                .add(offset_for_grand_product_poly)
                .cast::<Mersenne31Quartic>();
            let mut value = dst_ptr.read();
            value.mul_assign(&accumulator_value);
            dst_ptr.write(value);
        }
    };

    // we will re-read the trace for it
    let t = stage_2_trace.row_view(trace_len - 1..trace_len);
    let row = t.current_row_ref();
    let grand_product_accumulator = unsafe {
        let ptr = row
            .as_ptr()
            .add(offset_for_grand_product_poly)
            .cast::<Mersenne31Quartic>();
        debug_assert!(ptr.is_aligned());

        ptr.read()
    };

    // it must be last one
    assert_eq!(offset_for_grand_product_poly, stage_2_trace.width() - 4);

    // adjust over main domain. Note here: we have some base field columns, where we want to have c0 == 0 for basefield
    // shifted code in other domains
    adjust_to_zero_c0_var_length(
        &mut stage_2_trace,
        0..compiled_circuit.stage_2_layout.num_base_field_polys(),
        worker,
    );

    // we also want to adjust to zero sum the delegaiton requests poly to have simple constraint
    if handle_delegation_requests || process_delegations {
        let delegation_processing_aux_poly = compiled_circuit
            .stage_2_layout
            .delegation_processing_aux_poly
            .as_ref()
            .unwrap();
        adjust_to_zero_c0_var_length(
            &mut stage_2_trace,
            delegation_processing_aux_poly.full_range(),
            worker,
        );
    }

    // so our sum over the delegation requests is just -last element
    let mut sum_over_delegation_poly = unsafe {
        if handle_delegation_requests || process_delegations {
            let trace = stage_2_trace.row_view(trace_len - 1..trace_len);
            let offset = delegation_processing_aux_poly.start();
            let ptr = trace
                .current_row_ref()
                .as_ptr()
                .add(offset)
                .cast::<Mersenne31Quartic>();
            assert!(ptr.is_aligned());

            ptr.read()
        } else {
            Mersenne31Quartic::ZERO
        }
    };
    sum_over_delegation_poly.negate();

    let mut trace = stage_2_trace.row_view(trace_len - 1..trace_len);
    let row = trace.current_row();

    // and we should also zero-out last row for all intermediate polys that are part of our local lookup argument
    for set in [
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_range_check_16
            .ext_4_field_oracles,
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_timestamp_range_checks
            .ext_4_field_oracles,
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup,
        compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_range_check_16_multiplicity,
        compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_timestamp_range_check_multiplicity,
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_multiplicities,
    ]
    .into_iter()
    {
        for range in set.iter() {
            unsafe {
                let ptr = row
                    .as_mut_ptr()
                    .add(range.start)
                    .cast::<Mersenne31Quartic>();
                assert!(ptr.is_aligned());
                ptr.write(Mersenne31Quartic::ZERO);
            }
        }
    }

    // also zero out lazy init aux poly, as it contributes to the lookup
    if let Some(lazy_init_address_range_check_16) = compiled_circuit
        .stage_2_layout
        .lazy_init_address_range_check_16
        .as_ref()
    {
        let set = lazy_init_address_range_check_16.ext_4_field_oracles;
        for range in set.iter() {
            unsafe {
                let ptr = row
                    .as_mut_ptr()
                    .add(range.start)
                    .cast::<Mersenne31Quartic>();
                assert!(ptr.is_aligned());
                ptr.write(Mersenne31Quartic::ZERO);
            }
        }
    }

    if DEBUG_QUOTIENT {
        // check that all inputs into range checks are indeed range checked
        let mut exec_trace_view = stage_1_output.ldes[0].trace.row_view(0..(trace_len - 1));

        for _ in 0..trace_len - 1 {
            let (witness_row, memory_row) = unsafe {
                exec_trace_view
                    .current_row_ref()
                    .split_at_unchecked(stage_1_output.num_witness_columns)
            };
            for el in range_check_16_width_1_lookups_access.iter() {
                let a = ColumnAddress::WitnessSubtree(el.a_col);
                let b = ColumnAddress::WitnessSubtree(el.b_col);
                let a = read_value(a, witness_row, memory_row);
                let b = read_value(b, witness_row, memory_row);

                // high granularity check, 16 bits only
                assert!(
                    a.to_reduced_u32() < (1 << 16),
                    "failed at lookup set {:?}",
                    el
                );
                assert!(
                    b.to_reduced_u32() < (1 << 16),
                    "failed at lookup set {:?}",
                    el
                );
            }

            exec_trace_view.advance_row();
        }
    }

    if DEBUG_QUOTIENT {
        unsafe {
            let mut trace = stage_2_trace.row_view(0..trace_len);
            let mut next = Mersenne31Quartic::ONE;
            for row in 0..(trace_len - 1) {
                let previous = trace
                    .current_row_ref()
                    .as_ptr()
                    .add(offset_for_grand_product_poly - 4)
                    .cast::<Mersenne31Quartic>()
                    .read();
                let mut acc = trace
                    .current_row_ref()
                    .as_ptr()
                    .add(offset_for_grand_product_poly)
                    .cast::<Mersenne31Quartic>()
                    .read();
                assert_eq!(acc, next, "diverged at row {}", row);
                acc.mul_assign(&previous);
                next = acc;
                trace.advance_row();
            }

            let acc = trace
                .current_row_ref()
                .as_ptr()
                .add(offset_for_grand_product_poly)
                .cast::<Mersenne31Quartic>()
                .read();
            assert_eq!(acc, grand_product_accumulator);
            assert_eq!(next, grand_product_accumulator);
        }

        unsafe {
            // check sum over aux lookup polys
            let mut trace = stage_2_trace.row_view(0..trace_len);
            let mut sums = vec![Mersenne31Quartic::ZERO; 3];
            for row_idx in 0..trace_len {
                let row = trace.current_row_ref();
                let last_row = row_idx == trace_len - 1;
                let mut dst_iter = sums.iter_mut();

                // range check 16
                {
                    let mut term_contribution = Mersenne31Quartic::ZERO;

                    let multiplicity_aux = row
                        .as_ptr()
                        .add(
                            compiled_circuit
                                .stage_2_layout
                                .intermediate_poly_for_range_check_16_multiplicity
                                .get_range(0)
                                .start,
                        )
                        .cast::<Mersenne31Quartic>()
                        .read();
                    term_contribution.add_assign(&multiplicity_aux);

                    if last_row {
                        assert_eq!(multiplicity_aux, Mersenne31Quartic::ZERO);
                    }

                    if row_idx >= 1 << 16 {
                        assert_eq!(multiplicity_aux, Mersenne31Quartic::ZERO);
                    }

                    let bound = compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_range_check_16
                        .num_pairs;
                    for i in 0..bound {
                        let el = row
                            .as_ptr()
                            .add(
                                compiled_circuit
                                    .stage_2_layout
                                    .intermediate_polys_for_range_check_16
                                    .ext_4_field_oracles
                                    .get_range(i)
                                    .start,
                            )
                            .cast::<Mersenne31Quartic>()
                            .read();
                        if last_row {
                            assert_eq!(el, Mersenne31Quartic::ZERO);
                        }
                        term_contribution.sub_assign(&el);
                    }
                    // add lazy init value
                    if let Some(lazy_init_address_range_check_16) = compiled_circuit
                        .stage_2_layout
                        .lazy_init_address_range_check_16
                    {
                        let el = row
                            .as_ptr()
                            .add(
                                lazy_init_address_range_check_16
                                    .ext_4_field_oracles
                                    .get_range(0)
                                    .start,
                            )
                            .cast::<Mersenne31Quartic>()
                            .read();
                        if last_row {
                            assert_eq!(el, Mersenne31Quartic::ZERO);
                        }
                        term_contribution.sub_assign(&el);
                    }
                    if let Some(_remainder) =
                        compiled_circuit.stage_2_layout.remainder_for_range_check_16
                    {
                        todo!();
                    }

                    dst_iter.next().unwrap().add_assign(&term_contribution);
                }

                // timestamp range check
                {
                    let mut term_contribution = Mersenne31Quartic::ZERO;

                    let multiplicity_aux = row
                        .as_ptr()
                        .add(
                            compiled_circuit
                                .stage_2_layout
                                .intermediate_poly_for_timestamp_range_check_multiplicity
                                .get_range(0)
                                .start,
                        )
                        .cast::<Mersenne31Quartic>()
                        .read();
                    term_contribution.add_assign(&multiplicity_aux);

                    if last_row {
                        assert_eq!(multiplicity_aux, Mersenne31Quartic::ZERO);
                    }

                    if row_idx >= 1 << TIMESTAMP_COLUMNS_NUM_BITS {
                        assert_eq!(multiplicity_aux, Mersenne31Quartic::ZERO);
                    }

                    let bound = compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_timestamp_range_checks
                        .num_pairs;
                    for i in 0..bound {
                        let el = row
                            .as_ptr()
                            .add(
                                compiled_circuit
                                    .stage_2_layout
                                    .intermediate_polys_for_timestamp_range_checks
                                    .ext_4_field_oracles
                                    .get_range(i)
                                    .start,
                            )
                            .cast::<Mersenne31Quartic>()
                            .read();
                        if last_row {
                            assert_eq!(el, Mersenne31Quartic::ZERO);
                        }
                        term_contribution.sub_assign(&el);
                    }

                    dst_iter.next().unwrap().add_assign(&term_contribution);
                }

                // generic lookup
                {
                    let mut term_contribution = Mersenne31Quartic::ZERO;
                    for i in 0..compiled_circuit
                        .setup_layout
                        .generic_lookup_setup_columns
                        .num_elements()
                    {
                        let multiplicity_aux = row
                            .as_ptr()
                            .add(
                                compiled_circuit
                                    .stage_2_layout
                                    .intermediate_polys_for_generic_multiplicities
                                    .get_range(i)
                                    .start,
                            )
                            .cast::<Mersenne31Quartic>()
                            .read();
                        if last_row {
                            assert_eq!(multiplicity_aux, Mersenne31Quartic::ZERO);
                        }
                        term_contribution.add_assign(&multiplicity_aux);
                    }

                    // subtract all corresponding intermediates
                    for i in 0..compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_generic_lookup
                        .num_elements()
                    {
                        let el = row
                            .as_ptr()
                            .add(
                                compiled_circuit
                                    .stage_2_layout
                                    .intermediate_polys_for_generic_lookup
                                    .get_range(i)
                                    .start,
                            )
                            .cast::<Mersenne31Quartic>()
                            .read();
                        if last_row {
                            assert_eq!(el, Mersenne31Quartic::ZERO);
                        }
                        term_contribution.sub_assign(&el);
                    }

                    dst_iter.next().unwrap().add_assign(&term_contribution);
                }

                assert!(dst_iter.next().is_none());

                if row_idx == trace_len - 2 {
                    // all rows except last
                    for (column, sum) in sums.iter().enumerate() {
                        let column_name = match column {
                            0 => "range checks 16",
                            1 => "timestamp range checks",
                            2 => "generic lookups",
                            _ => unreachable!(),
                        };
                        if *sum != Mersenne31Quartic::ZERO {
                            println!(
                                "invalid lookup accumulation for column of {}, lookup diverged",
                                column_name
                            );
                        }
                    }
                }

                trace.advance_row();
            }

            // all rows

            for (column, sum) in sums.iter().enumerate() {
                let column_name = match column {
                    0 => "range checks 16",
                    1 => "timestamp range checks",
                    2 => "generic lookups",
                    _ => unreachable!(),
                };
                assert_eq!(
                    *sum,
                    Mersenne31Quartic::ZERO,
                    "invalid for column of {}, lookup diverged",
                    column_name
                );
            }
        }
    }

    // now we can LDE and make oracles
    let ldes = compute_wide_ldes(
        stage_2_trace,
        &twiddles,
        &lde_precomputations,
        0,
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

    let output = SecondStageOutput {
        ldes,
        trees,
        lookup_argument_linearization_challenges,
        lookup_argument_gamma,
        grand_product_accumulator,
        sum_over_delegation_poly,
    };

    output
}
