use super::*;
use crate::utils::*;
use ::field::Mersenne31Field;

pub(crate) fn preprocess_lookup_tables<const N: usize, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    trace_len: usize,
    setup_trace: &RowMajorTrace<Mersenne31Field, N, A>,
    lookup_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
    lookup_argument_gamma: Mersenne31Quartic,
    worker: &Worker,
) -> Vec<Mersenne31Quartic, A> {
    let generic_lookup_tables_size = compiled_circuit.total_tables_size;

    if generic_lookup_tables_size > 0 {
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

                            let (column, row) = lookup_index_into_encoding_tuple(
                                absolute_table_idx,
                                lookup_encoding_capacity,
                            );
                            let row = setup_trace.get_row(row as usize);
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

        generic_lookup_preprocessing
    } else {
        Vec::new_in(A::default())
    }
}

pub(crate) fn preprocess_range_check_16_table<A: GoodAllocator>(
    trace_len: usize,
    lookup_argument_gamma: Mersenne31Quartic,
    worker: &Worker,
) -> Vec<Mersenne31Quartic, A> {
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

    range_check_16_preprocessing
}

pub(crate) fn preprocess_timestamp_range_check_table<A: GoodAllocator>(
    trace_len: usize,
    lookup_argument_gamma: Mersenne31Quartic,
    worker: &Worker,
) -> Vec<Mersenne31Quartic, A> {
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

    timestamp_range_check_preprocessing
}

pub(crate) fn preprocess_executor_family_decoder_table<const N: usize, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    trace_len: usize,
    setup_trace: &RowMajorTrace<Mersenne31Field, N, A>,
    decoder_table_linearization_challenges:[Mersenne31Quartic; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_table_gamma: Mersenne31Quartic,
    worker: &Worker,
) -> Vec<Mersenne31Quartic, A> {
    if compiled_circuit
        .setup_layout
        .preprocessed_decoder_setup_columns
        .num_elements()
        > 0
    {
        let executor_family_decoder_table_size =
            compiled_circuit.executor_family_decoder_table_size;
        assert!(trace_len > executor_family_decoder_table_size);

        let mut decoder_preprocessing: Vec<Mersenne31Quartic, A> =
            Vec::with_capacity_in(executor_family_decoder_table_size, A::default());
        let mut dst =
            &mut decoder_preprocessing.spare_capacity_mut()[..executor_family_decoder_table_size];

        unsafe {
            worker.scope(executor_family_decoder_table_size, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let (chunk, rest) = dst.split_at_mut(chunk_size);
                    dst = rest;

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let mut batch_inverse_buffer = vec![Mersenne31Quartic::ZERO; chunk.len()];
                        for i in 0..chunk_size {
                            let absolute_row_idx = chunk_start + i;

                            let row = setup_trace.get_row(absolute_row_idx as usize);
                            let src = row.get_unchecked(
                                compiled_circuit
                                    .setup_layout
                                    .preprocessed_decoder_setup_columns
                                    .get_range(0)
                            );
                            assert_eq!(src.len(), EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH);

                            let el0 = src[0];
                            let rest: [Mersenne31Field; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES] = std::array::from_fn(|j| {
                                src[j + 1]
                            });

                            let denom = compute_aggregated_key_value(
                                el0,
                                rest,
                                decoder_table_linearization_challenges,
                                decoder_table_gamma,
                            );

                            chunk[i].write(denom);
                        }

                        // batch inverse
                        let buffer = chunk.assume_init_mut();
                        let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                        assert!(all_nonzero);
                    });
                }

                assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << 20, worker.get_num_cores());
            });
        }

        unsafe {
            decoder_preprocessing.set_len(executor_family_decoder_table_size);
        }

        decoder_preprocessing
    } else {
        Vec::new_in(A::default())
    }
}

pub(crate) unsafe fn stage2_process_range_check_16_trivial_checks(
    witness_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    range_check_16_preprocessing_ref: &[Mersenne31Quartic],
    range_check_16_width_1_lookups_access_ref: &[LookupWidth1SourceDestInformation],
) {
    // range check 16 are special as those are width-1
    for lookup_set in range_check_16_width_1_lookups_access_ref.iter() {
        let a = *witness_trace_row.get_unchecked(lookup_set.a_col);
        let b = *witness_trace_row.get_unchecked(lookup_set.b_col);
        if DEBUG_QUOTIENT {
            assert!(
                a.to_reduced_u32() < 1 << 16,
                "value {} is beyond the range",
                a.to_reduced_u32()
            );
            assert!(
                b.to_reduced_u32() < 1 << 16,
                "value {} is beyond the range",
                b.to_reduced_u32()
            );
        }

        let mut c = a;
        c.mul_assign(&b);

        stage_2_trace
            .as_mut_ptr()
            .add(lookup_set.base_field_quadratic_oracle_col)
            .write(c);

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
}

pub(crate) unsafe fn stage2_process_range_check_16_expressions(
    witness_trace_row: &[Mersenne31Field],
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    range_check_16_preprocessing_ref: &[Mersenne31Quartic],
    range_check_16_width_1_lookups_access_via_expressions_ref: &[LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>],
) {
    // then we have some non-trivial expressions too
    for lookup_set in range_check_16_width_1_lookups_access_via_expressions_ref.iter() {
        let LookupExpression::Expression(a) = &lookup_set.a_expr else {
            unreachable!()
        };
        let LookupExpression::Expression(b) = &lookup_set.b_expr else {
            unreachable!()
        };
        let a = a.evaluate_at_row_on_main_domain(witness_trace_row, memory_trace_row);
        let b = b.evaluate_at_row_on_main_domain(witness_trace_row, memory_trace_row);
        if DEBUG_QUOTIENT {
            assert!(
                a.to_reduced_u32() < 1 << 16,
                "value {} is beyond the range",
                a.to_reduced_u32()
            );
            assert!(
                b.to_reduced_u32() < 1 << 16,
                "value {} is beyond the range",
                b.to_reduced_u32()
            );
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
}

pub(crate) unsafe fn stage2_process_timestamp_range_check_expressions(
    witness_trace_row: &[Mersenne31Field],
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    timestamp_range_check_preprocessing_ref: &[Mersenne31Quartic],
    timestamp_range_check_width_1_lookups_access_via_expressions_ref: &[LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>],
) {
    // then expressions for the timestamps
    for lookup_set in timestamp_range_check_width_1_lookups_access_via_expressions_ref.iter() {
        let LookupExpression::Expression(a) = &lookup_set.a_expr else {
            unreachable!()
        };
        let LookupExpression::Expression(b) = &lookup_set.b_expr else {
            unreachable!()
        };
        let a = a.evaluate_at_row_on_main_domain(witness_trace_row, memory_trace_row);
        let b = b.evaluate_at_row_on_main_domain(witness_trace_row, memory_trace_row);
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
}

pub(crate) unsafe fn stage2_process_timestamp_range_check_expressions_with_extra_timestamp_contribution(
    witness_trace_row: &[Mersenne31Field],
    memory_trace_row: &[Mersenne31Field],
    setup_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    timestamp_range_check_preprocessing_ref: &[Mersenne31Quartic],
    timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref: &[LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>],
    memory_timestamp_high_from_circuit_idx: Mersenne31Field,
) {
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
}

pub(crate) unsafe fn stage2_process_generic_lookup_intermediate_polys(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    stage_2_trace: &mut [Mersenne31Field],
    lookup_indexes_view_row: &[u32],
    generic_lookup_preprocessing_ref: &[Mersenne31Quartic],
    width_3_intermediate_polys_offset: usize,
    generic_lookup_tables_size: usize,
) {
    // NOTE: as we have preprocessed the lookup setup, we can just pick a value by index

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

        let preprocessed_value =
            *generic_lookup_preprocessing_ref.get_unchecked(absolute_table_idx as usize);
        dst_ptr.write(preprocessed_value);

        dst_ptr = dst_ptr.add(1);
    }
}

pub(crate) unsafe fn stage2_process_executor_family_decoder_intermediate_poly(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    decoder_preprocessing_ref: &[Mersenne31Quartic],
) {
    // NOTE: as we have preprocessed the lookup setup, we can just pick a value by index

    let offset = compiled_circuit
        .stage_2_layout
        .intermediate_poly_for_decoder_accesses
        .start();

    let dst_ptr = stage_2_trace
        .as_mut_ptr()
        .add(offset)
        .cast::<Mersenne31Quartic>();
    assert!(dst_ptr.is_aligned());

    let intermediate_state_layout = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap();

    let predicate = memory_trace_row
        .get_unchecked(intermediate_state_layout.execute.start())
        .as_boolean();
    let pc_start = intermediate_state_layout.pc.start();

    // then it's included into the intermediate poly, otherwise it's 0
    if predicate {
        let pc_low = memory_trace_row.get_unchecked(pc_start).to_reduced_u32();
        let pc_high = memory_trace_row
            .get_unchecked(pc_start + 1)
            .to_reduced_u32();
        let pc = (pc_high << 16) | pc_low;

        if DEBUG_QUOTIENT {
            assert!(pc % 4 == 0);
        }

        let idx = pc / 4;
        let value = decoder_preprocessing_ref[idx as usize];
        dst_ptr.write(value);
    } else {
        dst_ptr.write(Mersenne31Quartic::ZERO);
    }
}

pub(crate) unsafe fn stage2_process_range_check_16_multiplicity_intermediate_poly(
    witness_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    range_check_16_preprocessing_ref: &[Mersenne31Quartic],
    range_check_16_multiplicities_src: usize,
    range_check_16_multiplicities_dst: usize,
    absolute_row_idx: usize,
) {
    let value = if absolute_row_idx < 1 << 16 {
        let m = *witness_trace_row.get_unchecked(range_check_16_multiplicities_src);

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

pub(crate) unsafe fn stage2_process_timestamp_range_check_multiplicity_intermediate_poly(
    witness_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    timestamp_range_check_preprocessing_ref: &[Mersenne31Quartic],
    timestamp_range_check_multiplicities_src: usize,
    timestamp_range_check_multiplicities_dst: usize,
    absolute_row_idx: usize,
) {
    let value = if absolute_row_idx < 1 << TIMESTAMP_COLUMNS_NUM_BITS {
        let m = *witness_trace_row.get_unchecked(timestamp_range_check_multiplicities_src);

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

pub(crate) unsafe fn stage2_process_executor_family_decoder_multiplicity_intermediate_poly(
    witness_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    decoder_table_preprocessing_ref: &[Mersenne31Quartic],
    decoder_table_multiplicities_src: usize,
    decoder_table_multiplicities_dst: usize,
    absolute_row_idx: usize,
) {
    let executor_family_decoder_table_size = compiled_circuit.executor_family_decoder_table_size;

    let value = if absolute_row_idx < executor_family_decoder_table_size {
        let m = *witness_trace_row.get_unchecked(decoder_table_multiplicities_src);

        // Read preprocessed column and read rational value 1/(table(alpha) + gammma)
        let mut value = decoder_table_preprocessing_ref[absolute_row_idx];
        // it's enough just to multiply by multiplicity
        value.mul_assign_by_base(&m);

        value
    } else {
        if DEBUG_QUOTIENT {
            assert_eq!(
                *witness_trace_row.get_unchecked(decoder_table_multiplicities_src),
                Mersenne31Field::ZERO,
                "multiplicity for timestamp range check is not zero for row {}",
                absolute_row_idx
            );
        }

        Mersenne31Quartic::ZERO
    };

    stage_2_trace
        .as_mut_ptr()
        .add(decoder_table_multiplicities_dst)
        .cast::<Mersenne31Quartic>()
        .write(value);
}

pub(crate) unsafe fn stage2_process_generic_lookup_multiplicity_intermediate_poly(
    witness_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    generic_lookup_preprocessing_ref: &[Mersenne31Quartic],
    lookup_encoding_capacity: usize,
    generic_lookup_multiplicities_src_start: usize,
    generic_lookup_multiplicities_dst_start: usize,
    generic_lookup_tables_size: usize,
    absolute_row_idx: usize,
) {
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
            let m = *witness_trace_row.get_unchecked(generic_lookup_multiplicities_src_start + i);
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
}

#[inline]
pub(crate) fn process_delegation_requests(
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    delegation_request_layout: &DelegationRequestLayout,
    delegation_processing_aux_poly: AlignedColumnSet<4>,
    delegation_challenges: &ExternalDelegationArgumentChallenges,
    batch_inverses_input: &mut Vec<Mersenne31Quartic>,
    mut timestamp_low: Mersenne31Field,
    timestamp_high: Mersenne31Field,
) {
    unsafe {
        let m = *memory_trace_row.get_unchecked(delegation_request_layout.multiplicity.start());
        assert!(m == Mersenne31Field::ZERO || m == Mersenne31Field::ONE);

        let numerator = Mersenne31Quartic::from_base(m);
        stage_2_trace
            .as_mut_ptr()
            .add(delegation_processing_aux_poly.start())
            .cast::<Mersenne31Quartic>()
            .write(numerator);

        // offset by access number
        timestamp_low.add_assign(&Mersenne31Field(
            delegation_request_layout.in_cycle_write_index as u32,
        ));

        let denom = compute_aggregated_key_value(
            *memory_trace_row.get_unchecked(delegation_request_layout.delegation_type.start()),
            [
                *memory_trace_row
                    .get_unchecked(delegation_request_layout.abi_mem_offset_high.start()),
                timestamp_low,
                timestamp_high,
            ],
            delegation_challenges.delegation_argument_linearization_challenges,
            delegation_challenges.delegation_argument_gamma,
        );

        batch_inverses_input.push(denom);

        if DEBUG_QUOTIENT {
            if m == Mersenne31Field::ZERO {
                // Conventions depend quite a lot on simulator/witness gen internals, so we are free do disable
                // these checks as there is no contribution to the delegation argument anyway in case of 0 multiplicity

                let mut valid_convention = memory_trace_row
                    .get_unchecked(delegation_request_layout.delegation_type.start())
                    .is_zero();
                if delegation_request_layout.abi_mem_offset_high.num_elements() > 0 {
                    valid_convention &= memory_trace_row
                        .get_unchecked(delegation_request_layout.abi_mem_offset_high.start())
                        .is_zero();
                };
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
}

pub(crate) unsafe fn process_lazy_init_range_checks(
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    range_check_16_preprocessing_ref: &[Mersenne31Quartic],
    lazy_init_address_range_check_16: &OptimizedOraclesForLookupWidth1,
    shuffle_ram_inits_and_teardowns: &[ShuffleRamInitAndTeardownLayout],
) {
    debug_assert_eq!(
        shuffle_ram_inits_and_teardowns.len(),
        lazy_init_address_range_check_16.num_pairs
    );
    for i in 0..lazy_init_address_range_check_16.num_pairs {
        let shuffle_ram_inits_and_teardowns = shuffle_ram_inits_and_teardowns.get_unchecked(i);
        let a_col = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        let b_col = a_col + 1;
        let a = *memory_trace_row.get_unchecked(a_col);
        let b = *memory_trace_row.get_unchecked(b_col);
        if DEBUG_QUOTIENT {
            assert!(
                a.to_reduced_u32() < 1 << 16,
                "value {} (low) is beyond the range for lazy init addresses check number {}",
                a.to_reduced_u32(),
                i
            );
            assert!(
                b.to_reduced_u32() < 1 << 16,
                "value {} (high) is beyond the range for lazy init addresses check number {}",
                b.to_reduced_u32(),
                i
            );
        }
        let mut c = a;
        c.mul_assign(&b);

        stage_2_trace
            .as_mut_ptr()
            .add(
                lazy_init_address_range_check_16
                    .base_field_oracles
                    .get_range(i)
                    .start,
            )
            .write(c);

        let a_idx = a.to_reduced_u32() as usize;
        let b_idx = b.to_reduced_u32() as usize;
        let mut final_value = *range_check_16_preprocessing_ref.get_unchecked(a_idx);
        final_value.add_assign(range_check_16_preprocessing_ref.get_unchecked(b_idx));

        let ptr = stage_2_trace
            .as_mut_ptr()
            .add(
                lazy_init_address_range_check_16
                    .ext_4_field_oracles
                    .get_range(i)
                    .start,
            )
            .cast::<Mersenne31Quartic>();
        debug_assert!(ptr.is_aligned());

        ptr.write(final_value);
    }
}
