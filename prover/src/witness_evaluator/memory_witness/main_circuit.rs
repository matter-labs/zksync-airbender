use super::*;
use cs::utils::*;

pub fn evaluate_memory_witness<O: Oracle<Mersenne31Field>, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cycles: usize,
    oracle: &O,
    lazy_init_data: &[LazyInitAndTeardown],
    worker: &Worker,
    allocator: A,
) -> MemoryOnlyWitnessEvaluationData<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    if compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_some()
    {
        assert_eq!(lazy_init_data.len(), cycles);
    }

    let trace_len = cycles.next_power_of_two();
    assert_eq!(cycles, trace_len - 1);

    let num_memory_columns = compiled_circuit.memory_layout.total_width;
    let memory_trace_view =
        RowMajorTrace::new_zeroed_for_size(trace_len, num_memory_columns, allocator.clone());

    // low timestamp chunk comes from the setup

    // NOTE: we only evaluate memory and can not rely on the circuit's machinery to evaluate witness at all

    worker.scope(cycles, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);

            let range = chunk_start..(chunk_start + chunk_size);
            let mut memory_trace_view = memory_trace_view.row_view(range.clone());

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for i in 0..chunk_size {
                    let absolute_row_idx = chunk_start + i;
                    let _is_last_cycle = absolute_row_idx == cycles - 1;

                    let memory_trace_view_row = memory_trace_view.current_row();

                    unsafe {
                        evaluate_memory_witness_inner(
                            &mut [],
                            memory_trace_view_row,
                            compiled_circuit,
                            oracle,
                            absolute_row_idx,
                            _is_last_cycle,
                            lazy_init_data,
                        );
                    }

                    memory_trace_view.advance_row();
                }
            });
        }
    });

    // we also do not care about multiplicities

    // now get aux variables

    let LazyInitAndTeardown {
        address: lazy_init_address_first_row,
        teardown_value: lazy_teardown_value_first_row,
        teardown_timestamp: lazy_teardown_timestamp_first_row,
    } = lazy_init_data[0];

    let LazyInitAndTeardown {
        address: lazy_init_address_one_before_last_row,
        teardown_value: lazy_teardown_value_one_before_last_row,
        teardown_timestamp: lazy_teardown_timestamp_one_before_last_row,
    } = lazy_init_data[cycles - 1];

    let (lazy_init_address_first_row_low, lazy_init_address_first_row_high) =
        split_u32_into_pair_u16(lazy_init_address_first_row);
    let (teardown_value_first_row_low, teardown_value_first_row_high) =
        split_u32_into_pair_u16(lazy_teardown_value_first_row);
    let (teardown_timestamp_first_row_low, teardown_timestamp_first_row_high) =
        split_timestamp(lazy_teardown_timestamp_first_row.as_scalar());

    let (lazy_init_address_one_before_last_row_low, lazy_init_address_one_before_last_row_high) =
        split_u32_into_pair_u16(lazy_init_address_one_before_last_row);
    let (teardown_value_one_before_last_row_low, teardown_value_one_before_last_row_high) =
        split_u32_into_pair_u16(lazy_teardown_value_one_before_last_row);
    let (teardown_timestamp_one_before_last_row_low, teardown_timestamp_one_before_last_row_high) =
        split_timestamp(lazy_teardown_timestamp_one_before_last_row.as_scalar());

    let aux_data = WitnessEvaluationAuxData {
        first_row_public_inputs: vec![],
        one_before_last_row_public_inputs: vec![],
        lazy_init_first_row: [
            Mersenne31Field(lazy_init_address_first_row_low as u32),
            Mersenne31Field(lazy_init_address_first_row_high as u32),
        ],
        teardown_value_first_row: [
            Mersenne31Field(teardown_value_first_row_low as u32),
            Mersenne31Field(teardown_value_first_row_high as u32),
        ],
        teardown_timestamp_first_row: [
            Mersenne31Field(teardown_timestamp_first_row_low),
            Mersenne31Field(teardown_timestamp_first_row_high),
        ],
        lazy_init_one_before_last_row: [
            Mersenne31Field(lazy_init_address_one_before_last_row_low as u32),
            Mersenne31Field(lazy_init_address_one_before_last_row_high as u32),
        ],
        teardown_value_one_before_last_row: [
            Mersenne31Field(teardown_value_one_before_last_row_low as u32),
            Mersenne31Field(teardown_value_one_before_last_row_high as u32),
        ],
        teardown_timestamp_one_before_last_row: [
            Mersenne31Field(teardown_timestamp_one_before_last_row_low),
            Mersenne31Field(teardown_timestamp_one_before_last_row_high),
        ],
    };

    MemoryOnlyWitnessEvaluationData {
        aux_data,
        memory_trace: memory_trace_view,
    }
}

#[inline]
pub(crate) unsafe fn process_lazy_init_work<const COMPUTE_WITNESS: bool>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    absolute_row_idx: usize,
    _is_last_cycle: bool,
    lazy_init_data: &[LazyInitAndTeardown],
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();
    if let Some(lazy_init_and_teardown) = compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
    {
        let Some(lazy_init_address_aux_vars) = compiled_circuit.lazy_init_address_aux_vars else {
            unreachable!()
        };

        let lazy_init = lazy_init_data[absolute_row_idx];
        let LazyInitAndTeardown {
            address: this_row_lazy_init_address,
            teardown_value: this_row_teardown_value,
            teardown_timestamp: this_row_teardown_timestamp,
        } = lazy_init;

        // copy lazy init values
        write_u32_value_into_memory_columns(
            lazy_init_and_teardown.lazy_init_addresses_columns,
            this_row_lazy_init_address,
            memory_row,
        );
        write_u32_value_into_memory_columns(
            lazy_init_and_teardown.lazy_teardown_values_columns,
            this_row_teardown_value,
            memory_row,
        );
        write_timestamp_value_into_memory_columns(
            lazy_init_and_teardown.lazy_teardown_timestamps_columns,
            this_row_teardown_timestamp.as_scalar(),
            memory_row,
        );

        if COMPUTE_WITNESS {
            // we should compute auxiliary variables for lazy init address ordering constraint,
            // and for read/write access sets for comparison that read timestamp < write timestamp

            let ShuffleRamAuxComparisonSet {
                aux_low_high: [low_place, high_place],
                intermediate_borrow,
                final_borrow,
            } = lazy_init_address_aux_vars;

            // lazy init ordering
            if let Some(next_row_lazy_init) = lazy_init_data.get(absolute_row_idx + 1).copied() {
                let LazyInitAndTeardown {
                    address: next_row_lazy_init_address,
                    ..
                } = next_row_lazy_init;

                let (((aux_low, aux_high), intermediate_borrow_value), final_borrow_value) =
                    u32_split_sub(this_row_lazy_init_address, next_row_lazy_init_address);

                write_value(
                    low_place,
                    Mersenne31Field(aux_low as u32),
                    witness_row,
                    &mut [],
                );
                write_value(
                    high_place,
                    Mersenne31Field(aux_high as u32),
                    witness_row,
                    &mut [],
                );
                write_value(
                    intermediate_borrow,
                    Mersenne31Field::from_boolean(intermediate_borrow_value),
                    witness_row,
                    &mut [],
                );
                write_value(
                    final_borrow,
                    Mersenne31Field::from_boolean(final_borrow_value),
                    witness_row,
                    &mut [],
                );

                if final_borrow_value == false {
                    assert_eq!(
                        this_row_lazy_init_address, 0,
                        "lazy init address is invalid for row {} in case of padding",
                        absolute_row_idx,
                    );
                    assert_eq!(
                        this_row_teardown_value, 0,
                        "lazy teardown value is invalid for row {} in case of padding",
                        absolute_row_idx,
                    );
                    assert_eq!(
                        this_row_teardown_timestamp.as_scalar(),
                        0,
                        "lazy teardown timestamp is invalid for row {} in case of padding",
                        absolute_row_idx,
                    );
                }
            } else {
                // VERY important - we will use the fact that final borrow value is unconstrained
                // when we will define lazy init/teardown padding constraint, so we manually right here write it
                // to the proper value - it must be `1`
                write_value(
                    final_borrow,
                    Mersenne31Field::from_boolean(true),
                    witness_row,
                    &mut [],
                );
            }
        }
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Lazy init processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn process_delegation_requests<O: Oracle<Mersenne31Field>>(
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    if let Some(delegation_request_layout) =
        compiled_circuit.memory_layout.delegation_request_layout
    {
        write_boolean_placeholder_into_memory_columns(
            delegation_request_layout.multiplicity,
            Placeholder::ExecuteDelegation,
            oracle,
            memory_row,
            absolute_row_idx,
        );
        write_u16_placeholder_into_memory_columns(
            delegation_request_layout.delegation_type,
            Placeholder::DelegationType,
            oracle,
            memory_row,
            absolute_row_idx,
        );
        write_u16_placeholder_into_memory_columns(
            delegation_request_layout.abi_mem_offset_high,
            Placeholder::DegelationABIOffset,
            oracle,
            memory_row,
            absolute_row_idx,
        );

        // timestamps come from the setup
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Delegation requests processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn process_shuffle_ram_accesses<
    O: Oracle<Mersenne31Field>,
    const COMPUTE_WITNESS: bool,
>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
    timestamp_high_from_circuit_sequence: TimestampScalar,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    debug_assert_eq!(
        compiled_circuit
            .memory_queries_timestamp_comparison_aux_vars
            .len(),
        compiled_circuit.memory_layout.shuffle_ram_access_sets.len()
    );

    // We also must write down read timestamps, as those are pure witness values from the prover
    for (access_idx, mem_query) in compiled_circuit
        .memory_layout
        .shuffle_ram_access_sets
        .iter()
        .enumerate()
    {
        match mem_query.get_address() {
            ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index }) => {
                write_u16_placeholder_into_memory_columns(
                    register_index,
                    Placeholder::ShuffleRamAddress(access_idx),
                    oracle,
                    memory_row,
                    absolute_row_idx,
                );
            }
            ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                is_register,
                address,
            }) => {
                let is_register_flag =
                    Oracle::<Mersenne31Field>::get_boolean_witness_from_placeholder(
                        oracle,
                        Placeholder::ShuffleRamIsRegisterAccess(access_idx),
                        absolute_row_idx,
                    );
                memory_row[is_register.start()] = Mersenne31Field::from_boolean(is_register_flag);

                write_u32_placeholder_into_memory_columns(
                    address,
                    Placeholder::ShuffleRamAddress(access_idx),
                    oracle,
                    memory_row,
                    absolute_row_idx,
                );
            }
        }

        write_timestamp_placeholder_into_memory_columns(
            mem_query.get_read_timestamp_columns(),
            Placeholder::ShuffleRamReadTimestamp(access_idx),
            oracle,
            memory_row,
            absolute_row_idx,
        );

        write_u32_placeholder_into_memory_columns(
            mem_query.get_read_value_columns(),
            Placeholder::ShuffleRamReadValue(access_idx),
            oracle,
            memory_row,
            absolute_row_idx,
        );

        if let ShuffleRamQueryColumns::Write(columns) = mem_query {
            // also do write
            write_u32_placeholder_into_memory_columns(
                columns.write_value,
                Placeholder::ShuffleRamWriteValue(access_idx),
                oracle,
                memory_row,
                absolute_row_idx,
            );
        }

        if COMPUTE_WITNESS {
            // for timestamps we already got our read timestamps from witness resolution, and
            // write timestamps are coming from the setup composition, but we will need to resolve aux variables
            let write_timestamp_base = timestamp_high_from_circuit_sequence
                + (((absolute_row_idx + 1) as TimestampScalar) << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);
            let write_timestamp_base = write_timestamp_base as TimestampScalar;

            let access_description = mem_query;
            let read_timestamp_low = access_description.get_read_timestamp_columns().start();
            let read_timestamp_high = read_timestamp_low + 1;

            let comparison_set = compiled_circuit
                .memory_queries_timestamp_comparison_aux_vars
                .get_unchecked(access_idx);
            let borrow_place = *comparison_set;
            // write timestamp is a combination of constant access index + values from setup combined,
            // and read timestamps are provided in witness, but we quickly simulate a logic here
            let read_timestamp_low = memory_row
                .get_unchecked(read_timestamp_low)
                .to_reduced_u32();
            let read_timestamp_high = memory_row
                .get_unchecked(read_timestamp_high)
                .to_reduced_u32();

            let (write_timestamp_low, write_timestamp_high) =
                split_timestamp(write_timestamp_base + (access_idx as TimestampScalar));

            // this - next is with borrow
            let (((_aux_low, _aux_high), intermediate_borrow), final_borrow) = timestamp_sub(
                (read_timestamp_low, read_timestamp_high),
                (write_timestamp_low, write_timestamp_high),
            );
            assert!(
                final_borrow,
                "failed to compare memory access timestamps at row {} for access {}: read is {}, write is {}",
                absolute_row_idx,
                access_idx,
                (read_timestamp_high << TIMESTAMP_COLUMNS_NUM_BITS) | read_timestamp_low,
                (write_timestamp_high << TIMESTAMP_COLUMNS_NUM_BITS) | write_timestamp_low,
            );

            write_value(
                borrow_place,
                Mersenne31Field::from_boolean(intermediate_borrow),
                witness_row,
                &mut [],
            );
        }
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Shuffle RAM processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn evaluate_memory_witness_inner<O: Oracle<Mersenne31Field>>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
    is_last_cycle: bool,
    lazy_init_data: &[LazyInitAndTeardown],
) {
    process_lazy_init_work::<false>(
        witness_row,
        memory_row,
        compiled_circuit,
        absolute_row_idx,
        is_last_cycle,
        lazy_init_data,
    );

    process_delegation_requests(memory_row, compiled_circuit, oracle, absolute_row_idx);

    process_shuffle_ram_accesses::<O, false>(
        witness_row,
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
        0,
    );

    // we can skip producing any other witness values, because none of them are placed into memory trace
}
