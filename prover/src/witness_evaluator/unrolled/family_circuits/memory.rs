use super::*;
use cs::utils::*;

pub fn evaluate_memory_witness_for_executor_family<O: Oracle<Mersenne31Field>, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cycles: usize,
    oracle: &O,
    worker: &Worker,
    allocator: A,
) -> MemoryOnlyWitnessEvaluationDataForExecutionFamily<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    assert!(compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_empty());

    let trace_len = cycles.next_power_of_two();
    assert_eq!(cycles, trace_len - 1);

    let num_memory_columns = compiled_circuit.memory_layout.total_width;
    let memory_trace_view =
        RowMajorTrace::new_zeroed_for_size(trace_len, num_memory_columns, allocator.clone());

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
                        evaluate_memory_witness_for_executor_family_inner(
                            &mut [],
                            memory_trace_view_row,
                            compiled_circuit,
                            oracle,
                            absolute_row_idx,
                            _is_last_cycle,
                        );
                    }

                    memory_trace_view.advance_row();
                }
            });
        }
    });

    // we also do not care about multiplicities

    MemoryOnlyWitnessEvaluationDataForExecutionFamily {
        memory_trace: memory_trace_view,
    }
}

#[inline]
pub(crate) unsafe fn process_machine_state_assuming_preprocessed_decoder<
    O: Oracle<Mersenne31Field>,
    const COMPUTE_WITNESS: bool,
>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    decoder_multiplicieties: &mut [u32],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    let input_state_and_decoder_parts = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .as_ref()
        .unwrap();
    let output_state = compiled_circuit
        .memory_layout
        .machine_state_layout
        .as_ref()
        .unwrap();

    // we need to assign execute flag, PCs, timestamps,
    let execute = oracle.get_boolean_witness_from_placeholder(
        Placeholder::ExecuteOpcodeFamilyCycle,
        absolute_row_idx,
    );
    write_boolean_value_into_columns(input_state_and_decoder_parts.execute, execute, memory_row);
    let initial_pc = oracle.get_u32_witness_from_placeholder(Placeholder::PcInit, absolute_row_idx);
    write_u32_value_into_columns(input_state_and_decoder_parts.pc, initial_pc, memory_row);
    write_timestamp_placeholder_into_columns(
        input_state_and_decoder_parts.timestamp,
        Placeholder::OpcodeFamilyCycleInitialTimestamp,
        oracle,
        memory_row,
        absolute_row_idx,
    );

    // and final state
    write_u32_placeholder_into_columns(
        output_state.pc,
        Placeholder::PcFin,
        oracle,
        memory_row,
        absolute_row_idx,
    );

    let initial_ts = oracle.get_timestamp_witness_from_placeholder(
        Placeholder::OpcodeFamilyCycleInitialTimestamp,
        absolute_row_idx,
    );
    let (final_ts, intermediate_carry) = timestamp_increment(initial_ts);

    write_timestamp_value_into_columns(output_state.timestamp, final_ts, memory_row);

    // rare case when it's in memory
    if let ColumnAddress::MemorySubtree(circuit_family_extra_mask) =
        input_state_and_decoder_parts.circuit_family_extra_mask
    {
        let decoder_data = oracle.get_executor_family_data(absolute_row_idx);
        write_u8_value_into_columns(
            ColumnSet::new(circuit_family_extra_mask, 1),
            decoder_data.opcode_family_bits,
            memory_row,
        );
    }

    if COMPUTE_WITNESS {
        // also write timestamp intermediate carry
        if let Some(executor_family_circuit_next_timestamp_aux_var) =
            compiled_circuit.executor_family_circuit_next_timestamp_aux_var
        {
            write_boolean_value_into_columns(
                ColumnSet::new(executor_family_circuit_next_timestamp_aux_var.offset(), 1),
                intermediate_carry,
                witness_row,
            );
        }

        let decoder_data = oracle.get_executor_family_data(absolute_row_idx);

        // and maybe some decoder values, that wouldn't end up as RS2/RD indexes and so on
        if let ColumnAddress::WitnessSubtree(offset) = input_state_and_decoder_parts.rs2_index {
            write_u8_value_into_columns(
                ColumnSet::new(offset, 1),
                decoder_data.rs2_index,
                witness_row,
            );
        }

        if let ColumnAddress::WitnessSubtree(offset) = input_state_and_decoder_parts.rd_index {
            write_u8_value_into_columns(
                ColumnSet::new(offset, 1),
                decoder_data.rd_index,
                witness_row,
            );
        }

        if let ColumnAddress::WitnessSubtree(circuit_family_extra_mask) =
            input_state_and_decoder_parts.circuit_family_extra_mask
        {
            write_u8_value_into_columns(
                ColumnSet::new(circuit_family_extra_mask, 1),
                decoder_data.opcode_family_bits,
                witness_row,
            );
        }

        if input_state_and_decoder_parts.decoder_witness_is_in_memory == false {
            // these variables are for sure in witness

            // pub rd_is_zero: ColumnSet<1>,
            // pub imm: ColumnSet<REGISTER_SIZE>,
            // pub funct3: ColumnSet<1>,
            // pub circuit_family_extra_mask: ColumnAddress,

            write_boolean_value_into_columns(
                input_state_and_decoder_parts.rd_is_zero,
                decoder_data.rd_is_zero,
                witness_row,
            );

            write_u32_value_into_columns(
                input_state_and_decoder_parts.imm,
                decoder_data.imm,
                witness_row,
            );

            write_u8_value_into_columns(
                input_state_and_decoder_parts.funct3,
                decoder_data.funct3,
                witness_row,
            );

            // and count multiplicity right away
            if execute {
                assert!(initial_pc % 4 == 0);
                let idx = initial_pc / 4;
                decoder_multiplicieties[idx as usize] += 1;
            }
        }
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Machine state processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn process_delegation_requests_in_executor_family<O: Oracle<Mersenne31Field>>(
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
        write_boolean_placeholder_into_columns(
            delegation_request_layout.multiplicity,
            Placeholder::ExecuteDelegation,
            oracle,
            memory_row,
            absolute_row_idx,
        );
        write_u16_placeholder_into_columns(
            delegation_request_layout.delegation_type,
            Placeholder::DelegationType,
            oracle,
            memory_row,
            absolute_row_idx,
        );
        if delegation_request_layout.abi_mem_offset_high.num_elements() > 0 {
            write_u16_placeholder_into_columns(
                delegation_request_layout.abi_mem_offset_high,
                Placeholder::DelegationABIOffset,
                oracle,
                memory_row,
                absolute_row_idx,
            );
        }

        // timestamps come from the other parts of the state
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Delegation requests processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn process_shuffle_ram_accesses_in_executor_family<
    O: Oracle<Mersenne31Field>,
    const COMPUTE_WITNESS: bool,
>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    debug_assert_eq!(
        compiled_circuit
            .memory_queries_timestamp_comparison_aux_vars
            .len(),
        compiled_circuit.memory_layout.shuffle_ram_access_sets.len()
    );

    let cycle_ts = oracle.get_timestamp_witness_from_placeholder(
        Placeholder::OpcodeFamilyCycleInitialTimestamp,
        absolute_row_idx,
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
                write_u8_placeholder_into_columns(
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

                write_u32_placeholder_into_columns(
                    address,
                    Placeholder::ShuffleRamAddress(access_idx),
                    oracle,
                    memory_row,
                    absolute_row_idx,
                );
            }
        }

        let read_ts = oracle.get_timestamp_witness_from_placeholder(
            Placeholder::ShuffleRamReadTimestamp(access_idx),
            absolute_row_idx,
        );

        write_timestamp_value_into_columns(
            mem_query.get_read_timestamp_columns(),
            read_ts,
            memory_row,
        );

        write_u32_placeholder_into_columns(
            mem_query.get_read_value_columns(),
            Placeholder::ShuffleRamReadValue(access_idx),
            oracle,
            memory_row,
            absolute_row_idx,
        );

        if let ShuffleRamQueryColumns::Write(columns) = mem_query {
            // also do write
            write_u32_placeholder_into_columns(
                columns.write_value,
                Placeholder::ShuffleRamWriteValue(access_idx),
                oracle,
                memory_row,
                absolute_row_idx,
            );
        }

        if COMPUTE_WITNESS {
            let write_ts = cycle_ts + (access_idx as TimestampScalar);

            let read_ts_split = split_timestamp(read_ts);
            let write_ts_split = split_timestamp(write_ts);

            let comparison_set = compiled_circuit
                .memory_queries_timestamp_comparison_aux_vars
                .get_unchecked(access_idx);
            let borrow_place = *comparison_set;

            // this - next is with borrow
            let (((_aux_low, _aux_high), intermediate_borrow), final_borrow) =
                timestamp_sub(read_ts_split, write_ts_split);
            assert!(
                final_borrow,
                "failed to compare memory access timestamps at row {} for access {}: read is {}, write is {}",
                absolute_row_idx,
                access_idx,
                read_ts,
                write_ts,
            );

            write_boolean_value_into_columns(
                ColumnSet::new(borrow_place.offset(), 1),
                intermediate_borrow,
                witness_row,
            );
        }
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Shuffle RAM processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn evaluate_memory_witness_for_executor_family_inner<
    O: Oracle<Mersenne31Field>,
>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
    _is_last_cycle: bool,
) {
    process_machine_state_assuming_preprocessed_decoder::<O, false>(
        witness_row,
        memory_row,
        &mut [],
        compiled_circuit,
        oracle,
        absolute_row_idx,
    );

    process_delegation_requests_in_executor_family::<O>(
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
    );

    process_shuffle_ram_accesses_in_executor_family::<O, false>(
        witness_row,
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
    );

    // we can skip producing any other witness values, because none of them are placed into memory trace
}
