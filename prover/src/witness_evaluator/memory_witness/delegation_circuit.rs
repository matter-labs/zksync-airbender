use cs::utils::timestamp_sub;

use super::*;

pub fn evaluate_delegation_memory_witness<O: Oracle<Mersenne31Field>, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cycles: usize,
    oracle: &O,
    worker: &Worker,
    allocator: A,
) -> DelegationMemoryOnlyWitnessEvaluationData<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    assert!(compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_none());
    assert!(compiled_circuit
        .memory_layout
        .shuffle_ram_access_sets
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
                        evaluate_delegation_memory_witness_inner(
                            memory_trace_view_row,
                            compiled_circuit,
                            oracle,
                            absolute_row_idx,
                            _is_last_cycle,
                            trace_len,
                        );
                    }

                    memory_trace_view.advance_row();
                }
            });
        }
    });

    DelegationMemoryOnlyWitnessEvaluationData {
        memory_trace: memory_trace_view,
    }
}

#[inline]
pub(crate) unsafe fn process_delegation_requests_execution<O: Oracle<Mersenne31Field>>(
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    if let Some(delegation_processor_layout) =
        compiled_circuit.memory_layout.delegation_processor_layout
    {
        write_boolean_placeholder_into_memory_columns(
            delegation_processor_layout.multiplicity,
            Placeholder::ExecuteDelegation,
            oracle,
            memory_row,
            absolute_row_idx,
        );
        write_u16_placeholder_into_memory_columns(
            delegation_processor_layout.abi_mem_offset_high,
            Placeholder::DegelationABIOffset,
            oracle,
            memory_row,
            absolute_row_idx,
        );
        write_timestamp_placeholder_into_memory_columns(
            delegation_processor_layout.write_timestamp,
            Placeholder::DelegationWriteTimestamp,
            oracle,
            memory_row,
            absolute_row_idx,
        );
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Delegation processing requests execution")
            .or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn evaluate_indirect_memory_accesses<
    O: Oracle<Mersenne31Field>,
    const COMPUTE_WITNESS: bool,
>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
) {
    if compiled_circuit
        .memory_layout
        .delegation_processor_layout
        .is_none()
    {
        // Only delegation circuits are expected to do it
        return;
    }

    assert_eq!(
        compiled_circuit
            .register_and_indirect_access_timestamp_comparison_aux_vars
            .aux_borrow_sets
            .len(),
        compiled_circuit
            .memory_layout
            .register_and_indirect_accesses
            .len()
    );

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    let (write_timestamp_low, write_timestamp_high, predicate) = if COMPUTE_WITNESS {
        let predicate = compiled_circuit
            .register_and_indirect_access_timestamp_comparison_aux_vars
            .predicate;
        let write_timestamp = compiled_circuit
            .register_and_indirect_access_timestamp_comparison_aux_vars
            .write_timestamp;

        let write_timestamp_low = memory_row[write_timestamp[0].offset()].to_reduced_u32();
        let write_timestamp_high = memory_row[write_timestamp[1].offset()].to_reduced_u32();
        let predicate = memory_row[predicate.offset()].as_boolean();

        (write_timestamp_low, write_timestamp_high, predicate)
    } else {
        (0, 0, false)
    };

    for (access_idx, mem_query) in compiled_circuit
        .memory_layout
        .register_and_indirect_accesses
        .iter()
        .enumerate()
    {
        let register_index = mem_query.register_access.get_register_index() as usize;
        // first serve register access by itself
        write_timestamp_placeholder_into_memory_columns(
            mem_query.register_access.get_read_timestamp_columns(),
            Placeholder::DelegationRegisterReadTimestamp(register_index),
            oracle,
            memory_row,
            absolute_row_idx,
        );
        write_u32_placeholder_into_memory_columns(
            mem_query.register_access.get_read_value_columns(),
            Placeholder::DelegationRegisterReadValue(register_index),
            oracle,
            memory_row,
            absolute_row_idx,
        );

        if let RegisterAccessColumns::WriteAccess { write_value, .. } = &mem_query.register_access {
            write_u32_placeholder_into_memory_columns(
                *write_value,
                Placeholder::DelegationRegisterWriteValue(register_index),
                oracle,
                memory_row,
                absolute_row_idx,
            );
        }

        let comparison_set = compiled_circuit
            .register_and_indirect_access_timestamp_comparison_aux_vars
            .aux_borrow_sets
            .get_unchecked(access_idx);
        let (borrow, indirects) = comparison_set;
        let borrow = *borrow;

        if COMPUTE_WITNESS {
            let access_description = mem_query;

            let read_timestamp_low = access_description
                .register_access
                .get_read_timestamp_columns()
                .start();
            let read_timestamp_high = read_timestamp_low + 1;

            // we want read timestamp < write timestamp if predicate is set
            let read_timestamp_low = memory_row
                .get_unchecked(read_timestamp_low)
                .to_reduced_u32();
            let read_timestamp_high = memory_row
                .get_unchecked(read_timestamp_high)
                .to_reduced_u32();

            // this - next is with borrow
            let (((_aux_low, _aux_high), intermediate_borrow), final_borrow) = timestamp_sub(
                (read_timestamp_low, read_timestamp_high),
                (write_timestamp_low, write_timestamp_high),
            );
            assert_eq!(
                predicate, final_borrow,
                "failed to compare register indirect memory access timestamps at row {} for access {}: read is {}, write is {}",
                absolute_row_idx,
                access_idx,
                ((read_timestamp_high as TimestampScalar) << TIMESTAMP_COLUMNS_NUM_BITS) | (read_timestamp_low as TimestampScalar),
                ((write_timestamp_high as TimestampScalar) << TIMESTAMP_COLUMNS_NUM_BITS) | (write_timestamp_low as TimestampScalar),
            );

            write_value(
                borrow,
                Mersenne31Field::from_boolean(intermediate_borrow),
                witness_row,
                &mut [],
            );
        }

        if mem_query.indirect_accesses.len() > 0 {
            let base_address = Oracle::<Mersenne31Field>::get_u32_witness_from_placeholder(
                oracle,
                Placeholder::DelegationRegisterReadValue(register_index),
                absolute_row_idx,
            );

            let high = base_address >> 16;

            // then all indirects
            for (indirect_access_idx, indirect_access) in
                mem_query.indirect_accesses.iter().enumerate()
            {
                debug_assert_eq!(
                    indirect_access_idx * 4,
                    indirect_access.get_offset() as usize
                );

                write_timestamp_placeholder_into_memory_columns(
                    indirect_access.get_read_timestamp_columns(),
                    Placeholder::DelegationIndirectReadTimestamp {
                        register_index,
                        word_index: indirect_access_idx,
                    },
                    oracle,
                    memory_row,
                    absolute_row_idx,
                );
                write_u32_placeholder_into_memory_columns(
                    indirect_access.get_read_value_columns(),
                    Placeholder::DelegationIndirectReadValue {
                        register_index,
                        word_index: indirect_access_idx,
                    },
                    oracle,
                    memory_row,
                    absolute_row_idx,
                );
                if let IndirectAccessColumns::WriteAccess { write_value, .. } = indirect_access {
                    write_u32_placeholder_into_memory_columns(
                        *write_value,
                        Placeholder::DelegationIndirectWriteValue {
                            register_index,
                            word_index: indirect_access_idx,
                        },
                        oracle,
                        memory_row,
                        absolute_row_idx,
                    );
                }

                if indirect_access_idx > 0 {
                    let carry_bit_column =
                        indirect_access.get_address_derivation_carry_bit_column();
                    if carry_bit_column.num_elements() > 0 {
                        // and the only non-trivial part is to compute address derivation carry bit
                        let (derived_address, of) = base_address.overflowing_add(
                            (indirect_access_idx * std::mem::size_of::<u32>()) as u32,
                        );
                        assert!(of == false);
                        let carry_bit = (derived_address >> 16) != high;

                        memory_row[carry_bit_column.start()] = Mersenne31Field(carry_bit as u32);
                    }
                }

                if COMPUTE_WITNESS {
                    let access_description = indirect_access;
                    let read_timestamp_low =
                        access_description.get_read_timestamp_columns().start();
                    let read_timestamp_high = read_timestamp_low + 1;

                    let comparison_set = indirects.get_unchecked(indirect_access_idx);
                    let borrow = *comparison_set;

                    // we want read timestamp < write timestamp if predicate is set
                    let read_timestamp_low = memory_row
                        .get_unchecked(read_timestamp_low)
                        .to_reduced_u32();
                    let read_timestamp_high = memory_row
                        .get_unchecked(read_timestamp_high)
                        .to_reduced_u32();

                    // this - next is with borrow
                    let (((_aux_low, _aux_high), intermediate_borrow), final_borrow) =
                        timestamp_sub(
                            (read_timestamp_low, read_timestamp_high),
                            (write_timestamp_low, write_timestamp_high),
                        );
                    assert_eq!(
                        predicate, final_borrow,
                        "failed to compare indirect memory access timestamps at row {} for access {}: read is {}, writes {}",
                        absolute_row_idx,
                        indirect_access_idx,
                        ((read_timestamp_high as TimestampScalar) << TIMESTAMP_COLUMNS_NUM_BITS) | (read_timestamp_low as TimestampScalar),
                        ((write_timestamp_high as TimestampScalar) << TIMESTAMP_COLUMNS_NUM_BITS) | (write_timestamp_low as TimestampScalar),
                    );

                    write_value(
                        borrow,
                        Mersenne31Field::from_boolean(intermediate_borrow),
                        witness_row,
                        &mut [],
                    );
                }
            }
        }
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Indirect memory accesses evaluation").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn evaluate_delegation_memory_witness_inner<O: Oracle<Mersenne31Field>>(
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
    _is_last_cycle: bool,
    _trace_len: usize,
) {
    assert!(compiled_circuit
        .memory_layout
        .batched_ram_accesses
        .is_empty());

    process_delegation_requests_execution(memory_row, compiled_circuit, oracle, absolute_row_idx);

    evaluate_indirect_memory_accesses::<O, false>(
        &mut [],
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
    );
}
