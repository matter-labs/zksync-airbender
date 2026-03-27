use super::*;
use crate::gkr::witness_gen::family_circuits::GKRMemoryOnlyWitnessTrace;
use cs::definitions::gkr::*;
use cs::tables::TableDriver;
use cs::utils::timestamp_sub;

pub fn evaluate_gkr_memory_witness_for_delegation_circuit<
    F: PrimeField,
    O: Oracle<F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    num_cycles: usize,
    oracle: &O,
    worker: &Worker,
    inner_allocator: A,
    outer_allocator: B,
) -> GKRMemoryOnlyWitnessTrace<F, A, B> {
    let trace_len = compiled_circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    assert!(num_cycles <= trace_len);
    let num_memory_columns = compiled_circuit.memory_layout.total_width;

    let mut memory_trace = GKRMemoryOnlyWitnessTrace::new(
        trace_len,
        num_memory_columns,
        inner_allocator,
        outer_allocator,
    );
    let table_driver = TableDriver::<F>::new();

    // NOTE: we only evaluate memory and can not rely on the circuit's machinery to evaluate witness at all

    worker.scope(trace_len, |scope, geometry| {
        let chunks = memory_trace.make_proxies_for_geometry(
            oracle,
            geometry,
            &table_driver,
            compiled_circuit.scratch_space_size,
            trace_len,
        );
        for (thread_idx, chunk) in chunks.into_iter().enumerate() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut chunk = chunk;
                for _i in 0..chunk_size {
                    unsafe {
                        evaluate_memory_witness_for_delegation_circuit_inner::<F, O>(
                            &mut chunk,
                            &compiled_circuit,
                        );

                        chunk.advance();
                    }
                }
            });
        }
    });

    // set filled rows
    for el in memory_trace.column_major_trace.iter_mut() {
        unsafe {
            el.set_len(trace_len);
        }
    }

    // we also do not care about multiplicities

    memory_trace
}

#[inline]
pub(crate) unsafe fn gkr_process_delegation_requests_execution<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    let delegation_state = compiled_circuit
        .memory_layout
        .delegation_state
        .as_ref()
        .unwrap();

    let execute = proxy.oracle.get_boolean_witness_from_placeholder(
        Placeholder::ExecuteDelegation,
        proxy.absolute_row_idx,
    );
    proxy.write_boolean_value_into_columns::<true>(delegation_state.execute, execute);

    let ts = proxy.oracle.get_timestamp_witness_from_placeholder(
        Placeholder::DelegationWriteTimestamp,
        proxy.absolute_row_idx,
    );
    proxy.write_timestamp_value_into_columns(delegation_state.invocation_timestamp, ts);

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Delegation processing requests execution")
            .or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn gkr_evaluate_indirect_memory_accesses<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
    const COMPUTE_WITNESS: bool,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    let delegation_state = compiled_circuit
        .memory_layout
        .delegation_state
        .as_ref()
        .unwrap();

    let predicate = proxy.oracle.get_boolean_witness_from_placeholder(
        Placeholder::ExecuteDelegation,
        proxy.absolute_row_idx,
    );

    let invocation_ts = proxy.oracle.get_timestamp_witness_from_placeholder(
        Placeholder::DelegationWriteTimestamp,
        proxy.absolute_row_idx,
    );

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    // fill variable offset values quickly

    for (variable_offset_idx, mem_offset) in compiled_circuit
        .memory_layout
        .indirect_access_variable_offsets
        .iter()
        .enumerate()
    {
        proxy.write_u16_placeholder_into_columns::<true>(
            *mem_offset,
            Placeholder::DelegationIndirectAccessVariableOffset {
                variable_index: variable_offset_idx,
            },
        );
    }

    // for delegation circuits we decide what we do based on the address type
    let mut read_ts;

    for (access_idx, mem_query) in compiled_circuit
        .memory_layout
        .ram_access_sets
        .iter()
        .enumerate()
    {
        match mem_query.get_address() {
            RamAddress::ConstantRegister(reg_idx) => {
                read_ts = proxy.oracle.get_timestamp_witness_from_placeholder(
                    Placeholder::DelegationRegisterReadTimestamp(reg_idx as usize),
                    proxy.absolute_row_idx,
                );
                proxy.write_timestamp_value_into_columns(
                    mem_query.get_read_timestamp_columns(),
                    read_ts,
                );

                match mem_query.get_read_value_columns() {
                    RamWordRepresentation::Zero => {
                        unreachable!()
                    }
                    RamWordRepresentation::U16Limbs(read_value) => {
                        proxy.write_u32_placeholder_into_columns::<true>(
                            read_value,
                            Placeholder::DelegationRegisterReadValue(reg_idx as usize),
                        );
                    }
                    RamWordRepresentation::U8Limbs(..) => {
                        unreachable!()
                    }
                }

                if let RamQuery::Write(query) = mem_query {
                    // also do write
                    match query.write_value {
                        RamWordRepresentation::Zero => {
                            unreachable!()
                        }
                        RamWordRepresentation::U16Limbs(write_value) => {
                            proxy.write_u32_placeholder_into_columns::<true>(
                                write_value,
                                Placeholder::DelegationRegisterWriteValue(reg_idx as usize),
                            );
                        }
                        RamWordRepresentation::U8Limbs(..) => {
                            unreachable!()
                        }
                    }
                }
            }
            RamAddress::RegisterOnly(..) => {
                unreachable!()
            }
            RamAddress::RegisterOrRam(..) => {
                unreachable!();
            }
            RamAddress::IndirectRam(IndirectRamAccessAddress {
                base_register_value,
                constant_offset,
                base_register_index,
                indirect_access_idx_for_register,
                ..
            }) => {
                // actually we do not have to write anything - there is a pass above that writes down
                // values for variable offsets, but we do not need to do anything else to finish address derivation
                debug_assert!({
                    let base_reg_value =
                        proxy.read_u32_value_from_columns::<true>(base_register_value);
                    let (_, of) = base_reg_value.overflowing_add(constant_offset as u32);

                    of == false
                });

                read_ts = proxy.oracle.get_timestamp_witness_from_placeholder(
                    Placeholder::DelegationIndirectReadTimestamp {
                        register_index: base_register_index as usize,
                        word_index: indirect_access_idx_for_register,
                    },
                    proxy.absolute_row_idx,
                );
                proxy.write_timestamp_value_into_columns(
                    mem_query.get_read_timestamp_columns(),
                    read_ts,
                );

                match mem_query.get_read_value_columns() {
                    RamWordRepresentation::Zero => {
                        unreachable!()
                    }
                    RamWordRepresentation::U16Limbs(read_value) => {
                        proxy.write_u32_placeholder_into_columns::<true>(
                            read_value,
                            Placeholder::DelegationIndirectReadValue {
                                register_index: base_register_index as usize,
                                word_index: indirect_access_idx_for_register,
                            },
                        );
                    }
                    RamWordRepresentation::U8Limbs(..) => {
                        unreachable!()
                    }
                }

                if let RamQuery::Write(query) = mem_query {
                    // also do write
                    match query.write_value {
                        RamWordRepresentation::Zero => {
                            unreachable!()
                        }
                        RamWordRepresentation::U16Limbs(write_value) => {
                            proxy.write_u32_placeholder_into_columns::<true>(
                                write_value,
                                Placeholder::DelegationIndirectWriteValue {
                                    register_index: base_register_index as usize,
                                    word_index: indirect_access_idx_for_register,
                                },
                            );
                        }
                        RamWordRepresentation::U8Limbs(..) => {
                            unreachable!()
                        }
                    }
                }
            }
        }

        if COMPUTE_WITNESS {
            let write_ts =
                invocation_ts + (mem_query.local_timestamp_in_cycle() as TimestampScalar);

            let read_ts_split = split_timestamp(read_ts);
            let write_ts_split = split_timestamp(write_ts);

            let comparison_set = compiled_circuit
                .aux_layout_data
                .shuffle_ram_timestamp_comparison_aux_vars
                .get_unchecked(access_idx);
            let GKRAddress::BaseLayerWitness(borrow_place) = comparison_set.intermediate_borrow
            else {
                unreachable!()
            };

            // this - next is with borrow
            let (((_aux_low, _aux_high), intermediate_borrow), _final_borrow) =
                timestamp_sub(read_ts_split, write_ts_split);
            assert!(
                _final_borrow,
                "failed to compare memory access timestamps at row {} for access {}: read is {}, write is {}. Cycle timestamp is {}",
                proxy.absolute_row_idx,
                access_idx,
                read_ts,
                write_ts,
                invocation_ts,
            );

            proxy.write_boolean_value_into_columns::<false>(borrow_place, intermediate_borrow);
        }
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Register and indirect RAM processing")
            .or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn evaluate_memory_witness_for_delegation_circuit_inner<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    gkr_process_delegation_requests_execution::<F, O>(proxy, compiled_circuit);

    gkr_evaluate_indirect_memory_accesses::<F, O, false>(proxy, compiled_circuit);
}
