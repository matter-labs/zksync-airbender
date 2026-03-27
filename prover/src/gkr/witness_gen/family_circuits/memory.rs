use super::*;
use common_constants::{
    TimestampScalar, NUM_TIMESTAMP_COLUMNS_FOR_RAM, TIMESTAMP_COLUMNS_NUM_BITS,
};
use cs::{
    definitions::{gkr::*, GKRAddress},
    gkr_compiler::GKRCircuitArtifact,
    tables::TableDriver,
    utils::*,
};
use field::PrimeField;
use worker::WorkerGeometry;

#[derive(Clone, Debug)]
pub struct GKRMemoryOnlyWitnessTrace<F: PrimeField, A: Allocator + Clone, B: Allocator + Clone> {
    pub column_major_trace: Vec<Vec<F, A>, B>,
}

impl<F: PrimeField, A: Allocator + Clone, B: Allocator + Clone> GKRMemoryOnlyWitnessTrace<F, A, B> {
    pub fn new(
        trace_len: usize,
        num_columns: usize,
        inner_allocator: A,
        outer_allocator: B,
    ) -> Self {
        // We allocate, but do not initialize, as we will use all the rows, and default padding is not guaranteed
        // to be zero one in general

        let mut column_major_trace = Vec::with_capacity_in(num_columns, outer_allocator);
        for _ in 0..num_columns {
            column_major_trace.push(Vec::with_capacity_in(trace_len, inner_allocator.clone()));
        }

        Self { column_major_trace }
    }

    pub fn make_proxies_for_geometry<'a, O: Oracle<F> + 'a>(
        &'a mut self,
        oracle: &'a O,
        geometry: WorkerGeometry,
        table_driver: &'a TableDriver<F>,
        scratch_space_size: usize,
        trace_len: usize,
    ) -> Vec<ColumnMajorWitnessProxy<'a, O, F>> {
        let mut result = Vec::with_capacity(geometry.len());

        let mut total_chunked = 0;
        let mut start_pointers: Vec<_> = self
            .column_major_trace
            .iter_mut()
            .map(|el| el.as_mut_ptr())
            .collect();

        for chunk_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(chunk_idx);
            let proxy = ColumnMajorWitnessProxy {
                witness_rows_starts: vec![].into_boxed_slice(),
                memory_rows_starts: start_pointers.clone().into_boxed_slice(),
                scratch_space: vec![].into_boxed_slice(),
                table_driver,
                multiplicity_counting_scratch: &mut [],
                lookup_mapping_rows_starts: vec![].into_boxed_slice(),
                oracle,
                absolute_row_idx: total_chunked,
            };
            result.push(proxy);

            for el in start_pointers.iter_mut() {
                unsafe {
                    *el = el.add(chunk_size);
                }
            }

            total_chunked += chunk_size;
        }

        assert!(
            total_chunked <= trace_len,
            "total chunks len is {} from worker geometry, while trace length is {}",
            total_chunked,
            trace_len
        );

        result
    }
}

pub fn evaluate_gkr_memory_witness_for_executor_family<
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
                        evaluate_memory_witness_for_executor_family_inner::<F, O>(
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

    // // pad the last rows - so far it's all zeroes
    // if num_cycles < trace_len {
    //     for el in memory_trace.column_major_trace.iter_mut() {
    //         el.resize(trace_len, F::ZERO);
    //     }
    // }

    // // and perform non-trivial padding if needed
    // non_trivial_padding_convention_for_executor_circuit_memory(
    //     &mut memory_trace.column_major_trace,
    //     compiled_circuit,
    //     num_cycles
    // );

    // we also do not care about multiplicities

    memory_trace
}

#[inline]
pub(crate) unsafe fn gkr_process_machine_state_assuming_preprocessed_decoder<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
    const COMPUTE_WITNESS: bool,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    let machine_state = compiled_circuit
        .memory_layout
        .machine_state
        .as_ref()
        .unwrap();

    // we need to assign execute flag, PCs, timestamps,
    let execute = proxy.oracle.get_boolean_witness_from_placeholder(
        Placeholder::ExecuteOpcodeFamilyCycle,
        proxy.absolute_row_idx,
    );
    proxy.write_boolean_value_into_columns::<true>(machine_state.execute, execute);

    // initial state
    let initial_pc = proxy
        .oracle
        .get_u32_witness_from_placeholder(Placeholder::PcInit, proxy.absolute_row_idx);
    proxy.write_u32_value_into_columns::<true>(machine_state.initial_state.pc, initial_pc);

    let initial_ts = proxy.oracle.get_timestamp_witness_from_placeholder(
        Placeholder::OpcodeFamilyCycleInitialTimestamp,
        proxy.absolute_row_idx,
    );
    proxy.write_timestamp_value_into_columns(machine_state.initial_state.timestamp, initial_ts);

    // final state
    proxy.write_u32_placeholder_into_columns::<true>(
        machine_state.final_state.pc,
        Placeholder::PcFin,
    );

    let (final_ts, _intermediate_carry) = timestamp_increment(initial_ts);
    debug_assert!(
        final_ts <= (1 << (TIMESTAMP_COLUMNS_NUM_BITS * (NUM_TIMESTAMP_COLUMNS_FOR_RAM as u32)))
    );
    proxy.write_timestamp_value_into_columns(machine_state.final_state.timestamp, final_ts);

    let decoder_input = compiled_circuit
        .memory_layout
        .decoder_input
        .as_ref()
        .expect("is present in execution families");
    let decoder_data = proxy
        .oracle
        .get_executor_family_data(proxy.absolute_row_idx);

    assert!(decoder_input.decoder_witness_is_in_memory == false);

    // all decoder values that can be in memory
    {
        if let GKRAddress::BaseLayerMemory(offset) = decoder_input.rs2_index {
            proxy.write_u16_value_into_columns::<true>(offset, decoder_data.rs2_index);
        }
        if let GKRAddress::BaseLayerMemory(offset) = decoder_input.rd_index {
            proxy.write_u8_value_into_columns::<true>(offset, decoder_data.rd_index);
        }
        // rare case when it's in memory
        for (i, el) in decoder_input.circuit_family_mask_bits.iter().enumerate() {
            if let GKRAddress::BaseLayerMemory(circuit_family_extra_mask) = *el {
                let bit = (decoder_data.opcode_family_bits & (1 << i)) > 0;
                proxy.write_boolean_value_into_columns::<true>(circuit_family_extra_mask, bit);
            }
        }
    }

    if COMPUTE_WITNESS {
        // same decoder values that can be in witness

        if let GKRAddress::BaseLayerWitness(offset) = decoder_input.rs2_index {
            proxy.write_u16_value_into_columns::<false>(offset, decoder_data.rs2_index);
        }
        if let GKRAddress::BaseLayerWitness(offset) = decoder_input.rd_index {
            proxy.write_u8_value_into_columns::<false>(offset, decoder_data.rd_index);
        }
        for (i, el) in decoder_input.circuit_family_mask_bits.iter().enumerate() {
            if let GKRAddress::BaseLayerWitness(circuit_family_extra_mask) = *el {
                let bit = (decoder_data.opcode_family_bits & (1 << i)) > 0;
                proxy.write_boolean_value_into_columns::<false>(circuit_family_extra_mask, bit);
            }
        }

        if decoder_input.decoder_witness_is_in_memory == false {
            // these variables are for sure in witness
            proxy.write_u32_value_into_columns::<false>(decoder_input.imm, decoder_data.imm);
            if let Some(funct3) = decoder_input.funct3 {
                if let Some(funct3_value) = decoder_data.funct3 {
                    proxy.write_u8_value_into_columns::<false>(funct3, funct3_value);
                } else {
                    // it should be unsupported and not executed
                    assert!(execute == false, "missing funct3 on the executed row");
                    proxy.write_u8_value_into_columns::<false>(funct3, 0);
                }
            }

            // and count multiplicity right away
            if execute {
                assert!(initial_pc % 4 == 0);
                let idx = (initial_pc / 4) as usize;
                let idx_with_decoder_offset = idx + compiled_circuit.offset_for_decoder_table;
                // count for mapping purposes
                proxy
                    .lookup_mapping_rows_starts
                    .last_mut()
                    .expect("must exist")
                    .write(idx_with_decoder_offset as u32);
                proxy.multiplicity_counting_scratch[idx_with_decoder_offset] += 1;
            }
        } else {
            todo!();
        }
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Machine state processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn gkr_process_shuffle_ram_accesses_in_executor_family<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
    const COMPUTE_WITNESS: bool,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    // debug_assert_eq!(
    //     compiled_circuit
    //         .memory_queries_timestamp_comparison_aux_vars
    //         .len(),
    //     compiled_circuit.memory_layout.shuffle_ram_access_sets.len()
    // );

    let cycle_ts = proxy.oracle.get_timestamp_witness_from_placeholder(
        Placeholder::OpcodeFamilyCycleInitialTimestamp,
        proxy.absolute_row_idx,
    );

    // We also must write down read timestamps, as those are pure witness values from the prover
    for (access_idx, mem_query) in compiled_circuit
        .memory_layout
        .ram_access_sets
        .iter()
        .enumerate()
    {
        match mem_query.get_address() {
            RamAddress::ConstantRegister(..) => {}
            RamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index }) => {
                proxy.write_u16_placeholder_into_columns::<true>(
                    register_index,
                    Placeholder::ShuffleRamAddress(access_idx),
                );

                // proxy.write_u8_placeholder_into_columns::<true>(
                //     register_index,
                //     Placeholder::ShuffleRamAddress(access_idx),
                // );
            }
            RamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                is_register,
                address,
            }) => {
                match is_register {
                    IsRegisterAddress::Is(is_register) => {
                        proxy.write_boolean_placeholder_into_columns::<true>(
                            is_register,
                            Placeholder::ShuffleRamIsRegisterAccess(access_idx),
                        );
                    }
                    IsRegisterAddress::Not(is_register) => {
                        let is_register_flag = Oracle::<F>::get_boolean_witness_from_placeholder(
                            proxy.oracle,
                            Placeholder::ShuffleRamIsRegisterAccess(access_idx),
                            proxy.absolute_row_idx,
                        );
                        let not_register = !is_register_flag;

                        proxy.write_boolean_value_into_columns::<true>(is_register, not_register);
                    }
                }
                proxy.write_u32_placeholder_into_columns::<true>(
                    address,
                    Placeholder::ShuffleRamAddress(access_idx),
                );
            }
            RamAddress::IndirectRam(IndirectRamAccessAddress { .. }) => {
                todo!()
            }
        }

        let read_ts = proxy.oracle.get_timestamp_witness_from_placeholder(
            Placeholder::ShuffleRamReadTimestamp(access_idx),
            proxy.absolute_row_idx,
        );
        proxy.write_timestamp_value_into_columns(mem_query.get_read_timestamp_columns(), read_ts);

        match mem_query.get_read_value_columns() {
            RamWordRepresentation::Zero => {}
            RamWordRepresentation::U16Limbs(read_value) => {
                proxy.write_u32_placeholder_into_columns::<true>(
                    read_value,
                    Placeholder::ShuffleRamReadValue(access_idx),
                );
            }
            RamWordRepresentation::U8Limbs(read_value) => {
                proxy.write_u32_placeholder_as_u8_chunks_into_columns::<true>(
                    read_value,
                    Placeholder::ShuffleRamReadValue(access_idx),
                );
            }
        }

        if let RamQuery::Write(query) = mem_query {
            // also do write
            match query.write_value {
                RamWordRepresentation::Zero => {}
                RamWordRepresentation::U16Limbs(write_value) => {
                    proxy.write_u32_placeholder_into_columns::<true>(
                        write_value,
                        Placeholder::ShuffleRamWriteValue(access_idx),
                    );
                }
                RamWordRepresentation::U8Limbs(write_value) => {
                    proxy.write_u32_placeholder_as_u8_chunks_into_columns::<true>(
                        write_value,
                        Placeholder::ShuffleRamWriteValue(access_idx),
                    );
                }
            }
        }

        if COMPUTE_WITNESS {
            let write_ts = cycle_ts + (mem_query.local_timestamp_in_cycle() as TimestampScalar);

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
                cycle_ts,
            );

            proxy.write_boolean_value_into_columns::<false>(borrow_place, intermediate_borrow);
        }
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Shuffle RAM processing").or_default() += t.elapsed();
    });
}

#[inline]
pub(crate) unsafe fn evaluate_memory_witness_for_executor_family_inner<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    gkr_process_machine_state_assuming_preprocessed_decoder::<F, O, false>(proxy, compiled_circuit);

    gkr_process_shuffle_ram_accesses_in_executor_family::<F, O, false>(proxy, compiled_circuit);

    // we can skip producing any other witness values, because none of them are placed into memory trace
}
