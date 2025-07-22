use super::*;
use crate::witness_evaluator::unrolled::family_circuits::memory::*;
use cs::cs::oracle::Oracle;
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::tables::TableDriver;
use fft::GoodAllocator;
use worker::Worker;

pub fn evaluate_witness_for_executor_family<O: Oracle<Mersenne31Field>, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witnes_eval_fn_ptr: fn(&mut SimpleWitnessProxy<'_, O>),
    cycles: usize,
    oracle: &O,
    table_driver: &TableDriver<Mersenne31Field>,
    worker: &Worker,
    allocator: A,
) -> WitnessEvaluationDataForExecutionFamily<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    assert!(compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_empty());
    assert!(compiled_circuit.public_inputs.is_empty());

    let trace_len = cycles.next_power_of_two();
    assert_eq!(cycles, trace_len - 1);

    assert!(
        compiled_circuit
            .witness_layout
            .range_check_16_lookup_expressions
            .len()
            % 2
            == 0
    );

    assert_eq!(cycles, trace_len - 1);
    let num_lookup_table_encoding_tuples = compiled_circuit.witness_layout.width_3_lookups.len();

    let num_witness_columns = compiled_circuit.witness_layout.total_width;
    let num_memory_columns = compiled_circuit.memory_layout.total_width;

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        el.clear();
    });

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();
    // we need some conventional values for undefined witness elements, so we zero it out
    let mut exec_trace = RowMajorTrace::<Mersenne31Field, DEFAULT_TRACE_PADDING_MULTIPLE, _>::new_zeroed_for_size_parallel(
        trace_len,
        num_witness_columns + num_memory_columns,
        allocator.clone(),
        worker,
    );

    let lookup_mapping =
        RowMajorTrace::<u32, DEFAULT_TRACE_PADDING_MULTIPLE, _>::new_zeroed_for_size_parallel(
            trace_len,
            num_lookup_table_encoding_tuples,
            allocator.clone(),
            worker,
        );

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Allocate trace holders").or_default() += t.elapsed();
    });

    #[cfg(feature = "debug_logs")]
    println!(
        "Timestamp contribution from circuit sequence is 0x{:08x}",
        timestamp_high_from_circuit_sequence
    );

    assert_eq!(table_driver.total_tables_len, compiled_circuit.total_tables_size,
        "table size diverged between compilation and evaluation: compilation expected {}, while in evaluation it's initialized for {}",
        table_driver.total_tables_len,
        compiled_circuit.total_tables_size
    );

    let generic_lookup_multiplicities_total_len = table_driver.total_tables_len;

    let geometry = worker.get_geometry(cycles);
    let mut range_16_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut timestamp_range_check_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut general_purpose_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut decoder_multiplicity_subcounters = vec![vec![]; geometry.len()];

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    unsafe {
        worker.scope(cycles, |scope, geometry| {
            let mut range_16_multiplicity_subcounters_chunks =
                range_16_multiplicity_subcounters.array_chunks_mut::<1>();
            let mut timestamp_range_check_multiplicity_subcounters_chunks =
                timestamp_range_check_multiplicity_subcounters.array_chunks_mut::<1>();
            let mut general_purpose_multiplicity_subcounters_chunks =
                general_purpose_multiplicity_subcounters.array_chunks_mut::<1>();
            let mut decoder_multiplicity_subcounters_chunks =
                decoder_multiplicity_subcounters.array_chunks_mut::<1>();

            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let exec_trace_view = exec_trace.row_view(range.clone());
                let lookup_mapping_view = lookup_mapping.row_view(range.clone());

                let [range_16_multiplicity_subcounters_chunk] =
                    range_16_multiplicity_subcounters_chunks.next().unwrap();
                let [timestamp_range_check_multiplicity_subcounters_chunks] =
                    timestamp_range_check_multiplicity_subcounters_chunks
                        .next()
                        .unwrap();
                let [general_purpose_multiplicity_subcounters_chunk] =
                    general_purpose_multiplicity_subcounters_chunks
                        .next()
                        .unwrap();
                let [decoder_multiplicity_subcounters_chunk] =
                    decoder_multiplicity_subcounters_chunks.next().unwrap();

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut range_check_16_multiplicities = vec![0u32; 1 << 16];
                    let mut timestamp_range_check_multiplicities =
                        vec![0u32; 1 << TIMESTAMP_COLUMNS_NUM_BITS];
                    let mut generic_lookup_multiplicities =
                        vec![0u32; generic_lookup_multiplicities_total_len];
                    let mut decoder_multiplicities = vec![0u32; 1 << 20];

                    evaluate_witness_for_executor_family_inner(
                        exec_trace_view,
                        lookup_mapping_view,
                        witnes_eval_fn_ptr,
                        range,
                        num_witness_columns,
                        compiled_circuit,
                        table_driver,
                        oracle,
                        &mut range_check_16_multiplicities,
                        &mut timestamp_range_check_multiplicities,
                        &mut generic_lookup_multiplicities,
                        &mut decoder_multiplicities,
                        trace_len,
                    );

                    *range_16_multiplicity_subcounters_chunk = range_check_16_multiplicities;
                    *timestamp_range_check_multiplicity_subcounters_chunks =
                        timestamp_range_check_multiplicities;
                    *general_purpose_multiplicity_subcounters_chunk = generic_lookup_multiplicities;
                    *decoder_multiplicity_subcounters_chunk = decoder_multiplicities;
                });
            }
        });
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Row-major evaluation").or_default() += t.elapsed();
    });

    // copy back multiplicities

    unsafe {
        postprocess_multiplicities(
            &mut exec_trace,
            num_witness_columns,
            range_16_multiplicity_subcounters,
            timestamp_range_check_multiplicity_subcounters,
            general_purpose_multiplicity_subcounters,
            decoder_multiplicity_subcounters,
            compiled_circuit,
            generic_lookup_multiplicities_total_len,
            trace_len,
            worker,
        )
    };

    let aux_data = ExecutorFamilyWitnessEvaluationAuxData {};

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow(|el| {
        for (k, v) in el.iter() {
            println!("Operation `{}` took {:?} in total", k, v);
        }
    });

    WitnessEvaluationDataForExecutionFamily {
        aux_data,
        exec_trace,
        num_witness_columns,
        lookup_mapping,
    }
}

#[inline]
pub(crate) unsafe fn evaluate_witness_static_work_for_executor_family<
    O: Oracle<Mersenne31Field>,
>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    decoder_multiplicieties: &mut [u32],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
    _is_last_cycle: bool,
) {
    process_machine_state_assuming_preprocessed_decoder::<O, true>(
        witness_row,
        memory_row,
        decoder_multiplicieties,
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

    process_shuffle_ram_accesses_in_executor_family::<O, true>(
        witness_row,
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
    );
}

unsafe fn count_special_multiplicities_for_executor_family(
    witness_trace_view_row: &mut [Mersenne31Field],
    memory_trace_view_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    absolute_row_idx: usize,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
    trace_len: usize,
) {
    assert!(trace_len.is_power_of_two());
    // range check 16 are special-cased in the lookup argument, and we do not need to compute mapping for them
    let num_trivial_relations = compiled_circuit
        .witness_layout
        .range_check_16_columns
        .num_elements();

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    // here we do NOT need extra mapping - we can just use a value!
    for range_check_expression in compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions[..num_trivial_relations]
        .iter()
    {
        let LookupExpression::Variable(place) = range_check_expression else {
            unreachable!()
        };
        let ColumnAddress::WitnessSubtree(offset) = place else {
            unreachable!()
        };
        let value = *witness_trace_view_row.get_unchecked(*offset);
        assert!(
            value.to_reduced_u32() <= u16::MAX as u32,
            "invalid value {:?} in range check 16 trivial expression {:?} at row {}",
            value,
            range_check_expression,
            absolute_row_idx,
        );
        let index = value.to_reduced_u32() as usize;
        *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
    }

    let nontrivial_range_check_16_relations = &compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions[num_trivial_relations..];
    assert!(nontrivial_range_check_16_relations.len() % 2 == 0);

    for range_check_expression in nontrivial_range_check_16_relations.iter() {
        let value = match range_check_expression {
            LookupExpression::Variable(place) => {
                let ColumnAddress::WitnessSubtree(offset) = place else {
                    unreachable!()
                };
                *witness_trace_view_row.get_unchecked(*offset)
            }
            LookupExpression::Expression(constraint) => constraint
                .evaluate_at_row_on_main_domain(&*witness_trace_view_row, &*memory_trace_view_row),
        };
        assert!(
            value.to_reduced_u32() <= u16::MAX as u32,
            "invalid value {:?} in range check 16 expression {:?} at row {}",
            absolute_row_idx,
            range_check_expression,
            value
        );
        let index = value.to_reduced_u32() as usize;
        *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
    }

    // now timestamp related relations - all are non-trivial

    let timestamp_range_check_relations = &compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions;
    assert!(timestamp_range_check_relations.len() % 2 == 0);

    for range_check_expression in timestamp_range_check_relations.iter() {
        let value = match range_check_expression {
            LookupExpression::Variable(place) => {
                let ColumnAddress::WitnessSubtree(offset) = place else {
                    unreachable!()
                };
                *witness_trace_view_row.get_unchecked(*offset)
            }
            LookupExpression::Expression(constraint) => constraint
                .evaluate_at_row_on_main_domain(&*witness_trace_view_row, &*memory_trace_view_row),
        };
        assert!(
            value.to_reduced_u32() < (1 << TIMESTAMP_COLUMNS_NUM_BITS),
            "invalid value {:?} in timestamp range check expression {:?} at row {}",
            value,
            range_check_expression,
            absolute_row_idx,
        );
        let index = value.to_reduced_u32() as usize;
        *timestamp_range_check_multiplicieties.get_unchecked_mut(index) += 1;
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Range check multiplicity counting").or_default() += t.elapsed();
    });
}

unsafe fn evaluate_witness_for_executor_family_inner<O: Oracle<Mersenne31Field>>(
    mut exec_trace_view: RowMajorTraceView<Mersenne31Field, DEFAULT_TRACE_PADDING_MULTIPLE>,
    mut lookup_mapping_view: RowMajorTraceView<u32, DEFAULT_TRACE_PADDING_MULTIPLE>,
    witnes_eval_fn_ptr: fn(&mut SimpleWitnessProxy<'_, O>),
    range: std::ops::Range<usize>,
    num_witness_columns: usize,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    table_driver: &TableDriver<Mersenne31Field>,
    oracle: &O,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
    generic_lookup_multiplicieties: &mut [u32],
    decoder_multiplicieties: &mut [u32],
    trace_len: usize,
) {
    assert!(trace_len.is_power_of_two());
    let cycles = trace_len - 1;
    let scratch_space_size = compiled_circuit.scratch_space_size_for_witness_gen;

    let mut scratch_space = Vec::with_capacity(scratch_space_size);

    for absolute_row_idx in range {
        let is_last_cycle = absolute_row_idx == cycles - 1;

        let (witness_row, memory_row) = exec_trace_view.current_row_split(num_witness_columns);
        let lookup_mapping_row = lookup_mapping_view.current_row();

        // fill the memory and auxiliary witness related to it

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        evaluate_witness_static_work_for_executor_family(
            witness_row,
            memory_row,
            decoder_multiplicieties,
            compiled_circuit,
            oracle,
            absolute_row_idx,
            is_last_cycle,
        );
        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Static witness work").or_default() += t.elapsed();
        });

        scratch_space.clear();
        scratch_space.resize(scratch_space_size, Mersenne31Field::ZERO);

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        let mut proxy = SimpleWitnessProxy {
            witness_row,
            memory_row,
            scratch_space: &mut scratch_space,
            table_driver: table_driver,
            multiplicity_counting_scratch: generic_lookup_multiplicieties,
            lookup_mapping_row,
            oracle,
            absolute_row_idx,
        };

        // use derived witness evaluation function for everything that circuit ITSELF requests (including oracles)
        (witnes_eval_fn_ptr)(&mut proxy);

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Generated witness evaluation function")
                .or_default() += t.elapsed();
        });

        // our witness evaluation would count multiplicities that result in explicit lookups, so we need only
        // to count ones that are from special range-checks

        count_special_multiplicities_for_executor_family(
            witness_row,
            memory_row,
            compiled_circuit,
            absolute_row_idx,
            range_check_16_multiplicieties,
            timestamp_range_check_multiplicieties,
            trace_len,
        );

        // and go to the next row
        exec_trace_view.advance_row();
        lookup_mapping_view.advance_row();
    }
}
