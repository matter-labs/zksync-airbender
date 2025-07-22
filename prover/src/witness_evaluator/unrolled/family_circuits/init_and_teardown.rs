use super::*;
use crate::witness_evaluator::memory_witness::main_circuit::get_aux_boundary_data;

pub fn evaluate_init_and_teardown_memory_witness<A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cycles: usize,
    lazy_init_data: &[LazyInitAndTeardown],
    worker: &Worker,
    allocator: A,
) -> MemoryOnlyWitnessEvaluationData<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    assert!(lazy_init_data.len() > 0);
    assert_eq!(
        lazy_init_data.len(),
        cycles
            * compiled_circuit
                .memory_layout
                .shuffle_ram_inits_and_teardowns
                .len()
    );

    assert_eq!(
        compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .len(),
        compiled_circuit.lazy_init_address_aux_vars.len()
    );

    let trace_len = cycles.next_power_of_two();
    assert_eq!(cycles, trace_len - 1);
    assert_eq!(trace_len, compiled_circuit.trace_len);

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
                    let is_one_before_last_row = absolute_row_idx == trace_len - 2;

                    let memory_trace_view_row = memory_trace_view.current_row();

                    unsafe {
                        evaluate_init_and_teardown_memory_witness_inner(
                            &mut [],
                            memory_trace_view_row,
                            compiled_circuit,
                            absolute_row_idx,
                            is_one_before_last_row,
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
    let aux_boundary_data = get_aux_boundary_data(compiled_circuit, cycles, lazy_init_data);

    let aux_data = WitnessEvaluationAuxData {
        first_row_public_inputs: vec![],
        one_before_last_row_public_inputs: vec![],
        aux_boundary_data,
    };

    MemoryOnlyWitnessEvaluationData {
        aux_data,
        memory_trace: memory_trace_view,
    }
}

#[inline]
unsafe fn evaluate_init_and_teardown_memory_witness_inner(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    absolute_row_idx: usize,
    is_one_before_last_row: bool,
    lazy_init_data: &[LazyInitAndTeardown],
) {
    process_lazy_init_work::<false>(
        witness_row,
        memory_row,
        compiled_circuit,
        absolute_row_idx,
        is_one_before_last_row,
        lazy_init_data,
    );

    // we can skip producing any other witness values, because none of them are placed into memory trace
}

pub fn evaluate_init_and_teardown_witness<A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cycles: usize,
    lazy_init_data: &[LazyInitAndTeardown],
    worker: &Worker,
    allocator: A,
) -> WitnessEvaluationData<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    assert!(lazy_init_data.len() > 0);
    assert_eq!(
        lazy_init_data.len(),
        cycles
            * compiled_circuit
                .memory_layout
                .shuffle_ram_inits_and_teardowns
                .len()
    );

    let trace_len = cycles.next_power_of_two();

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

    assert_eq!(num_lookup_table_encoding_tuples, 0);

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

    let geometry = worker.get_geometry(cycles);
    let mut range_16_multiplicity_subcounters = vec![vec![]; geometry.len()];

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    unsafe {
        worker.scope(cycles, |scope, geometry| {
            let mut range_16_multiplicity_subcounters_chunks =
                range_16_multiplicity_subcounters.array_chunks_mut::<1>();

            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let exec_trace_view = exec_trace.row_view(range.clone());

                let [range_16_multiplicity_subcounters_chunk] =
                    range_16_multiplicity_subcounters_chunks.next().unwrap();

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut range_check_16_multiplicities = vec![0u32; 1 << 16];

                    evaluate_init_and_teardown_witness_inner(
                        exec_trace_view,
                        range,
                        num_witness_columns,
                        compiled_circuit,
                        lazy_init_data,
                        &mut range_check_16_multiplicities,
                        trace_len,
                    );

                    *range_16_multiplicity_subcounters_chunk = range_check_16_multiplicities;
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
            vec![],
            vec![],
            vec![],
            compiled_circuit,
            0,
            trace_len,
            worker,
        )
    };

    // now get aux variables
    let aux_boundary_data = get_aux_boundary_data(compiled_circuit, cycles, lazy_init_data);

    let aux_data = WitnessEvaluationAuxData {
        first_row_public_inputs: vec![],
        one_before_last_row_public_inputs: vec![],
        aux_boundary_data,
    };

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow(|el| {
        for (k, v) in el.iter() {
            println!("Operation `{}` took {:?} in total", k, v);
        }
    });

    WitnessEvaluationData {
        aux_data,
        exec_trace,
        num_witness_columns,
        lookup_mapping,
    }
}

unsafe fn evaluate_init_and_teardown_witness_inner(
    mut exec_trace_view: RowMajorTraceView<Mersenne31Field, DEFAULT_TRACE_PADDING_MULTIPLE>,
    range: std::ops::Range<usize>,
    num_witness_columns: usize,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    lazy_init_data: &[LazyInitAndTeardown],
    range_check_16_multiplicieties: &mut [u32],
    trace_len: usize,
) {
    assert!(trace_len.is_power_of_two());
    for absolute_row_idx in range {
        let is_one_before_last_row = absolute_row_idx == trace_len - 2;

        let (witness_row, memory_row) = exec_trace_view.current_row_split(num_witness_columns);

        // fill the memory and auxiliary witness related to it

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        process_lazy_init_work::<true>(
            witness_row,
            memory_row,
            compiled_circuit,
            absolute_row_idx,
            is_one_before_last_row,
            lazy_init_data,
        );
        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Lazy init/teardown witness work").or_default() += t.elapsed();
        });

        // our witness evaluation would count multiplicities that result in explicit lookups, so we need only
        // to count ones that are from special range-checks

        let setup_row = &[];

        count_special_range_check_multiplicities(
            witness_row,
            memory_row,
            setup_row,
            compiled_circuit,
            absolute_row_idx,
            range_check_16_multiplicieties,
            &mut [],
            Mersenne31Field::ZERO,
            trace_len,
        );

        // and go to the next row
        exec_trace_view.advance_row();
    }
}
