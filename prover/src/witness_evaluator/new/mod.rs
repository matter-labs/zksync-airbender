use super::*;
use crate::witness_evaluator::memory_witness::main_circuit::get_aux_boundary_data;
use crate::WitnessEvaluationData;
use cs::cs::oracle::Oracle;
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::tables::TableDriver;
use fft::GoodAllocator;
use worker::Worker;

mod simple_proxy;
pub use self::simple_proxy::SimpleWitnessProxy;

pub fn evaluate_witness<O: Oracle<Mersenne31Field>, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witnes_eval_fn_ptr: fn(&mut SimpleWitnessProxy<'_, O>),
    cycles: usize,
    oracle: &O,
    lazy_init_data: &[LazyInitAndTeardown],
    table_driver: &TableDriver<Mersenne31Field>,
    circuit_sequence: usize,
    worker: &Worker,
    allocator: A,
) -> WitnessEvaluationData<DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    if compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_empty()
        == false
    {
        assert_eq!(
            lazy_init_data.len(),
            cycles
                * compiled_circuit
                    .memory_layout
                    .shuffle_ram_inits_and_teardowns
                    .len()
        );
    }

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

    // low timestamp chunk comes from the setup's two columns
    let timestamp_high_from_circuit_sequence =
        timestamp_high_contribution_from_circuit_sequence(circuit_sequence, trace_len);

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

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    unsafe {
        worker.scope(cycles, |scope, geometry| {
            let mut range_16_multiplicity_subcounters_chunks = range_16_multiplicity_subcounters
                .as_chunks_mut::<1>()
                .0
                .iter_mut();
            let mut timestamp_range_check_multiplicity_subcounters_chunks =
                timestamp_range_check_multiplicity_subcounters
                    .as_chunks_mut::<1>()
                    .0
                    .iter_mut();
            let mut general_purpose_multiplicity_subcounters_chunks =
                general_purpose_multiplicity_subcounters
                    .as_chunks_mut::<1>()
                    .0
                    .iter_mut();

            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let exec_trace_view = exec_trace.row_view(range.clone());
                let lookup_mapping_view = lookup_mapping.row_view(range.clone());

                // we will want to peek next row
                let lazy_init_data = if compiled_circuit
                    .memory_layout
                    .shuffle_ram_inits_and_teardowns
                    .is_empty()
                    == false
                {
                    lazy_init_data
                } else {
                    &[]
                };

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

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut range_check_16_multiplicities = vec![0u32; 1 << 16];
                    let mut timestamp_range_check_multiplicities =
                        vec![0u32; 1 << TIMESTAMP_COLUMNS_NUM_BITS];
                    let mut generic_lookup_multiplicities =
                        vec![0u32; generic_lookup_multiplicities_total_len];

                    evaluate_witness_inner(
                        exec_trace_view,
                        lookup_mapping_view,
                        witnes_eval_fn_ptr,
                        range,
                        num_witness_columns,
                        compiled_circuit,
                        table_driver,
                        oracle,
                        lazy_init_data,
                        timestamp_high_from_circuit_sequence,
                        &mut range_check_16_multiplicities,
                        &mut timestamp_range_check_multiplicities,
                        &mut generic_lookup_multiplicities,
                        trace_len,
                    );

                    *range_16_multiplicity_subcounters_chunk = range_check_16_multiplicities;
                    *timestamp_range_check_multiplicity_subcounters_chunks =
                        timestamp_range_check_multiplicities;
                    *general_purpose_multiplicity_subcounters_chunk = generic_lookup_multiplicities;
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
            vec![],
            compiled_circuit,
            generic_lookup_multiplicities_total_len,
            trace_len,
            worker,
        )
    };

    // now get aux variables
    let aux_boundary_data = get_aux_boundary_data(compiled_circuit, cycles, lazy_init_data);

    let mut first_row_public_inputs = vec![];
    let mut one_before_last_row_public_inputs = vec![];

    for (location, column_address) in compiled_circuit.public_inputs.iter() {
        match location {
            BoundaryConstraintLocation::FirstRow => {
                let t = exec_trace.row_view(0..1);
                let r = &t.current_row_ref()[..num_witness_columns];
                let value = read_value(*column_address, r, &[]);
                first_row_public_inputs.push(value);
            }
            BoundaryConstraintLocation::OneBeforeLastRow => {
                let t = exec_trace.row_view(cycles - 1..cycles);
                let r = &t.current_row_ref()[..num_witness_columns];
                let value = read_value(*column_address, r, &[]);
                one_before_last_row_public_inputs.push(value);
            }
            BoundaryConstraintLocation::LastRow => {
                panic!("public inputs on the last row are not supported");
            }
        }
    }

    let aux_data = WitnessEvaluationAuxData {
        first_row_public_inputs,
        one_before_last_row_public_inputs,
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

unsafe fn evaluate_witness_inner<O: Oracle<Mersenne31Field>>(
    mut exec_trace_view: RowMajorTraceView<Mersenne31Field, DEFAULT_TRACE_PADDING_MULTIPLE>,
    mut lookup_mapping_view: RowMajorTraceView<u32, DEFAULT_TRACE_PADDING_MULTIPLE>,
    witnes_eval_fn_ptr: fn(&mut SimpleWitnessProxy<'_, O>),
    range: std::ops::Range<usize>,
    num_witness_columns: usize,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    table_driver: &TableDriver<Mersenne31Field>,
    oracle: &O,
    lazy_init_data: &[LazyInitAndTeardown],
    timestamp_high_from_circuit_sequence: TimestampScalar,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
    generic_lookup_multiplicieties: &mut [u32],
    trace_len: usize,
) {
    assert!(trace_len.is_power_of_two());
    let scratch_space_size = compiled_circuit.scratch_space_size_for_witness_gen;

    let mut scratch_space = Vec::with_capacity(scratch_space_size);

    for absolute_row_idx in range {
        let is_one_before_last_row = absolute_row_idx == trace_len - 2;

        let (witness_row, memory_row) = exec_trace_view.current_row_split(num_witness_columns);
        let lookup_mapping_row = lookup_mapping_view.current_row();

        // fill the memory and auxiliary witness related to it

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        evaluate_witness_inner_static_work(
            witness_row,
            memory_row,
            compiled_circuit,
            oracle,
            absolute_row_idx,
            is_one_before_last_row,
            lazy_init_data,
            timestamp_high_from_circuit_sequence,
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

        // we can count multiplicities right away, but need some setup data for it

        let timestamp_high_contribution_if_shuffle_ram = Mersenne31Field(
            (timestamp_high_from_circuit_sequence >> TIMESTAMP_COLUMNS_NUM_BITS) as u32,
        );

        // here we simulate setup, as we only need two values there, that come first
        let [timestamp_low, timestamp_high] =
            row_into_timestamp_limbs_for_setup(absolute_row_idx as u32);
        let setup_row = [
            Mersenne31Field(timestamp_low),
            Mersenne31Field(timestamp_high),
        ];

        // our witness evaluation would count multiplicities that result in explicit lookups, so we need only
        // to count ones that are from special range-checks

        count_special_range_check_multiplicities(
            witness_row,
            memory_row,
            &setup_row,
            compiled_circuit,
            absolute_row_idx,
            range_check_16_multiplicieties,
            timestamp_range_check_multiplicieties,
            timestamp_high_contribution_if_shuffle_ram,
            trace_len,
        );

        // and go to the next row
        exec_trace_view.advance_row();
        lookup_mapping_view.advance_row();
    }
}
