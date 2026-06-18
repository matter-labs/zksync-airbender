use super::*;
use crate::gkr::witness_gen::family_circuits::witness::gkr_count_special_multiplicities;
use crate::gkr::witness_gen::family_circuits::witness::gkr_postprocess_multiplicities;
use crate::gkr::witness_gen::family_circuits::witness::QuasiCell;
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::oracle::Oracle;
use cs::tables::TableDriver;
use fft::GoodAllocator;
use field::PrimeField;
use worker::Worker;

pub fn evaluate_gkr_witness_for_delegation_circuit<
    F: PrimeField,
    O: Oracle<F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    witnes_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, O, F>),
    num_cycles: usize,
    oracle: &O,
    table_driver: &TableDriver<F>,
    worker: &Worker,
    inner_allocator: A,
    outer_allocator: B,
) -> GKRFullWitnessTrace<F, A, B> {
    let trace_len = compiled_circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    assert!(num_cycles <= trace_len);

    let num_memory_columns = compiled_circuit.memory_layout.total_width;
    let num_witness_columns = compiled_circuit.witness_layout.total_width;
    let mut num_generic_lookups = compiled_circuit.generic_lookups.len();
    if compiled_circuit.has_decoder_lookup {
        num_generic_lookups += 1;
    }
    let num_range_check_16_lookups = compiled_circuit.range_check_16_lookup_expressions.len();
    let num_timestamp_range_check_lookups = compiled_circuit
        .timestamp_range_check_lookup_expressions
        .len();

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        el.clear();
    });

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    let mut full_trace = GKRFullWitnessTrace::new(
        trace_len,
        num_memory_columns,
        num_witness_columns,
        compiled_circuit.scratch_space_size,
        num_generic_lookups,
        num_range_check_16_lookups,
        num_timestamp_range_check_lookups,
        inner_allocator,
        outer_allocator,
    );

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Allocate trace holders").or_default() += t.elapsed();
    });

    assert_eq!(table_driver.total_tables_len, compiled_circuit.offset_for_decoder_table,
        "table size diverged between compilation and evaluation: compilation expected {}, while in evaluation it's initialized for {}",
        table_driver.total_tables_len,
        compiled_circuit.offset_for_decoder_table
    );

    let generic_lookup_multiplicities_total_len = compiled_circuit.total_tables_size;

    let geometry = worker.get_geometry(num_cycles);
    let mut range_16_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut timestamp_range_check_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut general_purpose_multiplicity_subcounters = vec![vec![]; geometry.len()];

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    // NOTE: we walk over full trace length (as we have to compute multiplicities even on padding rows)
    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            let (proxies, range_check_16_mappings, timestamp_range_check_mappings) =
                full_trace.make_proxies_for_geometry(oracle, geometry, &table_driver, trace_len);

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

            for (thread_idx, ((proxy, range_check_16_chunk), timestamp_range_check_chunk)) in
                proxies
                    .into_iter()
                    .zip(range_check_16_mappings.into_iter())
                    .zip(timestamp_range_check_mappings.into_iter())
                    .enumerate()
            {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);

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

                let range_check_16_chunk = QuasiCell(range_check_16_chunk);
                let timestamp_range_check_chunk = QuasiCell(timestamp_range_check_chunk);

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let range_check_16_chunk = range_check_16_chunk;
                    let timestamp_range_check_chunk = timestamp_range_check_chunk;

                    let mut proxy = proxy;
                    let mut range_check_16_chunk = range_check_16_chunk.0;
                    let mut timestamp_range_check_chunk = timestamp_range_check_chunk.0;

                    let mut range_check_16_multiplicities = vec![0u32; 1 << 16];
                    let mut timestamp_range_check_multiplicities =
                        vec![0u32; 1 << TIMESTAMP_COLUMNS_NUM_BITS];
                    let mut generic_lookup_multiplicities =
                        vec![0u32; generic_lookup_multiplicities_total_len];
                    proxy.multiplicity_counting_scratch = &mut generic_lookup_multiplicities;

                    evaluate_gkr_witness_for_delegation_circuit_inner(
                        &mut proxy,
                        &mut range_check_16_chunk,
                        &mut timestamp_range_check_chunk,
                        witnes_eval_fn_ptr,
                        range,
                        compiled_circuit,
                        &mut range_check_16_multiplicities,
                        &mut timestamp_range_check_multiplicities,
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

    // everything but multiplicities is there
    full_trace.set_initialized_and_pad(num_cycles, trace_len, compiled_circuit);

    // copy back multiplicities
    if compiled_circuit
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .is_empty()
    {
        // effectively skip
        range_16_multiplicity_subcounters.clear();
    }
    if compiled_circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .is_empty()
    {
        // effectively skip
        general_purpose_multiplicity_subcounters.clear();
    }

    unsafe {
        gkr_postprocess_multiplicities(
            &mut full_trace,
            range_16_multiplicity_subcounters,
            timestamp_range_check_multiplicity_subcounters,
            general_purpose_multiplicity_subcounters,
            compiled_circuit,
            trace_len,
            worker,
        )
    };

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow(|el| {
        for (k, v) in el.iter() {
            println!("Operation `{}` took {:?} in total", k, v);
        }
    });

    full_trace
}

unsafe fn evaluate_gkr_witness_for_delegation_circuit_inner<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    range_check_16_chunk: &mut Box<[*mut u16]>,
    timestamp_range_check_chunk: &mut Box<[*mut u32]>,
    witnes_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, O, F>),
    range: std::ops::Range<usize>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
    trace_len: usize,
) {
    for absolute_row_idx in range {
        // fill the memory and auxiliary witness related to it

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        gkr_evaluate_witness_static_work_for_delegation_circuit(proxy, compiled_circuit);

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Static witness work").or_default() += t.elapsed();
        });

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        // use derived witness evaluation function for everything that circuit ITSELF requests (including oracles)
        (witnes_eval_fn_ptr)(proxy);

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Generated witness evaluation function")
                .or_default() += t.elapsed();
        });

        // our witness evaluation would count multiplicities that result in explicit lookups, so we need only
        // to count ones that are from special range-checks

        gkr_count_special_multiplicities(
            proxy,
            range_check_16_chunk,
            timestamp_range_check_chunk,
            compiled_circuit,
            absolute_row_idx,
            range_check_16_multiplicieties,
            timestamp_range_check_multiplicieties,
        );

        // and go to the next row
        proxy.advance();
        for el in range_check_16_chunk.iter_mut() {
            *el = el.add(1);
        }
        for el in timestamp_range_check_chunk.iter_mut() {
            *el = el.add(1);
        }
    }
}

#[inline]
pub(crate) unsafe fn gkr_evaluate_witness_static_work_for_delegation_circuit<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    use super::memory::*;

    gkr_process_delegation_requests_execution::<F, O>(proxy, compiled_circuit);
    gkr_evaluate_indirect_memory_accesses::<F, O, true>(proxy, compiled_circuit);
}
