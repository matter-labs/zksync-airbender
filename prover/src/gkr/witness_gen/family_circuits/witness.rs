use super::*;
use crate::witness_evaluator::utils::encoding_tuple_into_lookup_index;
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::cs::oracle::Oracle;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::tables::TableDriver;
use fft::GoodAllocator;
use field::PrimeField;
use worker::Worker;
use worker::WorkerGeometry;

struct QuasiCell<T: Sized>(Box<[*mut T]>);
unsafe impl Send for QuasiCell<u32> {}
unsafe impl Send for QuasiCell<u16> {}

#[derive(Clone, Debug)]
pub struct GKRFullWitnessTrace<F: PrimeField, A: Allocator + Clone, B: Allocator + Clone> {
    pub column_major_memory_trace: Vec<Vec<F, A>, B>,
    pub column_major_witness_trace: Vec<Vec<F, A>, B>,
    // we will use it for stage 2 - we can map (for free) every lookup tuple into the
    // corresponding index of the lookup tables (and more precisely - in the concatenation of all the tables)
    pub generic_lookup_mapping: Vec<Vec<u32, A>, B>,
    pub range_check_16_lookup_mapping: Vec<Vec<u16, A>, B>,
    pub timestamp_range_check_lookup_mapping: Vec<Vec<u32, A>, B>,
}

pub(crate) fn make_vec_vec<T: Sized, A: Allocator + Clone, B: Allocator + Clone>(
    inner_capacity: usize,
    num_vectors: usize,
    inner_allocator: A,
    outer_allocator: B,
) -> Vec<Vec<T, A>, B> {
    let mut result = Vec::with_capacity_in(num_vectors, outer_allocator);
    for _ in 0..num_vectors {
        result.push(Vec::with_capacity_in(
            inner_capacity,
            inner_allocator.clone(),
        ));
    }

    result
}

impl<F: PrimeField, A: Allocator + Clone, B: Allocator + Clone> GKRFullWitnessTrace<F, A, B> {
    pub fn new(
        trace_len: usize,
        num_memory_columns: usize,
        num_witness_columns: usize,
        num_generic_lookups: usize,
        num_range_check_16_lookups: usize,
        num_timestamp_range_check_lookups: usize,
        inner_allocator: A,
        outer_allocator: B,
    ) -> Self {
        // We allocate, but do not initialize, as we will use all the rows, and default padding is not guaranteed
        // to be zero one in general

        let column_major_memory_trace = make_vec_vec(
            trace_len,
            num_memory_columns,
            inner_allocator.clone(),
            outer_allocator.clone(),
        );
        let column_major_witness_trace = make_vec_vec(
            trace_len,
            num_witness_columns,
            inner_allocator.clone(),
            outer_allocator.clone(),
        );

        let generic_lookup_mapping = make_vec_vec(
            trace_len,
            num_generic_lookups,
            inner_allocator.clone(),
            outer_allocator.clone(),
        );
        let range_check_16_lookup_mapping = make_vec_vec(
            trace_len,
            num_range_check_16_lookups,
            inner_allocator.clone(),
            outer_allocator.clone(),
        );
        let timestamp_range_check_lookup_mapping = make_vec_vec(
            trace_len,
            num_timestamp_range_check_lookups,
            inner_allocator.clone(),
            outer_allocator.clone(),
        );

        Self {
            column_major_memory_trace,
            column_major_witness_trace,
            generic_lookup_mapping,
            range_check_16_lookup_mapping,
            timestamp_range_check_lookup_mapping,
        }
    }

    pub fn make_proxies_for_geometry<'a, O: Oracle<F> + 'a>(
        &'a mut self,
        oracle: &'a O,
        geometry: WorkerGeometry,
        table_driver: &'a TableDriver<F>,
        scratch_space_size: usize,
        trace_len: usize,
    ) -> (
        Vec<ColumnMajorWitnessProxy<'a, O, F>>,
        Vec<Box<[*mut u16]>>,
        Vec<Box<[*mut u32]>>,
    ) {
        let mut proxies = Vec::with_capacity(geometry.len());
        let mut range_check_16_chunks = Vec::with_capacity(geometry.len());
        let mut timestamp_range_check_chunks = Vec::with_capacity(geometry.len());

        let mut total_chunked = 0;
        let mut column_major_witness_trace_start_ptrs: Vec<_> = self
            .column_major_witness_trace
            .iter_mut()
            .map(|el| el.as_mut_ptr())
            .collect();

        let mut column_major_memory_trace_start_ptrs: Vec<_> = self
            .column_major_memory_trace
            .iter_mut()
            .map(|el| el.as_mut_ptr())
            .collect();

        let mut generic_lookup_mapping_start_ptrs: Vec<_> = self
            .generic_lookup_mapping
            .iter_mut()
            .map(|el| el.as_mut_ptr())
            .collect();

        let mut range_check_16_lookup_mapping_start_ptrs: Vec<_> = self
            .range_check_16_lookup_mapping
            .iter_mut()
            .map(|el| el.as_mut_ptr())
            .collect();

        let mut timestamp_range_check_lookup_mapping_start_ptrs: Vec<_> = self
            .timestamp_range_check_lookup_mapping
            .iter_mut()
            .map(|el| el.as_mut_ptr())
            .collect();

        for chunk_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(chunk_idx);
            let proxy = ColumnMajorWitnessProxy {
                witness_rows_starts: column_major_witness_trace_start_ptrs
                    .clone()
                    .into_boxed_slice(),
                memory_rows_starts: column_major_memory_trace_start_ptrs
                    .clone()
                    .into_boxed_slice(),
                scratch_space: vec![F::ZERO; scratch_space_size].into_boxed_slice(),
                table_driver,
                multiplicity_counting_scratch: &mut [],
                lookup_mapping_rows_starts: generic_lookup_mapping_start_ptrs
                    .clone()
                    .into_boxed_slice(),
                oracle,
                absolute_row_idx: total_chunked,
            };
            proxies.push(proxy);

            range_check_16_chunks.push(
                range_check_16_lookup_mapping_start_ptrs
                    .clone()
                    .into_boxed_slice(),
            );
            timestamp_range_check_chunks.push(
                timestamp_range_check_lookup_mapping_start_ptrs
                    .clone()
                    .into_boxed_slice(),
            );

            for el in column_major_witness_trace_start_ptrs.iter_mut() {
                unsafe {
                    *el = el.add(chunk_size);
                }
            }
            for el in column_major_memory_trace_start_ptrs.iter_mut() {
                unsafe {
                    *el = el.add(chunk_size);
                }
            }
            for el in generic_lookup_mapping_start_ptrs.iter_mut() {
                unsafe {
                    *el = el.add(chunk_size);
                }
            }

            for el in range_check_16_lookup_mapping_start_ptrs.iter_mut() {
                unsafe {
                    *el = el.add(chunk_size);
                }
            }
            for el in timestamp_range_check_lookup_mapping_start_ptrs.iter_mut() {
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

        (proxies, range_check_16_chunks, timestamp_range_check_chunks)
    }

    pub(crate) fn set_initialized_and_pad(
        &mut self,
        num_cycles: usize,
        trace_len: usize,
        compiled_circuit: &GKRCircuitArtifact<F>,
    ) {
        unsafe {
            assert!(num_cycles <= trace_len);
            for el in self.column_major_memory_trace.iter_mut() {
                debug_assert!(el.is_empty());
                el.set_len(trace_len);
                // el.set_len(num_cycles);
                // el.resize(trace_len, F::ZERO);
            }

            for el in self.generic_lookup_mapping.iter_mut() {
                debug_assert!(el.is_empty());
                el.set_len(trace_len);
                // el.set_len(num_cycles);
                // el.resize(trace_len, 0);
            }

            for el in self.range_check_16_lookup_mapping.iter_mut() {
                debug_assert!(el.is_empty());
                el.set_len(trace_len);
                // el.set_len(num_cycles);
                // el.resize(trace_len, 0);
            }

            for el in self.timestamp_range_check_lookup_mapping.iter_mut() {
                debug_assert!(el.is_empty());
                el.set_len(trace_len);
                // el.set_len(num_cycles);
                // el.resize(trace_len, 0);
            }

            // and witness should skip multiplicities
            for (idx, el) in self.column_major_witness_trace.iter_mut().enumerate() {
                if idx
                    == compiled_circuit
                        .witness_layout
                        .multiplicities_columns_for_range_check_16
                    || idx
                        == compiled_circuit
                            .witness_layout
                            .multiplicities_columns_for_timestamp_range_check
                    || compiled_circuit
                        .witness_layout
                        .multiplicities_columns_for_generic_lookup
                        .contains(&idx)
                {
                    el.resize(trace_len, F::ZERO);
                } else {
                    el.set_len(trace_len);
                    // el.set_len(num_cycles);
                    // el.resize(trace_len, F::ZERO);
                }
            }

            // non_trivial_padding_convention_for_executor_circuit_memory(&mut self.column_major_memory_trace, compiled_circuit, num_cycles);

            // // In case of padding rows intermediate borrow is always present
            // for el in compiled_circuit.aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars.iter() {
            //     let offset = el.intermediate_borrow.offset();
            //     self.column_major_witness_trace[offset][num_cycles..].fill(F::ONE);
            // }
        }
    }
}

pub fn evaluate_gkr_witness_for_executor_family<
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
    let mut num_generic_lookups = compiled_circuit.witness_layout.generic_lookups.len();
    if compiled_circuit.has_decoder_lookup {
        num_generic_lookups += 1;
    }
    let num_range_check_16_lookups = compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions
        .len();
    let num_timestamp_range_check_lookups = compiled_circuit
        .witness_layout
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

    assert_eq!(
        compiled_circuit.offset_for_decoder_table,
        table_driver.total_tables_len
    );

    let geometry = worker.get_geometry(num_cycles);
    let mut range_16_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut timestamp_range_check_multiplicity_subcounters = vec![vec![]; geometry.len()];
    let mut general_purpose_multiplicity_subcounters = vec![vec![]; geometry.len()];

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    // NOTE: we walk over full trace length (as we have to compute multiplicities even on padding rows)
    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            let (proxies, range_check_16_mappings, timestamp_range_check_mappings) = full_trace
                .make_proxies_for_geometry(
                    oracle,
                    geometry,
                    &table_driver,
                    compiled_circuit.scratch_space_size,
                    trace_len,
                );

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

                    gkr_evaluate_witness_for_executor_family_inner(
                        &mut proxy,
                        &mut range_check_16_chunk,
                        &mut timestamp_range_check_chunk,
                        witnes_eval_fn_ptr,
                        range,
                        compiled_circuit,
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

    // everything but multiplicities is there
    full_trace.set_initialized_and_pad(num_cycles, trace_len, compiled_circuit);

    // copy back multiplicities

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

unsafe fn gkr_evaluate_witness_for_executor_family_inner<'a, F: PrimeField, O: Oracle<F> + 'a>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    range_check_16_chunk: &mut Box<[*mut u16]>,
    timestamp_range_check_chunk: &mut Box<[*mut u32]>,
    witnes_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, O, F>),
    range: std::ops::Range<usize>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
    generic_lookup_multiplicieties: &mut [u32],
    trace_len: usize,
) {
    for absolute_row_idx in range {
        // fill the memory and auxiliary witness related to it

        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        gkr_evaluate_witness_static_work_for_executor_family(
            proxy,
            compiled_circuit,
            generic_lookup_multiplicieties,
        );

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

        gkr_count_special_multiplicities_for_executor_family(
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
pub(crate) unsafe fn gkr_evaluate_witness_static_work_for_executor_family<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    generic_lookup_multiplicieties: &mut [u32],
) {
    use crate::gkr::witness_gen::family_circuits::memory::*;

    gkr_process_machine_state_assuming_preprocessed_decoder::<F, O, true>(
        proxy,
        compiled_circuit,
        generic_lookup_multiplicieties,
    );

    gkr_process_shuffle_ram_accesses_in_executor_family::<F, O, true>(proxy, compiled_circuit);
}

pub(crate) unsafe fn gkr_count_special_multiplicities_for_executor_family<
    'a,
    F: PrimeField,
    O: Oracle<F> + 'a,
>(
    proxy: &mut ColumnMajorWitnessProxy<'a, O, F>,
    range_check_16_chunk: &mut Box<[*mut u16]>,
    timestamp_range_check_chunk: &mut Box<[*mut u32]>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    absolute_row_idx: usize,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
) {
    // range check 16 are special-cased in the lookup argument, and we do not need to compute mapping for them

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    for (idx, range_check_expression) in compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions
        .iter()
        .enumerate()
    {
        let value = evaluate_linear_relation(&range_check_expression.input, &*proxy);
        assert!(
            value.as_u32_reduced() <= u16::MAX as u32,
            "invalid value {:?} in range check 16 expression {:?} at row {}",
            absolute_row_idx,
            range_check_expression,
            value
        );
        let index = value.as_u32_reduced() as usize;
        debug_assert!(idx < range_check_16_chunk.len());
        range_check_16_chunk
            .get_unchecked_mut(idx)
            .write(index as u16);
        *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
    }

    // // special case for lazy init values
    // for shuffle_ram_inits_and_teardowns in compiled_circuit
    //     .memory_layout
    //     .shuffle_ram_inits_and_teardowns
    //     .iter()
    // {
    //     let start = shuffle_ram_inits_and_teardowns
    //         .lazy_init_addresses_columns
    //         .start();
    //     for offset in start..(start + 2) {
    //         let value = *memory_trace_view_row.get_unchecked(offset);
    //         assert!(
    //             value.to_reduced_u32() <= u16::MAX as u32,
    //             "invalid value {:?} in range check 16 in lazy init addresses at row {}",
    //             absolute_row_idx,
    //             value
    //         );
    //         let index = value.to_reduced_u32() as usize;
    //         *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
    //     }
    // }

    // now timestamp related relations - all are non-trivial

    let timestamp_range_check_relations = &compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions;
    assert!(timestamp_range_check_relations.len() % 2 == 0);

    for (idx, range_check_expression) in timestamp_range_check_relations.iter().enumerate() {
        let value = evaluate_linear_relation(&range_check_expression.input, &*proxy);
        assert!(
            value.as_u32_reduced() < (1u32 << TIMESTAMP_COLUMNS_NUM_BITS),
            "invalid value {:?} in timestamp range check expression {:?} at row {}",
            value,
            range_check_expression,
            absolute_row_idx,
        );
        let index = value.as_u32_reduced() as usize;
        debug_assert!(idx < timestamp_range_check_chunk.len());
        timestamp_range_check_chunk
            .get_unchecked_mut(idx)
            .write(index as u32);
        *timestamp_range_check_multiplicieties.get_unchecked_mut(index) += 1;
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Range check multiplicity counting").or_default() += t.elapsed();
    });
}

unsafe fn gkr_postprocess_multiplicities<
    F: PrimeField,
    A: Allocator + Clone,
    B: Allocator + Clone,
>(
    exec_trace: &mut GKRFullWitnessTrace<F, A, B>,
    mut range_16_multiplicity_subcounters: Vec<Vec<u32>>,
    mut timestamp_range_check_multiplicity_subcounters: Vec<Vec<u32>>,
    mut general_purpose_multiplicity_subcounters: Vec<Vec<u32>>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    trace_len: usize,
    worker: &Worker,
) {
    let generic_lookup_multiplicities_total_len = compiled_circuit.total_tables_size;

    // it's just fine to copy in the non-parallel manner for the range-check 16 and timestamp
    if range_16_multiplicity_subcounters.len() > 0 {
        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        let mut range_16_multiplicities = range_16_multiplicity_subcounters.pop().unwrap();
        for el in range_16_multiplicity_subcounters.into_iter() {
            assert_eq!(range_16_multiplicities.len(), el.len());

            for (dst, src) in range_16_multiplicities.iter_mut().zip(el.into_iter()) {
                *dst += src;
            }
        }

        // write them column_major
        unsafe {
            let offset = compiled_circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16;
            let dst = &mut exec_trace.column_major_witness_trace[offset];
            assert_eq!(dst.len(), trace_len);
            assert!(trace_len >= 1 << 16);
            for absolute_row_idx in 0..(1 << 16) {
                let multiplicity = *range_16_multiplicities.get_unchecked(absolute_row_idx);
                debug_assert!(multiplicity < F::CHARACTERISTICS as u32);
                *dst.get_unchecked_mut(absolute_row_idx) =
                    F::from_u32_unchecked(multiplicity as u32);
            }
        }

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Range check 16 multiplicity copy-back")
                .or_default() += t.elapsed();
        });
    }

    // add up and write timestamp multiplicities
    if timestamp_range_check_multiplicity_subcounters.len() > 0 {
        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        let mut timestamp_range_check_multiplicities =
            timestamp_range_check_multiplicity_subcounters
                .pop()
                .unwrap();
        for el in timestamp_range_check_multiplicity_subcounters.into_iter() {
            assert_eq!(timestamp_range_check_multiplicities.len(), el.len());

            for (dst, src) in timestamp_range_check_multiplicities
                .iter_mut()
                .zip(el.into_iter())
            {
                *dst += src;
            }
        }

        // write them column_major
        unsafe {
            let offset = compiled_circuit
                .witness_layout
                .multiplicities_columns_for_timestamp_range_check;
            let dst = &mut exec_trace.column_major_witness_trace[offset];
            assert_eq!(dst.len(), trace_len);
            assert!(trace_len >= 1 << TIMESTAMP_COLUMNS_NUM_BITS);
            for absolute_row_idx in 0..(1 << TIMESTAMP_COLUMNS_NUM_BITS) {
                let multiplicity =
                    *timestamp_range_check_multiplicities.get_unchecked(absolute_row_idx);
                debug_assert!(multiplicity < F::CHARACTERISTICS as u32);
                *dst.get_unchecked_mut(absolute_row_idx) =
                    F::from_u32_unchecked(multiplicity as u32);
            }
        }

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Timestamp range check multiplicity copy-back")
                .or_default() += t.elapsed();
        });
    }

    // now it's a little bit more tricky, we will walk over rows, and access semi-arbitrary indexes for lookups

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    if generic_lookup_multiplicities_total_len > 0 {
        let mut general_purpose_multiplicity =
            general_purpose_multiplicity_subcounters.pop().unwrap();

        if worker.num_cores > 1 {
            worker.scope(general_purpose_multiplicity.len(), |scope, geometry| {
                let mut dst_slice = &mut general_purpose_multiplicity[..];
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let range = chunk_start..(chunk_start + chunk_size);

                    let (dst, rest) = dst_slice.split_at_mut(chunk_size);
                    dst_slice = rest;

                    if thread_idx == geometry.len() - 1 {
                        assert!(dst_slice.is_empty());
                    }

                    let sources = general_purpose_multiplicity_subcounters
                        .iter()
                        .map(move |el| &el[range.clone()]);

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for src in sources {
                            assert_eq!(dst.len(), src.len());
                            for (dst, src) in dst.iter_mut().zip(src.iter()) {
                                *dst += *src;
                            }
                        }
                    });
                }
            });
        } else {
            // nothing
        }

        // and copy it back

        let encoding_capacity = trace_len;
        let general_purpose_multiplicity_ref = &general_purpose_multiplicity;

        unsafe {
            assert_eq!(
                compiled_circuit
                    .witness_layout
                    .multiplicities_columns_for_generic_lookup
                    .len(),
                1
            );
            // TODO: support > 1
            let mut backing = &mut exec_trace.column_major_witness_trace[compiled_circuit
                .witness_layout
                .multiplicities_columns_for_generic_lookup
                .start][..];

            worker.scope(trace_len, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let (dst, rest) = backing.split_at_mut(chunk_size);
                    backing = rest;

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for i in 0..chunk_size {
                            let absolute_row_idx = chunk_start + i;

                            let encoding_index = encoding_tuple_into_lookup_index(
                                0 as u32,
                                absolute_row_idx as u32,
                                encoding_capacity,
                            );
                            if encoding_index < general_purpose_multiplicity_ref.len() {
                                // so it's used
                                let multiplicity =
                                    *general_purpose_multiplicity_ref.get_unchecked(encoding_index);
                                debug_assert!(multiplicity < F::CHARACTERISTICS as u32);
                                *dst.get_unchecked_mut(i) =
                                    F::from_u32_unchecked(multiplicity as u32);
                            }

                            // for (column, dst) in dst.iter_mut().enumerate() {
                            //     use crate::utils::encoding_tuple_into_lookup_index;
                            //     let encoding_index = encoding_tuple_into_lookup_index(
                            //         column as u32,
                            //         absolute_row_idx as u32,
                            //         encoding_capacity,
                            //     );
                            //     if encoding_index < general_purpose_multiplicity_ref.len() {
                            //         // so it's used
                            //         let multiplicity = *general_purpose_multiplicity_ref
                            //             .get_unchecked(encoding_index);
                            //         debug_assert!(multiplicity < F::CHARACTERISTICS as u32);
                            //         *dst.get_unchecked_mut() = F::from_u32_unchecked(multiplicity as u64);
                            //     } else {
                            //         todo!()
                            //     }
                            // }
                        }
                    });
                }
            });
        }
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Multiplicities copy-back took").or_default() += t.elapsed();
    });
}
