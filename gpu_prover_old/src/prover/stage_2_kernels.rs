use super::arg_utils::*;
use super::context::DeviceProperties;
use super::unrolled_prover::stage_2_ram_shared::{
    stage2_process_lazy_init_and_ram_access,
    stage2_process_registers_and_indirect_access_in_delegation,
};
use super::unrolled_prover::stage_2_shared::{
    get_stage_2_e4_scratch, stage2_col_sum_adjustments_and_grand_product,
    stage2_handle_delegation_requests, stage2_process_delegations,
    stage2_process_generic_lookup_entry_invs_and_multiplicity,
    stage2_process_generic_lookup_intermediate_polys, stage2_process_lazy_init_range_checks,
    stage2_process_range_check_16_entry_invs_and_multiplicity,
    stage2_process_range_check_16_expressions, stage2_process_range_check_16_trivial_checks,
    stage2_process_timestamp_range_check_entry_invs_and_multiplicity,
    stage2_process_timestamp_range_check_expressions,
    stage2_process_timestamp_range_check_expressions_with_extra_timestamp_contribution,
    stage2_zero_last_row,
};
use crate::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
};
use crate::field::{BaseField, Ext4Field};
use crate::ops_simple::set_to_zero;

use cs::definitions::{NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE, TIMESTAMP_COLUMNS_NUM_BITS};
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::Field;
use prover::prover_stages::cached_data::ProverCachedData;

type BF = BaseField;
type E4 = Ext4Field;

pub fn compute_stage_2_args_on_main_domain(
    setup_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    generic_lookups_args_to_table_entries_map: &(impl DeviceMatrixChunkImpl<u32> + ?Sized),
    stage_2_cols: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    scratch_for_aggregated_entry_invs: &mut DeviceSlice<E4>,
    scratch_for_cub_ops: &mut DeviceSlice<u8>,
    maybe_batch_reduce_intermediates: &mut Option<&mut DeviceSlice<BF>>,
    scratch_for_col_sums: &mut DeviceSlice<BF>,
    lookup_challenges: &DeviceVariable<LookupChallenges>,
    // decoder_table_challenges: &DeviceVariable<DecoderTableChallenges>,
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    log_n: u32,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert_eq!(REGISTER_SIZE, 2);
    assert_eq!(NUM_TIMESTAMP_COLUMNS_FOR_RAM, 2);
    let n = 1 << log_n;
    let num_generic_table_rows = circuit.total_tables_size;
    let num_setup_cols = circuit.setup_layout.total_width;
    let num_witness_cols = circuit.witness_layout.total_width;
    let num_memory_cols = circuit.memory_layout.total_width;
    let num_generic_args = circuit
        .stage_2_layout
        .intermediate_polys_for_generic_lookup
        .num_elements();
    let num_memory_args = circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .num_elements();
    let num_init_teardown_sets = circuit
        .stage_2_layout
        .intermediate_polys_for_memory_init_teardown
        .num_elements();
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    assert_eq!(setup_cols.rows(), n);
    assert_eq!(setup_cols.cols(), num_setup_cols);
    assert_eq!(witness_cols.rows(), n);
    assert_eq!(witness_cols.cols(), num_witness_cols,);
    assert_eq!(memory_cols.rows(), n);
    assert_eq!(memory_cols.cols(), num_memory_cols,);
    assert_eq!(stage_2_cols.rows(), n);
    assert_eq!(stage_2_cols.cols(), circuit.stage_2_layout.total_width);
    assert_eq!(
        stage_2_cols.cols(),
        4 * (((num_stage_2_bf_cols + 3) / 4) + num_stage_2_e4_cols)
    );
    assert_eq!(
        scratch_for_aggregated_entry_invs.len(),
        get_stage_2_e4_scratch(n, circuit),
    );
    // for convenience, demarcate bf and vectorized e4 sections of stage_2_cols
    let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
    assert_eq!(e4_cols_offset % 4, 0);
    assert!(num_stage_2_bf_cols <= e4_cols_offset);
    assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
    // the above should also suffice to show e4_cols_offset = 4 * ceil(num_stage_2_bf_cols / 4)
    // which implies stage_2_cols.cols() = e4_cols_offset + num_stage_2_e4_cols
    let (mut stage_2_bf_cols, mut stage_2_e4_cols) = {
        let stride = stage_2_cols.stride();
        let offset = stage_2_cols.offset();
        let slice = stage_2_cols.slice_mut();
        // Make sure we zero any padding cols
        for padding_offset in num_stage_2_bf_cols..e4_cols_offset {
            let padding_slice_start = stride * padding_offset + offset;
            set_to_zero(
                &mut slice[padding_slice_start..padding_slice_start + n],
                stream,
            )?;
        }
        let (bf_slice, e4_slice) = slice.split_at_mut(e4_cols_offset * stride);
        (
            DeviceMatrixChunkMut::new(
                &mut bf_slice[0..num_stage_2_bf_cols * stride],
                stride,
                offset,
                n,
            ),
            DeviceMatrixChunkMut::new(e4_slice, stride, offset, n),
        )
    };
    let translate_e4_offset = |raw_col: usize| -> usize {
        assert_eq!(raw_col % 4, 0);
        assert!(raw_col >= e4_cols_offset);
        (raw_col - e4_cols_offset) / 4
    };
    // Retrieve lookup-related offsets and check assumptions
    // Much of the metadata in this struct is unnecessary or recomputed
    // by other means below, but some items are directly useful
    // and some are useful for doublechecks.
    let ProverCachedData {
        trace_len,
        memory_timestamp_high_from_circuit_idx,
        delegation_type,
        memory_argument_challenges,
        delegation_challenges,
        process_shuffle_ram_init,
        shuffle_ram_inits_and_teardowns,
        lazy_init_address_range_check_16,
        handle_delegation_requests,
        delegation_request_layout,
        process_batch_ram_access,
        process_registers_and_indirect_access,
        delegation_processor_layout,
        process_delegations,
        delegation_processing_aux_poly,
        num_set_polys_for_memory_shuffle,
        offset_for_grand_product_accumulation_poly: _,
        range_check_16_multiplicities_src,
        range_check_16_multiplicities_dst,
        timestamp_range_check_multiplicities_src,
        timestamp_range_check_multiplicities_dst,
        generic_lookup_multiplicities_src_start,
        generic_lookup_multiplicities_dst_start,
        generic_lookup_setup_columns_start,
        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
        ..
    } = cached_data.clone();
    if process_batch_ram_access {
        panic!("deprecated");
    }
    assert_eq!(trace_len, n);
    assert_eq!(
        circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .num_elements(),
        1,
    );
    assert_eq!(
        circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            .num_elements(),
        1,
    );
    let num_generic_multiplicities_cols = circuit
        .setup_layout
        .generic_lookup_setup_columns
        .num_elements();
    assert_eq!(circuit.setup_layout.generic_lookup_setup_columns.width(), 4,);
    assert_eq!(
        num_generic_multiplicities_cols,
        circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .num_elements(),
    );
    assert_eq!(
        generic_lookup_setup_columns_start,
        circuit.setup_layout.generic_lookup_setup_columns.start()
    );
    assert_eq!(process_shuffle_ram_init, num_init_teardown_sets > 0);
    assert_eq!(
        num_init_teardown_sets,
        shuffle_ram_inits_and_teardowns.len()
    );
    assert_eq!(
        num_init_teardown_sets,
        lazy_init_address_range_check_16
            .base_field_oracles
            .num_elements()
    );
    assert_eq!(
        num_init_teardown_sets,
        lazy_init_address_range_check_16
            .ext_4_field_oracles
            .num_elements()
    );
    let delegation_aux_poly_col = if handle_delegation_requests || process_delegations {
        translate_e4_offset(delegation_processing_aux_poly.start())
    } else {
        0
    };
    // overall size checks
    let mut num_expected_bf_args = 0;
    // we assume (and assert later) that the numbers of range check 8 and 16 cols are both even.
    num_expected_bf_args += circuit.witness_layout.range_check_16_columns.num_elements() / 2;
    num_expected_bf_args += range_check_16_width_1_lookups_access_via_expressions.len();
    num_expected_bf_args += timestamp_range_check_width_1_lookups_access_via_expressions.len();
    num_expected_bf_args +=
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.len();
    if process_shuffle_ram_init {
        // lazy init address cols are treated as 1 pair of range check 16
        num_expected_bf_args += lazy_init_address_range_check_16
            .base_field_oracles
            .num_elements();
    }
    assert_eq!(num_stage_2_bf_cols, num_expected_bf_args);
    let mut num_expected_e4_args = 0;
    num_expected_e4_args += 1; // range check 16 multiplicities dst
    num_expected_e4_args += 1; // timestamp range check multiplicities dst
    num_expected_e4_args += num_generic_multiplicities_cols;
    num_expected_e4_args += num_expected_bf_args; // each bf arg should have a corresponding e4 arg
    num_expected_e4_args += num_generic_args;
    if handle_delegation_requests || process_delegations {
        num_expected_e4_args += 1; // delegation_processing_aux_poly
    }
    if process_shuffle_ram_init {
        num_expected_e4_args += lazy_init_address_range_check_16
            .ext_4_field_oracles
            .num_elements();
    }
    num_expected_e4_args += num_memory_args;
    num_expected_e4_args += 1; // memory grand product
    assert_eq!(num_stage_2_e4_cols, num_expected_e4_args);
    let setup_cols = setup_cols.as_ptr_and_stride();
    let witness_cols = witness_cols.as_ptr_and_stride();
    let memory_cols = memory_cols.as_ptr_and_stride();
    let d_stage_2_e4_cols = stage_2_e4_cols.as_mut_ptr_and_stride();
    let d_stage_2_bf_cols = stage_2_bf_cols.as_mut_ptr_and_stride();
    let (aggregated_entry_invs_for_range_check_16, aggregated_entry_invs) =
        scratch_for_aggregated_entry_invs.split_at_mut(1 << 16);
    let (aggregated_entry_invs_for_timestamp_range_checks, aggregated_entry_invs) =
        aggregated_entry_invs.split_at_mut(1 << TIMESTAMP_COLUMNS_NUM_BITS);
    let (aggregated_entry_invs_for_generic_lookups, _) =
        aggregated_entry_invs.split_at_mut(circuit.total_tables_size);
    let aggregated_entry_invs_for_range_check_16 =
        aggregated_entry_invs_for_range_check_16.as_mut_ptr();
    let aggregated_entry_invs_for_timestamp_range_checks =
        aggregated_entry_invs_for_timestamp_range_checks.as_mut_ptr();
    let aggregated_entry_invs_for_generic_lookups =
        aggregated_entry_invs_for_generic_lookups.as_mut_ptr();
    let lookup_challenges = lookup_challenges.as_ptr();

    stage2_zero_last_row(
        d_stage_2_bf_cols,
        d_stage_2_e4_cols,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        log_n,
        stream,
    )?;

    stage2_process_range_check_16_entry_invs_and_multiplicity(
        lookup_challenges,
        setup_cols,
        witness_cols,
        aggregated_entry_invs_for_range_check_16,
        d_stage_2_e4_cols,
        range_check_16_multiplicities_src,
        range_check_16_multiplicities_dst,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    stage2_process_timestamp_range_check_entry_invs_and_multiplicity(
        lookup_challenges,
        setup_cols,
        witness_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        d_stage_2_e4_cols,
        timestamp_range_check_multiplicities_src,
        timestamp_range_check_multiplicities_dst,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    stage2_process_generic_lookup_entry_invs_and_multiplicity(
        lookup_challenges,
        setup_cols,
        witness_cols,
        aggregated_entry_invs_for_generic_lookups,
        d_stage_2_e4_cols,
        generic_lookup_setup_columns_start,
        num_generic_multiplicities_cols,
        num_generic_table_rows,
        generic_lookup_multiplicities_src_start,
        generic_lookup_multiplicities_dst_start,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    // layout sanity check
    if circuit.memory_layout.delegation_processor_layout.is_none()
        && circuit.memory_layout.delegation_request_layout.is_none()
    {
        assert_eq!(
            circuit
                .stage_2_layout
                .intermediate_polys_for_generic_multiplicities
                .full_range()
                .end,
            circuit
                .stage_2_layout
                .intermediate_polys_for_memory_argument
                .start()
        );
    } else {
        assert!(delegation_challenges.delegation_argument_gamma.is_zero() == false);
    }

    if handle_delegation_requests {
        assert!(!process_delegations);
        stage2_handle_delegation_requests(
            circuit,
            &delegation_challenges,
            Some(memory_timestamp_high_from_circuit_idx),
            &delegation_request_layout,
            memory_cols,
            setup_cols,
            d_stage_2_e4_cols,
            delegation_aux_poly_col,
            false,
            log_n,
            stream,
        )?;
    }

    if process_delegations {
        assert!(!handle_delegation_requests);
        stage2_process_delegations(
            &delegation_challenges,
            delegation_type,
            &delegation_processor_layout,
            memory_cols,
            d_stage_2_e4_cols,
            delegation_aux_poly_col,
            log_n,
            stream,
        )?;
    }

    stage2_process_range_check_16_trivial_checks(
        circuit,
        &range_check_16_width_1_lookups_access,
        &range_check_16_width_1_lookups_access_via_expressions,
        witness_cols,
        aggregated_entry_invs_for_range_check_16,
        d_stage_2_bf_cols,
        d_stage_2_e4_cols,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    stage2_process_range_check_16_expressions(
        &range_check_16_width_1_lookups_access_via_expressions,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_range_check_16,
        d_stage_2_bf_cols,
        d_stage_2_e4_cols,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        process_shuffle_ram_init,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    let lazy_init_teardown_layouts = if process_shuffle_ram_init {
        let lazy_init_teardown_layouts = LazyInitTeardownLayouts::new(
            circuit,
            &lazy_init_address_range_check_16,
            &shuffle_ram_inits_and_teardowns,
            &translate_e4_offset,
        );
        stage2_process_lazy_init_range_checks(
            lazy_init_teardown_layouts.clone(),
            memory_cols,
            aggregated_entry_invs_for_range_check_16,
            d_stage_2_bf_cols,
            d_stage_2_e4_cols,
            log_n,
            stream,
        )?;
        lazy_init_teardown_layouts
    } else {
        LazyInitTeardownLayouts::default()
    };

    stage2_process_timestamp_range_check_expressions(
        &timestamp_range_check_width_1_lookups_access_via_expressions,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        d_stage_2_bf_cols,
        d_stage_2_e4_cols,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        true, // expect_constant_terms_are_zero
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    stage2_process_timestamp_range_check_expressions_with_extra_timestamp_contribution(
        &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
        setup_cols,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        d_stage_2_bf_cols,
        d_stage_2_e4_cols,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        memory_timestamp_high_from_circuit_idx,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    stage2_process_generic_lookup_intermediate_polys(
        circuit,
        generic_lookups_args_to_table_entries_map,
        aggregated_entry_invs_for_generic_lookups,
        d_stage_2_e4_cols,
        num_generic_args,
        log_n,
        &translate_e4_offset,
        stream,
    )?;

    // Shuffle ram init/teardown and shuffle ram accesses are distinct things.
    // We expect:
    // inits > 0, access == 0: can happen in unrolled, never in non-unrolled
    // inits == 0, access > 0: can happen in unrolled, never in non-unrolled
    // both > 0              : can happen in non-unrolled (main), never in unrolled
    // both == 0             : can happen in non-unrolled (delegated), and also in unrolled
    // The following asserts might be fail for unrolled circuits.
    // They're a reminder of what I need to change.
    assert_eq!(
        process_shuffle_ram_init,
        circuit.memory_layout.shuffle_ram_access_sets.len() > 0,
    );
    assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
    let memory_challenges = MemoryChallenges::new(&memory_argument_challenges);
    let raw_memory_args_start = circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .start();
    let memory_args_start = translate_e4_offset(raw_memory_args_start);

    if process_shuffle_ram_init {
        assert!(!process_registers_and_indirect_access);
        // reminder of what needs to change for unrolled circuits
        assert_eq!(
            num_memory_args,
            circuit.memory_layout.shuffle_ram_access_sets.len(),
        );
        stage2_process_lazy_init_and_ram_access(
            circuit,
            memory_challenges.clone(),
            memory_timestamp_high_from_circuit_idx,
            lazy_init_teardown_layouts,
            setup_cols,
            memory_cols,
            d_stage_2_e4_cols,
            memory_args_start,
            log_n,
            stream,
        )?;
    }

    if process_registers_and_indirect_access {
        assert!(!process_shuffle_ram_init);
        // Layout checks that likely need to be modified for unrolled circuits
        let mut num_intermediate_polys_for_register_accesses = 0;
        for el in circuit.memory_layout.register_and_indirect_accesses.iter() {
            num_intermediate_polys_for_register_accesses += 1;
            num_intermediate_polys_for_register_accesses += el.indirect_accesses.len();
        }
        assert_eq!(
            num_memory_args,
            num_intermediate_polys_for_register_accesses,
        );
        assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
        stage2_process_registers_and_indirect_access_in_delegation(
            circuit,
            memory_challenges,
            &delegation_processor_layout,
            memory_cols,
            d_stage_2_e4_cols,
            memory_args_start,
            log_n,
            stream,
        )?;
    }

    stage2_col_sum_adjustments_and_grand_product(
        circuit,
        &mut stage_2_bf_cols,
        &mut stage_2_e4_cols,
        scratch_for_aggregated_entry_invs,
        scratch_for_cub_ops,
        maybe_batch_reduce_intermediates,
        scratch_for_col_sums,
        num_stage_2_bf_cols,
        delegation_aux_poly_col,
        n,
        handle_delegation_requests,
        process_delegations,
        false,
        stream,
        device_properties,
    )
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::device_context::DeviceContext;
    use crate::device_structures::{DeviceMatrix, DeviceMatrixChunk, DeviceMatrixMut};
    use crate::ops_complex::transpose;
    use crate::prover::{
        get_stage_2_col_sums_scratch, get_stage_2_cub_and_batch_reduce_intermediate_scratch,
        get_stage_2_e4_scratch,
    };

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Field;
    use prover::tests::{run_basic_delegation_test_impl, run_keccak_test_impl, GpuComparisonArgs};
    use serial_test::serial;

    type BF = BaseField;
    type E4 = Ext4Field;

    // CPU witness generation and checks are copied from zksync_airbender prover test.
    pub(crate) fn comparison_hook(gpu_comparison_args: &GpuComparisonArgs) {
        let device_properties = DeviceProperties::new().unwrap();
        let GpuComparisonArgs {
            circuit,
            setup,
            external_challenges,
            aux_boundary_values: _,
            public_inputs: _,
            twiddles: _,
            lde_precomputations: _,
            lookup_mapping,
            log_n,
            circuit_sequence,
            delegation_processing_type,
            is_unrolled: _,
            prover_data,
        } = gpu_comparison_args;
        let log_n = *log_n;
        let circuit_sequence = circuit_sequence.unwrap_or(0);
        let delegation_processing_type = delegation_processing_type.unwrap_or(0);
        let domain_size = 1 << log_n;
        let cached_data = ProverCachedData::new(
            &circuit,
            &external_challenges,
            domain_size,
            circuit_sequence,
            delegation_processing_type,
        );
        // double-check argument sizes if desired
        print_sizes();
        let range = 0..domain_size;
        let domain_index = 0;
        let num_setup_cols = circuit.setup_layout.total_width;
        let num_witness_cols = circuit.witness_layout.total_width;
        let num_memory_cols = circuit.memory_layout.total_width;
        let num_trace_cols = num_witness_cols + num_memory_cols;
        println!(
            "num_witness_cols {} num_memory_cols {}",
            num_witness_cols, num_memory_cols
        );
        let num_stage_2_cols = circuit.stage_2_layout.total_width;
        let num_generic_args = circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .num_elements();
        let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
        let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
        assert_eq!(
            num_stage_2_cols,
            4 * (((num_stage_2_bf_cols + 3) / 4) + num_stage_2_e4_cols)
        );

        let h_setup = &setup.ldes[domain_index].trace;
        let h_trace = &prover_data.stage_1_result.ldes[domain_index].trace;
        let h_setup_slice = h_setup.as_slice();
        let h_trace_slice = h_trace.as_slice();
        assert_eq!(h_setup_slice.len(), domain_size * h_setup.padded_width);
        assert_eq!(h_trace_slice.len(), domain_size * h_trace.padded_width);

        let mut h_stage_2_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_stage_2_cols];
        let mut lookup_mapping_view = lookup_mapping.row_view(range.clone());
        let mut h_generic_lookups_args_to_table_entries_map: Vec<u32> =
            vec![0; domain_size * num_generic_args];
        unsafe {
            // Repack lookup_mapping in an array with 1 padding row on the bottom
            // to ensure warp accesses are aligned
            let now = std::time::Instant::now();
            for i in 0..domain_size - 1 {
                let lookup_mapping_view_row = lookup_mapping_view.current_row_ref();
                let mut src = lookup_mapping_view_row.as_ptr();
                for j in 0..num_generic_args {
                    h_generic_lookups_args_to_table_entries_map[i + j * domain_size] = src.read();
                    src = src.add(1);
                }
                lookup_mapping_view.advance_row();
            }
            println!("repacking lookup_mapping took {:?}", now.elapsed());
        }
        let h_lookup_challenges = LookupChallenges::new(
            &prover_data
                .stage_2_result
                .lookup_argument_linearization_challenges,
            prover_data.stage_2_result.lookup_argument_gamma,
        );
        // Allocate GPU memory
        let stream = CudaStream::default();
        let num_memory_args = circuit
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .num_elements();
        let mut d_setup_row_major = DeviceAllocation::<BF>::alloc(h_setup_slice.len()).unwrap();
        let mut d_trace_row_major = DeviceAllocation::<BF>::alloc(h_trace_slice.len()).unwrap();
        let mut d_setup_column_major =
            DeviceAllocation::<BF>::alloc(domain_size * num_setup_cols).unwrap();
        let mut d_trace_column_major =
            DeviceAllocation::<BF>::alloc(domain_size * num_trace_cols).unwrap();
        let mut d_alloc_generic_lookups_args_to_table_entries_map =
            DeviceAllocation::<u32>::alloc(domain_size * num_generic_args).unwrap();
        let mut d_alloc_stage_2_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_stage_2_cols).unwrap();
        let num_e4_scratch_elems = get_stage_2_e4_scratch(domain_size, circuit);
        let mut d_alloc_e4_scratch = DeviceAllocation::<E4>::alloc(num_e4_scratch_elems).unwrap();

        let (cub_scratch_bytes, batch_reduce_intermediate_elems) =
            get_stage_2_cub_and_batch_reduce_intermediate_scratch(
                domain_size,
                num_stage_2_bf_cols,
                cached_data.handle_delegation_requests,
                cached_data.process_delegations,
                &device_properties,
            )
            .unwrap();
        let mut d_alloc_scratch_for_cub_ops =
            DeviceAllocation::<u8>::alloc(cub_scratch_bytes).unwrap();
        let mut maybe_batch_reduce_intermediates_alloc = if batch_reduce_intermediate_elems > 0 {
            let alloc = DeviceAllocation::<BF>::alloc(batch_reduce_intermediate_elems).unwrap();
            Some(alloc)
        } else {
            None
        };
        let mut maybe_batch_reduce_intermediates: Option<&mut DeviceSlice<BF>> =
            if let Some(ref mut d_alloc) = maybe_batch_reduce_intermediates_alloc {
                Some(d_alloc)
            } else {
                None
            };

        let col_sums_scratch_elems = get_stage_2_col_sums_scratch(num_stage_2_bf_cols);
        let mut d_alloc_scratch_for_col_sums =
            DeviceAllocation::<BF>::alloc(col_sums_scratch_elems).unwrap();

        let mut d_lookup_challenges = DeviceAllocation::<LookupChallenges>::alloc(1).unwrap();
        memory_copy_async(&mut d_setup_row_major, h_setup_slice, &stream).unwrap();
        memory_copy_async(&mut d_trace_row_major, h_trace_slice, &stream).unwrap();
        memory_copy_async(
            &mut d_alloc_generic_lookups_args_to_table_entries_map,
            &h_generic_lookups_args_to_table_entries_map,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut d_lookup_challenges, &[h_lookup_challenges], &stream).unwrap();
        let d_setup_row_major_matrix =
            DeviceMatrixChunk::new(&d_setup_row_major, h_setup.padded_width, 0, num_setup_cols);
        let d_trace_row_major_matrix =
            DeviceMatrixChunk::new(&d_trace_row_major, h_trace.padded_width, 0, num_trace_cols);
        let mut d_setup_cols = DeviceMatrixMut::new(&mut d_setup_column_major, domain_size);
        let mut d_trace_cols = DeviceMatrixMut::new(&mut d_trace_column_major, domain_size);
        transpose(&d_setup_row_major_matrix, &mut d_setup_cols, &stream).unwrap();
        transpose(&d_trace_row_major_matrix, &mut d_trace_cols, &stream).unwrap();
        let slice = d_trace_cols.slice();
        let stride = d_trace_cols.stride();
        let offset = d_trace_cols.offset();
        let d_witness_cols = DeviceMatrixChunk::new(
            &slice[0..num_witness_cols * stride],
            stride,
            offset,
            domain_size,
        );
        let d_memory_cols = DeviceMatrixChunk::new(
            &slice[num_witness_cols * stride..],
            stride,
            offset,
            domain_size,
        );
        let d_generic_lookups_args_to_table_entries_map = DeviceMatrix::new(
            &d_alloc_generic_lookups_args_to_table_entries_map,
            domain_size,
        );
        let mut d_stage_2_cols = DeviceMatrixMut::new(&mut d_alloc_stage_2_cols, domain_size);
        compute_stage_2_args_on_main_domain(
            &d_setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_generic_lookups_args_to_table_entries_map,
            &mut d_stage_2_cols,
            &mut d_alloc_e4_scratch,
            &mut d_alloc_scratch_for_cub_ops,
            &mut maybe_batch_reduce_intermediates,
            &mut d_alloc_scratch_for_col_sums,
            &d_lookup_challenges[0],
            &cached_data,
            &circuit,
            log_n as u32,
            &stream,
            &device_properties,
        )
        .unwrap();
        memory_copy_async(&mut h_stage_2_cols, &d_alloc_stage_2_cols, &stream).unwrap();
        stream.synchronize().unwrap();
        // Now compare GPU results to CPU results...but first we need to recall where
        // the data for each arg lies in the stage 2 matrices
        let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
        assert_eq!(e4_cols_offset % 4, 0);
        let translate_e4_offset = |raw_col: usize| -> usize {
            assert_eq!(raw_col % 4, 0);
            assert!(raw_col >= e4_cols_offset);
            (raw_col - e4_cols_offset) / 4
        };
        // collect locations of range check 16 args
        let args_metadata = &circuit.stage_2_layout.intermediate_polys_for_range_check_16;
        let range_check_16_num_bf_args = args_metadata.base_field_oracles.num_elements();
        let range_check_16_num_e4_args = args_metadata.ext_4_field_oracles.num_elements();
        assert_eq!(range_check_16_num_bf_args, range_check_16_num_e4_args);
        let range_check_16_bf_args_start = args_metadata.base_field_oracles.start();
        let range_check_16_e4_args_start =
            translate_e4_offset(args_metadata.ext_4_field_oracles.start());
        // collect locations of timestamp range check args
        let args_metadata = &circuit
            .stage_2_layout
            .intermediate_polys_for_timestamp_range_checks;
        let timestamp_range_check_num_bf_args = args_metadata.base_field_oracles.num_elements();
        let timestamp_range_check_num_e4_args = args_metadata.ext_4_field_oracles.num_elements();
        assert_eq!(
            timestamp_range_check_num_bf_args,
            timestamp_range_check_num_e4_args
        );
        let timestamp_range_check_bf_args_start = args_metadata.base_field_oracles.start();
        let timestamp_range_check_e4_args_start =
            translate_e4_offset(args_metadata.ext_4_field_oracles.start());
        // collect locations of lazy init address args
        let lazy_init_lookup_set = cached_data.lazy_init_address_range_check_16;
        assert_eq!(
            lazy_init_lookup_set.base_field_oracles.num_elements(),
            lazy_init_lookup_set.ext_4_field_oracles.num_elements(),
        );
        let (lazy_init_bf_args_start, lazy_init_e4_args_start, num_init_teardown_sets) =
            if cached_data.process_shuffle_ram_init {
                (
                    lazy_init_lookup_set.base_field_oracles.start(),
                    translate_e4_offset(lazy_init_lookup_set.ext_4_field_oracles.start()),
                    lazy_init_lookup_set.base_field_oracles.num_elements(),
                )
            } else {
                assert_eq!(lazy_init_lookup_set.base_field_oracles.num_elements(), 0);
                assert_eq!(lazy_init_lookup_set.ext_4_field_oracles.num_elements(), 0);
                (0, 0, 0)
            };
        // collect locations of generic args
        let raw_col = circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .start();
        let generic_args_start = translate_e4_offset(raw_col);
        // check locations of multiplicity args
        let multiplicities_args_start = cached_data.range_check_16_multiplicities_dst;
        assert_eq!(
            multiplicities_args_start + 4,
            cached_data.timestamp_range_check_multiplicities_dst,
        );
        assert_eq!(
            multiplicities_args_start + 8,
            cached_data.generic_lookup_multiplicities_dst_start,
        );
        let multiplicities_args_start = translate_e4_offset(multiplicities_args_start);
        let num_generic_multiplicities_cols = circuit
            .setup_layout
            .generic_lookup_setup_columns
            .num_elements();
        // one delegation aux poly col
        let delegation_aux_poly_col =
            if cached_data.handle_delegation_requests || cached_data.process_delegations {
                translate_e4_offset(cached_data.delegation_processing_aux_poly.start())
            } else {
                0
            };
        // collect locations of memory args
        let raw_col = circuit
            .stage_2_layout
            .intermediate_polys_for_memory_init_teardown
            .start();
        assert_eq!(
            num_init_teardown_sets,
            circuit
                .stage_2_layout
                .intermediate_polys_for_memory_init_teardown
                .num_elements(),
        );
        let lazy_init_teardown_args_start = translate_e4_offset(raw_col);
        let raw_col = circuit
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .start();
        let memory_args_start = translate_e4_offset(raw_col);
        let (_, grand_product_col) = get_grand_product_src_dst_cols(circuit, false);
        let h_stage_2_bf_cols = &h_stage_2_cols[0..num_stage_2_bf_cols * domain_size];
        let start = e4_cols_offset * domain_size;
        let end = start + 4 * num_stage_2_e4_cols * domain_size;
        let h_stage_2_e4_cols = &h_stage_2_cols[start..end];
        let get_vectorized_e4_val = |i: usize, j: usize| -> E4 {
            let components: [BF; 4] =
                std::array::from_fn(|k| h_stage_2_e4_cols[i + (k + 4 * j) * domain_size]);
            E4::from_array_of_base(components)
        };
        unsafe {
            let mut stage_2_trace_view = prover_data.stage_2_result.ldes[domain_index]
                .trace
                .row_view(range.clone());
            println!(
                "memory_args_start {} num_memory_args {}",
                memory_args_start, num_memory_args
            );
            for i in 0..domain_size {
                let stage_2_trace_view_row = stage_2_trace_view.current_row_ref();
                let src_bf = stage_2_trace_view_row.as_ptr();
                let src_e4 = stage_2_trace_view_row
                    .as_ptr()
                    .add(circuit.stage_2_layout.ext4_polys_offset)
                    .cast::<E4>();
                assert!(src_e4.is_aligned());
                // range check 16 comparisons
                let start = range_check_16_bf_args_start;
                let end = start + range_check_16_num_bf_args;
                for j in start..end {
                    assert_eq!(
                        h_stage_2_bf_cols[i + j * domain_size],
                        src_bf.add(j).read(),
                        "range check 16 bf failed at row {} col {}",
                        i,
                        j,
                    );
                }
                let start = range_check_16_e4_args_start;
                let end = start + range_check_16_num_e4_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "range check 16 e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // timestamp range check comparisons
                let start = timestamp_range_check_bf_args_start;
                let end = start + timestamp_range_check_num_bf_args;
                for j in start..end {
                    assert_eq!(
                        h_stage_2_bf_cols[i + j * domain_size],
                        src_bf.add(j).read(),
                        "timestamp range check bf failed at row {} col {}",
                        i,
                        j,
                    );
                }
                let start = timestamp_range_check_e4_args_start;
                let end = start + timestamp_range_check_num_e4_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "timestamp range check e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // Comparisons for 32-bit lazy init address args,
                // (treated as an extra pair of range check 16 args)
                let start = lazy_init_bf_args_start;
                let end = lazy_init_bf_args_start + num_init_teardown_sets;
                for j in start..end {
                    assert_eq!(
                        h_stage_2_bf_cols[i + j * domain_size],
                        src_bf.add(j).read(),
                        "lazy init address bf failed at row {}",
                        i,
                    );
                }
                let start = lazy_init_e4_args_start;
                let end = lazy_init_e4_args_start + num_init_teardown_sets;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "lazy init address e4 failed at row {}",
                        i,
                    );
                }
                // generic lookup comparisons
                let start = generic_args_start;
                let end = start + num_generic_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "generic e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // multiplicities args comparisons
                let start = multiplicities_args_start;
                let end = start + 2 + num_generic_multiplicities_cols;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "multiplicities args e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // delegation aux poly comparison
                if cached_data.handle_delegation_requests || cached_data.process_delegations {
                    let j = delegation_aux_poly_col;
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "delegation aux poly failed at row {}",
                        i,
                    );
                }
                // shuffle ram init/teardown comparison
                let start = lazy_init_teardown_args_start;
                let end = lazy_init_teardown_args_start + num_init_teardown_sets;
                if i == 0 {
                    println!("start {} end {}", start, end);
                }
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "init/teardown e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // memory arg comparisons
                let start = memory_args_start;
                let end = start + num_memory_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src_e4.add(j).read(),
                        "memory e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // memory grand product comparison
                let j = grand_product_col;
                assert_eq!(
                    get_vectorized_e4_val(i, j),
                    src_e4.add(j).read(),
                    "grand product e4 failed at row {} col {}",
                    i,
                    j,
                );
                stage_2_trace_view.advance_row();
            }
        }
    }

    #[test]
    #[serial]
    fn test_standalone_stage_2_non_unrolled_for_main_and_blake() {
        let ctx = DeviceContext::create(12).unwrap();
        run_basic_delegation_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_standalone_stage_2_non_unrolled_for_main_and_keccak() {
        let ctx = DeviceContext::create(12).unwrap();
        run_keccak_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }
}
