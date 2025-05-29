use super::BF;
use crate::device_structures::{
    DeviceMatrixChunkMut, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl, MutPtrAndStride,
    PtrAndStride,
};
use crate::ops_cub::device_radix_sort::{get_sort_keys_temp_storage_bytes, sort_keys};
use crate::ops_cub::device_run_length_encode::{encode, get_encode_temp_storage_bytes};
use crate::ops_simple::set_by_val;
use crate::prover::arg_utils::{
    FlattenedLookupExpressionsForShuffleRamLayout, FlattenedLookupExpressionsLayout,
    RangeCheck16ArgsLayout,
};
use crate::prover::context::ProverContext;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use cs::definitions::{split_timestamp, TimestampScalar, TIMESTAMP_COLUMNS_NUM_BITS};
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use prover::prover_stages::cached_data::{
    get_range_check_16_lookup_accesses, get_timestamp_range_check_lookup_accesses,
};

cuda_kernel!(GenerateMultiplicities,
    generate_multiplicities_kernel(
        unique_indexes: *const u32,
        counts: *const u32,
        num_runs: *const u32,
        multiplicities: MutPtrAndStride<BF>,
        count: u32,
    )
);

pub(crate) fn generate_generic_lookup_multiplicities<C: ProverContext>(
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    multiplicities: &mut impl DeviceMatrixMutImpl<BF>,
    context: &C,
) -> CudaResult<()> {
    let stride = lookup_mapping.stride();
    assert!(stride.is_power_of_two());
    assert_eq!(stride, multiplicities.stride());
    let stream = context.get_exec_stream();
    set_by_val(
        0xffffffff,
        &mut DeviceMatrixChunkMut::new(lookup_mapping.slice_mut(), stride, stride - 1, 1),
        stream,
    )?;
    let lookup_mapping_slice = lookup_mapping.slice();
    let lookup_mapping_size = lookup_mapping_slice.len();
    let mut sorted_lookup_mapping = context.alloc(lookup_mapping_size)?;
    assert!(lookup_mapping_size <= u32::MAX as usize);
    let lookup_mapping_size = lookup_mapping_size as u32;
    let lookup_mapping_bits_count = multiplicities
        .slice()
        .len()
        .next_power_of_two()
        .trailing_zeros() as i32;
    let lookup_mapping_sort_temp_storage_size = get_sort_keys_temp_storage_bytes::<u32>(
        false,
        lookup_mapping_size,
        0,
        lookup_mapping_bits_count,
    )?;
    let mut mapping_sort_temp_storage =
        context.alloc::<u8>(lookup_mapping_sort_temp_storage_size)?;
    sort_keys(
        false,
        &mut mapping_sort_temp_storage,
        lookup_mapping_slice,
        &mut sorted_lookup_mapping,
        0,
        lookup_mapping_bits_count,
        stream,
    )?;
    drop(mapping_sort_temp_storage);
    let multiplicities_size = multiplicities.slice().len();
    let mut unique_lookup_mapping = context.alloc(multiplicities_size)?;
    let mut counts = context.alloc(multiplicities_size)?;
    let mut num_runs = context.alloc(1)?;
    let encode_temp_storage_bytes =
        get_encode_temp_storage_bytes::<u32>(lookup_mapping_size as i32)?;
    let mut encode_temp_storage = context.alloc::<u8>(encode_temp_storage_bytes)?;
    encode(
        &mut encode_temp_storage,
        &sorted_lookup_mapping,
        &mut unique_lookup_mapping,
        &mut counts,
        &mut num_runs[0],
        stream,
    )?;
    drop(encode_temp_storage);
    let unique_indexes = unique_lookup_mapping.as_ptr();
    let counts = counts.as_ptr();
    let num_runs = num_runs.as_ptr();
    let multiplicities_ptr = multiplicities.as_mut_ptr_and_stride();
    assert!(multiplicities_size <= u32::MAX as usize);
    let count = multiplicities_size as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMultiplicitiesArguments::new(
        unique_indexes,
        counts,
        num_runs,
        multiplicities_ptr,
        count,
    );
    GenerateMultiplicitiesFunction::default().launch(&config, &args)
}

cuda_kernel!(GenerateRangeCheckLookupMappings,
    generate_range_check_lookup_mappings_kernel(
        setup_cols: PtrAndStride<BF>,
        witness_cols: PtrAndStride<BF>,
        memory_cols: PtrAndStride<BF>,
        range_check_16_lookup_mapping: MutPtrAndStride<u32>,
        timestamp_lookup_mapping: MutPtrAndStride<u32>,
        explicit_range_check_16_layout: RangeCheck16ArgsLayout,
        expressions: FlattenedLookupExpressionsLayout,
        expressions_for_shuffle_ram: FlattenedLookupExpressionsForShuffleRamLayout,
        memory_timestamp_high_from_circuit_idx: BF,
        process_shuffle_ram_init: bool,
        lazy_init_address_start: u32,
        trace_len: u32,
    )
);

pub(crate) fn generate_range_check_multiplicities<C: ProverContext>(
    circuit: &CompiledCircuitArtifact<BF>,
    d_setup: &impl DeviceMatrixImpl<BF>,
    d_witness: &mut impl DeviceMatrixMutImpl<BF>,
    d_memory: &impl DeviceMatrixImpl<BF>,
    timestamp_high_from_circuit_sequence: TimestampScalar,
    trace_len: usize,
    context: &C,
) -> CudaResult<()> {
    assert!(trace_len.is_power_of_two());
    let num_witness_cols = circuit.witness_layout.total_width;
    let num_memory_cols = circuit.memory_layout.total_width;
    assert_eq!(d_witness.stride(), trace_len);
    assert_eq!(d_witness.cols(), num_witness_cols,);
    assert_eq!(d_memory.stride(), trace_len);
    assert_eq!(d_memory.cols(), num_memory_cols,);
    // Stage 2 layout info is not used by the kernel, it's just to unblock
    // some checks in my layout structures.
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
    assert_eq!(e4_cols_offset % 4, 0);
    assert!(num_stage_2_bf_cols <= e4_cols_offset);
    assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
    let translate_e4_offset = |raw_col: usize| -> usize {
        assert_eq!(raw_col % 4, 0);
        assert!(raw_col >= e4_cols_offset);
        (raw_col - e4_cols_offset) / 4
    };
    let (
        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,
    ) = get_range_check_16_lookup_accesses(circuit);

    let (
        timestamp_range_check_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
    ) = get_timestamp_range_check_lookup_accesses(circuit);

    let (process_shuffle_ram_init, lazy_init_address_start) =
        if let Some(shuffle_ram_inits_and_teardowns) =
            circuit.memory_layout.shuffle_ram_inits_and_teardowns
        {
            let init_address_start = shuffle_ram_inits_and_teardowns
                .lazy_init_addresses_columns
                .start();
            (true, init_address_start)
        } else {
            (false, 0)
        };
    // For convenience, we repurpose some metadata structs used by stage 2 and 3 arguments.
    // These structs compute a bit more layout info than we need for multiplicity counting,
    // but there's no performance impact.
    let explicit_range_check_16_layout = RangeCheck16ArgsLayout::new(
        circuit,
        &range_check_16_width_1_lookups_access,
        &range_check_16_width_1_lookups_access_via_expressions,
        &translate_e4_offset,
    );
    let expressions_layout = if range_check_16_width_1_lookups_access_via_expressions.len() > 0
        || timestamp_range_check_width_1_lookups_access_via_expressions.len() > 0
    {
        let expect_constant_terms_are_zero = process_shuffle_ram_init;
        FlattenedLookupExpressionsLayout::new(
            &range_check_16_width_1_lookups_access_via_expressions,
            &timestamp_range_check_width_1_lookups_access_via_expressions,
            num_stage_2_bf_cols,
            num_stage_2_e4_cols,
            expect_constant_terms_are_zero,
            &translate_e4_offset,
        )
    } else {
        FlattenedLookupExpressionsLayout::default()
    };
    let expressions_for_shuffle_ram_layout =
        if timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.len() > 0 {
            FlattenedLookupExpressionsForShuffleRamLayout::new(
                &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
                num_stage_2_bf_cols,
                num_stage_2_e4_cols,
                &translate_e4_offset,
            )
        } else {
            FlattenedLookupExpressionsForShuffleRamLayout::default()
        };
    let stream = context.get_exec_stream();
    // Allocate lookup mapping for range check 16 lookups
    let mut num_range_check_16_explicit_cols =
        2 * explicit_range_check_16_layout.num_dst_cols as usize;
    if process_shuffle_ram_init {
        num_range_check_16_explicit_cols += 2; // lazy init address limbs
    }
    let num_range_check_16_expressions =
        2 * expressions_layout.num_range_check_16_expression_pairs as usize;
    let num_range_check_16_lookup_mapping_cols =
        num_range_check_16_explicit_cols + num_range_check_16_expressions;
    // A circuit with no range check 16s would be strange
    assert!(num_range_check_16_lookup_mapping_cols > 0);
    let mut d_range_check_16_lookup_mapping_alloc =
        context.alloc(num_range_check_16_lookup_mapping_cols * trace_len)?;
    let mut d_range_check_16_lookup_mapping =
        DeviceMatrixMut::new(&mut d_range_check_16_lookup_mapping_alloc, trace_len);
    set_by_val(
        0xffffffffu32,
        &mut DeviceMatrixChunkMut::new(
            d_range_check_16_lookup_mapping.slice_mut(),
            trace_len,
            trace_len - 1,
            1,
        ),
        stream,
    )?;
    // Allocate lookup mapping for timestamp lookups
    let mut num_timestamp_lookup_mapping_cols =
        2 * expressions_layout.num_timestamp_expression_pairs as usize;
    num_timestamp_lookup_mapping_cols +=
        2 * expressions_for_shuffle_ram_layout.num_expression_pairs as usize;
    // A circuit with no range check 16s would be strange
    assert!(num_timestamp_lookup_mapping_cols > 0);
    let mut d_timestamp_lookup_mapping_alloc =
        context.alloc(num_timestamp_lookup_mapping_cols * trace_len)?;
    let mut d_timestamp_lookup_mapping =
        DeviceMatrixMut::new(&mut d_timestamp_lookup_mapping_alloc, trace_len);
    set_by_val(
        0xffffffffu32,
        &mut DeviceMatrixChunkMut::new(
            d_timestamp_lookup_mapping.slice_mut(),
            trace_len,
            trace_len - 1,
            1,
        ),
        stream,
    )?;
    let setup_cols = d_setup.as_ptr_and_stride();
    let witness_cols = d_witness.as_ptr_and_stride();
    let memory_cols = d_memory.as_ptr_and_stride();
    let range_check_16_lookup_mapping = d_range_check_16_lookup_mapping.as_mut_ptr_and_stride();
    let timestamp_lookup_mapping = d_timestamp_lookup_mapping.as_mut_ptr_and_stride();
    let (_, high) = split_timestamp(timestamp_high_from_circuit_sequence);
    assert!(high <= (1 << TIMESTAMP_COLUMNS_NUM_BITS - 1));
    let memory_timestamp_high_from_circuit_idx = BF::new(high);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, trace_len as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateRangeCheckLookupMappingsArguments::new(
        setup_cols,
        witness_cols,
        memory_cols,
        range_check_16_lookup_mapping,
        timestamp_lookup_mapping,
        explicit_range_check_16_layout,
        expressions_layout,
        expressions_for_shuffle_ram_layout,
        memory_timestamp_high_from_circuit_idx,
        process_shuffle_ram_init,
        lazy_init_address_start as u32,
        trace_len as u32,
    );
    GenerateRangeCheckLookupMappingsFunction::default().launch(&config, &args)?;
    let mut finalize_multiplicities = |multiplicities_col: usize,
                                       d_lookup_mapping: &mut DeviceMatrixMut<u32>|
     -> CudaResult<()> {
        let d_multiplicities = &mut d_witness.slice_mut()
            [multiplicities_col * trace_len..(multiplicities_col + 1) * trace_len];
        generate_generic_lookup_multiplicities(
            d_lookup_mapping,
            &mut DeviceMatrixMut::new(d_multiplicities, trace_len),
            context,
        )
    };
    let range_check_16_multiplicities_col = circuit
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .start();
    finalize_multiplicities(
        range_check_16_multiplicities_col,
        &mut d_range_check_16_lookup_mapping,
    )?;

    let timestamp_range_check_multiplicities_col = circuit
        .witness_layout
        .multiplicities_columns_for_timestamp_range_check
        .start();
    finalize_multiplicities(
        timestamp_range_check_multiplicities_col,
        &mut d_timestamp_lookup_mapping,
    )
}
