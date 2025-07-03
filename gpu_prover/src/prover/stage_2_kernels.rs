use super::arg_utils::*;
use crate::device_structures::{
    DeviceMatrix, DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut,
    DeviceMatrixChunkMutImpl, DeviceMatrixMut, MutPtrAndStride, PtrAndStride,
};
use crate::field::{BaseField, Ext4Field};
use crate::ops_complex::transpose;
use crate::ops_cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
};
use crate::ops_cub::device_scan::{get_scan_temp_storage_bytes, scan, ScanOperation};
use crate::ops_simple::{set_to_zero, sub_into_x};
use crate::utils::WARP_SIZE;

use cs::definitions::{NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE, TIMESTAMP_COLUMNS_NUM_BITS};
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::Field;
use prover::prover_stages::cached_data::ProverCachedData;
use std::cmp::max;

type BF = BaseField;
type E4 = Ext4Field;

cuda_kernel!(
    RangeCheckAggregatedEntryInvsAndMultiplicitiesArg,
    range_check_aggregated_entry_invs_and_multiplicities_arg,
    lookup_challenges: *const LookupChallenges,
    witness_cols: PtrAndStride<BF>,
    setup_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    aggregated_entry_invs: *mut E4,
    start_col_in_setup: u32,
    multiplicities_src_cols_start: u32,
    multiplicities_dst_cols_start: u32,
    num_multiplicities_cols: u32,
    num_table_rows_tail: u32,
    log_n: u32,
);

range_check_aggregated_entry_invs_and_multiplicities_arg!(
    range_check_aggregated_entry_invs_and_multiplicities_arg_kernel
);

cuda_kernel!(
    GenericAggregatedEntryInvsAndMultiplicitiesArg,
    generic_aggregated_entry_invs_and_multiplicities_arg,
    lookup_challenges: *const LookupChallenges,
    witness_cols: PtrAndStride<BF>,
    setup_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    aggregated_entry_invs: *mut E4,
    start_col_in_setup: u32,
    multiplicities_src_cols_start: u32,
    multiplicities_dst_cols_start: u32,
    num_multiplicities_cols: u32,
    num_table_rows_tail: u32,
    log_n: u32,
);

generic_aggregated_entry_invs_and_multiplicities_arg!(
    generic_aggregated_entry_invs_and_multiplicities_arg_kernel
);

cuda_kernel!(
    DelegationAuxPoly,
    delegation_aux_poly,
    delegation_challenge: DelegationChallenges,
    request_metadata: DelegationRequestMetadata,
    processing_metadata: DelegationProcessingMetadata,
    memory_cols: PtrAndStride<BF>,
    setup_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    delegation_aux_poly_col: u32,
    handle_delegation_requests: bool,
    log_n: u32,
);

delegation_aux_poly!(delegation_aux_poly_kernel);

cuda_kernel!(
    LookupArgs,
    lookup_args,
    range_check_16_layout: RangeCheck16ArgsLayout,
    expressions: FlattenedLookupExpressionsLayout,
    expressions_for_shuffle_ram: FlattenedLookupExpressionsForShuffleRamLayout,
    lazy_init_teardown_layout: LazyInitTeardownLayout,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *const E4,
    aggregated_entry_invs_for_timestamp_range_checks: *const E4,
    aggregated_entry_invs_for_generic_lookups: *const E4,
    generic_args_start: u32,
    num_generic_args: u32,
    generic_lookups_args_to_table_entries_map: PtrAndStride<u32>,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_timestamp_high_from_circuit_idx: BF,
    num_stage_2_bf_cols: u32,
    num_stage_2_e4_cols: u32,
    log_n: u32,
);

lookup_args!(lookup_args_kernel);

// Q: Why not use a unified memory and lookup args kernel?
// Possible advantages of unified kernel:
//   - Lookup args are probably memory bound and memory args are probably compute bound,
//     so putting them in one kernel might use resources more evenly.
//   - They both read 2 BF "lazy init address" cols. Unification allows avoiding this (small)
//     redundant load.
// Possible disadvantage of unified kernel:
//   - Lookup args want aggregated_entry_invs to persist in L2 as much as possible.
//     Unrelated memory arg traffic could hurt the persistence.
// Turns out it's a wash: I tried a unified kernel and its runtime was roughly
// equal to the total runtime of the two separate kernels, at least on L4.
// I decided to just keep the kernels separate for organizational clarity.
cuda_kernel!(
    ShuffleRamMemoryArgs,
    shuffle_ram_memory_args,
    memory_challenges: MemoryChallenges,
    shuffle_ram_accesses: ShuffleRamAccesses,
    setup_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    lazy_init_teardown_layout: LazyInitTeardownLayout,
    memory_timestamp_high_from_circuit_idx: BF,
    memory_args_start: u32,
    log_n: u32,
);

shuffle_ram_memory_args!(shuffle_ram_memory_args_kernel);

cuda_kernel!(
    BatchedRamMemoryArgs,
    batched_ram_memory_args,
    memory_challenges: MemoryChallenges,
    batched_ram_accesses: BatchedRamAccesses,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_args_start: u32,
    log_n: u32,
);

batched_ram_memory_args!(batched_ram_memory_args_kernel);

cuda_kernel!(
    RegisterAndIndirectMemoryArgs,
    register_and_indirect_memory_args,
    memory_challenges: MemoryChallenges,
    register_and_indirect_accesses: RegisterAndIndirectAccesses,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_args_start: u32,
    log_n: u32,
);

register_and_indirect_memory_args!(register_and_indirect_memory_args_kernel);

pub fn get_stage_2_e4_scratch_elems(
    domain_size: usize,
    circuit: &CompiledCircuitArtifact<BF>,
) -> usize {
    max(
        (1 << 16) + (1 << TIMESTAMP_COLUMNS_NUM_BITS) + circuit.total_tables_size,
        2 * domain_size, // for transposed grand product
    )
}

pub fn get_stage_2_cub_scratch_bytes_internal(
    domain_size: usize,
    num_stage_2_bf_cols: usize,
) -> CudaResult<(usize, (usize, usize, usize))> {
    let domain_size = domain_size as i32;
    let bf_args_batch_reduce_bytes = get_batch_reduce_temp_storage_bytes::<BF>(
        ReduceOperation::Sum,
        num_stage_2_bf_cols as i32,
        domain_size,
    )?;
    let delegation_aux_batch_reduce_bytes = get_batch_reduce_temp_storage_bytes::<BF>(
        ReduceOperation::Sum,
        4 as i32, // one vectorized E4 col
        domain_size,
    )?;
    let grand_product_bytes =
        get_scan_temp_storage_bytes::<E4>(ScanOperation::Product, false, domain_size)?;
    Ok((
        max(
            max(
                bf_args_batch_reduce_bytes,
                delegation_aux_batch_reduce_bytes,
            ),
            grand_product_bytes,
        ),
        (
            bf_args_batch_reduce_bytes,
            delegation_aux_batch_reduce_bytes,
            grand_product_bytes,
        ),
    ))
}

pub fn get_stage_2_cub_scratch_bytes(
    domain_size: usize,
    num_stage_2_bf_cols: usize,
) -> CudaResult<usize> {
    let (cub_scratch_bytes, _) =
        get_stage_2_cub_scratch_bytes_internal(domain_size, num_stage_2_bf_cols)?;
    Ok(cub_scratch_bytes)
}

pub fn get_stage_2_bf_scratch_elems(num_stage_2_bf_cols: usize) -> usize {
    max(num_stage_2_bf_cols, 4)
}

pub fn compute_stage_2_args_on_main_domain(
    setup_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    generic_lookups_args_to_table_entries_map: &(impl DeviceMatrixChunkImpl<u32> + ?Sized),
    stage_2_cols: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    scratch_for_aggregated_entry_invs: &mut DeviceSlice<E4>,
    scratch_for_cub_ops: &mut DeviceSlice<u8>,
    scratch_for_col_sums: &mut DeviceSlice<BF>,
    lookup_challenges: &DeviceVariable<LookupChallenges>,
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    num_generic_table_rows: usize,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(REGISTER_SIZE, 2);
    assert_eq!(NUM_TIMESTAMP_COLUMNS_FOR_RAM, 2);
    let n = 1 << log_n;
    let num_setup_cols = circuit.setup_layout.total_width;
    let num_witness_cols = circuit.witness_layout.total_width;
    let num_memory_cols = circuit.memory_layout.total_width;
    // NB: num_generic_args might be 0.
    // Subsequent code should handle that case gracefully (I hope)
    let num_generic_args = circuit
        .stage_2_layout
        .intermediate_polys_for_generic_lookup
        .num_elements();
    let num_memory_args = circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .num_elements();
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    assert_eq!(setup_cols.rows(), n);
    assert_eq!(setup_cols.cols(), num_setup_cols);
    assert_eq!(witness_cols.rows(), n);
    assert_eq!(witness_cols.cols(), num_witness_cols,);
    assert_eq!(memory_cols.rows(), n);
    assert_eq!(memory_cols.cols(), num_memory_cols,);
    assert_eq!(generic_lookups_args_to_table_entries_map.rows(), n);
    assert_eq!(
        generic_lookups_args_to_table_entries_map.cols(),
        num_generic_args,
    );
    assert_eq!(stage_2_cols.rows(), n);
    assert_eq!(stage_2_cols.cols(), circuit.stage_2_layout.total_width);
    assert_eq!(
        stage_2_cols.cols(),
        4 * (((num_stage_2_bf_cols + 3) / 4) + num_stage_2_e4_cols)
    );
    assert_eq!(
        scratch_for_aggregated_entry_invs.len(),
        get_stage_2_e4_scratch_elems(n, circuit),
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
        delegation_type: _,
        memory_argument_challenges,
        execute_delegation_argument,
        delegation_challenges,
        process_shuffle_ram_init,
        shuffle_ram_inits_and_teardowns,
        lazy_init_address_range_check_16,
        handle_delegation_requests,
        delegation_request_layout: _,
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
        memory_accumulator_dst_start,
        ..
    } = cached_data.clone();
    assert_eq!(trace_len, n);
    assert_eq!(
        circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .num_elements(),
        1
    );
    assert_eq!(
        circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            .num_elements(),
        1
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
    // overall size checks
    let mut num_expected_bf_args = 0;
    // we assume (and assert later) that the numbers of range check 8 and 16 cols are both even.
    num_expected_bf_args += circuit.witness_layout.range_check_16_columns.num_elements() / 2;
    num_expected_bf_args += range_check_16_width_1_lookups_access_via_expressions.len();
    num_expected_bf_args += timestamp_range_check_width_1_lookups_access_via_expressions.len();
    num_expected_bf_args +=
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.len();
    if process_shuffle_ram_init {
        num_expected_bf_args += 1; // lazy init address cols are treated as 1 pair of range check 16
    }
    assert_eq!(num_stage_2_bf_cols, num_expected_bf_args);
    let mut num_expected_e4_args = 0;
    num_expected_e4_args += 1; // range check 16 multiplicities dst
    num_expected_e4_args += 1; // timestamp range check multiplicities dst
    num_expected_e4_args += num_generic_multiplicities_cols;
    num_expected_e4_args += num_expected_bf_args; // each bf arg should have a corresponding e4 arg
    num_expected_e4_args += num_generic_args;
    num_expected_e4_args += num_memory_args;
    if handle_delegation_requests || process_delegations {
        num_expected_e4_args += 1; // delegation_processing_aux_poly
    }
    assert_eq!(num_stage_2_e4_cols, num_expected_e4_args);
    let setup_cols = setup_cols.as_ptr_and_stride();
    let witness_cols = witness_cols.as_ptr_and_stride();
    let memory_cols = memory_cols.as_ptr_and_stride();
    let d_stage_2_e4_cols = stage_2_e4_cols.as_mut_ptr_and_stride();
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
    // range check table values are just row indexes,
    // so i don't need to read their setup entries
    let dummy_setup_column = 0;
    let num_range_check_16_rows = 1 << 16;
    assert!(num_range_check_16_rows < n); // just in case
    let num_range_check_16_multiplicities_cols = 1;
    let range_check_16_multiplicities_dst_col =
        translate_e4_offset(range_check_16_multiplicities_dst);
    let block_dim = WARP_SIZE * 4;
    let grid_dim = (n as u32 + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = RangeCheckAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
        lookup_challenges,
        witness_cols,
        setup_cols,
        d_stage_2_e4_cols,
        aggregated_entry_invs_for_range_check_16,
        dummy_setup_column,
        range_check_16_multiplicities_src as u32,
        range_check_16_multiplicities_dst_col as u32,
        num_range_check_16_multiplicities_cols as u32,
        num_range_check_16_rows as u32,
        log_n as u32,
    );
    RangeCheckAggregatedEntryInvsAndMultiplicitiesArgFunction(
        range_check_aggregated_entry_invs_and_multiplicities_arg_kernel,
    )
    .launch(&config, &args)?;
    let num_timestamp_range_check_rows = 1 << TIMESTAMP_COLUMNS_NUM_BITS;
    assert!(num_timestamp_range_check_rows < n); // just in case
    let num_timestamp_multiplicities_cols = 1;
    let timestamp_range_check_multiplicities_dst_col =
        translate_e4_offset(timestamp_range_check_multiplicities_dst);
    let block_dim = WARP_SIZE * 4;
    let grid_dim = (n as u32 + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = RangeCheckAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
        lookup_challenges,
        witness_cols,
        setup_cols,
        d_stage_2_e4_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        dummy_setup_column,
        timestamp_range_check_multiplicities_src as u32,
        timestamp_range_check_multiplicities_dst_col as u32,
        num_timestamp_multiplicities_cols as u32,
        num_timestamp_range_check_rows as u32,
        log_n as u32,
    );
    RangeCheckAggregatedEntryInvsAndMultiplicitiesArgFunction(
        range_check_aggregated_entry_invs_and_multiplicities_arg_kernel,
    )
    .launch(&config, &args)?;
    if num_generic_table_rows > 0 {
        // In theory the following assert is not a hard requirement:
        // a circuit could have a non-empty width-3 table but not actually
        // use it to create any args. But such a circuit wouldn't make sense,
        // and we don't expect our circuits to be like that in practice.
        assert!(num_generic_args > 0);
        let generic_lookup_multiplicities_dst_cols_start =
            translate_e4_offset(generic_lookup_multiplicities_dst_start);
        let lookup_encoding_capacity = n - 1;
        let num_generic_table_rows_tail = num_generic_table_rows % lookup_encoding_capacity;
        assert_eq!(
            num_generic_multiplicities_cols,
            (num_generic_table_rows + lookup_encoding_capacity - 1) / lookup_encoding_capacity
        );
        let grid_dim = (n as u32 + block_dim - 1) / block_dim;
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = GenericAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
            lookup_challenges,
            witness_cols,
            setup_cols,
            d_stage_2_e4_cols,
            aggregated_entry_invs_for_generic_lookups,
            generic_lookup_setup_columns_start as u32,
            generic_lookup_multiplicities_src_start as u32,
            generic_lookup_multiplicities_dst_cols_start as u32,
            num_generic_multiplicities_cols as u32,
            num_generic_table_rows_tail as u32,
            log_n as u32,
        );
        GenericAggregatedEntryInvsAndMultiplicitiesArgFunction(
            generic_aggregated_entry_invs_and_multiplicities_arg_kernel,
        )
        .launch(&config, &args)?;
    } else {
        assert_eq!(num_generic_args, 0);
    }
    // Compute delegation aux poly
    // first, a check on zksync_airbender's own layout, copied from zksync_airbenders's stage2.rs
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
    if handle_delegation_requests || process_delegations {
        assert!(execute_delegation_argument);
        let delegation_challenges = DelegationChallenges::new(&delegation_challenges);
        let (request_metadata, processing_metadata) = get_delegation_metadata(cached_data, circuit);
        let delegation_aux_poly_col = translate_e4_offset(delegation_processing_aux_poly.start());
        let block_dim = 128;
        let grid_dim = (n as u32 + 127) / 128;
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = DelegationAuxPolyArguments::new(
            delegation_challenges,
            request_metadata,
            processing_metadata,
            memory_cols,
            setup_cols,
            d_stage_2_e4_cols,
            delegation_aux_poly_col as u32,
            handle_delegation_requests,
            log_n as u32,
        );
        DelegationAuxPolyFunction(delegation_aux_poly_kernel).launch(&config, &args)?;
    }
    // Identify range check 16 src (witness) cols, bf args, and e4 args
    // CPU code doesn't fully support an isolated (odd-tail) remainder col yet.
    // For now, we assert the number of cols is even such that all cols can be paired,
    // and add support for a lone remainder col when the CPU does.
    let range_check_16_layout = RangeCheck16ArgsLayout::new(
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
    // 32-bit lazy init addresses are treated as a pair of range check 16 cols
    let lazy_init_teardown_layout = if process_shuffle_ram_init {
        LazyInitTeardownLayout::new(
            circuit,
            &lazy_init_address_range_check_16,
            &shuffle_ram_inits_and_teardowns,
            &translate_e4_offset,
        )
    } else {
        LazyInitTeardownLayout::default()
    };
    // Width-3 lookups
    let generic_args_start = if num_generic_args > 0 {
        translate_e4_offset(
            circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .start(),
        )
    } else {
        0
    };
    let generic_lookups_args_to_table_entries_map =
        generic_lookups_args_to_table_entries_map.as_ptr_and_stride();
    let d_stage_2_bf_cols = stage_2_bf_cols.as_mut_ptr_and_stride();
    let lazy_init_teardown_layout_copy = lazy_init_teardown_layout.clone();
    let block_dim = 128;
    let grid_dim = (n as u32 + 127) / 128;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LookupArgsArguments::new(
        range_check_16_layout,
        expressions_layout,
        expressions_for_shuffle_ram_layout,
        lazy_init_teardown_layout_copy,
        setup_cols,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_range_check_16,
        aggregated_entry_invs_for_timestamp_range_checks,
        aggregated_entry_invs_for_generic_lookups,
        generic_args_start as u32,
        num_generic_args as u32,
        generic_lookups_args_to_table_entries_map,
        d_stage_2_bf_cols,
        d_stage_2_e4_cols,
        memory_timestamp_high_from_circuit_idx,
        num_stage_2_bf_cols as u32,
        num_stage_2_e4_cols as u32,
        log_n as u32,
    );
    LookupArgsFunction(lookup_args_kernel).launch(&config, &args)?;
    // Pack metadata for memory args
    let memory_challenges = MemoryChallenges::new(&memory_argument_challenges);
    let raw_memory_args_start = circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .start();
    assert_eq!(raw_memory_args_start, memory_accumulator_dst_start);
    let memory_args_start = translate_e4_offset(raw_memory_args_start);
    if process_shuffle_ram_init {
        assert!(!process_batch_ram_access);
        assert!(!process_registers_and_indirect_access);
        assert_eq!(lazy_init_teardown_layout.process_shuffle_ram_init, true);
        assert!(!process_batch_ram_access);
        assert_eq!(circuit.memory_layout.batched_ram_accesses.len(), 0);
        let write_timestamp_in_setup_start = circuit.setup_layout.timestamp_setup_columns.start();
        let shuffle_ram_access_sets = &circuit.memory_layout.shuffle_ram_access_sets;
        assert_eq!(
            num_memory_args,
            1/* lazy init/teardown */ + shuffle_ram_access_sets.len() + 1, /* grand product */
        );
        assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
        let shuffle_ram_accesses =
            ShuffleRamAccesses::new(shuffle_ram_access_sets, write_timestamp_in_setup_start);
        let block_dim = 128;
        let grid_dim = (n as u32 + 127) / 128;
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = ShuffleRamMemoryArgsArguments::new(
            memory_challenges.clone(),
            shuffle_ram_accesses,
            setup_cols,
            memory_cols,
            d_stage_2_e4_cols,
            lazy_init_teardown_layout,
            memory_timestamp_high_from_circuit_idx,
            memory_args_start as u32,
            log_n as u32,
        );
        ShuffleRamMemoryArgsFunction(shuffle_ram_memory_args_kernel).launch(&config, &args)?;
    } else {
        assert!(process_batch_ram_access || process_registers_and_indirect_access);
        // In principle we can rig batch ram access and registers_and_indirect_access
        // to coexist in the same circuit. However, our current circuits use either one
        // or the other, so we expect only one to be true.
        // TODO: If we ever do want to run them in the same circuit,
        // consider combining their two kernels to use the same write timestamp contribution
        // (but make sure batched ram accesses and indirect accesses do not overlap)
        assert!(process_batch_ram_access != process_registers_and_indirect_access);
        assert_eq!(circuit.memory_layout.shuffle_ram_access_sets.len(), 0);
        let num_batched_ram_accesses = circuit.memory_layout.batched_ram_accesses.len();
        let mut num_intermediate_polys_for_register_accesses = 0;
        for el in circuit.memory_layout.register_and_indirect_accesses.iter() {
            num_intermediate_polys_for_register_accesses += 1;
            num_intermediate_polys_for_register_accesses += el.indirect_accesses.len();
        }
        assert_eq!(
            num_memory_args,
            num_batched_ram_accesses + num_intermediate_polys_for_register_accesses + 1, /* grand product */
        );
        assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
    }
    if process_batch_ram_access {
        let batched_ram_accesses = &circuit.memory_layout.batched_ram_accesses;
        assert!(batched_ram_accesses.len() > 0);
        let write_timestamp_col = delegation_processor_layout.write_timestamp.start();
        let abi_mem_offset_high_col = delegation_processor_layout.abi_mem_offset_high.start();
        let batched_ram_accesses = BatchedRamAccesses::new(
            &memory_challenges,
            batched_ram_accesses,
            write_timestamp_col,
            abi_mem_offset_high_col,
        );
        let block_dim = 128;
        let grid_dim = (n as u32 + 127) / 128;
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = BatchedRamMemoryArgsArguments::new(
            memory_challenges.clone(),
            batched_ram_accesses,
            memory_cols,
            d_stage_2_e4_cols,
            memory_args_start as u32,
            log_n as u32,
        );
        BatchedRamMemoryArgsFunction(batched_ram_memory_args_kernel).launch(&config, &args)?;
    }
    if process_registers_and_indirect_access {
        let register_and_indirect_accesses = &circuit.memory_layout.register_and_indirect_accesses;
        assert!(register_and_indirect_accesses.len() > 0);
        let write_timestamp_col = delegation_processor_layout.write_timestamp.start();
        let register_and_indirect_accesses = RegisterAndIndirectAccesses::new(
            &memory_challenges,
            register_and_indirect_accesses,
            write_timestamp_col,
        );
        let block_dim = 128;
        let grid_dim = (n as u32 + 127) / 128;
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = RegisterAndIndirectMemoryArgsArguments::new(
            memory_challenges,
            register_and_indirect_accesses,
            memory_cols,
            d_stage_2_e4_cols,
            memory_args_start as u32,
            log_n as u32,
        );
        RegisterAndIndirectMemoryArgsFunction(register_and_indirect_memory_args_kernel)
            .launch(&config, &args)?;
    }
    // quick and dirty c0 = 0 adjustment for bf cols
    assert_eq!(
        scratch_for_col_sums.len(),
        get_stage_2_bf_scratch_elems(num_stage_2_bf_cols)
    );
    let (
        cub_scratch_bytes,
        (
            bf_args_batch_reduce_scratch_bytes,
            delegation_aux_batch_reduce_scratch_bytes,
            grand_product_scratch_bytes,
        ),
    ) = get_stage_2_cub_scratch_bytes_internal(n, num_stage_2_bf_cols)?;
    assert_eq!(scratch_for_cub_ops.len(), cub_scratch_bytes);
    batch_reduce::<BF>(
        ReduceOperation::Sum,
        &mut scratch_for_cub_ops[0..bf_args_batch_reduce_scratch_bytes],
        &stage_2_bf_cols,
        &mut scratch_for_col_sums[0..num_stage_2_bf_cols],
        stream,
    )?;
    let stride = stage_2_bf_cols.stride();
    let offset = stage_2_bf_cols.offset();
    let mut last_row =
        DeviceMatrixChunkMut::new(stage_2_bf_cols.slice_mut(), stride, offset + n - 1, 1);
    let scratch_for_col_sums_match_last_row_shape =
        DeviceMatrixChunk::new(&scratch_for_col_sums[0..num_stage_2_bf_cols], 1, 0, 1);
    sub_into_x(
        &mut last_row,
        &scratch_for_col_sums_match_last_row_shape,
        stream,
    )?;
    // c0 = 0 adjustment isn't helpful for e4 col LDEs, but the CPU code does it
    // anyway for the delegation aux poly, because the verifier needs to know
    // the sum of all elements except the last, and placing the negative sum
    // into the last element lets us set up convenient constraints to prove
    // the sum value.
    if handle_delegation_requests || process_delegations {
        let start_col = 4 * translate_e4_offset(delegation_processing_aux_poly.start());
        let stride = stage_2_e4_cols.stride();
        let offset = stage_2_e4_cols.offset();
        let slice =
            &mut (stage_2_e4_cols.slice_mut())[start_col * stride..(start_col + 4) * stride];
        let delegation_aux_poly_cols = DeviceMatrixChunkMut::new(slice, stride, offset, n);
        batch_reduce::<BF>(
            ReduceOperation::Sum,
            &mut scratch_for_cub_ops[0..delegation_aux_batch_reduce_scratch_bytes],
            &delegation_aux_poly_cols,
            &mut scratch_for_col_sums[0..4],
            stream,
        )?;
        let mut last_row = DeviceMatrixChunkMut::new(slice, stride, offset + n - 1, 1);
        let scratch_for_col_sums_match_last_row_shape =
            DeviceMatrixChunk::new(&scratch_for_col_sums[0..4], 1, 0, 1);
        sub_into_x(
            &mut last_row,
            &scratch_for_col_sums_match_last_row_shape,
            stream,
        )?;
    }
    // last memory arg is the grand product of the second-to-last memory arg
    // Args are vectorized E4, so I need to transpose the second-to-last col
    // to a col of E4 tuples, do the grand product, then transpose back.
    assert!(num_memory_args >= 2); // weird if this is not the case
    let stride = stage_2_e4_cols.stride();
    let offset = stage_2_e4_cols.offset();
    let second_to_last_slice_start = 4 * (memory_args_start + num_memory_args - 2) * stride;
    let (_, slice) = stage_2_e4_cols
        .slice_mut()
        .split_at_mut(second_to_last_slice_start);
    let (second_to_last_slice, last_slice) = slice.split_at_mut(4 * stride);
    let second_to_last_col = DeviceMatrixChunk::new(second_to_last_slice, stride, offset, n);
    let mut last_col = DeviceMatrixChunkMut::new(last_slice, stride, offset, n);
    // Repurposes aggregated_entry_inv scratch space, which should have
    // an underlying allocation of size >= 2 * n E4 elements
    // I think 2 size-n scratch arrays is the best we can do, keeping in mind that device scan
    // is out-of-place and we don't want to clobber the vectorized second to last column:
    //   Vectorized e4 second to last column -> nonvectorized e4 scratch ->
    //   nonvectorized grand product scratch -> vectorized last column
    let (transposed_scratch_slice, grand_product_e4_scratch_slice) =
        scratch_for_aggregated_entry_invs.split_at_mut(n);
    let (grand_product_e4_scratch_slice, _) = grand_product_e4_scratch_slice.split_at_mut(n);
    let transposed_scratch_slice = unsafe { transposed_scratch_slice.transmute_mut::<BF>() };
    let mut second_to_last_col_transposed = DeviceMatrixMut::new(transposed_scratch_slice, 4);
    transpose(
        &second_to_last_col,
        &mut second_to_last_col_transposed,
        stream,
    )?;
    let transposed_scratch_slice = unsafe { transposed_scratch_slice.transmute_mut::<E4>() };
    let grand_product_e4_scratch_slice =
        unsafe { grand_product_e4_scratch_slice.transmute_mut::<E4>() };
    scan(
        ScanOperation::Product,
        false,
        &mut scratch_for_cub_ops[0..grand_product_scratch_bytes],
        transposed_scratch_slice,
        grand_product_e4_scratch_slice,
        stream,
    )?;
    let grand_product_e4_scratch_slice =
        unsafe { grand_product_e4_scratch_slice.transmute_mut::<BF>() };
    let grand_product_transposed = DeviceMatrix::new(grand_product_e4_scratch_slice, 4);
    transpose(&grand_product_transposed, &mut last_col, stream)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::Context;
    use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Field;
    use prover::tests::{run_basic_delegation_test_impl, GpuComparisonArgs};
    use serial_test::serial;

    type BF = BaseField;
    type E4 = Ext4Field;

    // CPU witness generation and checks are copied from zksync_airbender prover test.
    fn comparison_hook(gpu_comparison_args: &GpuComparisonArgs) {
        let GpuComparisonArgs {
            circuit,
            setup,
            external_values,
            public_inputs: _,
            twiddles: _,
            lde_precomputations: _,
            table_driver,
            lookup_mapping,
            log_n,
            circuit_sequence,
            delegation_processing_type,
            prover_data,
        } = gpu_comparison_args;
        let log_n = *log_n;
        let circuit_sequence = *circuit_sequence;
        let delegation_processing_type = delegation_processing_type.unwrap_or(0);
        let domain_size = 1 << log_n;
        let cached_data = ProverCachedData::new(
            &circuit,
            &external_values,
            domain_size,
            circuit_sequence,
            delegation_processing_type,
        );
        // double-check argument sizes if desired
        print_sizes();
        // Repackage row-major data as column-major for GPU
        let range = 0..domain_size;
        let domain_index = 0;
        let num_setup_cols = circuit.setup_layout.total_width;
        let num_witness_cols = circuit.witness_layout.total_width;
        let num_memory_cols = circuit.memory_layout.total_width;
        let num_trace_cols = num_witness_cols + num_memory_cols;
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
        let mut h_setup_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_setup_cols];
        let mut h_trace_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_trace_cols];
        let mut h_generic_lookups_args_to_table_entries_map: Vec<u32> =
            vec![0; domain_size * num_generic_args];
        let mut h_stage_2_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_stage_2_cols];
        // imitating access patterns in zksync_airbender's prover_stages/stage4.rs
        let mut trace_view = prover_data.stage_1_result.ldes[domain_index]
            .trace
            .row_view(range.clone());
        let mut setup_trace_view = setup.ldes[domain_index].trace.row_view(range.clone());
        let mut lookup_mapping_view = lookup_mapping.row_view(range.clone());
        unsafe {
            for i in 0..domain_size {
                let setup_trace_view_row = setup_trace_view.current_row_ref();
                let trace_view_row = trace_view.current_row_ref();
                {
                    let mut src = setup_trace_view_row.as_ptr();
                    for j in 0..num_setup_cols {
                        h_setup_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                {
                    let mut src = trace_view_row.as_ptr();
                    for j in 0..num_trace_cols {
                        h_trace_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                setup_trace_view.advance_row();
                trace_view.advance_row();
            }
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
            println!("now.elapsed() {:?}", now.elapsed());
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
        let mut d_alloc_setup_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_setup_cols).unwrap();
        let mut d_alloc_trace_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_trace_cols).unwrap();
        let mut d_alloc_generic_lookups_args_to_table_entries_map =
            DeviceAllocation::<u32>::alloc(domain_size * num_generic_args).unwrap();
        let mut d_alloc_stage_2_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_stage_2_cols).unwrap();
        let num_e4_scratch_elems = get_stage_2_e4_scratch_elems(domain_size, circuit);
        let mut d_alloc_e4_scratch = DeviceAllocation::<E4>::alloc(num_e4_scratch_elems).unwrap();
        let cub_scratch_bytes =
            get_stage_2_cub_scratch_bytes(domain_size, num_stage_2_bf_cols).unwrap();
        let mut d_alloc_scratch_for_cub_ops =
            DeviceAllocation::<u8>::alloc(cub_scratch_bytes).unwrap();
        let num_bf_scratch_elems = get_stage_2_bf_scratch_elems(num_stage_2_bf_cols);
        let mut d_alloc_scratch_for_col_sums =
            DeviceAllocation::<BF>::alloc(num_bf_scratch_elems).unwrap();
        let mut d_lookup_challenges = DeviceAllocation::<LookupChallenges>::alloc(1).unwrap();
        memory_copy_async(&mut d_alloc_setup_cols, &h_setup_cols, &stream).unwrap();
        memory_copy_async(&mut d_alloc_trace_cols, &h_trace_cols, &stream).unwrap();
        memory_copy_async(
            &mut d_alloc_generic_lookups_args_to_table_entries_map,
            &h_generic_lookups_args_to_table_entries_map,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut d_lookup_challenges, &[h_lookup_challenges], &stream).unwrap();
        let d_setup_cols = DeviceMatrix::new(&d_alloc_setup_cols, domain_size);
        let d_trace_cols = DeviceMatrix::new(&d_alloc_trace_cols, domain_size);
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
            &mut d_alloc_scratch_for_col_sums,
            &d_lookup_challenges[0],
            &cached_data,
            &circuit,
            table_driver.total_tables_len, // may be > trace_len. that's ok.
            log_n as u32,
            &stream,
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
        let (lazy_init_bf_arg_col, lazy_init_e4_arg_col) = if cached_data.process_shuffle_ram_init {
            (
                lazy_init_lookup_set.base_field_oracles.start(),
                translate_e4_offset(lazy_init_lookup_set.ext_4_field_oracles.start()),
            )
        } else {
            (0, 0)
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
            .intermediate_polys_for_memory_argument
            .start();
        let memory_args_start = translate_e4_offset(raw_col);
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
            for i in 0..domain_size {
                let stage_2_trace_view_row = stage_2_trace_view.current_row_ref();
                // range check 16 comparisons
                let src = stage_2_trace_view_row.as_ptr();
                let start = range_check_16_bf_args_start;
                let end = start + range_check_16_num_bf_args;
                for j in start..end {
                    assert_eq!(
                        h_stage_2_bf_cols[i + j * domain_size],
                        src.add(j).read(),
                        "range check 16 bf failed at row {} col {}",
                        i,
                        j,
                    );
                }
                let src = stage_2_trace_view_row
                    .as_ptr()
                    .add(circuit.stage_2_layout.ext4_polys_offset)
                    .cast::<E4>();
                assert!(src.is_aligned());
                let start = range_check_16_e4_args_start;
                let end = start + range_check_16_num_e4_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src.add(j).read(),
                        "range check 16 e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // timestamp range check comparisons
                let src = stage_2_trace_view_row.as_ptr();
                let start = timestamp_range_check_bf_args_start;
                let end = start + timestamp_range_check_num_bf_args;
                for j in start..end {
                    assert_eq!(
                        h_stage_2_bf_cols[i + j * domain_size],
                        src.add(j).read(),
                        "timestamp range check bf failed at row {} col {}",
                        i,
                        j,
                    );
                }
                let src = stage_2_trace_view_row
                    .as_ptr()
                    .add(circuit.stage_2_layout.ext4_polys_offset)
                    .cast::<E4>();
                assert!(src.is_aligned());
                let start = timestamp_range_check_e4_args_start;
                let end = start + timestamp_range_check_num_e4_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src.add(j).read(),
                        "timestamp range check e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                // Comparisons for 32-bit lazy init address args,
                // (treated as an extra pair of range check 16 args)
                if cached_data.process_shuffle_ram_init {
                    let src = stage_2_trace_view_row.as_ptr();
                    let j = lazy_init_bf_arg_col;
                    assert_eq!(
                        h_stage_2_bf_cols[i + j * domain_size],
                        src.add(j).read(),
                        "lazy init address bf failed at row {}",
                        i,
                    );
                    let src = stage_2_trace_view_row
                        .as_ptr()
                        .add(circuit.stage_2_layout.ext4_polys_offset)
                        .cast::<E4>();
                    assert!(src.is_aligned());
                    let j = lazy_init_e4_arg_col;
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src.add(j).read(),
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
                        src.add(j).read(),
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
                        src.add(j).read(),
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
                        src.add(j).read(),
                        "delegation aux poly failed at row {}",
                        i,
                    );
                }
                // memory arg comparisons
                let start = memory_args_start;
                let end = start + num_memory_args;
                for j in start..end {
                    assert_eq!(
                        get_vectorized_e4_val(i, j),
                        src.add(j).read(),
                        "memory e4 failed at row {} col {}",
                        i,
                        j,
                    );
                }
                stage_2_trace_view.advance_row();
            }
        }
    }

    // #[test]
    // #[serial]
    // fn test_stage_2_for_basic_circuit() {
    //     let ctx = Context::create(12).unwrap();
    //     run_basic_test_impl(Some(Box::new(comparison_hook)));
    //     ctx.destroy().unwrap();
    // }

    #[test]
    #[serial]
    fn test_stage_2_for_delegation_circuit() {
        let ctx = Context::create(12).unwrap();
        run_basic_delegation_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }
}
