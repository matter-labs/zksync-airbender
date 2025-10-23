use crate::device_structures::{
    DeviceMatrix, DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut,
    DeviceMatrixChunkMutImpl, DeviceMatrixMut, MutPtrAndStride, PtrAndStride,
};
use crate::field::{BaseField, Ext4Field};
use crate::ops_complex::transpose;
use crate::ops_cub::device_reduce::{
    batch_reduce_with_adaptive_parallelism,
    get_batch_reduce_with_adaptive_parallelism_temp_storage, ReduceOperation,
};
use crate::ops_cub::device_scan::{get_scan_temp_storage_bytes, scan, ScanOperation};
use crate::ops_simple::sub_into_x;
use crate::prover::arg_utils::*;
use crate::prover::context::DeviceProperties;
use crate::utils::WARP_SIZE;

use cs::definitions::{
    DelegationProcessingLayout, DelegationRequestLayout, TIMESTAMP_COLUMNS_NUM_BITS,
};
use cs::one_row_compiler::{
    CompiledCircuitArtifact, LookupWidth1SourceDestInformation,
    LookupWidth1SourceDestInformationForExpressions,
};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use field::{Field, PrimeField};
use prover::definitions::ExternalDelegationArgumentChallenges;
use std::cmp::max;

type BF = BaseField;
type E4 = Ext4Field;

cuda_kernel!(
    ZeroStage2LastRow,
    zero_stage_2_last_row,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_stage_2_bf_cols: u32,
    num_stage_2_e4_cols: u32,
    log_n: u32,
);

zero_stage_2_last_row!(ab_zero_stage_2_last_row_kernel);

cuda_kernel!(
    RangeCheckAggregatedEntryInvsAndMultiplicitiesArg,
    range_check_aggregated_entry_invs_and_multiplicities_arg,
    challenges: *const LookupChallenges,
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
    ab_range_check_aggregated_entry_invs_and_multiplicities_arg_kernel
);

cuda_kernel!(
    DecoderAggregatedEntryInvsAndMultiplicitiesArg,
    decoder_aggregated_entry_invs_and_multiplicities_arg,
    challenges: *const DecoderTableChallenges,
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

decoder_aggregated_entry_invs_and_multiplicities_arg!(
    ab_decoder_aggregated_entry_invs_and_multiplicities_arg_kernel
);

cuda_kernel!(
    GenericAggregatedEntryInvsAndMultiplicitiesArg,
    generic_aggregated_entry_invs_and_multiplicities_arg,
    challenges: *const LookupChallenges,
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
    ab_generic_aggregated_entry_invs_and_multiplicities_arg_kernel
);

cuda_kernel!(
    ProcessRangeCheck16TrivialChecks,
    process_range_check_16_trivial_checks,
    range_check_16_layout: RangeCheck16ArgsLayout,
    witness_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
);

process_range_check_16_trivial_checks!(ab_range_check_16_trivial_checks_kernel);

cuda_kernel!(
    ProcessRangeCheckExpressions,
    process_range_check_expressions,
    expressions: TEMPORARYFlattenedLookupExpressionsLayout,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
);

process_range_check_expressions!(ab_range_check_expressions_kernel);

cuda_kernel!(
    ProcessLazyInitRangeChecks,
    process_lazy_init_range_checks,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
);

process_lazy_init_range_checks!(ab_lazy_init_range_checks_kernel);

cuda_kernel!(
    ProcessRangeCheckExpressionsForShuffleRam,
    process_range_check_expressions_for_shuffle_ram,
    expressions_for_shuffle_ram: FlattenedLookupExpressionsForShuffleRamLayout,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_timestamp_high_from_circuit_idx: BF,
    log_n: u32,
);

process_range_check_expressions_for_shuffle_ram!(ab_range_check_expressions_for_shuffle_ram_kernel);

cuda_kernel!(
    ProcessDecoderLookupIntermediatePoly,
    process_decoder_lookup_intermediate_poly,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_decoder_lookups: *const E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    decoder_lookup_arg_col: u32,
    predicate_col: u32,
    pc_start_col: u32,
    log_n: u32,
);

process_decoder_lookup_intermediate_poly!(ab_decoder_lookup_intermediate_poly_kernel);

cuda_kernel!(
    ProcessGenericLookupIntermediatePolys,
    process_generic_lookup_intermediate_polys,
    generic_lookups_args_to_table_entries_map: PtrAndStride<u32>,
    aggregated_entry_invs_for_generic_lookups: *const E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    generic_args_start: u32,
    num_generic_args: u32,
    log_n: u32,
);

process_generic_lookup_intermediate_polys!(ab_generic_lookup_intermediate_polys_kernel);

cuda_kernel!(
    HandleDelegationRequests,
    handle_delegation_requests,
    delegation_challenges: DelegationChallenges,
    request_metadata: DelegationRequestMetadata,
    memory_cols: PtrAndStride<BF>,
    setup_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    delegation_aux_poly_col: u32,
    is_unrolled: bool,
    log_n: u32,
);

handle_delegation_requests!(ab_handle_delegation_requests_kernel);

cuda_kernel!(
    ProcessDelegations,
    process_delegations,
    delegation_challenges: DelegationChallenges,
    processing_metadata: DelegationProcessingMetadata,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    delegation_aux_poly_col: u32,
    log_n: u32,
);

process_delegations!(ab_process_delegations_kernel);

pub(crate) fn stage2_zero_last_row(
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_stage_2_bf_cols: usize,
    num_stage_2_e4_cols: usize,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let max_cols = max(num_stage_2_bf_cols, num_stage_2_e4_cols) as u32;
    let block_dim = WARP_SIZE * 4;
    let grid_dim = (max_cols + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ZeroStage2LastRowArguments::new(
        stage_2_bf_cols,
        stage_2_e4_cols,
        num_stage_2_bf_cols as u32,
        num_stage_2_e4_cols as u32,
        log_n,
    );
    ZeroStage2LastRowFunction(ab_zero_stage_2_last_row_kernel).launch(&config, &args)
}

pub(crate) fn stage2_process_range_check_16_trivial_checks<F: Fn(usize) -> usize>(
    circuit: &CompiledCircuitArtifact<BF>,
    range_check_16_width_1_lookups_access: &Vec<LookupWidth1SourceDestInformation>,
    range_check_16_width_1_lookups_access_via_expressions: &Vec<
        LookupWidth1SourceDestInformationForExpressions<BF>,
    >,
    witness_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    let range_check_16_layout = RangeCheck16ArgsLayout::new(
        circuit,
        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,
        translate_e4_offset,
    );
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessRangeCheck16TrivialChecksArguments::new(
        range_check_16_layout,
        witness_cols,
        aggregated_entry_invs_for_range_check_16,
        stage_2_bf_cols,
        stage_2_e4_cols,
        log_n,
    );
    ProcessRangeCheck16TrivialChecksFunction(ab_range_check_16_trivial_checks_kernel)
        .launch(&config, &args)
}

fn process_range_check_expressions_impl<F: Fn(usize) -> usize>(
    range_check_width_1_lookups_access_via_expressions: &Vec<
        LookupWidth1SourceDestInformationForExpressions<BF>,
    >,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_stage_2_bf_cols: usize,
    num_stage_2_e4_cols: usize,
    expect_constant_terms_are_zero: bool,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    if range_check_width_1_lookups_access_via_expressions.len() == 0 {
        return Ok(());
    }
    let expressions = TEMPORARYFlattenedLookupExpressionsLayout::new(
        range_check_width_1_lookups_access_via_expressions,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        expect_constant_terms_are_zero,
        translate_e4_offset,
    );
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessRangeCheckExpressionsArguments::new(
        expressions,
        witness_cols,
        memory_cols,
        aggregated_entry_invs,
        stage_2_bf_cols,
        stage_2_e4_cols,
        log_n,
    );
    ProcessRangeCheckExpressionsFunction(ab_range_check_expressions_kernel).launch(&config, &args)
}

pub(crate) fn stage2_process_range_check_16_expressions<F: Fn(usize) -> usize>(
    range_check_16_width_1_lookups_access_via_expressions: &Vec<
        LookupWidth1SourceDestInformationForExpressions<BF>,
    >,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_stage_2_bf_cols: usize,
    num_stage_2_e4_cols: usize,
    expect_constant_terms_are_zero: bool,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    process_range_check_expressions_impl(
        range_check_16_width_1_lookups_access_via_expressions,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_range_check_16,
        stage_2_bf_cols,
        stage_2_e4_cols,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        expect_constant_terms_are_zero,
        log_n,
        translate_e4_offset,
        stream,
    )
}

// This function's logic is identical to stage2_process_range_check_16_expressions.
// I'm making it distinct to match Alex's API.
pub(crate) fn stage2_process_timestamp_range_check_expressions<F: Fn(usize) -> usize>(
    timestamp_range_check_width_1_lookups_access_via_expressions: &Vec<
        LookupWidth1SourceDestInformationForExpressions<BF>,
    >,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_timestamp_range_checks: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_stage_2_bf_cols: usize,
    num_stage_2_e4_cols: usize,
    expect_constant_terms_are_zero: bool,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    process_range_check_expressions_impl(
        timestamp_range_check_width_1_lookups_access_via_expressions,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        stage_2_bf_cols,
        stage_2_e4_cols,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        expect_constant_terms_are_zero,
        log_n,
        translate_e4_offset,
        stream,
    )
}

pub(crate) fn stage2_process_lazy_init_range_checks(
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessLazyInitRangeChecksArguments::new(
        lazy_init_teardown_layouts,
        memory_cols,
        aggregated_entry_invs_for_range_check_16,
        stage_2_bf_cols,
        stage_2_e4_cols,
        log_n,
    );
    ProcessLazyInitRangeChecksFunction(ab_lazy_init_range_checks_kernel).launch(&config, &args)
}

pub(crate) fn stage2_process_timestamp_range_check_expressions_with_extra_timestamp_contribution<
    F: Fn(usize) -> usize,
>(
    timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram: &Vec<
        LookupWidth1SourceDestInformationForExpressions<BF>,
    >,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_timestamp_range_checks: *const E4,
    stage_2_bf_cols: MutPtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_stage_2_bf_cols: usize,
    num_stage_2_e4_cols: usize,
    memory_timestamp_high_from_circuit_idx: BF,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    if timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.len() == 0 {
        return Ok(());
    }
    let expressions = FlattenedLookupExpressionsForShuffleRamLayout::new(
        &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
        num_stage_2_bf_cols,
        num_stage_2_e4_cols,
        &translate_e4_offset,
    );
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessRangeCheckExpressionsForShuffleRamArguments::new(
        expressions,
        setup_cols,
        witness_cols,
        memory_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        stage_2_bf_cols,
        stage_2_e4_cols,
        memory_timestamp_high_from_circuit_idx,
        log_n,
    );
    ProcessRangeCheckExpressionsForShuffleRamFunction(
        ab_range_check_expressions_for_shuffle_ram_kernel,
    )
    .launch(&config, &args)
}

pub(crate) fn stage2_process_executor_family_decoder_intermediate_poly<F: Fn(usize) -> usize>(
    circuit: &CompiledCircuitArtifact<BF>,
    memory_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_decoder_lookups: *const E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    let decoder_lookup_poly = &circuit
        .stage_2_layout
        .intermediate_poly_for_decoder_accesses;
    assert_eq!(decoder_lookup_poly.num_elements(), 1);
    let decoder_lookup_arg_col = translate_e4_offset(decoder_lookup_poly.start());
    let intermediate_state_layout = circuit.memory_layout.intermediate_state_layout.unwrap();
    let predicate_col = intermediate_state_layout.execute.start();
    let pc_start_col = intermediate_state_layout.pc.start();
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessDecoderLookupIntermediatePolyArguments::new(
        memory_cols,
        aggregated_entry_invs_for_decoder_lookups,
        stage_2_e4_cols,
        decoder_lookup_arg_col as u32,
        predicate_col as u32,
        pc_start_col as u32,
        log_n,
    );
    ProcessDecoderLookupIntermediatePolyFunction(ab_decoder_lookup_intermediate_poly_kernel)
        .launch(&config, &args)
}

pub(crate) fn stage2_process_generic_lookup_intermediate_polys<F: Fn(usize) -> usize>(
    circuit: &CompiledCircuitArtifact<BF>,
    generic_lookups_args_to_table_entries_map: &(impl DeviceMatrixChunkImpl<u32> + ?Sized),
    aggregated_entry_invs_for_generic_lookups: *const E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    num_generic_args: usize,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(num_generic_args > 0);
    assert_eq!(
        generic_lookups_args_to_table_entries_map.rows(),
        (1 << log_n) as usize
    );
    assert_eq!(
        generic_lookups_args_to_table_entries_map.cols(),
        num_generic_args,
    );
    let generic_args_start = translate_e4_offset(
        circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .start(),
    );
    let generic_lookups_args_to_table_entries_map =
        generic_lookups_args_to_table_entries_map.as_ptr_and_stride();
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessGenericLookupIntermediatePolysArguments::new(
        generic_lookups_args_to_table_entries_map,
        aggregated_entry_invs_for_generic_lookups,
        stage_2_e4_cols,
        generic_args_start as u32,
        num_generic_args as u32,
        log_n,
    );
    ProcessGenericLookupIntermediatePolysFunction(ab_generic_lookup_intermediate_polys_kernel)
        .launch(&config, &args)
}

pub(crate) fn stage2_process_range_check_16_entry_invs_and_multiplicity<F: Fn(usize) -> usize>(
    lookup_challenges: *const LookupChallenges,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_range_check_16: *mut E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    range_check_16_multiplicities_src: usize,
    range_check_16_multiplicities_dst: usize,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    // range check table values are just row indexes,
    // so i don't need to read their setup entries
    let dummy_setup_column = 0;
    let num_range_check_16_rows = 1 << 16;
    assert!(num_range_check_16_rows < (1 << log_n as usize)); // just in case
    let num_range_check_16_multiplicities_cols = 1;
    let range_check_16_multiplicities_dst_col =
        translate_e4_offset(range_check_16_multiplicities_dst);
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = RangeCheckAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
        lookup_challenges,
        witness_cols,
        setup_cols,
        stage_2_e4_cols,
        aggregated_entry_invs_for_range_check_16,
        dummy_setup_column,
        range_check_16_multiplicities_src as u32,
        range_check_16_multiplicities_dst_col as u32,
        num_range_check_16_multiplicities_cols as u32,
        num_range_check_16_rows as u32,
        log_n as u32,
    );
    RangeCheckAggregatedEntryInvsAndMultiplicitiesArgFunction(
        ab_range_check_aggregated_entry_invs_and_multiplicities_arg_kernel,
    )
    .launch(&config, &args)
}

pub(crate) fn stage2_process_timestamp_range_check_entry_invs_and_multiplicity<
    F: Fn(usize) -> usize,
>(
    lookup_challenges: *const LookupChallenges,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_timestamp_range_checks: *mut E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    timestamp_range_check_multiplicities_src: usize,
    timestamp_range_check_multiplicities_dst: usize,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    // timestamp table values are just row indexes,
    // so i don't need to read their setup entries
    let dummy_setup_column = 0;
    let num_timestamp_range_check_rows = 1 << TIMESTAMP_COLUMNS_NUM_BITS;
    assert!(num_timestamp_range_check_rows < (1 << log_n as usize)); // just in case
    let num_timestamp_multiplicities_cols = 1;
    let timestamp_range_check_multiplicities_dst_col =
        translate_e4_offset(timestamp_range_check_multiplicities_dst);
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = RangeCheckAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
        lookup_challenges,
        witness_cols,
        setup_cols,
        stage_2_e4_cols,
        aggregated_entry_invs_for_timestamp_range_checks,
        dummy_setup_column,
        timestamp_range_check_multiplicities_src as u32,
        timestamp_range_check_multiplicities_dst_col as u32,
        num_timestamp_multiplicities_cols as u32,
        num_timestamp_range_check_rows as u32,
        log_n as u32,
    );
    RangeCheckAggregatedEntryInvsAndMultiplicitiesArgFunction(
        ab_range_check_aggregated_entry_invs_and_multiplicities_arg_kernel,
    )
    .launch(&config, &args)
}

pub(crate) fn stage2_process_executor_family_decoder_entry_invs_and_multiplicity<
    F: Fn(usize) -> usize,
>(
    circuit: &CompiledCircuitArtifact<BF>,
    decoder_table_challenges: *const DecoderTableChallenges,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_decoder_lookups: *mut E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_decoder_table_rows = circuit.executor_family_decoder_table_size;
    assert!(num_decoder_table_rows > 0);
    let setup_src = &circuit.setup_layout.preprocessed_decoder_setup_columns;
    let multiplicities_src = &circuit
        .witness_layout
        .multiplicities_columns_for_decoder_in_executor_families;
    let multiplicities_dst = &circuit
        .stage_2_layout
        .intermediate_polys_for_decoder_multiplicities;
    let num_decoder_multiplicities_cols = setup_src.num_elements();
    // Just a sanity check. We can handle > 1 if needed.
    assert_eq!(num_decoder_multiplicities_cols, 1);
    assert_eq!(
        num_decoder_multiplicities_cols,
        multiplicities_src.num_elements()
    );
    assert_eq!(
        num_decoder_multiplicities_cols,
        multiplicities_dst.num_elements()
    );
    let start_col_in_setup = setup_src.start();
    let multiplicities_src_cols_start = multiplicities_src.start();
    let multiplicities_dst_cols_start = translate_e4_offset(multiplicities_dst.start());
    let lookup_encoding_capacity = (1 << log_n as usize) - 1;
    let num_decoder_table_rows_tail = num_decoder_table_rows % lookup_encoding_capacity;
    assert_eq!(
        num_decoder_multiplicities_cols,
        (num_decoder_table_rows + lookup_encoding_capacity - 1) / lookup_encoding_capacity
    );
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = DecoderAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
        decoder_table_challenges,
        witness_cols,
        setup_cols,
        stage_2_e4_cols,
        aggregated_entry_invs_for_decoder_lookups,
        start_col_in_setup as u32,
        multiplicities_src_cols_start as u32,
        multiplicities_dst_cols_start as u32,
        num_decoder_multiplicities_cols as u32,
        num_decoder_table_rows_tail as u32,
        log_n as u32,
    );
    DecoderAggregatedEntryInvsAndMultiplicitiesArgFunction(
        ab_decoder_aggregated_entry_invs_and_multiplicities_arg_kernel,
    )
    .launch(&config, &args)
}

pub(crate) fn stage2_process_generic_lookup_entry_invs_and_multiplicity<F: Fn(usize) -> usize>(
    lookup_challenges: *const LookupChallenges,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    aggregated_entry_invs_for_generic_lookups: *mut E4,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    generic_lookup_setup_columns_start: usize,
    num_generic_multiplicities_cols: usize,
    num_generic_table_rows: usize,
    generic_lookup_multiplicities_src_start: usize,
    generic_lookup_multiplicities_dst_start: usize,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    // If we ever need a circuit without generic args, I can refactor.
    assert!(num_generic_table_rows > 0);
    let generic_lookup_multiplicities_dst_cols_start =
        translate_e4_offset(generic_lookup_multiplicities_dst_start);
    let lookup_encoding_capacity = (1 << log_n as usize) - 1;
    let num_generic_table_rows_tail = num_generic_table_rows % lookup_encoding_capacity;
    assert_eq!(
        num_generic_multiplicities_cols,
        (num_generic_table_rows + lookup_encoding_capacity - 1) / lookup_encoding_capacity
    );
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenericAggregatedEntryInvsAndMultiplicitiesArgArguments::new(
        lookup_challenges,
        witness_cols,
        setup_cols,
        stage_2_e4_cols,
        aggregated_entry_invs_for_generic_lookups,
        generic_lookup_setup_columns_start as u32,
        generic_lookup_multiplicities_src_start as u32,
        generic_lookup_multiplicities_dst_cols_start as u32,
        num_generic_multiplicities_cols as u32,
        num_generic_table_rows_tail as u32,
        log_n as u32,
    );
    GenericAggregatedEntryInvsAndMultiplicitiesArgFunction(
        ab_generic_aggregated_entry_invs_and_multiplicities_arg_kernel,
    )
    .launch(&config, &args)
}

pub(crate) fn stage2_handle_delegation_requests(
    circuit: &CompiledCircuitArtifact<BF>,
    delegation_challenges: &ExternalDelegationArgumentChallenges,
    memory_timestamp_high_from_circuit_idx: Option<BF>,
    layout: &DelegationRequestLayout,
    memory_cols: PtrAndStride<BF>,
    setup_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    delegation_aux_poly_col: usize,
    is_unrolled: bool,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let delegation_challenges = DelegationChallenges::new(delegation_challenges);
    let (timestamp_columns, memory_timestamp_high_from_circuit_idx) = if is_unrolled {
        assert!(memory_timestamp_high_from_circuit_idx.is_none());
        (
            &circuit
                .memory_layout
                .intermediate_state_layout
                .unwrap()
                .timestamp,
            BF::ZERO,
        )
    } else {
        (
            &circuit.setup_layout.timestamp_setup_columns,
            memory_timestamp_high_from_circuit_idx.unwrap(),
        )
    };
    let has_abi_mem_offset_high = layout.abi_mem_offset_high.num_elements() > 0;
    let abi_mem_offset_high_col = if has_abi_mem_offset_high {
        layout.abi_mem_offset_high.start() as u32
    } else {
        0
    };
    let request_metadata = DelegationRequestMetadata {
        multiplicity_col: layout.multiplicity.start() as u32,
        timestamp_col: timestamp_columns.start() as u32,
        memory_timestamp_high_from_circuit_idx,
        delegation_type_col: layout.delegation_type.start() as u32,
        in_cycle_write_idx: BF::from_u64_unchecked(layout.in_cycle_write_index as u64),
        abi_mem_offset_high_col,
        has_abi_mem_offset_high,
    };
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = HandleDelegationRequestsArguments::new(
        delegation_challenges,
        request_metadata,
        memory_cols,
        setup_cols,
        stage_2_e4_cols,
        delegation_aux_poly_col as u32,
        is_unrolled,
        log_n,
    );
    HandleDelegationRequestsFunction(ab_handle_delegation_requests_kernel).launch(&config, &args)
}

pub(crate) fn stage2_process_delegations(
    delegation_challenges: &ExternalDelegationArgumentChallenges,
    delegation_type: BF,
    layout: &DelegationProcessingLayout,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    delegation_aux_poly_col: usize,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let delegation_challenges = DelegationChallenges::new(delegation_challenges);
    let has_abi_mem_offset_high = layout.abi_mem_offset_high.num_elements() > 0;
    let abi_mem_offset_high_col = if has_abi_mem_offset_high {
        layout.abi_mem_offset_high.start() as u32
    } else {
        0
    };
    let processing_metadata = DelegationProcessingMetadata {
        multiplicity_col: layout.multiplicity.start() as u32,
        delegation_type,
        write_timestamp_col: layout.write_timestamp.start() as u32,
        abi_mem_offset_high_col,
        has_abi_mem_offset_high,
    };
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ProcessDelegationsArguments::new(
        delegation_challenges,
        processing_metadata,
        memory_cols,
        stage_2_e4_cols,
        delegation_aux_poly_col as u32,
        log_n,
    );
    ProcessDelegationsFunction(ab_process_delegations_kernel).launch(&config, &args)
}

pub(crate) fn get_stage_2_cub_and_batch_reduce_intermediate_scratch_internal(
    domain_size: usize,
    num_stage_2_bf_cols: usize,
    handle_delegation_requests: bool,
    process_delegations: bool,
    device_properties: &DeviceProperties,
) -> CudaResult<((usize, usize, usize), (usize, usize))> {
    let (bf_args_batch_reduce_scratch_bytes, bf_args_batch_reduce_intermediate_elems) =
        get_batch_reduce_with_adaptive_parallelism_temp_storage::<BF>(
            ReduceOperation::Sum,
            num_stage_2_bf_cols,
            domain_size,
            device_properties,
        )?;
    let (delegation_aux_batch_reduce_scratch_bytes, delegation_aux_batch_reduce_intermediate_elems) =
        if handle_delegation_requests || process_delegations {
            let (x, y) = get_batch_reduce_with_adaptive_parallelism_temp_storage::<BF>(
                ReduceOperation::Sum,
                4, // one vectorized E4 col
                domain_size,
                device_properties,
            )?;
            (x, y)
        } else {
            (0, 0)
        };
    let grand_product_scratch_bytes =
        get_scan_temp_storage_bytes::<E4>(ScanOperation::Product, false, domain_size as i32)?;
    Ok((
        (
            bf_args_batch_reduce_scratch_bytes,
            delegation_aux_batch_reduce_scratch_bytes,
            grand_product_scratch_bytes,
        ),
        (
            bf_args_batch_reduce_intermediate_elems,
            delegation_aux_batch_reduce_intermediate_elems,
        ),
    ))
}

pub(crate) fn get_stage_2_cub_and_batch_reduce_intermediate_scratch(
    domain_size: usize,
    num_stage_2_bf_cols: usize,
    handle_delegation_requests: bool,
    process_delegations: bool,
    device_properties: &DeviceProperties,
) -> CudaResult<(usize, usize)> {
    let (
        (
            bf_args_batch_reduce_scratch_bytes,
            delegation_aux_batch_reduce_scratch_bytes,
            grand_product_scratch_bytes,
        ),
        (bf_args_batch_reduce_intermediate_elems, delegation_aux_batch_reduce_intermediate_elems),
    ) = get_stage_2_cub_and_batch_reduce_intermediate_scratch_internal(
        domain_size,
        num_stage_2_bf_cols,
        handle_delegation_requests,
        process_delegations,
        device_properties,
    )?;
    Ok((
        max(
            max(
                bf_args_batch_reduce_scratch_bytes,
                delegation_aux_batch_reduce_scratch_bytes,
            ),
            grand_product_scratch_bytes,
        ),
        max(
            bf_args_batch_reduce_intermediate_elems,
            delegation_aux_batch_reduce_intermediate_elems,
        ),
    ))
}

pub(crate) fn get_stage_2_col_sums_scratch(num_stage_2_bf_cols: usize) -> usize {
    max(num_stage_2_bf_cols, 4)
}

pub(crate) fn get_stage_2_e4_scratch(
    domain_size: usize,
    circuit: &CompiledCircuitArtifact<BF>,
) -> usize {
    max(
        (1 << 16)
            + (1 << TIMESTAMP_COLUMNS_NUM_BITS)
            + circuit.executor_family_decoder_table_size
            + circuit.total_tables_size,
        2 * domain_size, // for transposed grand product
    )
}

pub(crate) fn stage2_col_sum_adjustments_and_grand_product(
    circuit: &CompiledCircuitArtifact<BF>,
    stage_2_bf_cols: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stage_2_e4_cols: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    scratch_for_aggregated_entry_invs: &mut DeviceSlice<E4>,
    scratch_for_cub_ops: &mut DeviceSlice<u8>,
    maybe_batch_reduce_intermediates: &mut Option<&mut DeviceSlice<BF>>,
    scratch_for_col_sums: &mut DeviceSlice<BF>,
    num_stage_2_bf_cols: usize,
    delegation_aux_poly_col: usize,
    n: usize,
    handle_delegation_requests: bool,
    process_delegations: bool,
    unrolled: bool,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    // BF col sum adjustments
    assert_eq!(
        scratch_for_col_sums.len(),
        get_stage_2_col_sums_scratch(num_stage_2_bf_cols)
    );
    let (
        (
            bf_args_batch_reduce_scratch_bytes,
            delegation_aux_batch_reduce_scratch_bytes,
            grand_product_scratch_bytes,
        ),
        (bf_args_batch_reduce_intermediate_elems, delegation_aux_batch_reduce_intermediate_elems),
    ) = get_stage_2_cub_and_batch_reduce_intermediate_scratch_internal(
        n,
        num_stage_2_bf_cols,
        handle_delegation_requests,
        process_delegations,
        device_properties,
    )?;
    assert_eq!(
        scratch_for_cub_ops.len(),
        max(
            max(
                bf_args_batch_reduce_scratch_bytes,
                delegation_aux_batch_reduce_scratch_bytes,
            ),
            grand_product_scratch_bytes,
        ),
    );
    if bf_args_batch_reduce_intermediate_elems > 0
        || delegation_aux_batch_reduce_intermediate_elems > 0
    {
        assert_eq!(
            maybe_batch_reduce_intermediates.as_ref().unwrap().len(),
            max(
                bf_args_batch_reduce_intermediate_elems,
                delegation_aux_batch_reduce_intermediate_elems,
            ),
        )
    } else {
        assert!(maybe_batch_reduce_intermediates.is_none());
    };
    let maybe_intermediates: Option<&mut DeviceSlice<BF>> =
        if bf_args_batch_reduce_intermediate_elems > 0 {
            Some(
                &mut (maybe_batch_reduce_intermediates.as_mut().unwrap())
                    [0..bf_args_batch_reduce_intermediate_elems],
            )
        } else {
            None
        };
    batch_reduce_with_adaptive_parallelism::<BF>(
        ReduceOperation::Sum,
        &mut scratch_for_cub_ops[0..bf_args_batch_reduce_scratch_bytes],
        maybe_intermediates,
        stage_2_bf_cols,
        &mut scratch_for_col_sums[0..num_stage_2_bf_cols],
        stream,
        device_properties,
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
    // Delegation aux poly (E4) col sum adjustment
    // c0 = 0 adjustment isn't helpful for e4 col LDEs, but the CPU code does it
    // anyway for the delegation aux poly, because the verifier needs to know
    // the sum of all elements except the last, and placing the negative sum
    // into the last element lets us set up convenient constraints to prove
    // the sum value.
    if handle_delegation_requests || process_delegations {
        let start_col = 4 * delegation_aux_poly_col;
        let stride = stage_2_e4_cols.stride();
        let offset = stage_2_e4_cols.offset();
        let slice =
            &mut (stage_2_e4_cols.slice_mut())[start_col * stride..(start_col + 4) * stride];
        let delegation_aux_poly_cols = DeviceMatrixChunkMut::new(slice, stride, offset, n);
        let maybe_intermediates: Option<&mut DeviceSlice<BF>> =
            if delegation_aux_batch_reduce_intermediate_elems > 0 {
                Some(
                    &mut (maybe_batch_reduce_intermediates.as_mut().unwrap())
                        [0..delegation_aux_batch_reduce_intermediate_elems],
                )
            } else {
                None
            };
        batch_reduce_with_adaptive_parallelism::<BF>(
            ReduceOperation::Sum,
            &mut scratch_for_cub_ops[0..delegation_aux_batch_reduce_scratch_bytes],
            maybe_intermediates,
            &delegation_aux_poly_cols,
            &mut scratch_for_col_sums[0..4],
            stream,
            device_properties,
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
    // Grand product
    // Data is vectorized E4, so I need to transpose the second-to-last col
    // to a col of E4 tuples, do the grand product, then transpose back.
    let (grand_product_src, grand_product_dst) = get_grand_product_src_dst_cols(circuit, unrolled);
    // sanity check, not essential for correctness
    assert_eq!(grand_product_dst, grand_product_src + 1);
    let stride = stage_2_e4_cols.stride();
    let offset = stage_2_e4_cols.offset();
    let src_slice_start = 4 * grand_product_src * stride;
    let (_, rest) = stage_2_e4_cols.slice_mut().split_at_mut(src_slice_start);
    let (src_slice, rest) = rest.split_at_mut(4 * stride);
    let grand_product_slice_start_in_rest = 4 * (grand_product_dst - grand_product_src - 1);
    let (_, rest) = rest.split_at_mut(grand_product_slice_start_in_rest);
    let (grand_product_slice, _) = rest.split_at_mut(4 * stride);
    let src_matrix = DeviceMatrixChunk::new(src_slice, stride, offset, n);
    let mut grand_product = DeviceMatrixChunkMut::new(grand_product_slice, stride, offset, n);
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
    let mut src_matrix_transposed = DeviceMatrixMut::new(transposed_scratch_slice, 4);
    transpose(&src_matrix, &mut src_matrix_transposed, stream)?;
    let transposed_scratch_slice = unsafe { transposed_scratch_slice.transmute_mut::<E4>() };
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
    transpose(&grand_product_transposed, &mut grand_product, stream)
}
