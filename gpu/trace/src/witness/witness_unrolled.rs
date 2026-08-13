use crate::upstream::GKRCircuitArtifact;
use crate::witness::circuit_type::{
    UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::witness::memory_unrolled::{AuxLayoutData, UnrolledMemoryLayout};
use crate::witness::multiplicities::LookupExpressions;
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledMemoryOracle, UnrolledMemoryTraceDevice,
    UnrolledMemoryTraceRaw, UnrolledNonMemoryOracle, UnrolledNonMemoryTraceDevice,
    UnrolledNonMemoryTraceRaw, UnrolledUnifiedOracle, UnrolledUnifiedTraceDevice,
    UnrolledUnifiedTraceRaw,
};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixImpl, DeviceMatrixMutImpl};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

cuda_kernel!(GenerateFusedUnrolledMemoryKernel,
    generate_fused_unrolled_memory_kernel,
    layout: UnrolledMemoryLayout,
    aux_layout_data: AuxLayoutData,
    oracle: UnrolledMemoryOracle,
    generic_lookup_tables: *const BF,
    memory: *mut BF,
    witness: *mut BF,
    scratch: *mut BF,
    generic_lookup_mapping: *mut u32,
    decoder_lookup_mapping: *mut u32,
    range_check_16_lookup_expressions: LookupExpressions,
    range_check_16_lookup_mapping: *mut u32,
    range_check_timestamp_lookup_expressions: LookupExpressions,
    range_check_timestamp_lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_fused_unrolled_memory_kernel!(ab_generate_fused_load_store_subword_only_kernel);
generate_fused_unrolled_memory_kernel!(ab_generate_fused_load_store_word_only_kernel);

cuda_kernel!(GenerateFusedUnrolledNonMemoryKernel,
    generate_fused_unrolled_non_memory_kernel,
    layout: UnrolledMemoryLayout,
    aux_layout_data: AuxLayoutData,
    oracle: UnrolledNonMemoryOracle,
    generic_lookup_tables: *const BF,
    memory: *mut BF,
    witness: *mut BF,
    scratch: *mut BF,
    generic_lookup_mapping: *mut u32,
    decoder_lookup_mapping: *mut u32,
    range_check_16_lookup_expressions: LookupExpressions,
    range_check_16_lookup_mapping: *mut u32,
    range_check_timestamp_lookup_expressions: LookupExpressions,
    range_check_timestamp_lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_fused_unrolled_non_memory_kernel!(ab_generate_fused_add_sub_lui_auipc_mop_kernel);
generate_fused_unrolled_non_memory_kernel!(ab_generate_fused_jump_branch_slt_kernel);
generate_fused_unrolled_non_memory_kernel!(ab_generate_fused_mul_div_unsigned_kernel);
generate_fused_unrolled_non_memory_kernel!(ab_generate_fused_shift_binary_kernel);

cuda_kernel!(GenerateFusedUnrolledUnifiedKernel,
    ab_generate_fused_unified_reduced_machine_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledUnifiedOracle,
        generic_lookup_tables: *const BF,
        memory: *mut BF,
        witness: *mut BF,
        scratch: *mut BF,
        generic_lookup_mapping: *mut u32,
        decoder_lookup_mapping: *mut u32,
        range_check_16_lookup_expressions: LookupExpressions,
        range_check_16_lookup_mapping: *mut u32,
        range_check_timestamp_lookup_expressions: LookupExpressions,
        range_check_timestamp_lookup_mapping: *mut u32,
        stride: u32,
        count: u32,
    )
);

cuda_kernel!(GenerateWitnessUnrolledMemoryKernel,
    generate_witness_unrolled_memory_kernel,
    trace: UnrolledMemoryTraceRaw,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    scratch: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_unrolled_memory_kernel!(ab_generate_witness_values_load_store_subword_only_kernel);
generate_witness_unrolled_memory_kernel!(ab_generate_witness_values_load_store_word_only_kernel);

pub fn generate_witness_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    trace: &UnrolledMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    let stride = generic_lookup_tables.stride();
    assert_eq!(memory.stride(), stride);
    assert_eq!(witness.stride(), stride);
    assert_eq!(scratch.stride(), stride);
    assert_eq!(lookup_mapping.stride(), stride);
    assert!(stride < u32::MAX as usize);
    let stride = stride as u32;
    assert!(count < u32::MAX as usize);
    let count = count as u32;
    let trace = trace.into();
    let generic_lookup_tables = generic_lookup_tables.as_ptr();
    let memory = memory.as_ptr();
    let witness = witness.as_mut_ptr();
    let scratch = scratch.as_mut_ptr();
    let lookup_mapping = lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateWitnessUnrolledMemoryKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        lookup_mapping,
        stride,
        count,
    );
    let kernel = match circuit_type {
        UnrolledMemoryCircuitType::LoadStoreSubwordOnly => {
            ab_generate_witness_values_load_store_subword_only_kernel
        }
        UnrolledMemoryCircuitType::LoadStoreWordOnly => {
            ab_generate_witness_values_load_store_word_only_kernel
        }
    };
    GenerateWitnessUnrolledMemoryKernelFunction(kernel).launch(&config, &args)
}

cuda_kernel!(GenerateWitnessUnrolledNonMemoryKernel,
    generate_witness_unrolled_non_memory_kernel,
    trace: UnrolledNonMemoryTraceRaw,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    scratch: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_unrolled_non_memory_kernel!(
    ab_generate_witness_values_add_sub_lui_auipc_mop_kernel
);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_jump_branch_slt_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_mul_div_unsigned_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_shift_binary_kernel);

pub fn generate_witness_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    trace: &UnrolledNonMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    let stride = generic_lookup_tables.stride();
    assert_eq!(memory.stride(), stride);
    assert_eq!(witness.stride(), stride);
    assert_eq!(scratch.stride(), stride);
    assert_eq!(lookup_mapping.stride(), stride);
    assert!(stride < u32::MAX as usize);
    let stride = stride as u32;
    assert!(count < u32::MAX as usize);
    let count = count as u32;
    let trace = trace.into();
    let generic_lookup_tables = generic_lookup_tables.as_ptr();
    let memory = memory.as_ptr();
    let witness = witness.as_mut_ptr();
    let scratch = scratch.as_mut_ptr();
    let lookup_mapping = lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateWitnessUnrolledNonMemoryKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        lookup_mapping,
        stride,
        count,
    );
    let kernel = match circuit_type {
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop => {
            ab_generate_witness_values_add_sub_lui_auipc_mop_kernel
        }
        UnrolledNonMemoryCircuitType::JumpBranchSlt => {
            ab_generate_witness_values_jump_branch_slt_kernel
        }
        UnrolledNonMemoryCircuitType::MulDivUnsigned => {
            ab_generate_witness_values_mul_div_unsigned_kernel
        }
        UnrolledNonMemoryCircuitType::ShiftBinary => ab_generate_witness_values_shift_binary_kernel,
    };
    GenerateWitnessUnrolledNonMemoryKernelFunction(kernel).launch(&config, &args)
}

cuda_kernel!(GenerateWitnessUnrolledUnifiedKernel,
    generate_witness_unrolled_unified_kernel,
    trace: UnrolledUnifiedTraceRaw,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    scratch: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_unrolled_unified_kernel!(
    ab_generate_witness_values_unified_reduced_machine_kernel
);

pub fn generate_witness_values_unrolled_unified(
    trace: &UnrolledUnifiedTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledCircuitType::Unified.get_domain_size();
    let stride = generic_lookup_tables.stride();
    assert_eq!(memory.stride(), stride);
    assert_eq!(witness.stride(), stride);
    assert_eq!(scratch.stride(), stride);
    assert_eq!(lookup_mapping.stride(), stride);
    assert!(stride < u32::MAX as usize);
    let stride = stride as u32;
    assert!(count < u32::MAX as usize);
    let count = count as u32;
    let trace: UnrolledUnifiedTraceRaw = trace.into();
    let generic_lookup_tables = generic_lookup_tables.as_ptr();
    let memory = memory.as_ptr();
    let witness = witness.as_mut_ptr();
    let scratch = scratch.as_mut_ptr();
    let lookup_mapping = lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateWitnessUnrolledUnifiedKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        lookup_mapping,
        stride,
        count,
    );
    GenerateWitnessUnrolledUnifiedKernelFunction(
        ab_generate_witness_values_unified_reduced_machine_kernel,
    )
    .launch(&config, &args)
}

#[allow(clippy::too_many_arguments)]
pub fn generate_fused_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    circuit: &GKRCircuitArtifact<BF>,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    generic_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    range_check_16_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_timestamp_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    assert_eq!(circuit.trace_len, count);
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), circuit.memory_layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), circuit.witness_layout.total_width);
    assert_eq!(scratch.stride(), count);
    assert_eq!(scratch.cols(), circuit.scratch_space_size);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(generic_lookup_mapping.cols(), circuit.generic_lookups.len());
    assert_eq!(
        decoder_lookup_mapping.len(),
        usize::from(circuit.has_decoder_lookup) * count
    );
    assert_eq!(range_check_16_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_16_lookup_mapping.cols(),
        circuit.range_check_16_lookup_expressions.len()
    );
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_timestamp_lookup_mapping.cols(),
        circuit.timestamp_range_check_lookup_expressions.len()
    );
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = UnrolledMemoryLayout::from_parts(
        &circuit.memory_layout,
        circuit.offset_for_decoder_table as u32,
    );
    let aux_layout_data = AuxLayoutData::from(&circuit.aux_layout_data);
    let oracle = UnrolledMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let range_check_16_lookup_expressions =
        LookupExpressions::from(&circuit.range_check_16_lookup_expressions);
    let range_check_timestamp_lookup_expressions =
        LookupExpressions::from(&circuit.timestamp_range_check_lookup_expressions);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateFusedUnrolledMemoryKernelArguments::new(
        layout,
        aux_layout_data,
        oracle,
        generic_lookup_tables.as_ptr(),
        memory.as_mut_ptr(),
        witness.as_mut_ptr(),
        scratch.as_mut_ptr(),
        generic_lookup_mapping.as_mut_ptr(),
        decoder_lookup_mapping.as_mut_ptr(),
        range_check_16_lookup_expressions,
        range_check_16_lookup_mapping.as_mut_ptr(),
        range_check_timestamp_lookup_expressions,
        range_check_timestamp_lookup_mapping.as_mut_ptr(),
        count,
        count,
    );
    let kernel = match circuit_type {
        UnrolledMemoryCircuitType::LoadStoreSubwordOnly => {
            ab_generate_fused_load_store_subword_only_kernel
        }
        UnrolledMemoryCircuitType::LoadStoreWordOnly => {
            ab_generate_fused_load_store_word_only_kernel
        }
    };
    GenerateFusedUnrolledMemoryKernelFunction(kernel).launch(&config, &args)
}

#[allow(clippy::too_many_arguments)]
pub fn generate_fused_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    circuit: &GKRCircuitArtifact<BF>,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledNonMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    generic_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    range_check_16_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_timestamp_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    assert_eq!(circuit.trace_len, count);
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), circuit.memory_layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), circuit.witness_layout.total_width);
    assert_eq!(scratch.stride(), count);
    assert_eq!(scratch.cols(), circuit.scratch_space_size);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(generic_lookup_mapping.cols(), circuit.generic_lookups.len());
    assert_eq!(
        decoder_lookup_mapping.len(),
        usize::from(circuit.has_decoder_lookup) * count
    );
    assert_eq!(range_check_16_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_16_lookup_mapping.cols(),
        circuit.range_check_16_lookup_expressions.len()
    );
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_timestamp_lookup_mapping.cols(),
        circuit.timestamp_range_check_lookup_expressions.len()
    );
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = UnrolledMemoryLayout::from_parts(
        &circuit.memory_layout,
        circuit.offset_for_decoder_table as u32,
    );
    let aux_layout_data = AuxLayoutData::from(&circuit.aux_layout_data);
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: circuit_type.get_default_pc_value_in_padding(),
    };
    let range_check_16_lookup_expressions =
        LookupExpressions::from(&circuit.range_check_16_lookup_expressions);
    let range_check_timestamp_lookup_expressions =
        LookupExpressions::from(&circuit.timestamp_range_check_lookup_expressions);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateFusedUnrolledNonMemoryKernelArguments::new(
        layout,
        aux_layout_data,
        oracle,
        generic_lookup_tables.as_ptr(),
        memory.as_mut_ptr(),
        witness.as_mut_ptr(),
        scratch.as_mut_ptr(),
        generic_lookup_mapping.as_mut_ptr(),
        decoder_lookup_mapping.as_mut_ptr(),
        range_check_16_lookup_expressions,
        range_check_16_lookup_mapping.as_mut_ptr(),
        range_check_timestamp_lookup_expressions,
        range_check_timestamp_lookup_mapping.as_mut_ptr(),
        count,
        count,
    );
    let kernel = match circuit_type {
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop => {
            ab_generate_fused_add_sub_lui_auipc_mop_kernel
        }
        UnrolledNonMemoryCircuitType::JumpBranchSlt => ab_generate_fused_jump_branch_slt_kernel,
        UnrolledNonMemoryCircuitType::MulDivUnsigned => ab_generate_fused_mul_div_unsigned_kernel,
        UnrolledNonMemoryCircuitType::ShiftBinary => ab_generate_fused_shift_binary_kernel,
    };
    GenerateFusedUnrolledNonMemoryKernelFunction(kernel).launch(&config, &args)
}

#[allow(clippy::too_many_arguments)]
pub fn generate_fused_values_unrolled_unified(
    circuit: &GKRCircuitArtifact<BF>,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledUnifiedTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    generic_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    range_check_16_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_timestamp_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledCircuitType::Unified.get_domain_size();
    assert_eq!(circuit.trace_len, count);
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), circuit.memory_layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), circuit.witness_layout.total_width);
    assert_eq!(scratch.stride(), count);
    assert_eq!(scratch.cols(), circuit.scratch_space_size);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(generic_lookup_mapping.cols(), circuit.generic_lookups.len());
    assert_eq!(
        decoder_lookup_mapping.len(),
        usize::from(circuit.has_decoder_lookup) * count
    );
    assert_eq!(range_check_16_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_16_lookup_mapping.cols(),
        circuit.range_check_16_lookup_expressions.len()
    );
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_timestamp_lookup_mapping.cols(),
        circuit.timestamp_range_check_lookup_expressions.len()
    );
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = UnrolledMemoryLayout::from_parts(
        &circuit.memory_layout,
        circuit.offset_for_decoder_table as u32,
    );
    let aux_layout_data = AuxLayoutData::from(&circuit.aux_layout_data);
    let oracle = UnrolledUnifiedOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let range_check_16_lookup_expressions =
        LookupExpressions::from(&circuit.range_check_16_lookup_expressions);
    let range_check_timestamp_lookup_expressions =
        LookupExpressions::from(&circuit.timestamp_range_check_lookup_expressions);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateFusedUnrolledUnifiedKernelArguments::new(
        layout,
        aux_layout_data,
        oracle,
        generic_lookup_tables.as_ptr(),
        memory.as_mut_ptr(),
        witness.as_mut_ptr(),
        scratch.as_mut_ptr(),
        generic_lookup_mapping.as_mut_ptr(),
        decoder_lookup_mapping.as_mut_ptr(),
        range_check_16_lookup_expressions,
        range_check_16_lookup_mapping.as_mut_ptr(),
        range_check_timestamp_lookup_expressions,
        range_check_timestamp_lookup_mapping.as_mut_ptr(),
        count,
        count,
    );
    GenerateFusedUnrolledUnifiedKernelFunction::default().launch(&config, &args)
}
