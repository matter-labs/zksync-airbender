use super::BF;
use crate::circuit_type::{
    UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::device_structures::{DeviceMatrixImpl, DeviceMatrixMutImpl};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::witness::trace_unrolled::{
    UnrolledMemoryTraceDevice, UnrolledMemoryTraceRaw, UnrolledNonMemoryTraceDevice,
    UnrolledNonMemoryTraceRaw, UnrolledUnifiedTraceDevice, UnrolledUnifiedTraceRaw,
};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

cuda_kernel!(GenerateWitnessUnrolledMemoryKernel,
    generate_witness_unrolled_memory_kernel,
    trace: UnrolledMemoryTraceRaw,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_unrolled_memory_kernel!(ab_generate_witness_values_load_store_subword_only_kernel);
generate_witness_unrolled_memory_kernel!(ab_generate_witness_values_load_store_word_only_kernel);

pub(crate) fn generate_witness_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    trace: &UnrolledMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_num_cycles();
    let stride = generic_lookup_tables.stride();
    assert_eq!(memory.stride(), stride);
    assert_eq!(witness.stride(), stride);
    assert_eq!(lookup_mapping.stride(), stride);
    assert!(stride < u32::MAX as usize);
    let stride = stride as u32;
    assert!(count < u32::MAX as usize);
    let count = count as u32;
    let trace = trace.into();
    let generic_lookup_tables = generic_lookup_tables.as_ptr();
    let memory = memory.as_ptr();
    let witness = witness.as_mut_ptr();
    let lookup_mapping = lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateWitnessUnrolledMemoryKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
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
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_unrolled_non_memory_kernel!(
    ab_generate_witness_values_add_sub_lui_auipc_mop_kernel
);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_jump_branch_slt_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_mul_div_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_mul_div_unsigned_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_witness_values_shift_binary_csr_kernel);

pub(crate) fn generate_witness_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    trace: &UnrolledNonMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_num_cycles();
    let stride = generic_lookup_tables.stride();
    assert_eq!(memory.stride(), stride);
    assert_eq!(witness.stride(), stride);
    assert_eq!(lookup_mapping.stride(), stride);
    assert!(stride < u32::MAX as usize);
    let stride = stride as u32;
    assert!(count < u32::MAX as usize);
    let count = count as u32;
    let trace = trace.into();
    let generic_lookup_tables = generic_lookup_tables.as_ptr();
    let memory = memory.as_ptr();
    let witness = witness.as_mut_ptr();
    let lookup_mapping = lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateWitnessUnrolledNonMemoryKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
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
        UnrolledNonMemoryCircuitType::MulDiv => ab_generate_witness_values_mul_div_kernel,
        UnrolledNonMemoryCircuitType::MulDivUnsigned => {
            ab_generate_witness_values_mul_div_unsigned_kernel
        }
        UnrolledNonMemoryCircuitType::ShiftBinaryCsr => {
            ab_generate_witness_values_shift_binary_csr_kernel
        }
    };
    GenerateWitnessUnrolledNonMemoryKernelFunction(kernel).launch(&config, &args)
}

cuda_kernel!(GenerateWitnessUnrolledUnifiedKernel,
    ab_generate_witness_values_unified_reduced_machine_kernel(
        trace: UnrolledUnifiedTraceRaw,
        generic_lookup_tables: *const BF,
        memory: *const BF,
        witness: *mut BF,
        lookup_mapping: *mut u32,
        stride: u32,
        count: u32,
    )
);

pub(crate) fn generate_witness_values_unrolled_unified(
    trace: &UnrolledUnifiedTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledCircuitType::Unified.get_num_cycles();
    let stride = generic_lookup_tables.stride();
    assert_eq!(memory.stride(), stride);
    assert_eq!(witness.stride(), stride);
    assert_eq!(lookup_mapping.stride(), stride);
    assert!(stride < u32::MAX as usize);
    let stride = stride as u32;
    assert!(count < u32::MAX as usize);
    let count = count as u32;
    let trace = trace.into();
    let generic_lookup_tables = generic_lookup_tables.as_ptr();
    let memory = memory.as_ptr();
    let witness = witness.as_mut_ptr();
    let lookup_mapping = lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateWitnessUnrolledUnifiedKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        lookup_mapping,
        stride,
        count,
    );
    GenerateWitnessUnrolledUnifiedKernelFunction::default().launch(&config, &args)
}
