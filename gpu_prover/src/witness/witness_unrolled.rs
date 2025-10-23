use super::BF;
use crate::circuit_type::{UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType};
use crate::device_structures::{
    DeviceMatrix, DeviceMatrixChunkImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::witness::trace_unrolled::{
    UnrolledMemoryTraceDevice, UnrolledMemoryTraceRaw, UnrolledNonMemoryTraceDevice,
    UnrolledNonMemoryTraceRaw,
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

generate_witness_unrolled_memory_kernel!(ab_generate_load_store_subword_only_witness_kernel);
generate_witness_unrolled_memory_kernel!(ab_generate_load_store_word_only_witness_kernel);

pub fn generate_witness_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    trace: &UnrolledMemoryTraceDevice,
    generic_lookup_tables: &DeviceMatrix<BF>,
    memory: &DeviceMatrix<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    lookup_mapping: &mut DeviceMatrixMut<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycles_count;
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
            ab_generate_load_store_subword_only_witness_kernel
        }
        UnrolledMemoryCircuitType::LoadStoreWordOnly => {
            ab_generate_load_store_word_only_witness_kernel
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

generate_witness_unrolled_non_memory_kernel!(ab_generate_add_sub_lui_auipc_mop_witness_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_jump_branch_slt_witness_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_mul_div_witness_kernel);
generate_witness_unrolled_non_memory_kernel!(ab_generate_mul_div_unsigned_witness_kernel);
generate_witness_unrolled_non_memory_kernel!(
    ab_generate_shift_binary_csr_all_delegations_witness_kernel
);
generate_witness_unrolled_non_memory_kernel!(
    ab_generate_shift_binary_csr_blake_only_delegation_witness_kernel
);

pub fn generate_witness_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    trace: &UnrolledNonMemoryTraceDevice,
    generic_lookup_tables: &DeviceMatrix<BF>,
    memory: &DeviceMatrix<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    lookup_mapping: &mut DeviceMatrixMut<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycles_count;
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
            ab_generate_add_sub_lui_auipc_mop_witness_kernel
        }
        UnrolledNonMemoryCircuitType::JumpBranchSlt => ab_generate_jump_branch_slt_witness_kernel,
        UnrolledNonMemoryCircuitType::MulDiv => ab_generate_mul_div_witness_kernel,
        UnrolledNonMemoryCircuitType::MulDivUnsigned => ab_generate_mul_div_unsigned_witness_kernel,
        UnrolledNonMemoryCircuitType::ShiftBinaryCsrAllDelegations => {
            ab_generate_shift_binary_csr_all_delegations_witness_kernel
        }
        UnrolledNonMemoryCircuitType::ShiftBinaryCsrBlakeOnlyDelegation => {
            ab_generate_shift_binary_csr_blake_only_delegation_witness_kernel
        }
    };
    GenerateWitnessUnrolledNonMemoryKernelFunction(kernel).launch(&config, &args)
}
