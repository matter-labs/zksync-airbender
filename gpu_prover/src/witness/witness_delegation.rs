use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use super::BF;
use crate::circuit_type::DelegationCircuitType;
use crate::device_structures::{
    DeviceMatrix, DeviceMatrixChunkImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use crate::prover::context::ProverContext;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

cuda_kernel!(GenerateWitnessDelegationKernel,
    generate_witness_delegation_kernel,
    trace: DelegationTraceRaw,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_delegation_kernel!(generate_bigint_with_control_witness_kernel);
generate_witness_delegation_kernel!(generate_blake2_with_compression_witness_kernel);

pub fn generate_witness_values_delegation<C: ProverContext>(
    circuit_type: DelegationCircuitType,
    trace: &DelegationTraceDevice<C>,
    generic_lookup_tables: &DeviceMatrix<BF>,
    memory: &DeviceMatrix<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    lookup_mapping: &mut DeviceMatrixMut<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.num_requests;
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
    let args = GenerateWitnessDelegationKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        lookup_mapping,
        stride,
        count,
    );
    let kernel = match circuit_type {
        DelegationCircuitType::BigIntWithControl => generate_bigint_with_control_witness_kernel,
        DelegationCircuitType::Blake2WithCompression => {
            generate_blake2_with_compression_witness_kernel
        }
    };
    GenerateWitnessDelegationKernelFunction(kernel).launch(&config, &args)
}
