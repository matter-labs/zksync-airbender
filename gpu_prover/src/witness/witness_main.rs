use super::trace_main::{MainTraceDevice, MainTraceRaw};
use super::BF;
use crate::circuit_type::MainCircuitType;
use crate::device_structures::{
    DeviceMatrix, DeviceMatrixChunkImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use crate::prover::context::ProverContext;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use era_cudart::stream::CudaStream;

cuda_kernel!(GenerateWitnessMainKernel,
    generate_witness_main_kernel,
    trace: MainTraceRaw,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

generate_witness_main_kernel!(generate_final_reduced_risc_v_machine_witness_kernel);
generate_witness_main_kernel!(generate_machine_without_signed_mul_div_witness_kernel);
generate_witness_main_kernel!(generate_reduced_risc_v_machine_witness_kernel);
generate_witness_main_kernel!(generate_risc_v_cycles_witness_kernel);

pub fn generate_witness_values_main<C: ProverContext>(
    circuit_type: MainCircuitType,
    trace: &MainTraceDevice<C>,
    generic_lookup_tables: &DeviceMatrix<BF>,
    memory: &DeviceMatrix<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    lookup_mapping: &mut DeviceMatrixMut<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycle_data.len();
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
    let args = GenerateWitnessMainKernelArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        lookup_mapping,
        stride,
        count,
    );
    let kernel = match circuit_type {
        MainCircuitType::FinalReducedRiscVMachine => {
            generate_final_reduced_risc_v_machine_witness_kernel
        }
        MainCircuitType::MachineWithoutSignedMulDiv => {
            generate_machine_without_signed_mul_div_witness_kernel
        }
        MainCircuitType::ReducedRiscVMachine => generate_reduced_risc_v_machine_witness_kernel,
        MainCircuitType::RiscVCycles => generate_risc_v_cycles_witness_kernel,
    };
    GenerateWitnessMainKernelFunction(kernel).launch(&config, &args)
}
