use super::memory_delegation::{DelegationAuxLayoutData, DelegationMemoryLayout};
use super::multiplicities::LookupExpressions;
use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use crate::upstream::GKRCircuitArtifact;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::device_structures::{DeviceMatrixImpl, DeviceMatrixMutImpl};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

cuda_kernel_signature_arguments_and_function!(
    GenerateWitnessValues<T>,
    trace: DelegationTraceRaw<T>,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    scratch_storage: *mut BF,
    lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GenerateFusedDelegationValues<T>,
    layout: DelegationMemoryLayout,
    aux_layout_data: DelegationAuxLayoutData,
    trace: DelegationTraceRaw<T>,
    generic_lookup_tables: *const BF,
    memory: *mut BF,
    witness: *mut BF,
    scratch_storage: *mut BF,
    generic_lookup_mapping: *mut u32,
    range_check_16_lookup_expressions: LookupExpressions,
    range_check_16_lookup_mapping: *mut u32,
    range_check_timestamp_lookup_expressions: LookupExpressions,
    range_check_timestamp_lookup_mapping: *mut u32,
    stride: u32,
    count: u32,
);

macro_rules! generate_witness_values_kernel {
    ($name:ident, $type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_generate_witness_values_ $name _kernel>](
                    trace: DelegationTraceRaw<$type>,
                    generic_lookup_tables: *const BF,
                    memory: *const BF,
                    witness: *mut BF,
                    scratch_storage: *mut BF,
                    lookup_mapping: *mut u32,
                    stride: u32,
                    count: u32,
                )
            );
        }
    };
}

macro_rules! generate_fused_delegation_values_kernel {
    ($name:ident, $type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_generate_fused_ $name _kernel>](
                    layout: DelegationMemoryLayout,
                    aux_layout_data: DelegationAuxLayoutData,
                    trace: DelegationTraceRaw<$type>,
                    generic_lookup_tables: *const BF,
                    memory: *mut BF,
                    witness: *mut BF,
                    scratch_storage: *mut BF,
                    generic_lookup_mapping: *mut u32,
                    range_check_16_lookup_expressions: LookupExpressions,
                    range_check_16_lookup_mapping: *mut u32,
                    range_check_timestamp_lookup_expressions: LookupExpressions,
                    range_check_timestamp_lookup_mapping: *mut u32,
                    stride: u32,
                    count: u32,
                )
            );
        }
    };
}

pub(crate) trait GenerateWitnessDelegation: Sized {
    const SIGNATURE: GenerateWitnessValuesSignature<Self>;
}

pub(crate) trait GenerateFusedDelegation: Sized {
    const SIGNATURE: GenerateFusedDelegationValuesSignature<Self>;
}

macro_rules! generate_witness_values_impl {
    ($name:ident, $witness_type:ty) => {
        paste! {
            generate_witness_values_kernel!($name, $witness_type);
            generate_fused_delegation_values_kernel!($name, $witness_type);
            impl GenerateWitnessDelegation for $witness_type {
                const SIGNATURE: GenerateWitnessValuesSignature<Self> = [<ab_generate_witness_values_ $name _kernel>];
            }
            impl GenerateFusedDelegation for $witness_type {
                const SIGNATURE: GenerateFusedDelegationValuesSignature<Self> = [<ab_generate_fused_ $name _kernel>];
            }
        }
    };
}

generate_witness_values_impl!(bigint_with_control, BigintDelegationWitness);

generate_witness_values_impl!(
    blake2_with_compression,
    Blake2sRoundFunctionDelegationWitness
);

generate_witness_values_impl!(blake2_g_function, Blake2sGFunctionDelegationWitness);

generate_witness_values_impl!(keccak_special5, KeccakSpecial5DelegationWitness);

// `private_bounds`: `GenerateWitnessDelegation` is a deliberately sealed
// dispatch trait, mirroring `GenerateMemoryDelegation` in
// `memory_delegation.rs` — see the justification there.
#[allow(private_bounds)]
pub fn generate_witness_values_delegation<T: GenerateWitnessDelegation>(
    trace: &DelegationTraceDevice<T>,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let stride = generic_lookup_tables.stride();
    let count = memory.stride();
    assert_eq!(count, stride);
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
    let args = GenerateWitnessValuesArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        lookup_mapping,
        stride,
        count,
    );
    GenerateWitnessValuesFunction(T::SIGNATURE).launch(&config, &args)
}

#[allow(private_bounds, clippy::too_many_arguments)]
pub fn generate_fused_values_delegation<T: GenerateFusedDelegation>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    trace: &DelegationTraceDevice<T>,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    generic_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_16_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_timestamp_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = compiled_circuit.trace_len;
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), compiled_circuit.memory_layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), compiled_circuit.witness_layout.total_width);
    assert_eq!(scratch.stride(), count);
    assert_eq!(scratch.cols(), compiled_circuit.scratch_space_size);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(
        generic_lookup_mapping.cols(),
        compiled_circuit.generic_lookups.len()
    );
    assert_eq!(range_check_16_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_16_lookup_mapping.cols(),
        compiled_circuit.range_check_16_lookup_expressions.len()
    );
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), count);
    assert_eq!(
        range_check_timestamp_lookup_mapping.cols(),
        compiled_circuit
            .timestamp_range_check_lookup_expressions
            .len()
    );
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = DelegationMemoryLayout::from(&compiled_circuit.memory_layout);
    let aux_layout_data = DelegationAuxLayoutData::from(&compiled_circuit.aux_layout_data);
    let trace = trace.into();
    let range_check_16_lookup_expressions =
        LookupExpressions::from(&compiled_circuit.range_check_16_lookup_expressions);
    let range_check_timestamp_lookup_expressions =
        LookupExpressions::from(&compiled_circuit.timestamp_range_check_lookup_expressions);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateFusedDelegationValuesArguments::new(
        layout,
        aux_layout_data,
        trace,
        generic_lookup_tables.as_ptr(),
        memory.as_mut_ptr(),
        witness.as_mut_ptr(),
        scratch.as_mut_ptr(),
        generic_lookup_mapping.as_mut_ptr(),
        range_check_16_lookup_expressions,
        range_check_16_lookup_mapping.as_mut_ptr(),
        range_check_timestamp_lookup_expressions,
        range_check_timestamp_lookup_mapping.as_mut_ptr(),
        count,
        count,
    );
    GenerateFusedDelegationValuesFunction(T::SIGNATURE).launch(&config, &args)
}
