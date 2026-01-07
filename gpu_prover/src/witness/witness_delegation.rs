use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use super::BF;
use crate::circuit_type::DelegationCircuitType;
use crate::device_structures::{DeviceMatrixImpl, DeviceMatrixMutImpl};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

cuda_kernel_signature_arguments_and_function!(
    GenerateWitnessValues<T>,
    trace: DelegationTraceRaw<T>,
    generic_lookup_tables: *const BF,
    memory: *const BF,
    witness: *mut BF,
    lookup_mapping: *mut u32,
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
                    lookup_mapping: *mut u32,
                    stride: u32,
                    count: u32,
                )
            );
        }
    };
}

pub(crate) trait GenerateWitnessDelegation: Sized {
    const CIRCUIT_TYPE: DelegationCircuitType;
    const SIGNATURE: GenerateWitnessValuesSignature<Self>;
}

macro_rules! generate_witness_values_impl {
    ($name:ident, $witness_type:ty, $circuit_type:ty) => {
        paste! {
            generate_witness_values_kernel!($name, $witness_type);
            impl GenerateWitnessDelegation for $witness_type {
                const CIRCUIT_TYPE: DelegationCircuitType = $circuit_type;
                const SIGNATURE: GenerateWitnessValuesSignature<Self> = [<ab_generate_witness_values_ $name _kernel>];
            }
        }
    };
}

generate_witness_values_impl!(
    bigint_with_control,
    BigintDelegationWitness,
    DelegationCircuitType::BigIntWithControl
);

generate_witness_values_impl!(
    blake2_with_compression,
    Blake2sRoundFunctionDelegationWitness,
    DelegationCircuitType::Blake2WithCompression
);

generate_witness_values_impl!(
    keccak_special5,
    KeccakSpecial5DelegationWitness,
    DelegationCircuitType::KeccakSpecial5
);

pub(crate) fn generate_witness_values_delegation<T: GenerateWitnessDelegation>(
    trace: &DelegationTraceDevice<T>,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = T::CIRCUIT_TYPE.get_num_cycles();
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
    let args = GenerateWitnessValuesArguments::new(
        trace,
        generic_lookup_tables,
        memory,
        witness,
        lookup_mapping,
        stride,
        count,
    );
    GenerateWitnessValuesFunction(T::SIGNATURE).launch(&config, &args)
}
