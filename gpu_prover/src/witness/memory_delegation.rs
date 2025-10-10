use super::layout::DelegationProcessingLayout;
use super::ram_access::{
    RegisterAndIndirectAccessDescription, RegisterAndIndirectAccessTimestampComparisonAuxVars,
};
use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use super::BF;
use crate::circuit_type::DelegationCircuitType;
use crate::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use cs::definitions::MemorySubtree;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use std::ops::Deref;

const MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterAndIndirectAccessDescriptions {
    pub count: u32,
    pub descriptions:
        [RegisterAndIndirectAccessDescription; MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT],
}

impl<T: Deref<Target = [cs::definitions::RegisterAndIndirectAccessDescription]>> From<&T>
    for RegisterAndIndirectAccessDescriptions
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT);
        let count = len as u32;
        let mut descriptions = [RegisterAndIndirectAccessDescription::default();
            MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT];
        for (src, dst) in value.iter().zip(descriptions.iter_mut()) {
            *dst = src.clone().into();
        }
        Self {
            count,
            descriptions,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct DelegationMemorySubtree {
    delegation_processor_layout: DelegationProcessingLayout,
    register_and_indirect_access_descriptions: RegisterAndIndirectAccessDescriptions,
}

impl From<&MemorySubtree> for DelegationMemorySubtree {
    fn from(value: &MemorySubtree) -> Self {
        assert!(value.shuffle_ram_inits_and_teardowns.is_empty());
        assert!(value.shuffle_ram_access_sets.is_empty());
        assert!(value.delegation_request_layout.is_none());
        assert!(value.batched_ram_accesses.is_empty());
        let delegation_processor_layout = value.delegation_processor_layout.unwrap().into();
        let register_and_indirect_access_descriptions = {
            let count = value.register_and_indirect_accesses.len() as u32;
            assert!(count <= MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT as u32);
            let mut descriptions = [RegisterAndIndirectAccessDescription::default();
                MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT];
            for (i, value) in value.register_and_indirect_accesses.iter().enumerate() {
                descriptions[i] = value.clone().into();
            }
            RegisterAndIndirectAccessDescriptions {
                count,
                descriptions,
            }
        };
        Self {
            delegation_processor_layout,
            register_and_indirect_access_descriptions,
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    GenerateMemoryValues<T>,
    subtree: DelegationMemorySubtree,
    trace: DelegationTraceRaw<T>,
    memory: MutPtrAndStride<BF>,
    count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GenerateMemoryAndWitnessValues<T>,
        subtree: DelegationMemorySubtree,
        aux_vars: RegisterAndIndirectAccessTimestampComparisonAuxVars,
        trace: DelegationTraceRaw<T>,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        count: u32,
);

macro_rules! generate_delegation_kernels {
    ($name:ident, $type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_generate_memory_values_ $name _kernel>](
                    subtree: DelegationMemorySubtree,
                    trace: DelegationTraceRaw<$type>,
                    memory: MutPtrAndStride<BF>,
                    count: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_generate_memory_and_witness_values_ $name _kernel>](
                    subtree: DelegationMemorySubtree,
                    aux_vars: RegisterAndIndirectAccessTimestampComparisonAuxVars,
                    trace: DelegationTraceRaw<$type>,
                    memory: MutPtrAndStride<BF>,
                    witness: MutPtrAndStride<BF>,
                    count: u32,
                )
            );
        }
    };
}

pub(crate) trait GenerateMemoryDelegation: Sized {
    const CIRCUIT_TYPE: DelegationCircuitType;
    const MEMORY_SIGNATURE: GenerateMemoryValuesSignature<Self>;
    const MEMORY_AND_WITNESS_SIGNATURE: GenerateMemoryAndWitnessValuesSignature<Self>;
}

macro_rules! generate_memory_values_impl {
    ($name:ident, $witness_type:ty, $circuit_type:ty) => {
        paste! {
            generate_delegation_kernels!($name, $witness_type);
            impl GenerateMemoryDelegation for $witness_type {
                const CIRCUIT_TYPE: DelegationCircuitType = $circuit_type;
                const MEMORY_SIGNATURE: GenerateMemoryValuesSignature<Self> = [<ab_generate_memory_values_ $name _kernel>];
                const MEMORY_AND_WITNESS_SIGNATURE: GenerateMemoryAndWitnessValuesSignature<Self> = [<ab_generate_memory_and_witness_values_ $name _kernel>];
            }
        }
    };
}

generate_memory_values_impl!(
    bigint_with_control,
    BigintDelegationWitness,
    DelegationCircuitType::BigIntWithControl
);

generate_memory_values_impl!(
    blake2_with_compression,
    Blake2sRoundFunctionDelegationWitness,
    DelegationCircuitType::Blake2WithCompression
);

generate_memory_values_impl!(
    keccak_special5,
    KeccakSpecial5DelegationWitness,
    DelegationCircuitType::KeccakSpecial5
);

pub(crate) fn generate_memory_values_delegation<T: GenerateMemoryDelegation>(
    subtree: &MemorySubtree,
    trace: &DelegationTraceDevice<T>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = T::CIRCUIT_TYPE.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesArguments::new(subtree, trace, memory, count);
    GenerateMemoryValuesFunction(T::MEMORY_SIGNATURE).launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_delegation<T: GenerateMemoryDelegation>(
    subtree: &MemorySubtree,
    aux_vars: &cs::definitions::RegisterAndIndirectAccessTimestampComparisonAuxVars,
    trace: &DelegationTraceDevice<T>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = T::CIRCUIT_TYPE.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert_eq!(witness.stride(), count + 1);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let aux_vars = aux_vars.clone().into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesArguments::new(
        subtree, aux_vars, trace, memory, witness, count,
    );
    GenerateMemoryAndWitnessValuesFunction(T::MEMORY_AND_WITNESS_SIGNATURE).launch(&config, &args)
}
