use super::layout::DelegationProcessingLayout;
use super::ram_access::{RamAuxComparisonSet, RamQuery};
use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use crate::primitives::circuit_type::DelegationCircuitType;
use crate::primitives::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use crate::primitives::field::BF;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use cs::definitions::gkr::GKRMemoryLayout;
use cs::gkr_compiler::{GKRAuxLayoutData, GKRCircuitArtifact};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

const MAX_DELEGATION_RAM_ACCESS_SETS_COUNT: usize = 64;
const MAX_DELEGATION_VARIABLE_OFFSETS_COUNT: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct DelegationMemoryLayout {
    total_width: u32,
    delegation_processor_layout: DelegationProcessingLayout,
    indirect_access_variable_offsets_count: u32,
    indirect_access_variable_offsets: [u16; MAX_DELEGATION_VARIABLE_OFFSETS_COUNT],
    ram_access_sets_count: u32,
    ram_access_sets: [RamQuery; MAX_DELEGATION_RAM_ACCESS_SETS_COUNT],
}

impl Default for DelegationMemoryLayout {
    fn default() -> Self {
        Self {
            total_width: 0,
            delegation_processor_layout: DelegationProcessingLayout::default(),
            indirect_access_variable_offsets_count: 0,
            indirect_access_variable_offsets: [0u16; MAX_DELEGATION_VARIABLE_OFFSETS_COUNT],
            ram_access_sets_count: 0,
            ram_access_sets: [RamQuery::default(); MAX_DELEGATION_RAM_ACCESS_SETS_COUNT],
        }
    }
}

impl From<&GKRMemoryLayout> for DelegationMemoryLayout {
    fn from(value: &GKRMemoryLayout) -> Self {
        assert!(value.total_width <= u32::MAX as usize);
        let delegation_processor_layout = value.into();

        let variable_offsets_len = value.indirect_access_variable_offsets.len();
        assert!(
            variable_offsets_len <= MAX_DELEGATION_VARIABLE_OFFSETS_COUNT,
            "delegation layout uses {} indirect access variable offsets, but the GPU ABI supports at most {}",
            variable_offsets_len,
            MAX_DELEGATION_VARIABLE_OFFSETS_COUNT,
        );
        let mut indirect_access_variable_offsets = [0u16; MAX_DELEGATION_VARIABLE_OFFSETS_COUNT];
        for (&src, dst) in value
            .indirect_access_variable_offsets
            .iter()
            .zip(indirect_access_variable_offsets.iter_mut())
        {
            assert!(src <= u16::MAX as usize);
            *dst = src as u16;
        }

        let ram_access_sets_len = value.ram_access_sets.len();
        assert!(
            ram_access_sets_len <= MAX_DELEGATION_RAM_ACCESS_SETS_COUNT,
            "delegation layout uses {} RAM accesses, but the GPU ABI supports at most {}",
            ram_access_sets_len,
            MAX_DELEGATION_RAM_ACCESS_SETS_COUNT,
        );
        let mut ram_access_sets = [RamQuery::default(); MAX_DELEGATION_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in value.ram_access_sets.iter().zip(ram_access_sets.iter_mut()) {
            *dst = src.into();
        }

        Self {
            total_width: value.total_width as u32,
            delegation_processor_layout,
            indirect_access_variable_offsets_count: variable_offsets_len as u32,
            indirect_access_variable_offsets,
            ram_access_sets_count: ram_access_sets_len as u32,
            ram_access_sets,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct DelegationAuxLayoutData {
    pub shuffle_ram_timestamp_comparison_aux_vars:
        [RamAuxComparisonSet; MAX_DELEGATION_RAM_ACCESS_SETS_COUNT],
}

impl Default for DelegationAuxLayoutData {
    fn default() -> Self {
        Self {
            shuffle_ram_timestamp_comparison_aux_vars: [RamAuxComparisonSet::default();
                MAX_DELEGATION_RAM_ACCESS_SETS_COUNT],
        }
    }
}

impl From<&GKRAuxLayoutData> for DelegationAuxLayoutData {
    fn from(value: &GKRAuxLayoutData) -> Self {
        let len = value.shuffle_ram_timestamp_comparison_aux_vars.len();
        assert!(
            len <= MAX_DELEGATION_RAM_ACCESS_SETS_COUNT,
            "delegation layout uses {} timestamp comparison aux slots, but the GPU ABI supports at most {}",
            len,
            MAX_DELEGATION_RAM_ACCESS_SETS_COUNT,
        );
        let mut shuffle_ram_timestamp_comparison_aux_vars =
            [RamAuxComparisonSet::default(); MAX_DELEGATION_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in value
            .shuffle_ram_timestamp_comparison_aux_vars
            .iter()
            .zip(shuffle_ram_timestamp_comparison_aux_vars.iter_mut())
        {
            *dst = src.into();
        }

        Self {
            shuffle_ram_timestamp_comparison_aux_vars,
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    GenerateMemoryValues<T>,
    layout: DelegationMemoryLayout,
    trace: DelegationTraceRaw<T>,
    memory: MutPtrAndStride<BF>,
    count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GenerateMemoryAndWitnessValues<T>,
    layout: DelegationMemoryLayout,
    aux_layout_data: DelegationAuxLayoutData,
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
                    layout: DelegationMemoryLayout,
                    trace: DelegationTraceRaw<$type>,
                    memory: MutPtrAndStride<BF>,
                    count: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_generate_memory_and_witness_values_ $name _kernel>](
                    layout: DelegationMemoryLayout,
                    aux_layout_data: DelegationAuxLayoutData,
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
    compiled_circuit: &GKRCircuitArtifact<BF>,
    trace: &DelegationTraceDevice<T>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = compiled_circuit.trace_len;
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), compiled_circuit.memory_layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = (&compiled_circuit.memory_layout).into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesArguments::new(layout, trace, memory, count);
    GenerateMemoryValuesFunction(T::MEMORY_SIGNATURE).launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_delegation<T: GenerateMemoryDelegation>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    trace: &DelegationTraceDevice<T>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = compiled_circuit.trace_len;
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), compiled_circuit.memory_layout.total_width);
    assert_eq!(witness.stride(), count);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = (&compiled_circuit.memory_layout).into();
    let aux_layout_data = (&compiled_circuit.aux_layout_data).into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesArguments::new(
        layout,
        aux_layout_data,
        trace,
        memory,
        witness,
        count,
    );
    GenerateMemoryAndWitnessValuesFunction(T::MEMORY_AND_WITNESS_SIGNATURE).launch(&config, &args)
}
