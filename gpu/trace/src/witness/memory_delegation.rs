use super::circuit_type::DelegationCircuitType;
use super::layout::DelegationProcessingLayout;
use super::ram_access::RamQuery;
use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use gpu_core::primitives::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

use crate::upstream::{
    CSRamAuxComparisonSet, CSRelativeTimestampGroup, GKRAddress, GKRAuxLayoutData,
    GKRCircuitArtifact, GKRMemoryLayout,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_f1600::{
    KeccakChi5DelegationWitness, KeccakColumnParityDelegationWitness,
    KeccakThetaRhoDelegationWitness,
};
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

const MAX_DELEGATION_RAM_ACCESS_SETS_COUNT: usize = 64;
const MAX_DELEGATION_VARIABLE_OFFSETS_COUNT: usize = 16;
const MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUPS_COUNT: usize = 8;
const MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT: usize = 16;

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
#[derive(Clone, Copy, Default, Debug)]
struct RelativeTimestampGroup {
    borrow: u32,
    members_count: u32,
    members: [u32; MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT],
}

impl From<&CSRelativeTimestampGroup> for RelativeTimestampGroup {
    fn from(value: &CSRelativeTimestampGroup) -> Self {
        let members_count = value.members.len();
        assert!(
            members_count > 0
                && members_count <= MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT,
            "relative timestamp group has {} members, but the GPU ABI supports 1 to {}",
            members_count,
            MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT,
        );
        let mut members = [0u32; MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUP_MEMBERS_COUNT];
        for (&src, dst) in value.members.iter().zip(members.iter_mut()) {
            *dst = src as u32;
        }
        Self {
            borrow: {
                assert!(value.borrow <= u32::MAX as usize);
                value.borrow as u32
            },
            members_count: members_count as u32,
            members,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct OptionalRamAuxComparisonSet {
    tag: u32,
    intermediate_borrow: u32,
}

impl From<Option<CSRamAuxComparisonSet>> for OptionalRamAuxComparisonSet {
    fn from(value: Option<CSRamAuxComparisonSet>) -> Self {
        match value {
            Some(CSRamAuxComparisonSet {
                intermediate_borrow: GKRAddress::BaseLayerWitness(column),
            }) => {
                assert!(column <= u32::MAX as usize);
                Self {
                    tag: 1,
                    intermediate_borrow: column as u32,
                }
            }
            Some(set) => panic!(
                "delegation timestamp borrow {:?} is not a base layer witness column",
                set.intermediate_borrow
            ),
            None => Self::default(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct DelegationAuxLayoutData {
    shuffle_ram_timestamp_comparison_aux_vars:
        [OptionalRamAuxComparisonSet; MAX_DELEGATION_RAM_ACCESS_SETS_COUNT],
    relative_timestamp_groups_count: u32,
    relative_timestamp_groups:
        [RelativeTimestampGroup; MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUPS_COUNT],
}

const _: () = {
    use core::mem::{offset_of, size_of};
    assert!(size_of::<OptionalRamAuxComparisonSet>() == 8);
    assert!(offset_of!(OptionalRamAuxComparisonSet, intermediate_borrow) == 4);
    assert!(size_of::<RelativeTimestampGroup>() == 72);
    assert!(offset_of!(RelativeTimestampGroup, borrow) == 0);
    assert!(offset_of!(RelativeTimestampGroup, members_count) == 4);
    assert!(offset_of!(RelativeTimestampGroup, members) == 8);
    assert!(offset_of!(DelegationAuxLayoutData, relative_timestamp_groups_count) == 512);
    assert!(offset_of!(DelegationAuxLayoutData, relative_timestamp_groups) == 516);
    assert!(size_of::<DelegationAuxLayoutData>() == 1092);
};

impl Default for DelegationAuxLayoutData {
    fn default() -> Self {
        Self {
            shuffle_ram_timestamp_comparison_aux_vars: [OptionalRamAuxComparisonSet::default();
                MAX_DELEGATION_RAM_ACCESS_SETS_COUNT],
            relative_timestamp_groups_count: 0,
            relative_timestamp_groups: [RelativeTimestampGroup::default();
                MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUPS_COUNT],
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
        let groups_count = value.relative_timestamp_groups.len();
        assert!(
            groups_count <= MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUPS_COUNT,
            "delegation layout uses {} relative timestamp groups, but the GPU ABI supports at most {}",
            groups_count,
            MAX_DELEGATION_RELATIVE_TIMESTAMP_GROUPS_COUNT,
        );
        let mut result = Self::default();
        for (&src, dst) in value
            .shuffle_ram_timestamp_comparison_aux_vars
            .iter()
            .zip(result.shuffle_ram_timestamp_comparison_aux_vars.iter_mut())
        {
            *dst = src.into();
        }
        for (src, dst) in value
            .relative_timestamp_groups
            .iter()
            .zip(result.relative_timestamp_groups.iter_mut())
        {
            for &member in src.members.iter() {
                assert!(
                    member < len
                        && value.shuffle_ram_timestamp_comparison_aux_vars[member].is_none(),
                    "relative timestamp group member {} is not an uncompared RAM access",
                    member,
                );
            }
            *dst = src.into();
        }
        result.relative_timestamp_groups_count = groups_count as u32;

        result
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

pub(crate) trait GenerateMemoryDelegation<const CSR: u16>: Sized {
    const MEMORY_SIGNATURE: GenerateMemoryValuesSignature<Self>;
    const MEMORY_AND_WITNESS_SIGNATURE: GenerateMemoryAndWitnessValuesSignature<Self>;
}

macro_rules! generate_memory_values_impl {
    ($name:ident, $witness_type:ty, $circuit:ident) => {
        paste! {
            generate_delegation_kernels!($name, $witness_type);
            impl GenerateMemoryDelegation<{ DelegationCircuitType::$circuit as u16 }> for $witness_type {
                const MEMORY_SIGNATURE: GenerateMemoryValuesSignature<Self> = [<ab_generate_memory_values_ $name _kernel>];
                const MEMORY_AND_WITNESS_SIGNATURE: GenerateMemoryAndWitnessValuesSignature<Self> = [<ab_generate_memory_and_witness_values_ $name _kernel>];
            }
        }
    };
}

generate_memory_values_impl!(
    bigint_with_control,
    BigintDelegationWitness,
    BigIntWithControl
);
generate_memory_values_impl!(
    blake2_g_function,
    Blake2sGFunctionDelegationWitness,
    Blake2GFunction
);
generate_memory_values_impl!(
    blake2_with_compression,
    Blake2sRoundFunctionDelegationWitness,
    Blake2WithCompression
);
generate_memory_values_impl!(keccak_chi5, KeccakChi5DelegationWitness, KeccakChi5);
generate_memory_values_impl!(
    keccak_column_parity,
    KeccakColumnParityDelegationWitness,
    KeccakColumnParity
);
generate_memory_values_impl!(
    keccak_special5,
    KeccakSpecial5DelegationWitness,
    KeccakSpecial5
);
generate_memory_values_impl!(
    keccak_theta_rho,
    KeccakThetaRhoDelegationWitness,
    KeccakThetaRho
);

pub(crate) fn generate_memory_values_delegation<
    T: GenerateMemoryDelegation<CSR>,
    const CSR: u16,
>(
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

// `private_bounds`: `GenerateMemoryDelegation` is a deliberately sealed
// dispatch trait — only the marker witness types this file's macro impls
// cover (e.g. `BigintDelegationWitness`) implement it. `gpu_gkr`'s production
// call sites (`gkr::stage1`) never name the trait; `T` is inferred from a
// `DelegationTraceDevice<T>` argument, so the bound stays private by design.
#[allow(private_bounds)]
pub fn generate_memory_and_witness_values_delegation<
    T: GenerateMemoryDelegation<CSR>,
    const CSR: u16,
>(
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
