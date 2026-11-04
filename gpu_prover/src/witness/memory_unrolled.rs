use super::layout::{
    DelegationRequestLayout, ShuffleRamInitAndTeardownLayout,
    SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH,
};
use super::option::u32::Option;
use crate::circuit_type::{
    UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::witness::column::{
    ColumnAddress, ColumnSet, NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE,
};
use crate::witness::ram_access::{ShuffleRamAuxComparisonSet, ShuffleRamQueryColumns};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, ShuffleRamInitsAndTeardownsDevice, ShuffleRamInitsAndTeardownsRaw,
    UnrolledMemoryOracle, UnrolledMemoryTraceDevice, UnrolledNonMemoryOracle,
    UnrolledNonMemoryTraceDevice, UnrolledUnifiedOracle, UnrolledUnifiedTraceDevice,
};
use crate::witness::BF;
use cs::definitions::MemorySubtree;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use std::ops::Deref;

pub const MAX_INITS_AND_TEARDOWNS_SETS_COUNT: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamInitAndTeardownLayouts {
    pub count: u32,
    pub layouts: [ShuffleRamInitAndTeardownLayout; MAX_INITS_AND_TEARDOWNS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ShuffleRamInitAndTeardownLayout]>> From<&T>
    for ShuffleRamInitAndTeardownLayouts
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_INITS_AND_TEARDOWNS_SETS_COUNT);
        let count = len as u32;
        let mut layouts =
            [ShuffleRamInitAndTeardownLayout::default(); MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(layouts.iter_mut()) {
            *dst = src.into();
        }
        Self { count, layouts }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamAuxComparisonSets {
    pub count: u32,
    pub sets: [ShuffleRamAuxComparisonSet; MAX_INITS_AND_TEARDOWNS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ShuffleRamAuxComparisonSet]>> From<&T>
    for ShuffleRamAuxComparisonSets
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_INITS_AND_TEARDOWNS_SETS_COUNT);
        let count = len as u32;
        let mut sets = [ShuffleRamAuxComparisonSet::default(); MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(sets.iter_mut()) {
            *dst = src.into();
        }
        Self { count, sets }
    }
}

pub const MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct MemoryQueriesTimestampComparisonAuxVars {
    count: u32,
    addresses: [ColumnAddress; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ColumnAddress]>> From<&T>
    for MemoryQueriesTimestampComparisonAuxVars
{
    fn from(value: &T) -> Self {
        let value = value.as_ref();
        let len = value.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let count = len as u32;
        let mut addresses = [ColumnAddress::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(addresses.iter_mut()) {
            *dst = src.into();
        }
        Self { count, addresses }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamAccessSets {
    pub count: u32,
    pub sets: [ShuffleRamQueryColumns; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ShuffleRamQueryColumns]>> From<&T>
    for ShuffleRamAccessSets
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let count = len as u32;
        let mut sets = [ShuffleRamQueryColumns::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(sets.iter_mut()) {
            *dst = src.into();
        }
        Self { count, sets }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct MachineStatePermutationVariables {
    pub pc: ColumnSet<2>,
    pub timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
}

impl From<cs::definitions::MachineStatePermutationVariables> for MachineStatePermutationVariables {
    fn from(value: cs::definitions::MachineStatePermutationVariables) -> Self {
        Self {
            pc: value.pc.into(),
            timestamp: value.timestamp.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct IntermediateStatePermutationVariables {
    pub execute: ColumnSet<1>,
    pub pc: ColumnSet<2>,
    pub timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub rs1_index: ColumnSet<1>,
    pub rs2_index: ColumnAddress,
    pub rd_index: ColumnAddress,
    pub decoder_witness_is_in_memory: bool,
    pub rd_is_zero: ColumnSet<1>,
    pub imm: ColumnSet<REGISTER_SIZE>,
    pub funct3: ColumnSet<1>,
    pub funct7: ColumnSet<1>,
    pub circuit_family: ColumnSet<1>,
    pub circuit_family_extra_mask: ColumnAddress,
}

impl From<cs::definitions::IntermediateStatePermutationVariables>
    for IntermediateStatePermutationVariables
{
    fn from(value: cs::definitions::IntermediateStatePermutationVariables) -> Self {
        Self {
            execute: value.execute.into(),
            pc: value.pc.into(),
            timestamp: value.timestamp.into(),
            rs1_index: value.rs1_index.into(),
            rs2_index: value.rs2_index.into(),
            rd_index: value.rd_index.into(),
            decoder_witness_is_in_memory: value.decoder_witness_is_in_memory,
            rd_is_zero: value.rd_is_zero.into(),
            imm: value.imm.into(),
            funct3: value.funct3.into(),
            funct7: value.funct7.into(),
            circuit_family: value.circuit_family.into(),
            circuit_family_extra_mask: value.circuit_family_extra_mask.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone)]
pub(crate) struct UnrolledFamilyMemorySubtree {
    pub init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
    pub machine_state_layout: MachineStatePermutationVariables,
    pub intermediate_state_layout: IntermediateStatePermutationVariables,
    pub shuffle_ram_access_sets: ShuffleRamAccessSets,
    pub delegation_request_layout: Option<DelegationRequestLayout>,
}

impl From<&MemorySubtree> for UnrolledFamilyMemorySubtree {
    fn from(value: &MemorySubtree) -> Self {
        assert!(value.delegation_processor_layout.is_none());
        assert!(value.batched_ram_accesses.is_empty());
        assert!(value.register_and_indirect_accesses.is_empty());
        let init_and_teardown_layouts = (&value.shuffle_ram_inits_and_teardowns).into();
        let machine_state_layout = value.machine_state_layout.unwrap().into();
        let intermediate_state_layout = value.intermediate_state_layout.unwrap().into();
        let shuffle_ram_access_sets = (&value.shuffle_ram_access_sets).into();
        let delegation_request_layout = value.delegation_request_layout.into();
        Self {
            init_and_teardown_layouts,
            machine_state_layout,
            intermediate_state_layout,
            shuffle_ram_access_sets,
            delegation_request_layout,
        }
    }
}

cuda_kernel!(GenerateMemoryValuesUnrolledMemory,
    ab_generate_memory_values_unrolled_memory_kernel(
        subtree: UnrolledFamilyMemorySubtree,
        oracle: UnrolledMemoryOracle,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryValuesUnrolledNonMemory,
    ab_generate_memory_values_unrolled_non_memory_kernel(
        subtree: UnrolledFamilyMemorySubtree,
        oracle: UnrolledNonMemoryOracle,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryValuesUnrolledInitsAndTeardowns,
    ab_generate_memory_values_unrolled_inits_and_teardowns_kernel(
        init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
        inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryValuesUnrolledUnified,
    ab_generate_memory_values_unrolled_unified_kernel(
        subtree: UnrolledFamilyMemorySubtree,
        inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
        oracle: UnrolledUnifiedOracle,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledMemory,
    ab_generate_memory_and_witness_values_unrolled_memory_kernel(
        subtree: UnrolledFamilyMemorySubtree,
        executor_family_circuit_next_timestamp_aux_var: Option<ColumnAddress>,
        memory_queries_timestamp_comparison_aux_vars: MemoryQueriesTimestampComparisonAuxVars,
        oracle: UnrolledMemoryOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: *mut u32,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledNonMemory,
    ab_generate_memory_and_witness_values_unrolled_non_memory_kernel(
        subtree: UnrolledFamilyMemorySubtree,
        executor_family_circuit_next_timestamp_aux_var: Option<ColumnAddress>,
        memory_queries_timestamp_comparison_aux_vars: MemoryQueriesTimestampComparisonAuxVars,
        oracle: UnrolledNonMemoryOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: *mut u32,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledInitsAndTeardowns,
    ab_generate_memory_and_witness_values_unrolled_inits_and_teardowns_kernel(
        init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
        aux_comparison_sets: ShuffleRamAuxComparisonSets,
        inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledUnified,
    ab_generate_memory_and_witness_values_unrolled_unified_kernel(
        subtree: UnrolledFamilyMemorySubtree,
        aux_comparison_sets: ShuffleRamAuxComparisonSets,
        executor_family_circuit_next_timestamp_aux_var: Option<ColumnAddress>,
        memory_queries_timestamp_comparison_aux_vars: MemoryQueriesTimestampComparisonAuxVars,
        inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
        oracle: UnrolledUnifiedOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: *mut u32,
        count: u32,
    )
);

pub(crate) fn generate_memory_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    subtree: &MemorySubtree,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let oracle = UnrolledMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledMemoryArguments::new(subtree, oracle, memory, count);
    GenerateMemoryValuesUnrolledMemoryFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    subtree: &MemorySubtree,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledNonMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: circuit_type.get_default_pc_value_in_padding(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledNonMemoryArguments::new(subtree, oracle, memory, count);
    GenerateMemoryValuesUnrolledNonMemoryFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_values_unrolled_inits_and_teardowns(
    subtree: &MemorySubtree,
    inits_and_teardowns: &ShuffleRamInitsAndTeardownsDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = memory.stride() - 1;
    let cols = memory.cols();
    assert_eq!(cols, subtree.total_width);
    assert!(cols.is_multiple_of(SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH));
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layouts = (&subtree.shuffle_ram_inits_and_teardowns).into();
    let inits_and_teardowns = inits_and_teardowns.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledInitsAndTeardownsArguments::new(
        layouts,
        inits_and_teardowns,
        memory,
        count,
    );
    GenerateMemoryValuesUnrolledInitsAndTeardownsFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_values_unrolled_unified(
    subtree: &MemorySubtree,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    inits_and_teardowns: &std::option::Option<ShuffleRamInitsAndTeardownsDevice>,
    trace: &UnrolledUnifiedTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledCircuitType::Unified.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let inits_and_teardowns = inits_and_teardowns
        .as_ref()
        .map(<&ShuffleRamInitsAndTeardownsDevice>::into)
        .unwrap_or_default();
    let oracle = UnrolledUnifiedOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledUnifiedArguments::new(
        subtree,
        inits_and_teardowns,
        oracle,
        memory,
        count,
    );
    GenerateMemoryValuesUnrolledUnifiedFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    subtree: &MemorySubtree,
    executor_family_circuit_next_timestamp_aux_var: std::option::Option<
        cs::definitions::ColumnAddress,
    >,
    memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let executor_family_circuit_next_timestamp_aux_var =
        executor_family_circuit_next_timestamp_aux_var.into();
    let memory_queries_timestamp_comparison_aux_vars =
        (&memory_queries_timestamp_comparison_aux_vars).into();
    let oracle = UnrolledMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let decoder_lookup_mapping = decoder_lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesUnrolledMemoryArguments::new(
        subtree,
        executor_family_circuit_next_timestamp_aux_var,
        memory_queries_timestamp_comparison_aux_vars,
        oracle,
        memory,
        witness,
        decoder_lookup_mapping,
        count,
    );
    GenerateMemoryAndWitnessValuesUnrolledMemoryFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    subtree: &MemorySubtree,
    executor_family_circuit_next_timestamp_aux_var: std::option::Option<
        cs::definitions::ColumnAddress,
    >,
    memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledNonMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let executor_family_circuit_next_timestamp_aux_var =
        executor_family_circuit_next_timestamp_aux_var.into();
    let memory_queries_timestamp_comparison_aux_vars =
        (&memory_queries_timestamp_comparison_aux_vars).into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: circuit_type.get_default_pc_value_in_padding(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let decoder_lookup_mapping = decoder_lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesUnrolledNonMemoryArguments::new(
        subtree,
        executor_family_circuit_next_timestamp_aux_var,
        memory_queries_timestamp_comparison_aux_vars,
        oracle,
        memory,
        witness,
        decoder_lookup_mapping,
        count,
    );
    GenerateMemoryAndWitnessValuesUnrolledNonMemoryFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_unrolled_inits_and_teardowns(
    subtree: &MemorySubtree,
    aux_comparison_sets: &[cs::definitions::ShuffleRamAuxComparisonSet],
    inits_and_teardowns: &ShuffleRamInitsAndTeardownsDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = memory.stride() - 1;
    let cols = memory.cols();
    assert_eq!(cols, subtree.total_width);
    assert!(cols.is_multiple_of(SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH));
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layouts = (&subtree.shuffle_ram_inits_and_teardowns).into();
    let inits_and_teardowns = inits_and_teardowns.into();
    let aux_comparison_sets = (&aux_comparison_sets).into();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesUnrolledInitsAndTeardownsArguments::new(
        layouts,
        aux_comparison_sets,
        inits_and_teardowns,
        memory,
        witness,
        count,
    );
    GenerateMemoryAndWitnessValuesUnrolledInitsAndTeardownsFunction::default()
        .launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_unrolled_unified(
    subtree: &MemorySubtree,
    aux_comparison_sets: &[cs::definitions::ShuffleRamAuxComparisonSet],
    executor_family_circuit_next_timestamp_aux_var: std::option::Option<
        cs::definitions::ColumnAddress,
    >,
    memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    inits_and_teardowns: &std::option::Option<ShuffleRamInitsAndTeardownsDevice>,
    trace: &UnrolledUnifiedTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledCircuitType::Unified.get_num_cycles();
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let aux_comparison_sets = (&aux_comparison_sets).into();
    let executor_family_circuit_next_timestamp_aux_var =
        executor_family_circuit_next_timestamp_aux_var.into();
    let memory_queries_timestamp_comparison_aux_vars =
        (&memory_queries_timestamp_comparison_aux_vars).into();
    let inits_and_teardowns = inits_and_teardowns
        .as_ref()
        .map(<&ShuffleRamInitsAndTeardownsDevice>::into)
        .unwrap_or_default();
    let oracle = UnrolledUnifiedOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let decoder_lookup_mapping = decoder_lookup_mapping.as_mut_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesUnrolledUnifiedArguments::new(
        subtree,
        aux_comparison_sets,
        executor_family_circuit_next_timestamp_aux_var,
        memory_queries_timestamp_comparison_aux_vars,
        inits_and_teardowns,
        oracle,
        memory,
        witness,
        decoder_lookup_mapping,
        count,
    );
    GenerateMemoryAndWitnessValuesUnrolledUnifiedFunction::default().launch(&config, &args)
}
