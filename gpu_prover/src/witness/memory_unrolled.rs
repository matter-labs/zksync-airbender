use super::layout::{DelegationRequestLayout, SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH};
use super::memory::{
    MemoryQueriesTimestampComparisonAuxVars, ShuffleRamAccessSets, ShuffleRamAuxComparisonSets,
    ShuffleRamInitAndTeardownLayouts,
};
use super::option::u32::Option;
use crate::device_structures::{
    DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl, MutPtrAndStride,
};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::witness::column::{
    ColumnAddress, ColumnSet, NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE,
};
use crate::witness::trace::{ShuffleRamInitsAndTeardownsDevice, ShuffleRamInitsAndTeardownsRaw};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledMemoryOracle, UnrolledMemoryTraceDevice,
    UnrolledNonMemoryOracle, UnrolledNonMemoryTraceDevice,
};
use crate::witness::BF;
use cs::definitions::MemorySubtree;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

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
    pub delegation_request_layout: Option<DelegationRequestLayout>,
    pub machine_state_layout: MachineStatePermutationVariables,
    pub intermediate_state_layout: IntermediateStatePermutationVariables,
    pub shuffle_ram_access_sets: ShuffleRamAccessSets,
}

impl From<&MemorySubtree> for UnrolledFamilyMemorySubtree {
    fn from(value: &MemorySubtree) -> Self {
        assert!(value.delegation_processor_layout.is_none());
        assert!(value.batched_ram_accesses.is_empty());
        assert!(value.register_and_indirect_accesses.is_empty());
        assert!(value.shuffle_ram_inits_and_teardowns.is_empty());
        let delegation_request_layout = value.delegation_request_layout.into();
        let machine_state_layout = value.machine_state_layout.unwrap().into();
        let intermediate_state_layout = value.intermediate_state_layout.unwrap().into();
        let shuffle_ram_access_sets = (&value.shuffle_ram_access_sets).into();
        Self {
            delegation_request_layout,
            machine_state_layout,
            intermediate_state_layout,
            shuffle_ram_access_sets,
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

cuda_kernel!(GenerateMemoryValuesInitsAndTeardowns,
    ab_generate_memory_values_inits_and_teardowns_kernel(
        init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
        inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
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

cuda_kernel!(GenerateMemoryAndWitnessValuesInitsAndTeardowns,
    ab_generate_memory_and_witness_values_inits_and_teardowns_kernel(
        init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
        inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
        aux_comparison_sets: ShuffleRamAuxComparisonSets,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        count: u32,
    )
);

pub(crate) fn generate_memory_values_unrolled_memory(
    subtree: &MemorySubtree,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    memory: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycles_count;
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
    subtree: &MemorySubtree,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    default_pc_value_in_padding: u32,
    trace: &UnrolledNonMemoryTraceDevice,
    memory: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycles_count;
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding,
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledNonMemoryArguments::new(subtree, oracle, memory, count);
    GenerateMemoryValuesUnrolledNonMemoryFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_values_inits_and_teardowns(
    subtree: &MemorySubtree,
    inits_and_teardowns: &ShuffleRamInitsAndTeardownsDevice,
    memory: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = memory.stride() - 1;
    let cols = memory.cols();
    let len = inits_and_teardowns.inits_and_teardowns.len();
    assert_eq!(cols, subtree.total_width);
    assert!(cols.is_multiple_of(SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH));
    let sets = cols / SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH;
    assert_eq!(len, count * sets);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layouts = (&subtree.shuffle_ram_inits_and_teardowns).into();
    let inits_and_teardowns = inits_and_teardowns.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesInitsAndTeardownsArguments::new(
        layouts,
        inits_and_teardowns,
        memory,
        count,
    );
    GenerateMemoryValuesInitsAndTeardownsFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_unrolled_memory(
    subtree: &MemorySubtree,
    memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
    executor_family_circuit_next_timestamp_aux_var: std::option::Option<
        cs::definitions::ColumnAddress,
    >,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    memory: &mut DeviceMatrixMut<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycles_count;
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let memory_queries_timestamp_comparison_aux_vars =
        (&memory_queries_timestamp_comparison_aux_vars).into();
    let executor_family_circuit_next_timestamp_aux_var =
        executor_family_circuit_next_timestamp_aux_var.into();
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
    subtree: &MemorySubtree,
    memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
    executor_family_circuit_next_timestamp_aux_var: std::option::Option<
        cs::definitions::ColumnAddress,
    >,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    default_pc_value_in_padding: u32,
    trace: &UnrolledNonMemoryTraceDevice,
    memory: &mut DeviceMatrixMut<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycles_count;
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let memory_queries_timestamp_comparison_aux_vars =
        (&memory_queries_timestamp_comparison_aux_vars).into();
    let executor_family_circuit_next_timestamp_aux_var =
        executor_family_circuit_next_timestamp_aux_var.into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding,
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

pub(crate) fn generate_memory_and_witness_values_inits_and_teardowns(
    subtree: &MemorySubtree,
    inits_and_teardowns: &ShuffleRamInitsAndTeardownsDevice,
    aux_comparison_sets: &[cs::definitions::ShuffleRamAuxComparisonSet],
    memory: &mut DeviceMatrixMut<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = memory.stride() - 1;
    let cols = memory.cols();
    let len = inits_and_teardowns.inits_and_teardowns.len();
    assert_eq!(cols, subtree.total_width);
    assert!(cols.is_multiple_of(SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH));
    let sets = cols / SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH;
    assert_eq!(len, count * sets);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layouts = (&subtree.shuffle_ram_inits_and_teardowns).into();
    let inits_and_teardowns = inits_and_teardowns.into();
    let aux_comparison_sets = (&aux_comparison_sets).into();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesInitsAndTeardownsArguments::new(
        layouts,
        inits_and_teardowns,
        aux_comparison_sets,
        memory,
        witness,
        count,
    );
    GenerateMemoryAndWitnessValuesInitsAndTeardownsFunction::default().launch(&config, &args)
}
