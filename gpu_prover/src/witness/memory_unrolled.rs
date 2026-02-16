use std::ops::Deref;
use crate::circuit_type::{UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType};
use crate::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use crate::field::BF;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::witness::option::u32::Option;
use crate::witness::ram_access::{RamAuxComparisonSet, RamQuery};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledMemoryOracle, UnrolledMemoryTraceDevice,
    UnrolledNonMemoryOracle, UnrolledNonMemoryTraceDevice,
};
use crate::witness::Address;
use cs::definitions::gkr::{GKRMachineState, GKRMemoryLayout};
use cs::definitions::{NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE};
use cs::gkr_compiler::GKRAuxLayoutData;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct MachineState {
    pub pc: [u32; REGISTER_SIZE],
    pub timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
}

impl From<GKRMachineState> for MachineState {
    fn from(value: GKRMachineState) -> Self {
        Self {
            pc: value.pc.map(|x| x as u32),
            timestamp: value.timestamp.map(|x| x as u32),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct MachineStatePermutationDescription {
    pub execute: u32,
    pub initial_state: MachineState,
    pub final_state: MachineState,
}

impl From<cs::definitions::gkr::MachineStatePermutationDescription>
    for MachineStatePermutationDescription
{
    fn from(value: cs::definitions::gkr::MachineStatePermutationDescription) -> Self {
        Self {
            execute: value.execute as u32,
            initial_state: value.initial_state.into(),
            final_state: value.final_state.into(),
        }
    }
}

const MAX_CIRCUIT_FAMILY_MASK_BITS: usize = 32;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct DecoderPlacementDescription {
    pub rs1_index: u32,
    pub rs2_index: Address,
    pub rd_index: Address,
    pub circuit_family_mask_bits_count: u32,
    pub circuit_family_mask_bits: [Address; MAX_CIRCUIT_FAMILY_MASK_BITS],
    pub decoder_witness_is_in_memory: bool,
    pub rd_is_zero: u32,
    pub imm: [u32; REGISTER_SIZE],
    pub funct3: Option<u32>,
}

impl From<cs::definitions::gkr::DecoderPlacementDescription> for DecoderPlacementDescription {
    fn from(value: cs::definitions::gkr::DecoderPlacementDescription) -> Self {
        let rs1_index = value.rs1_index as u32;
        let rs2_index = value.rs2_index.into();
        let rd_index = value.rd_index.into();
        let circuit_family_mask_bits_len = value.circuit_family_mask_bits.len();
        assert!(circuit_family_mask_bits_len <= MAX_CIRCUIT_FAMILY_MASK_BITS);
        let circuit_family_mask_bits_count = circuit_family_mask_bits_len as u32;
        let mut circuit_family_mask_bits = [Address::default(); MAX_CIRCUIT_FAMILY_MASK_BITS];
        for (&src, dst) in value
            .circuit_family_mask_bits
            .iter()
            .zip(circuit_family_mask_bits.iter_mut())
        {
            *dst = src.into();
        }
        let decoder_witness_is_in_memory = value.decoder_witness_is_in_memory;
        let rd_is_zero = value.rd_is_zero as u32;
        let imm = value.imm.map(|x| x as u32);
        let funct3 = value.funct3.map(|x| x as u32).into();
        Self {
            rs1_index,
            rs2_index,
            rd_index,
            circuit_family_mask_bits_count,
            circuit_family_mask_bits,
            decoder_witness_is_in_memory,
            rd_is_zero,
            imm,
            funct3,
        }
    }
}

pub const MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct UnrolledMemoryLayout {
    pub shuffle_ram_access_sets_count: u32,
    pub shuffle_ram_access_sets: [RamQuery; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
    pub machine_state: MachineStatePermutationDescription,
    pub decoder_input: DecoderPlacementDescription,
}

impl From<&GKRMemoryLayout> for UnrolledMemoryLayout {
    fn from(value: &GKRMemoryLayout) -> Self {
        assert!(value.register_and_indirect_accesses.is_empty());
        let (shuffle_ram_access_sets_count, shuffle_ram_access_sets) = {
            let ram_access_sets = &value.shuffle_ram_access_sets;
            let len = ram_access_sets.len();
            assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
            let count = len as u32;
            let mut sets = [RamQuery::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
            for (&src, dst) in ram_access_sets.iter().zip(sets.iter_mut()) {
                *dst = src.into();
            }
            (count, sets)
        };
        let machine_state = value.machine_state.unwrap().into();
        let decoder_input = value.decoder_input.clone().unwrap().into();
        Self {
            shuffle_ram_access_sets_count,
            shuffle_ram_access_sets,
            machine_state,
            decoder_input,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct AuxLayoutData {
    pub shuffle_ram_timestamp_comparison_aux_vars:
        [RamAuxComparisonSet; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl From<&GKRAuxLayoutData> for AuxLayoutData {
    fn from(value: &GKRAuxLayoutData) -> Self {
        let vars = &value.shuffle_ram_timestamp_comparison_aux_vars;
        let len = vars.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let mut shuffle_ram_timestamp_comparison_aux_vars =
            [RamAuxComparisonSet::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in vars
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

// pub const SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH: usize =
//     REGISTER_SIZE * 2 + NUM_TIMESTAMP_COLUMNS_FOR_RAM;
// 
// #[repr(C)]
// #[derive(Clone, Copy, Default, Debug)]
// pub struct ShuffleRamInitAndTeardownLayout {
//     pub lazy_init_addresses_columns: [u32; REGISTER_SIZE],
//     pub lazy_teardown_values_columns: [u32; REGISTER_SIZE],
//     pub lazy_teardown_timestamps_columns: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
// }
// 
// pub const MAX_INITS_AND_TEARDOWNS_SETS_COUNT: usize = 16;
//
// #[repr(C)]
// #[derive(Clone, Copy, Default, Debug)]
// pub struct ShuffleRamInitAndTeardownLayouts {
//     pub count: u32,
//     pub layouts: [ShuffleRamInitAndTeardownLayout; MAX_INITS_AND_TEARDOWNS_SETS_COUNT],
// }
//
// impl<T: Deref<Target = [cs::definitions::ShuffleRamInitAndTeardownLayout]>> From<&T>
//     for ShuffleRamInitAndTeardownLayouts
// {
//     fn from(value: &T) -> Self {
//         let len = value.len();
//         assert!(len <= MAX_INITS_AND_TEARDOWNS_SETS_COUNT);
//         let count = len as u32;
//         let mut layouts =
//             [ShuffleRamInitAndTeardownLayout::default(); MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
//         for (&src, dst) in value.iter().zip(layouts.iter_mut()) {
//             *dst = src.into();
//         }
//         Self { count, layouts }
//     }
// }

cuda_kernel!(GenerateMemoryValuesUnrolledMemory,
    ab_generate_memory_values_unrolled_memory_kernel(
        layout: UnrolledMemoryLayout,
        oracle: UnrolledMemoryOracle,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryValuesUnrolledNonMemory,
    ab_generate_memory_values_unrolled_non_memory_kernel(
        layout: UnrolledMemoryLayout,
        oracle: UnrolledNonMemoryOracle,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

// cuda_kernel!(GenerateMemoryValuesUnrolledInitsAndTeardowns,
//     ab_generate_memory_values_unrolled_inits_and_teardowns_kernel(
//         init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
//         inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
//         memory: MutPtrAndStride<BF>,
//         count: u32,
//     )
// );
//
// cuda_kernel!(GenerateMemoryValuesUnrolledUnified,
//     ab_generate_memory_values_unrolled_unified_kernel(
//         subtree: UnrolledFamilyMemorySubtree,
//         inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
//         oracle: UnrolledUnifiedOracle,
//         memory: MutPtrAndStride<BF>,
//         count: u32,
//     )
// );

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledMemory,
    ab_generate_memory_and_witness_values_unrolled_memory_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledMemoryOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: *mut u32,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledNonMemory,
    ab_generate_memory_and_witness_values_unrolled_non_memory_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledNonMemoryOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: *mut u32,
        count: u32,
    )
);

// cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledInitsAndTeardowns,
//     ab_generate_memory_and_witness_values_unrolled_inits_and_teardowns_kernel(
//         init_and_teardown_layouts: ShuffleRamInitAndTeardownLayouts,
//         aux_comparison_sets: ShuffleRamAuxComparisonSets,
//         inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
//         memory: MutPtrAndStride<BF>,
//         witness: MutPtrAndStride<BF>,
//         count: u32,
//     )
// );
//
// cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledUnified,
//     ab_generate_memory_and_witness_values_unrolled_unified_kernel(
//         subtree: UnrolledFamilyMemorySubtree,
//         aux_comparison_sets: ShuffleRamAuxComparisonSets,
//         executor_family_circuit_next_timestamp_aux_var: Option<ColumnAddress>,
//         memory_queries_timestamp_comparison_aux_vars: MemoryQueriesTimestampComparisonAuxVars,
//         inits_and_teardowns: ShuffleRamInitsAndTeardownsRaw,
//         oracle: UnrolledUnifiedOracle,
//         memory: MutPtrAndStride<BF>,
//         witness: MutPtrAndStride<BF>,
//         decoder_lookup_mapping: *mut u32,
//         count: u32,
//     )
// );

pub(crate) fn generate_memory_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    memory_layout: &GKRMemoryLayout,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), memory_layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = memory_layout.into();
    let oracle = UnrolledMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledMemoryArguments::new(layout, oracle, memory, count);
    GenerateMemoryValuesUnrolledMemoryFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    memory_layout: &GKRMemoryLayout,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledNonMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), memory_layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = memory_layout.into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: circuit_type.get_default_pc_value_in_padding(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledNonMemoryArguments::new(layout, oracle, memory, count);
    GenerateMemoryValuesUnrolledNonMemoryFunction::default().launch(&config, &args)
}

// pub(crate) fn generate_memory_values_unrolled_inits_and_teardowns(
//     subtree: &MemorySubtree,
//     inits_and_teardowns: &ShuffleRamInitsAndTeardownsDevice,
//     memory: &mut impl DeviceMatrixMutImpl<BF>,
//     stream: &CudaStream,
// ) -> CudaResult<()> {
//     let count = memory.stride() - 1;
//     let cols = memory.cols();
//     assert_eq!(cols, subtree.total_width);
//     assert!(cols.is_multiple_of(SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH));
//     assert!(count <= u32::MAX as usize);
//     let count = count as u32;
//     let layouts = (&subtree.shuffle_ram_inits_and_teardowns).into();
//     let inits_and_teardowns = inits_and_teardowns.into();
//     let memory = memory.as_mut_ptr_and_stride();
//     let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
//     let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
//     let args = GenerateMemoryValuesUnrolledInitsAndTeardownsArguments::new(
//         layouts,
//         inits_and_teardowns,
//         memory,
//         count,
//     );
//     GenerateMemoryValuesUnrolledInitsAndTeardownsFunction::default().launch(&config, &args)
// }
//
// pub(crate) fn generate_memory_values_unrolled_unified(
//     subtree: &MemorySubtree,
//     decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
//     inits_and_teardowns: &std::option::Option<ShuffleRamInitsAndTeardownsDevice>,
//     trace: &UnrolledUnifiedTraceDevice,
//     memory: &mut impl DeviceMatrixMutImpl<BF>,
//     stream: &CudaStream,
// ) -> CudaResult<()> {
//     let count = UnrolledCircuitType::Unified.get_num_cycles();
//     assert_eq!(memory.stride(), count + 1);
//     assert_eq!(memory.cols(), subtree.total_width);
//     assert!(count <= u32::MAX as usize);
//     let count = count as u32;
//     let subtree = subtree.into();
//     let inits_and_teardowns = inits_and_teardowns
//         .as_ref()
//         .map(<&ShuffleRamInitsAndTeardownsDevice>::into)
//         .unwrap_or_default();
//     let oracle = UnrolledUnifiedOracle {
//         trace: trace.into(),
//         decoder_table: decoder_table.as_ptr(),
//     };
//     let memory = memory.as_mut_ptr_and_stride();
//     let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
//     let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
//     let args = GenerateMemoryValuesUnrolledUnifiedArguments::new(
//         subtree,
//         inits_and_teardowns,
//         oracle,
//         memory,
//         count,
//     );
//     GenerateMemoryValuesUnrolledUnifiedFunction::default().launch(&config, &args)
// }

pub(crate) fn generate_memory_and_witness_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = layout.into();
    let aux_layout_data = aux_layout_data.into();
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
        layout,
        aux_layout_data,
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
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledNonMemoryTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit_type.get_domain_size();
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = layout.into();
    let aux_layout_data = aux_layout_data.into();
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
        layout,
        aux_layout_data,
        oracle,
        memory,
        witness,
        decoder_lookup_mapping,
        count,
    );
    GenerateMemoryAndWitnessValuesUnrolledNonMemoryFunction::default().launch(&config, &args)
}

// pub(crate) fn generate_memory_and_witness_values_unrolled_inits_and_teardowns(
//     subtree: &MemorySubtree,
//     aux_comparison_sets: &[cs::definitions::ShuffleRamAuxComparisonSet],
//     inits_and_teardowns: &ShuffleRamInitsAndTeardownsDevice,
//     memory: &mut impl DeviceMatrixMutImpl<BF>,
//     witness: &mut impl DeviceMatrixMutImpl<BF>,
//     stream: &CudaStream,
// ) -> CudaResult<()> {
//     let count = memory.stride() - 1;
//     let cols = memory.cols();
//     assert_eq!(cols, subtree.total_width);
//     assert!(cols.is_multiple_of(SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH));
//     assert!(count <= u32::MAX as usize);
//     let count = count as u32;
//     let layouts = (&subtree.shuffle_ram_inits_and_teardowns).into();
//     let inits_and_teardowns = inits_and_teardowns.into();
//     let aux_comparison_sets = (&aux_comparison_sets).into();
//     let memory = memory.as_mut_ptr_and_stride();
//     let witness = witness.as_mut_ptr_and_stride();
//     let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
//     let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
//     let args = GenerateMemoryAndWitnessValuesUnrolledInitsAndTeardownsArguments::new(
//         layouts,
//         aux_comparison_sets,
//         inits_and_teardowns,
//         memory,
//         witness,
//         count,
//     );
//     GenerateMemoryAndWitnessValuesUnrolledInitsAndTeardownsFunction::default()
//         .launch(&config, &args)
// }
//
// pub(crate) fn generate_memory_and_witness_values_unrolled_unified(
//     subtree: &MemorySubtree,
//     aux_comparison_sets: &[cs::definitions::ShuffleRamAuxComparisonSet],
//     executor_family_circuit_next_timestamp_aux_var: std::option::Option<
//         cs::definitions::ColumnAddress,
//     >,
//     memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
//     decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
//     inits_and_teardowns: &std::option::Option<ShuffleRamInitsAndTeardownsDevice>,
//     trace: &UnrolledUnifiedTraceDevice,
//     memory: &mut impl DeviceMatrixMutImpl<BF>,
//     witness: &mut impl DeviceMatrixMutImpl<BF>,
//     decoder_lookup_mapping: &mut DeviceSlice<u32>,
//     stream: &CudaStream,
// ) -> CudaResult<()> {
//     let count = UnrolledCircuitType::Unified.get_num_cycles();
//     assert_eq!(memory.stride(), count + 1);
//     assert_eq!(memory.cols(), subtree.total_width);
//     assert!(count <= u32::MAX as usize);
//     let count = count as u32;
//     let subtree = subtree.into();
//     let aux_comparison_sets = (&aux_comparison_sets).into();
//     let executor_family_circuit_next_timestamp_aux_var =
//         executor_family_circuit_next_timestamp_aux_var.into();
//     let memory_queries_timestamp_comparison_aux_vars =
//         (&memory_queries_timestamp_comparison_aux_vars).into();
//     let inits_and_teardowns = inits_and_teardowns
//         .as_ref()
//         .map(<&ShuffleRamInitsAndTeardownsDevice>::into)
//         .unwrap_or_default();
//     let oracle = UnrolledUnifiedOracle {
//         trace: trace.into(),
//         decoder_table: decoder_table.as_ptr(),
//     };
//     let memory = memory.as_mut_ptr_and_stride();
//     let witness = witness.as_mut_ptr_and_stride();
//     let decoder_lookup_mapping = decoder_lookup_mapping.as_mut_ptr();
//     let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
//     let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
//     let args = GenerateMemoryAndWitnessValuesUnrolledUnifiedArguments::new(
//         subtree,
//         aux_comparison_sets,
//         executor_family_circuit_next_timestamp_aux_var,
//         memory_queries_timestamp_comparison_aux_vars,
//         inits_and_teardowns,
//         oracle,
//         memory,
//         witness,
//         decoder_lookup_mapping,
//         count,
//     );
//     GenerateMemoryAndWitnessValuesUnrolledUnifiedFunction::default().launch(&config, &args)
// }
