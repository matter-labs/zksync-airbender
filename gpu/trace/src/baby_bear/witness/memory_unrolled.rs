use crate::witness::circuit_type::{
    UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::witness::memory_unrolled::{AuxLayoutData, UnrolledMemoryLayout};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledMemoryOracle, UnrolledMemoryTraceDevice,
    UnrolledNonMemoryOracle, UnrolledNonMemoryTraceDevice, UnrolledUnifiedOracle,
    UnrolledUnifiedTraceDevice,
};
use gpu_core::primitives::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

use crate::upstream::{GKRAuxLayoutData, GKRMemoryLayout};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

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

cuda_kernel!(GenerateMemoryValuesUnrolledUnified,
    ab_generate_memory_values_unrolled_unified_kernel(
        layout: UnrolledMemoryLayout,
        oracle: UnrolledUnifiedOracle,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

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

crate::witness::memory_unrolled::define_inits_and_teardowns!(
    BF,
    generate_memory_and_witness_values_unrolled_inits_and_teardowns,
    ab_generate_memory_and_witness_values_unrolled_inits_and_teardowns_kernel
);

cuda_kernel!(GenerateMemoryAndWitnessValuesUnrolledUnified,
    ab_generate_memory_and_witness_values_unrolled_unified_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledUnifiedOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: *mut u32,
        count: u32,
    )
);

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

pub(crate) fn unified_trace_len(circuit_type: UnrolledCircuitType) -> usize {
    match circuit_type {
        UnrolledCircuitType::Unified | UnrolledCircuitType::Unified22 => {
            circuit_type.get_domain_size()
        }
        _ => panic!(
            "the unified witness launchers require Unified or Unified22, got {circuit_type:?}"
        ),
    }
}

pub(crate) fn generate_memory_values_unrolled_unified(
    circuit_type: UnrolledCircuitType,
    memory_layout: &GKRMemoryLayout,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledUnifiedTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = unified_trace_len(circuit_type);
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), memory_layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = memory_layout.into();
    let oracle = UnrolledUnifiedOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesUnrolledUnifiedArguments::new(layout, oracle, memory, count);
    GenerateMemoryValuesUnrolledUnifiedFunction::default().launch(&config, &args)
}

pub fn generate_memory_and_witness_values_unrolled_memory(
    circuit_type: UnrolledMemoryCircuitType,
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    decoder_lookup_offset: u32,
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
    let layout = UnrolledMemoryLayout::from_parts(layout, decoder_lookup_offset);
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

pub fn generate_memory_and_witness_values_unrolled_non_memory(
    circuit_type: UnrolledNonMemoryCircuitType,
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    decoder_lookup_offset: u32,
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
    let layout = UnrolledMemoryLayout::from_parts(layout, decoder_lookup_offset);
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

/// NOTE (unified two-launch composition): this launcher writes only the per-row
/// machine_state + shuffle_ram columns and does NOT zero the matrix. The unified
/// inits/teardowns columns are produced by a SEPARATE page launch
/// (`generate_memory_and_witness_values_unrolled_inits_and_teardowns`), which
/// `set_to_zero`s the ENTIRE memory matrix before its sparse writes. The i/t page
/// launch MUST therefore run BEFORE this per-row launch, or it will wipe the
/// machine/shuffle columns this kernel produced.
pub fn generate_memory_and_witness_values_unrolled_unified(
    circuit_type: UnrolledCircuitType,
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    decoder_lookup_offset: u32,
    trace: &UnrolledUnifiedTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = unified_trace_len(circuit_type);
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), layout.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let layout = UnrolledMemoryLayout::from_parts(layout, decoder_lookup_offset);
    let aux_layout_data = aux_layout_data.into();
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
        layout,
        aux_layout_data,
        oracle,
        memory,
        witness,
        decoder_lookup_mapping,
        count,
    );
    GenerateMemoryAndWitnessValuesUnrolledUnifiedFunction::default().launch(&config, &args)
}
