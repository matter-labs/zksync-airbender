use super::relations::{Proth120LookupExpressions, Proth120LookupRelations};
use super::Proth120WitnessBuffers;
use crate::upstream::GKRCircuitArtifact;
use crate::witness::memory_unrolled::{AuxLayoutData, UnrolledMemoryLayout};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledUnifiedOracle, UnrolledUnifiedTraceDevice,
};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixImpl, DeviceMatrixMutImpl};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_ops::simple::set_to_zero;

cuda_kernel!(GenerateFusedProth120Unified,
    ab_pr_generate_fused_unified_reduced_machine_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledUnifiedOracle,
        generic_lookup_tables: *const PR,
        memory: *mut PR,
        witness: *mut PR,
        scratch: *mut PR,
        generic_lookup_mapping: *mut u32,
        decoder_lookup_mapping: *mut u32,
        range_check_16_lookup_expressions: Proth120LookupExpressions,
        range_check_16_lookup_mapping: *mut u32,
        range_check_timestamp_lookup_expressions: Proth120LookupExpressions,
        range_check_timestamp_lookup_mapping: *mut u32,
        stride: u32,
        count: u32,
    )
);

pub fn generate_fused_values(
    circuit: &GKRCircuitArtifact<PR>,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledUnifiedTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<PR>,
    relations: &Proth120LookupRelations,
    outputs: &mut Proth120WitnessBuffers<'_>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = circuit.trace_len;
    let (range_check_16_count, timestamp_count) = relations.counts();
    assert_eq!(
        range_check_16_count,
        circuit.range_check_16_lookup_expressions.len()
    );
    assert_eq!(
        timestamp_count,
        circuit.timestamp_range_check_lookup_expressions.len()
    );
    let Proth120WitnessBuffers {
        memory,
        witness,
        scratch,
        generic_lookup_mapping,
        range_check_16_lookup_mapping,
        range_check_timestamp_lookup_mapping,
        decoder_lookup_mapping,
    } = outputs;
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), circuit.memory_layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), circuit.witness_layout.total_width);
    assert_eq!(scratch.stride(), count);
    assert_eq!(scratch.cols(), circuit.scratch_space_size);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(
        generic_lookup_tables.cols(),
        circuit.generic_lookup_tables_width
    );
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(generic_lookup_mapping.cols(), circuit.generic_lookups.len());
    assert_eq!(
        decoder_lookup_mapping.len(),
        usize::from(circuit.has_decoder_lookup) * count
    );
    assert_eq!(range_check_16_lookup_mapping.stride(), count);
    assert_eq!(range_check_16_lookup_mapping.cols(), range_check_16_count);
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), count);
    assert_eq!(range_check_timestamp_lookup_mapping.cols(), timestamp_count);
    assert!(trace.tracing_data.len() <= count);
    assert!(count <= u32::MAX as usize);
    set_to_zero(witness.slice_mut(), stream)?;
    set_to_zero(scratch.slice_mut(), stream)?;
    let count = count as u32;
    let layout = UnrolledMemoryLayout::from_parts(
        &circuit.memory_layout,
        circuit.offset_for_decoder_table as u32,
    );
    let aux_layout_data = AuxLayoutData::from(&circuit.aux_layout_data);
    let oracle = UnrolledUnifiedOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
    };
    let (range_check_16_lookup_expressions, range_check_timestamp_lookup_expressions) =
        relations.expressions();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateFusedProth120UnifiedArguments::new(
        layout,
        aux_layout_data,
        oracle,
        generic_lookup_tables.as_ptr(),
        memory.as_mut_ptr(),
        witness.as_mut_ptr(),
        scratch.as_mut_ptr(),
        generic_lookup_mapping.as_mut_ptr(),
        decoder_lookup_mapping.as_mut_ptr(),
        range_check_16_lookup_expressions,
        range_check_16_lookup_mapping.as_mut_ptr(),
        range_check_timestamp_lookup_expressions,
        range_check_timestamp_lookup_mapping.as_mut_ptr(),
        count,
        count,
    );
    GenerateFusedProth120UnifiedFunction::default().launch(&config, &args)
}
