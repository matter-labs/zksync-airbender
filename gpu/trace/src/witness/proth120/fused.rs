use super::relations::{
    LookupRelationsPr, Proth120LookupExpressions, RANGE_CHECK_16_RELATIONS, TIMESTAMP_RELATIONS,
};
use super::Proth120WitnessBuffers;
use crate::upstream::GKRCircuitArtifact;
use crate::witness::memory_unrolled::{AuxLayoutData, UnrolledMemoryLayout};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledUnifiedOracle, UnrolledUnifiedTraceDevice,
};
use era_cudart::cuda_kernel_declaration;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::DeviceMatrixImpl;
use gpu_core::primitives::field::PR;

cuda_kernel_declaration!(ab_pr_generate_fused_unified_reduced_machine_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledUnifiedOracle,
        generic_lookup_tables: *const PR,
        memory: *mut PR,
        witness: *mut PR,
        scratch: *mut PR,
        generic_lookup_mapping: *mut u32,
        decoder_lookup_mapping: *mut u32,
        range_check_16_lookup_expressions: Proth120LookupExpressions<RANGE_CHECK_16_RELATIONS>,
        range_check_16_lookup_mapping: *mut u32,
        range_check_timestamp_lookup_expressions: Proth120LookupExpressions<TIMESTAMP_RELATIONS>,
        range_check_timestamp_lookup_mapping: *mut u32,
        stride: u32,
        count: u32,
));

#[repr(C)]
struct FusedArgumentsLayout {
    layout: UnrolledMemoryLayout,
    aux_layout_data: AuxLayoutData,
    oracle: UnrolledUnifiedOracle,
    generic_lookup_tables: *const PR,
    memory: *mut PR,
    witness: *mut PR,
    scratch: *mut PR,
    generic_lookup_mapping: *mut u32,
    decoder_lookup_mapping: *mut u32,
    range_check_16: Proth120LookupExpressions<RANGE_CHECK_16_RELATIONS>,
    range_check_16_mapping: *mut u32,
    timestamp: Proth120LookupExpressions<TIMESTAMP_RELATIONS>,
    timestamp_mapping: *mut u32,
    stride: u32,
    count: u32,
}
const _: () = assert!(size_of::<FusedArgumentsLayout>() <= 32764);

pub fn generate_fused_values(
    circuit: &GKRCircuitArtifact<PR>,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    trace: &UnrolledUnifiedTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<PR>,
    relations: &LookupRelationsPr,
    outputs: &mut Proth120WitnessBuffers<'_>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let Proth120WitnessBuffers {
        memory,
        witness,
        scratch,
        generic_lookup_mapping,
        range_check_16_lookup_mapping,
        range_check_timestamp_lookup_mapping,
        decoder_lookup_mapping,
    } = outputs;
    crate::witness::witness_unrolled::launch_fused_unified(
        circuit,
        decoder_table,
        trace,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        generic_lookup_mapping,
        decoder_lookup_mapping,
        range_check_16_lookup_mapping,
        range_check_timestamp_lookup_mapping,
        relations.range_check_16,
        relations.timestamp,
        stream,
        true,
        ab_pr_generate_fused_unified_reduced_machine_kernel,
    )
}
