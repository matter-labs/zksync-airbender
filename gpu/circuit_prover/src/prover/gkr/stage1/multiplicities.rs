use crate::primitives::device_structures::{DeviceMatrixMut, DeviceMatrixMutImpl};
use crate::primitives::field::BF;
use crate::prover::ProverContext;
use crate::upstream::GKRCircuitArtifact;
use era_cudart::result::CudaResult;
use gpu_trace::witness::multiplicities::generate_generic_lookup_multiplicities;

pub(crate) fn generate_range_check_multiplicities_from_mappings(
    circuit: &GKRCircuitArtifact<BF>,
    range_check_16_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_timestamp_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let witness_layout = &circuit.witness_layout;
    let num_witness_cols = witness_layout.total_width;
    assert_eq!(range_check_16_lookup_mapping.stride(), trace_len);
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), trace_len);
    assert_eq!(witness.stride(), trace_len);
    assert_eq!(witness.cols(), num_witness_cols);
    let range_check_16_lookup_multiplicities_range = circuit
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .clone();
    let range_check_16_lookup_multiplicities = &mut witness.slice_mut()
        [range_check_16_lookup_multiplicities_range.start * trace_len
            ..range_check_16_lookup_multiplicities_range.end * trace_len];
    generate_generic_lookup_multiplicities(
        range_check_16_lookup_mapping,
        &mut DeviceMatrixMut::new(range_check_16_lookup_multiplicities, trace_len),
        17, // 16-bit values + 1 sentinel bit
        context,
    )?;
    let range_check_timestamp_lookup_multiplicities_range = circuit
        .witness_layout
        .multiplicities_columns_for_timestamp_range_check
        .clone();
    let range_check_timestamp_lookup_multiplicities = &mut witness.slice_mut()
        [range_check_timestamp_lookup_multiplicities_range.start * trace_len
            ..range_check_timestamp_lookup_multiplicities_range.end * trace_len];
    generate_generic_lookup_multiplicities(
        range_check_timestamp_lookup_mapping,
        &mut DeviceMatrixMut::new(range_check_timestamp_lookup_multiplicities, trace_len),
        20, // 19-bit values (TIMESTAMP_COLUMNS_NUM_BITS) + 1 sentinel bit
        context,
    )?;
    Ok(())
}
