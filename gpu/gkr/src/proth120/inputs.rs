use std::sync::Arc;

use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixChunkImpl, DeviceMatrixImpl,
};

use crate::upstream::{GKRCircuitArtifact, PR};

pub struct Proth120GkrWitnessInputs<'a> {
    pub scratch: Arc<DeviceAllocation<PR>>,
    pub scratch_columns: usize,
    pub scratch_stride: usize,
    pub generic_lookup_mapping: DeviceMatrix<'a, u32>,
    pub range_check_16_lookup_mapping: DeviceMatrix<'a, u32>,
    pub range_check_timestamp_lookup_mapping: DeviceMatrix<'a, u32>,
    pub decoder_lookup_mapping: &'a DeviceSlice<u32>,
    pub multiplicities: DeviceMatrix<'a, PR>,
}

impl<'a> Proth120GkrWitnessInputs<'a> {
    pub fn new(
        circuit: &GKRCircuitArtifact<PR>,
        scratch: Arc<DeviceAllocation<PR>>,
        scratch_columns: usize,
        scratch_stride: usize,
        generic_lookup_mapping: DeviceMatrix<'a, u32>,
        range_check_16_lookup_mapping: DeviceMatrix<'a, u32>,
        range_check_timestamp_lookup_mapping: DeviceMatrix<'a, u32>,
        decoder_lookup_mapping: &'a DeviceSlice<u32>,
        multiplicities: DeviceMatrix<'a, PR>,
    ) -> Self {
        let rows = circuit.trace_len;
        assert_eq!(
            scratch_columns, circuit.scratch_space_size,
            "Proth120 scratch columns mismatch"
        );
        assert_eq!(scratch_stride, rows, "Proth120 scratch stride mismatch");
        assert_eq!(
            scratch.len(),
            scratch_columns
                .checked_mul(rows)
                .expect("Proth120 scratch length overflow"),
            "Proth120 scratch allocation length mismatch"
        );
        let check = |name: &str, matrix: &DeviceMatrix<'_, u32>, columns: usize| {
            assert_eq!(matrix.rows(), rows, "Proth120 {name} rows mismatch");
            assert_eq!(
                DeviceMatrixImpl::stride(matrix),
                rows,
                "Proth120 {name} stride mismatch"
            );
            assert_eq!(
                DeviceMatrixImpl::cols(matrix),
                columns,
                "Proth120 {name} columns mismatch"
            );
        };
        check(
            "generic mapping",
            &generic_lookup_mapping,
            circuit.generic_lookups.len(),
        );
        check(
            "range16 mapping",
            &range_check_16_lookup_mapping,
            circuit.range_check_16_lookup_expressions.len(),
        );
        check(
            "timestamp mapping",
            &range_check_timestamp_lookup_mapping,
            circuit.timestamp_range_check_lookup_expressions.len(),
        );
        assert_eq!(
            decoder_lookup_mapping.len(),
            usize::from(circuit.has_decoder_lookup) * rows,
            "Proth120 decoder mapping length mismatch"
        );
        assert_eq!(
            multiplicities.rows(),
            rows,
            "Proth120 multiplicities rows mismatch"
        );
        assert_eq!(
            DeviceMatrixImpl::stride(&multiplicities),
            rows,
            "Proth120 multiplicities stride mismatch"
        );
        assert_eq!(
            DeviceMatrixImpl::cols(&multiplicities),
            circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .len()
                + circuit
                    .witness_layout
                    .multiplicities_columns_for_timestamp_range_check
                    .len()
                + circuit
                    .witness_layout
                    .multiplicities_columns_for_generic_lookup
                    .len(),
            "Proth120 multiplicities columns mismatch"
        );
        Self {
            scratch,
            scratch_columns,
            scratch_stride,
            generic_lookup_mapping,
            range_check_16_lookup_mapping,
            range_check_timestamp_lookup_mapping,
            decoder_lookup_mapping,
            multiplicities,
        }
    }
}
