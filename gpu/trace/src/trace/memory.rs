use crate::upstream::{BaseColumns, BaseCommitmentGeometry, GKRCircuitArtifact};

/// Field-independent shape binding for separate or concatenated stage1 storage.
pub fn validate_stage1_commitment_geometry<F: crate::upstream::PrimeField>(
    geometry: &BaseCommitmentGeometry,
    compiled_circuit: &GKRCircuitArtifact<F>,
) {
    assert_eq!(
        geometry.logical_columns(),
        BaseColumns::of(compiled_circuit),
        "memory precommit columns disagree with compiled circuit"
    );
    assert_eq!(
        1usize << geometry.trace_len_log2(),
        compiled_circuit.trace_len,
        "memory precommit trace length disagrees with compiled circuit"
    );
}
