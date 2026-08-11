use super::circuit_type::CircuitType;
use super::generated_fingerprints::expected_generated_witness_fingerprint;
use crate::upstream::GKRCircuitArtifact;
use gpu_core::primitives::field::BF;
use gpu_gkr_model::fingerprint::{witness_artifact_fingerprint, WitnessArtifactFingerprint};

#[derive(Debug)]
pub enum GeneratedWitnessArtifactError {
    Serialize {
        circuit_type: CircuitType,
        message: String,
    },
    FingerprintMismatch {
        circuit_type: CircuitType,
        expected: WitnessArtifactFingerprint,
        actual: WitnessArtifactFingerprint,
    },
    DecoderWitnessInMemory {
        circuit_type: CircuitType,
    },
}

impl std::fmt::Display for GeneratedWitnessArtifactError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Serialize {
                circuit_type,
                message,
            } => write!(
                formatter,
                "failed to fingerprint generated witness artifact for {circuit_type:?}: {message}"
            ),
            Self::FingerprintMismatch {
                circuit_type,
                expected,
                actual,
            } => write!(
                formatter,
                "generated witness artifact fingerprint mismatch for {circuit_type:?}: expected {expected:08x?}, actual {actual:08x?}"
            ),
            Self::DecoderWitnessInMemory { circuit_type } => write!(
                formatter,
                "generated witness artifact for {circuit_type:?} uses unsupported decoder witness in memory"
            ),
        }
    }
}

impl std::error::Error for GeneratedWitnessArtifactError {}

pub fn validate_generated_witness_artifact(
    circuit_type: CircuitType,
    artifact: &GKRCircuitArtifact<BF>,
) -> Result<(), GeneratedWitnessArtifactError> {
    let Some(expected) = expected_generated_witness_fingerprint(circuit_type) else {
        debug_assert!(matches!(
            circuit_type,
            CircuitType::Unrolled(super::circuit_type::UnrolledCircuitType::InitsAndTeardowns)
        ));
        return Ok(());
    };

    if artifact.has_decoder_lookup
        && artifact
            .memory_layout
            .decoder_input
            .as_ref()
            .is_some_and(|decoder| decoder.decoder_witness_is_in_memory)
    {
        return Err(GeneratedWitnessArtifactError::DecoderWitnessInMemory { circuit_type });
    }

    let actual = witness_artifact_fingerprint(artifact).map_err(|error| {
        GeneratedWitnessArtifactError::Serialize {
            circuit_type,
            message: error.to_string(),
        }
    })?;
    if actual != expected {
        return Err(GeneratedWitnessArtifactError::FingerprintMismatch {
            circuit_type,
            expected,
            actual,
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::validate_generated_witness_artifact;
    use crate::upstream::GKRCircuitArtifact;
    use crate::witness::circuit_type::{
        CircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };
    use gpu_core::primitives::field::BF;
    use std::fs::File;
    use std::path::PathBuf;

    fn load_artifact(name: &str) -> GKRCircuitArtifact<BF> {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join(format!("../../cs/compiled_circuits/{name}_layout_gkr.json"));
        serde_json::from_reader(File::open(path).expect("open committed layout"))
            .expect("deserialize committed layout")
    }

    fn add_sub_type() -> CircuitType {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        ))
    }

    #[test]
    fn cpu_generated_witness_artifact_accepts_committed_layout() {
        let artifact = load_artifact("add_sub_lui_auipc_mop");
        validate_generated_witness_artifact(add_sub_type(), &artifact)
            .expect("accept committed artifact");
    }

    #[test]
    fn cpu_generated_witness_artifact_rejects_layout_drift() {
        let mut artifact = load_artifact("add_sub_lui_auipc_mop");
        artifact.timestamp_range_check_lookup_expressions[2].lookup_set_index += 1;
        let error = validate_generated_witness_artifact(add_sub_type(), &artifact)
            .expect_err("reject drifted artifact");
        assert!(error.to_string().contains("fingerprint mismatch"));
    }

    #[test]
    fn cpu_generated_witness_artifact_allows_inits_and_teardowns() {
        let artifact = load_artifact("inits_and_teardowns");
        validate_generated_witness_artifact(
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            &artifact,
        )
        .expect("inits/teardowns has no generated CUDA body");
    }

    #[test]
    fn cpu_generated_witness_artifact_rejects_decoder_in_memory() {
        let mut artifact = load_artifact("add_sub_lui_auipc_mop");
        artifact
            .memory_layout
            .decoder_input
            .as_mut()
            .expect("add/sub decoder")
            .decoder_witness_is_in_memory = true;
        let error = validate_generated_witness_artifact(add_sub_type(), &artifact)
            .expect_err("reject unsupported decoder placement");
        assert!(error.to_string().contains("decoder witness in memory"));
    }
}
