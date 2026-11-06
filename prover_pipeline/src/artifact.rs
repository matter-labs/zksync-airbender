use super::{
    BlakeMode, ProofCounts, ProofTarget, ProofTimingsMs, ProverBackend, SecurityLevel,
    SoundnessMode,
};
use full_statement_verifier::program_proof::ProgramProof;
use serde::{Deserialize, Serialize};
use setups::Setups;

pub const ARTIFACT_SCHEMA_VERSION: u32 = 4;

fn default_blake_tag() -> String {
    BlakeMode::Compression.tag().to_owned()
}

/// JSON proof artifact, schema v4. `proof` + `setups` are enough to verify natively; `chain_end_params` is the ordered list of layer
/// `end_params` from base onward, from which the recursion chain state after
/// this artifact's layer (`chain_hash` / `chain_preimage`) is reconstructed
/// for staged continuation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofArtifact {
    #[serde(deserialize_with = "deserialize_artifact_version")]
    pub schema_version: u32,
    pub security_level: SecurityLevel,
    pub soundness_mode: SoundnessMode,
    pub target: ProofTarget,
    pub backend: ProverBackend,
    pub batch_id: u64,
    /// `proof.executed_cycles()` of the artifact's (final) proof layer.
    pub cycles: u64,
    /// `executed_cycles()` of the base layer: the program's own cycle count.
    pub program_cycles: u64,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    pub timings_ms: ProofTimingsMs,
    pub proof_counts: ProofCounts,
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final]`.
    pub chain_end_params: Vec<[u32; 8]>,
    /// Recursion-chain state AFTER this artifact's layer.
    pub chain_hash: [u32; 8],
    pub chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the pipeline used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    #[serde(default = "default_blake_tag")]
    pub blake_unrolled: String,
    #[serde(default = "default_blake_tag")]
    pub blake_bridge: String,
    #[serde(default = "default_blake_tag")]
    pub blake_final: String,
    pub proof: ProgramProof,
    pub setups: Setups,
}

fn deserialize_artifact_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version != ARTIFACT_SCHEMA_VERSION {
        return Err(<D::Error as serde::de::Error>::custom(unsupported_version(
            version,
        )));
    }
    Ok(version)
}

fn unsupported_version(version: u32) -> String {
    format!(
        "UnsupportedArtifactVersion: {version}; the supported version is {ARTIFACT_SCHEMA_VERSION}"
    )
}

impl ProofArtifact {
    /// Validate the caller's acceptance policy before source loading or backend work: the
    /// schema version (decoding checks it too; this covers artifacts built in memory) and the
    /// soundness mode.
    pub fn validate_expected_mode(&self, expected: SoundnessMode) -> Result<(), String> {
        if self.schema_version != ARTIFACT_SCHEMA_VERSION {
            return Err(unsupported_version(self.schema_version));
        }
        if self.soundness_mode != expected {
            return Err(format!(
                "SoundnessModeMismatch: expected {expected:?}, artifact is {:?}",
                self.soundness_mode
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn artifact(mode: SoundnessMode) -> ProofArtifact {
        ProofArtifact {
            schema_version: ARTIFACT_SCHEMA_VERSION,
            security_level: SecurityLevel::Sec100,
            soundness_mode: mode,
            target: ProofTarget::Base,
            backend: ProverBackend::Cpu,
            batch_id: 0,
            cycles: 0,
            program_cycles: 0,
            program_bin_keccak: [0; 32],
            program_text_keccak: [0; 32],
            timings_ms: ProofTimingsMs::default(),
            proof_counts: ProofCounts::default(),
            chain_end_params: vec![[0; 8]],
            chain_hash: [0; 8],
            chain_preimage: [0; 16],
            blake_unrolled: default_blake_tag(),
            blake_bridge: default_blake_tag(),
            blake_final: default_blake_tag(),
            proof: ProgramProof {
                riscv_proofs: Default::default(),
                compiled_riscv_circuits: Default::default(),
                inits_and_teardown_proofs: Vec::new(),
                inits_and_teardowns_circuit: None,
                delegation_proofs: Default::default(),
                compiled_delegation_circuits: Default::default(),
                register_final_values: Vec::new(),
                final_pc: 0,
                final_timestamp: 4,
                end_params: [0; 8],
                recursion_chain_preimage: None,
                recursion_chain_hash: None,
                pow_challenge: 0,
                num_it_circuits: None,
            },
            setups: Setups::new(),
        }
    }

    #[test]
    fn incompatible_artifact_metadata_is_refused() {
        for &mode in SoundnessMode::ALL {
            let original = artifact(mode);
            let bytes = serde_json::to_vec(&original).unwrap();
            let decoded: ProofArtifact = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(decoded.schema_version, 4);
            assert_eq!(decoded.soundness_mode, mode);
            decoded.validate_expected_mode(mode).unwrap();
        }
        let mut value = serde_json::to_value(artifact(SoundnessMode::DEFAULT)).unwrap();
        value.as_object_mut().unwrap().remove("soundness_mode");
        assert!(serde_json::from_value::<ProofArtifact>(value.clone())
            .unwrap_err()
            .to_string()
            .contains("missing field `soundness_mode`"));
        for (invalid, expected_error) in [
            (serde_json::Value::Null, "invalid type: null"),
            (serde_json::json!("unknown"), "unknown variant `unknown`"),
        ] {
            value["soundness_mode"] = invalid;
            let error = serde_json::from_value::<ProofArtifact>(value.clone())
                .unwrap_err()
                .to_string();
            assert!(error.contains(expected_error), "{error}");
        }

        assert!(
            serde_json::from_str::<ProofArtifact>(r#"{"schema_version":3}"#)
                .unwrap_err()
                .to_string()
                .contains("UnsupportedArtifactVersion: 3")
        );
        let mut old = artifact(SoundnessMode::DEFAULT);
        old.schema_version = 3;
        assert!(old
            .validate_expected_mode(SoundnessMode::DEFAULT)
            .unwrap_err()
            .starts_with("UnsupportedArtifactVersion:"));
        let source = crate::ProgramSource::legacy_binaries_from_bin("/missing/program.bin");
        for &mode in SoundnessMode::ALL {
            let expected = SoundnessMode::ALL
                .iter()
                .copied()
                .find(|&other| other != mode)
                .unwrap();
            let error =
                crate::verify_artifact_in_mode(&artifact(mode), &source, expected).unwrap_err();
            assert!(error.starts_with("SoundnessModeMismatch:"), "{error}");
        }
    }
}
