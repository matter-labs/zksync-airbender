use super::{
    BlakeMode, L1Bundle, ProofCounts, ProofTarget, ProofTimingsMs, ProverBackend, SecurityLevel,
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
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final,
    /// feeder_1, .., feeder_k]`, one entry per proven layer.
    pub chain_end_params: Vec<[u32; 8]>,
    /// Number of L1 feeder layers in `chain_end_params` (0 before the feeder
    /// stage, `1..=MAX_FEEDER_LAYERS` after it). Validated routing metadata:
    /// consecutive feeder layers prove the same binary on the same machine,
    /// so their end params are equal and the VM-authenticated chain hash
    /// (which deduplicates equal consecutive entries) cannot attest this
    /// count; verification rejects an isolated length mismatch only.
    #[serde(default)]
    pub feeder_layers: u32,
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
    #[serde(default)]
    pub l1: Option<L1Bundle>,
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
    use std::path::Path;

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
            feeder_layers: 0,
            chain_hash: [0; 8],
            chain_preimage: [0; 16],
            blake_unrolled: default_blake_tag(),
            blake_bridge: default_blake_tag(),
            blake_final: default_blake_tag(),
            l1: None,
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
    fn v4_requires_a_known_explicit_mode() {
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
    }

    #[test]
    fn in_memory_artifacts_of_another_schema_are_refused() {
        let mut other = artifact(SoundnessMode::DEFAULT);
        other.schema_version = 3;
        assert_eq!(
            other.validate_expected_mode(SoundnessMode::DEFAULT),
            Err("UnsupportedArtifactVersion: 3; the supported version is 4".to_owned())
        );
    }

    #[test]
    fn unknown_schema_and_duplicate_metadata_are_rejected() {
        for version in [0, 2, 3, 5, 6, u32::MAX] {
            // A version error is explicit even without a proof payload.
            let value = serde_json::json!({"schema_version": version});
            assert!(serde_json::from_value::<ProofArtifact>(value)
                .unwrap_err()
                .to_string()
                .contains(&format!(
                    "UnsupportedArtifactVersion: {version}; the supported version is 4"
                )));
        }
        let error =
            serde_json::from_str::<ProofArtifact>(r#"{"schema_version":4,"schema_version":3}"#)
                .unwrap_err();
        assert!(error.to_string().contains("duplicate field"));
    }

    #[test]
    fn expected_mode_rejection_precedes_source_loading() {
        let source =
            crate::ProgramSource::legacy_binaries_from_bin(Path::new("/missing/program.bin"));
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
