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

/// JSON proof artifact, schema v4; v3 decodes explicitly as legacy pessimistic. `proof` + `setups` are enough to
/// verify natively; `chain_end_params` is the ordered list of layer
/// `end_params` from base onward, from which the recursion chain state after
/// this artifact's layer (`chain_hash` / `chain_preimage`) is reconstructed
/// for staged continuation.
#[derive(Clone, Debug, Serialize)]
pub struct ProofArtifact {
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
    pub l1: Option<L1Bundle>,
    pub proof: ProgramProof,
    pub setups: Setups,
}

#[derive(Deserialize)]
struct ProofArtifactWire {
    #[serde(deserialize_with = "deserialize_artifact_version")]
    schema_version: u32,
    security_level: SecurityLevel,
    soundness_mode: Option<SoundnessMode>,
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    /// `proof.executed_cycles()` of the artifact's (final) proof layer.
    cycles: u64,
    /// `executed_cycles()` of the base layer: the program's own cycle count.
    program_cycles: u64,
    program_bin_keccak: [u8; 32],
    program_text_keccak: [u8; 32],
    timings_ms: ProofTimingsMs,
    proof_counts: ProofCounts,
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final, feeder_1, ..]`.
    chain_end_params: Vec<[u32; 8]>,
    #[serde(default)]
    feeder_layers: u32,
    /// Recursion-chain state AFTER this artifact's layer.
    chain_hash: [u32; 8],
    chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the pipeline used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    #[serde(default = "default_blake_tag")]
    blake_unrolled: String,
    #[serde(default = "default_blake_tag")]
    blake_bridge: String,
    #[serde(default = "default_blake_tag")]
    blake_final: String,
    #[serde(default)]
    l1: Option<L1Bundle>,
    proof: ProgramProof,
    setups: Setups,
}

fn deserialize_artifact_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version != 3 && version != ARTIFACT_SCHEMA_VERSION {
        return Err(<D::Error as serde::de::Error>::custom(format!("UnsupportedArtifactVersion: {version}; supported versions are 3 (legacy pessimistic) and 4")));
    }
    Ok(version)
}

impl<'de> Deserialize<'de> for ProofArtifact {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = ProofArtifactWire::deserialize(deserializer)?;
        let mode = match (wire.schema_version, wire.soundness_mode) {
            (3, None | Some(SoundnessMode::PessimisticConjecture)) => {
                SoundnessMode::PessimisticConjecture
            }
            (3, Some(_)) => {
                return Err(<D::Error as serde::de::Error>::custom(
                    "ConflictingLegacySoundnessMode: schema v3 is legacy pessimistic",
                ))
            }
            (ARTIFACT_SCHEMA_VERSION, Some(mode)) => mode,
            (_, None) => {
                return Err(<D::Error as serde::de::Error>::custom(
                    "MissingSoundnessMode: schema v4 requires soundness_mode",
                ))
            }
            (version, _) => {
                return Err(<D::Error as serde::de::Error>::custom(format!(
                    "UnsupportedArtifactVersion: {version}"
                )))
            }
        };
        Ok(Self {
            schema_version: wire.schema_version,
            security_level: wire.security_level,
            soundness_mode: mode,
            target: wire.target,
            backend: wire.backend,
            batch_id: wire.batch_id,
            cycles: wire.cycles,
            program_cycles: wire.program_cycles,
            program_bin_keccak: wire.program_bin_keccak,
            program_text_keccak: wire.program_text_keccak,
            timings_ms: wire.timings_ms,
            proof_counts: wire.proof_counts,
            chain_end_params: wire.chain_end_params,
            feeder_layers: wire.feeder_layers,
            chain_hash: wire.chain_hash,
            chain_preimage: wire.chain_preimage,
            blake_unrolled: wire.blake_unrolled,
            blake_bridge: wire.blake_bridge,
            blake_final: wire.blake_final,
            l1: wire.l1,
            proof: wire.proof,
            setups: wire.setups,
        })
    }
}
impl ProofArtifact {
    pub(crate) fn validate_schema(&self) -> Result<(), String> {
        match self.schema_version {
            3 if self.soundness_mode != SoundnessMode::PessimisticConjecture => {
                return Err(
                    "ConflictingLegacySoundnessMode: schema v3 is legacy pessimistic".to_owned(),
                )
            }
            3 | ARTIFACT_SCHEMA_VERSION => {}
            version => {
                return Err(format!(
                    "UnsupportedArtifactVersion: {version}; supported versions are 3 and 4"
                ))
            }
        }
        Ok(())
    }

    /// Validate the caller's acceptance policy before source loading or backend work.
    pub fn validate_expected_mode(&self, expected: SoundnessMode) -> Result<(), String> {
        self.validate_schema()?;
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
            .contains("MissingSoundnessMode"));
        for invalid in [serde_json::Value::Null, serde_json::json!("unknown")] {
            value["soundness_mode"] = invalid;
            let expected_error = if value["soundness_mode"].is_null() {
                "MissingSoundnessMode"
            } else {
                "unknown variant"
            };
            assert!(serde_json::from_value::<ProofArtifact>(value.clone())
                .unwrap_err()
                .to_string()
                .contains(expected_error));
        }
    }

    #[test]
    fn v3_is_explicitly_legacy_pessimistic() {
        let mut value = serde_json::to_value(artifact(SoundnessMode::DEFAULT)).unwrap();
        value["schema_version"] = serde_json::json!(3);
        value.as_object_mut().unwrap().remove("soundness_mode");
        let decoded: ProofArtifact = serde_json::from_value(value.clone()).unwrap();
        assert_eq!(decoded.schema_version, 3);
        assert_eq!(decoded.soundness_mode, SoundnessMode::PessimisticConjecture);
        assert!(decoded
            .validate_expected_mode(SoundnessMode::EthproofsSoundnessCalc)
            .unwrap_err()
            .contains("SoundnessModeMismatch"));
        value["soundness_mode"] =
            serde_json::to_value(SoundnessMode::EthproofsSoundnessCalc).unwrap();
        assert!(serde_json::from_value::<ProofArtifact>(value)
            .unwrap_err()
            .to_string()
            .contains("ConflictingLegacySoundnessMode"));
    }

    #[test]
    fn unknown_schema_and_duplicate_metadata_are_rejected() {
        for version in [0, 2, 5, 6, u32::MAX] {
            // A version error is explicit even without a proof payload.
            let value = serde_json::json!({"schema_version": version});
            assert!(serde_json::from_value::<ProofArtifact>(value)
                .unwrap_err()
                .to_string()
                .contains("UnsupportedArtifactVersion"));
        }
        let error =
            serde_json::from_str::<ProofArtifact>(r#"{"schema_version":4,"schema_version":3}"#)
                .unwrap_err();
        assert!(error.to_string().contains("duplicate field"));
    }

    #[test]
    fn expected_mode_rejection_precedes_source_loading() {
        let source =
            crate::ProgramSource::legacy_binaries_from_bin(Path::new("/missing/task-s.bin"));
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
