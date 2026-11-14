use super::{L1Bundle, ProofCounts, ProofTarget, ProofTimingsMs, SecurityLevel, SoundnessMode};
use full_statement_verifier::program_proof::ProgramProof;
use serde::{Deserialize, Serialize};
use setups::Setups;

/// The current proof artifact schema.
pub const ARTIFACT_SCHEMA_VERSION: u32 = 5;

/// JSON proof artifact, schema v5. `proof` + `setups` are enough to verify natively; `chain_end_params` is the ordered list of layer
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
    pub batch_id: u64,
    /// `proof.executed_cycles()` of the artifact's (final) proof layer.
    pub cycles: u64,
    /// `executed_cycles()` of the base layer: the program's own cycle count.
    pub program_cycles: u64,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    #[serde(skip)]
    pub timings_ms: ProofTimingsMs,
    pub proof_counts: ProofCounts,
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final,
    /// compression_0, compression_1, compression_2]`, one entry per proven layer.
    pub chain_end_params: Vec<[u32; 8]>,
    /// Recursion-chain state AFTER this artifact's layer.
    pub chain_hash: [u32; 8],
    pub chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the pipeline used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    pub blake_unrolled: String,
    pub blake_bridge: String,
    pub blake_final: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub l1: Option<L1Bundle>,
    pub proof: ProgramProof,
    pub setups: Setups,
}

fn deserialize_artifact_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version != ARTIFACT_SCHEMA_VERSION {
        return Err(<D::Error as serde::de::Error>::custom(format!(
            "artifact schema version {version} is not the supported {ARTIFACT_SCHEMA_VERSION}; regenerate"
        )));
    }
    Ok(version)
}

impl ProofArtifact {
    /// Admit the caller's soundness mode and the fixed pipeline Blake modes.
    pub fn validate_expected_mode(&self, expected: SoundnessMode) -> Result<(), String> {
        for tag in [&self.blake_unrolled, &self.blake_bridge, &self.blake_final] {
            if tag != verifier_common::fsv_binaries::BlakeMode::Compression.tag() {
                return Err(format!(
                    "artifact Blake mode {tag:?} does not match the fixed pipeline mode"
                ));
            }
        }
        // Wrap artifacts exist only in PessimisticConjecture: neither an ethproofs request nor
        // an ethproofs label reaches a wrap verifier or continuation.
        for mode in [expected, self.soundness_mode] {
            super::assert_target_mode(self.target, mode);
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
    use crate::BlakeMode;

    fn artifact(mode: SoundnessMode) -> ProofArtifact {
        ProofArtifact {
            schema_version: ARTIFACT_SCHEMA_VERSION,
            security_level: SecurityLevel::Sec100,
            soundness_mode: mode,
            target: ProofTarget::Base,
            batch_id: 0,
            cycles: 0,
            program_cycles: 0,
            program_bin_keccak: [0; 32],
            program_text_keccak: [0; 32],
            timings_ms: ProofTimingsMs::default(),
            proof_counts: ProofCounts::default(),
            chain_end_params: vec![[0; 8]],
            l1: None,
            chain_hash: [0; 8],
            chain_preimage: [0; 16],
            blake_unrolled: BlakeMode::Compression.tag().to_owned(),
            blake_bridge: BlakeMode::Compression.tag().to_owned(),
            blake_final: BlakeMode::Compression.tag().to_owned(),
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
    fn transient_proving_metadata_is_not_stored() {
        let mut artifact = artifact(SoundnessMode::DEFAULT);
        artifact.timings_ms.total_ms = 123;
        let value = serde_json::to_value(&artifact).unwrap();
        assert!(value.get("backend").is_none());
        assert!(value.get("timings_ms").is_none());
        let decoded: ProofArtifact = serde_json::from_value(value).unwrap();
        assert_eq!(decoded.timings_ms.total_ms, 0);
    }

    #[test]
    fn only_current_schema_decodes() {
        for version in [
            ARTIFACT_SCHEMA_VERSION - 1,
            ARTIFACT_SCHEMA_VERSION,
            ARTIFACT_SCHEMA_VERSION + 1,
        ] {
            let mut value = serde_json::to_value(artifact(SoundnessMode::DEFAULT)).unwrap();
            value["schema_version"] = version.into();
            let decoded = serde_json::from_value::<ProofArtifact>(value);
            assert_eq!(decoded.is_ok(), version == ARTIFACT_SCHEMA_VERSION);
        }
    }

    #[test]
    fn committed_chain_encoding() {
        for &mode in SoundnessMode::ALL {
            for chain in proof_fixtures::CHAINS {
                let path = proof_fixtures::chain_artifact(mode.file_suffix(), chain);
                let artifact: ProofArtifact = proof_fixtures::read_file(&path);
                let (target, entries) = match chain {
                    "base" => (ProofTarget::Base, 1),
                    "unified" => (ProofTarget::RecursionUnified, 3),
                    "unrolled" => (ProofTarget::RecursionUnrolled, 2),
                    "unrolled_unified" => (ProofTarget::RecursionUnified, 4),
                    _ => unreachable!(),
                };
                assert_eq!(artifact.soundness_mode, mode);
                assert_eq!(artifact.target, target);
                assert_eq!(artifact.program_cycles, 97);
                assert_eq!(artifact.chain_end_params.len(), entries);
                assert_eq!(
                    proof_fixtures::encode(&artifact, Vec::new()),
                    std::fs::read(path).unwrap()
                );
            }
        }
    }
}
