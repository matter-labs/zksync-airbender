use super::{
    ProofCounts, ProofTarget, ProofTimingsMs, ProverBackend, SecurityLevel, SoundnessMode,
};
use full_statement_verifier::program_proof::ProgramProof;
use serde::{Deserialize, Serialize};
use setups::Setups;

pub const ARTIFACT_SCHEMA_VERSION: u32 = 4;

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
    pub blake_unrolled: String,
    pub blake_bridge: String,
    pub blake_final: String,
    pub proof: ProgramProof,
    pub setups: Setups,
}

fn deserialize_artifact_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version != ARTIFACT_SCHEMA_VERSION {
        return Err(<D::Error as serde::de::Error>::custom(format!(
            "artifact schema version {version} is not the supported {ARTIFACT_SCHEMA_VERSION}"
        )));
    }
    Ok(version)
}

impl ProofArtifact {
    /// Check the caller's soundness mode before source loading or backend work. Decoding
    /// already rejects any other schema version.
    pub fn validate_expected_mode(&self, expected: SoundnessMode) -> Result<(), String> {
        if self.soundness_mode != expected {
            return Err(format!(
                "SoundnessModeMismatch: expected {expected:?}, artifact is {:?}",
                self.soundness_mode
            ));
        }
        Ok(())
    }
}
