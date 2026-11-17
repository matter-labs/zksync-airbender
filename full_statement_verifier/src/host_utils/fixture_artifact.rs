//! Read-only projection of a committed CLI chain artifact.

use crate::program_proof::ProgramProof;
use serde::Deserialize;
use setups::Setups;
use sha3::{Digest, Keccak256};
use verifier_common::prover::definitions::{SecurityLevel, SoundnessMode};

#[derive(Debug, Deserialize, PartialEq, Eq)]
pub enum ProofTarget {
    Base,
    RecursionUnrolled,
    RecursionUnified,
    Compression,
}

#[derive(Deserialize)]
pub struct ChainArtifact {
    schema_version: u32,
    pub security_level: SecurityLevel,
    pub soundness_mode: SoundnessMode,
    pub target: ProofTarget,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    pub chain_hash: [u32; 8],
    pub proof: ProgramProof,
    pub setups: Setups,
}

impl ChainArtifact {
    pub fn load(mode: SoundnessMode, chain: &str) -> Self {
        let artifact: Self =
            proof_fixtures::read_file(proof_fixtures::chain_artifact(mode.file_suffix(), chain));
        assert_eq!(artifact.schema_version, 5);
        assert_eq!(artifact.soundness_mode, mode);
        let target = match chain {
            "base" => ProofTarget::Base,
            "unrolled" => ProofTarget::RecursionUnrolled,
            "unified" | "unrolled_unified" => ProofTarget::RecursionUnified,
            "compression" => ProofTarget::Compression,
            _ => unreachable!(),
        };
        assert_eq!(artifact.target, target);
        let bin = proof_fixtures::root().join("examples/basic_fibonacci/app.bin");
        let bin_hash: [u8; 32] = Keccak256::digest(std::fs::read(&bin).unwrap()).into();
        let text_hash: [u8; 32] =
            Keccak256::digest(std::fs::read(bin.with_extension("text")).unwrap()).into();
        assert_eq!(artifact.program_bin_keccak, bin_hash);
        assert_eq!(artifact.program_text_keccak, text_hash);
        artifact
    }
}
