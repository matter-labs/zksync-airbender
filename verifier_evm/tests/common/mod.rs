//! Versioned inputs shared by contract generation and proof serialization.
#![allow(dead_code)] // Each integration-test binary uses a different subset.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::gkr::prover_config::example_configs::l1_wrap_2p22;
use prover::gkr::prover_config::ProverConfig;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use std::path::{Path, PathBuf};
use trace_and_split::setups::program_setups::find_binary_exit_point;

pub type Circuit = GKRCircuitArtifact<Proth120>;
pub type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

#[derive(Clone, Copy)]
pub enum ExitPcSource {
    Frozen(u32),
    Binary(&'static str),
}

#[derive(Clone, Copy)]
pub struct Version {
    pub name: &'static str,
    pub layout: &'static str,
    pub config: fn(SecurityLevel) -> ProverConfig,
    pub pack_log2: usize,
    pub external_pow_floor: u32,
    pub exit_pc: ExitPcSource,
    pub proof: &'static str,
    pub aux: &'static str,
    pub contracts_root: &'static str,
    pub data_root: &'static str,
    pub pow_cap: u32,
    pub gkr_pow_cap: u32,
}

pub const L1_WRAP_2P22: Version = Version {
    name: "2p22",
    layout: "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    config: l1_wrap_2p22::packed_prover_config,
    pack_log2: l1_wrap_2p22::PACK_LOG2,
    external_pow_floor: l1_wrap_2p22::EXTERNAL_CHALLENGES_POW_BITS,
    // Preserve the checked-in contracts, independent of W2's rebuilt binary.
    // The historical proof has PC 2303948: use the matched 3931e6eca bundle
    // for gas comparisons until the frozen regression bundle is repaired.
    exit_pc: ExitPcSource::Frozen(2171784),
    proof: "../prover/unified_circuit_proof_proth120.json",
    aux: "../prover/unified_circuit_proof_proth120_commitment_mod_aux_data.json",
    contracts_root: "generated_contracts",
    data_root: "debug_data",
    pow_cap: 30,
    gkr_pow_cap: 25,
};

// W3 Tasks 2/5/6 add L1_WRAP_2P21 here once its layout and proof exist:
// config = example_configs::l1_wrap_2p21::packed_prover_config;
// layout/proof/aux use the `_2p21` suffix;
// exit_pc = ExitPcSource::Binary("../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_wrap_special_opcodes_extension.bin");
// roots = generated_contracts/l1_wrap_2p21 and debug_data/l1_wrap_2p21.
// Register it in VERSIONS so every drift/serialization gate covers it.
pub const VERSIONS: &[Version] = &[L1_WRAP_2P22];

/// Select only writes for a harness version; normal tests cover all descriptors.
pub fn selected_versions() -> Vec<Version> {
    match std::env::var("AB_EVM_VERSION") {
        Ok(name) => vec![*VERSIONS
            .iter()
            .find(|version| version.name == name)
            .unwrap_or_else(|| {
                panic!("verifier version {name} has no registered artifact bundle")
            })],
        Err(std::env::VarError::NotPresent) => VERSIONS.to_vec(),
        Err(error) => panic!("invalid AB_EVM_VERSION: {error}"),
    }
}

impl Version {
    /// gkr.sol consumes monomial rounds, transcript-identical to the windowed
    /// prover schedule. All other parameters come from the version's config.
    pub fn prover_config(&self) -> ProverConfig {
        let mut config = (self.config)(SecurityLevel::Sec100);
        config.same_size_sumcheck_schedule = prover::gkr::prover_config::naive_same_size_schedule();
        config
    }

    pub fn circuit(&self) -> Circuit {
        serde_json::from_reader(std::fs::File::open(self.layout).expect("circuit layout"))
            .expect("deserialize circuit")
    }

    pub fn load(&self) -> (Circuit, Proof, CommitmentMode) {
        (
            self.circuit(),
            serde_json::from_reader(std::fs::File::open(self.proof).expect("proof"))
                .expect("deserialize proof"),
            self.commitment_mode(),
        )
    }

    pub fn commitment_mode(&self) -> CommitmentMode {
        serde_json::from_reader(std::fs::File::open(self.aux).expect("commitment mode"))
            .expect("deserialize commitment mode")
    }

    pub fn final_pc(&self) -> u32 {
        match self.exit_pc {
            ExitPcSource::Frozen(pc) => pc,
            ExitPcSource::Binary(path) => {
                let bytes = std::fs::read(path)
                    .unwrap_or_else(|error| panic!("read program {path}: {error}"));
                let (words, tail) = bytes.as_chunks::<4>();
                assert!(tail.is_empty(), "binary section not word-aligned");
                let binary: Vec<u32> = words.iter().copied().map(u32::from_le_bytes).collect();
                find_binary_exit_point(&binary)
            }
        }
    }

    pub fn contract_path(&self, name: &str) -> PathBuf {
        Path::new(self.contracts_root).join(name)
    }

    pub fn data_path(&self, name: &str) -> PathBuf {
        Path::new(self.data_root).join(name)
    }
}
