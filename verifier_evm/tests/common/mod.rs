//! Versioned inputs shared by contract generation and proof serialization.
#![allow(dead_code)] // Each integration-test binary uses a different subset.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::gkr::prover_config::example_configs::l1_wrap_2p21;
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
    pub allow_missing_proof: bool,
    pub mutation_fields_file: Option<&'static str>,
    pub wrong_final_pc_contract: Option<&'static str>,
    /// Merkle digest bytes on the F1 wire (the commitment profile of the proof).
    pub digest_bytes: usize,
}

pub const L1_WRAP_2P21: Version = Version {
    name: "2p21",
    layout: "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json",
    config: l1_wrap_2p21::packed_prover_config,
    pack_log2: l1_wrap_2p21::PACK_LOG2,
    external_pow_floor: l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
    exit_pc: ExitPcSource::Binary("../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_wrap_special_opcodes_extension.bin"),
    proof: "../prover/unified_circuit_proof_proth120_2p21.json",
    aux: "../prover/unified_circuit_proof_proth120_2p21_commitment_mod_aux_data.json",
    contracts_root: "generated_contracts/l1_wrap_2p21",
    data_root: "debug_data/l1_wrap_2p21",
    pow_cap: 30,
    gkr_pow_cap: 25,
    // Task 5 will export the real proof. Remove this allowance once it is committed.
    allow_missing_proof: true,
    mutation_fields_file: Some("calldata_fields.json"),
    wrong_final_pc_contract: Some("gkr_negative/src/GkrVerifierWrongFinalPc.sol"),
    digest_bytes: 32,
};
pub const VERSIONS: &[Version] = &[L1_WRAP_2P21];

pub fn available_versions(check: &str) -> Vec<&'static Version> {
    VERSIONS
        .iter()
        .filter(|version| version.available_for_read(check))
        .collect()
}

/// Select only writes for a harness version; normal tests cover all descriptors.
pub fn selected_versions() -> Vec<Version> {
    match std::env::var("AB_EVM_VERSION") {
        Ok(name) => {
            let version = VERSIONS
                .iter()
                .find(|version| version.name == name)
                .unwrap_or_else(|| {
                    panic!("verifier version {name} has no registered artifact bundle")
                });
            version.require_bundle();
            vec![*version]
        }
        Err(std::env::VarError::NotPresent) => available_versions("artifact generation")
            .into_iter()
            .copied()
            .collect(),
        Err(error) => panic!("invalid AB_EVM_VERSION: {error}"),
    }
}

impl Version {
    pub fn require_bundle(&self) {
        assert!(
            Path::new(self.proof).is_file(),
            "{}: proof is missing: {}; cannot generate or verify this bundle",
            self.name,
            self.proof
        );
        assert!(
            Path::new(self.aux).is_file(),
            "{}: proof aux is missing: {}",
            self.name,
            self.aux
        );
    }

    pub fn available_for_read(&self, check: &str) -> bool {
        if self.allow_missing_proof
            && !Path::new(self.proof)
                .try_exists()
                .expect("inspect proof path")
        {
            assert!(
                self.existing_generated_output().is_none(),
                "{}: proof is missing but generated outputs already exist; restore the proof instead of skipping drift checks",
                self.name
            );
            // Direct stderr remains visible even when libtest captures successful tests.
            use std::io::Write;
            writeln!(std::io::stderr().lock(), "SKIP {check} [{}]: proof absent at {}; no artifact validation performed for this version", self.name, self.proof).unwrap();
            return false;
        }
        self.require_bundle();
        true
    }

    fn existing_generated_output(&self) -> Option<PathBuf> {
        // The scaffold's registry/configs exist before the proof; generated
        // verifier sources and calldata must never outlive an absent proof.
        let contracts = [
            "gkr/src/GkrVerifier.sol",
            "gkr/src/GkrVerifierProduction.sol",
            "whir/src/WhirVerifier.sol",
            "whir/src/WhirVerifierProduction.sol",
            "single_tx/gkr/src/GkrVerifier.sol",
            "single_tx/whir/src/WhirVerifier.sol",
        ];
        let wrong_final_pc = self
            .wrong_final_pc_contract
            .into_iter()
            .flat_map(|rel| [rel.to_string(), format!("single_tx/{rel}")]);
        for rel in contracts
            .into_iter()
            .map(str::to_string)
            .chain(wrong_final_pc)
        {
            let path = self.contract_path(&rel);
            if path.try_exists().expect("inspect generated contract path") {
                return Some(path);
            }
        }
        match std::fs::read_dir(self.data_root) {
            Ok(mut entries) => entries
                .next()
                .map(|entry| entry.expect("inspect generated data entry").path()),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!(
                "inspect generated data directory {}: {error}",
                self.data_root
            ),
        }
    }

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
        self.require_bundle();
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

pub fn calldata_field_metadata(
    gkr: &verifier_evm::flatten::GkrCalldataFields,
    whir: &verifier_evm::flatten::WhirCalldataFields,
) -> serde_json::Value {
    let field = |field: &verifier_evm::flatten::CalldataField, encoding: &str| {
        serde_json::json!({
            "offset": field.offset,
            "bytes": format!("0x{}", hex::encode(&field.value)),
            "encoding": encoding,
        })
    };
    serde_json::json!({
        "gkr": {
            "final_pc": field(&gkr.final_pc, "u32_le"),
            "external_pow_nonce": field(&gkr.external_pow_nonce, "u64_be"),
        },
        "whir": { "batched_opening": field(&whir.batched_opening, "proth120_be") },
    })
}

/// Require a named rejection while allowing missing pending proof bundles to skip reads.
pub fn assert_panics_with<T>(expected: &str, action: impl FnOnce() -> T + std::panic::UnwindSafe) {
    let payload = std::panic::catch_unwind(action)
        .err()
        .expect("expected rejection");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .expect("text panic");
    assert!(
        message.contains(expected),
        "expected {expected:?}, got {message:?}"
    );
}

pub const F1_CALLDATA: &str = "single_tx_f1.hex";
pub const F1_FIELDS: &str = "single_tx_f1_fields.json";

impl Version {
    pub fn f1_params(&self) -> verifier_evm::encoding::FormatParams {
        verifier_evm::encoding::FormatParams::from_config(
            &self.prover_config(),
            self.pack_log2,
            self.digest_bytes,
        )
    }
}

/// The F1 field map as committed JSON: `{gkr_bytes, fields: {name: {offset, length}}}`.
pub fn f1_field_metadata(f1: &verifier_evm::encoding::SingleTxCalldata) -> serde_json::Value {
    let fields: serde_json::Map<String, serde_json::Value> = f1
        .fields
        .iter()
        .map(|(name, (offset, length))| {
            (
                name.clone(),
                serde_json::json!({ "offset": offset, "length": length }),
            )
        })
        .collect();
    serde_json::json!({ "gkr_bytes": f1.gkr_bytes, "bytes": f1.bytes.len(), "fields": fields })
}
