//! The canonical L1 wrap inputs shared by contract and calldata generation.
#![allow(dead_code)] // Each integration-test binary uses a different subset.
pub mod pow;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::definitions::SoundnessMode;
use prover::gkr::prover::{GKRProof, OperationMode};
use prover::gkr::prover_config::example_configs::l1_wrap;
use prover::gkr::prover_config::ProverConfig;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use std::path::{Path, PathBuf};
use trace_and_split::setups::program_setups::find_binary_exit_point;
use verifier_common::fsv_binaries::{FsvDescriptor, FsvProfile};

pub type Circuit = GKRCircuitArtifact<Proth120>;
pub type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

pub const INITS_TEARDOWNS_TOP_BITS: &[u32] = &[0, 1];
pub use prover::merkle_trees::keccak256_hash_leafs::KECCAK256_MERKLE_DIGEST_BYTES as DIGEST_BYTES;

/// gkr.sol consumes monomial rounds, transcript-identical to the windowed prover schedule.
pub fn prover_config(mode: SoundnessMode) -> ProverConfig {
    let mut config = l1_wrap::packed_prover_config_in_mode(mode);
    config.same_size_sumcheck_schedule = prover::gkr::prover_config::naive_same_size_schedule();
    config
}

pub fn load(mode: SoundnessMode) -> (Circuit, Proof, OperationMode) {
    let layout_dir = match mode {
        SoundnessMode::PessimisticConjecture => "unified_reduced_machine_proth120",
        SoundnessMode::EthproofsSoundnessCalc => "unified_reduced_machine_proth120_2_22",
    };
    let layout = Path::new("../circuit_defs/unrolled_circuits")
        .join(layout_dir)
        .join("generated/layout.json");
    let circuit = serde_json::from_reader(std::fs::File::open(layout).expect("circuit layout"))
        .expect("deserialize circuit");
    let bundle = load_bundle(proof_fixtures::chain_artifact(mode.file_suffix(), "l1"));
    (circuit, bundle.proof, bundle.operation_mode)
}

pub fn final_pc(mode: SoundnessMode) -> u32 {
    let descriptor = FsvDescriptor::compression(mode, FsvProfile::CompressionFinalWrap);
    let elf = Path::new("../tools/gkr_verifier/full_statement_verifiers")
        .join(descriptor.relative_path());
    let image = riscv_transpiler::elf::read_elf_from_path_with_rom(
        &elf,
        riscv_transpiler::elf::ElfReadMode::Legacy,
        riscv_transpiler::common_constants::rom::L1_WRAP_ROM,
    )
    .expect("wrap FSV image");
    find_binary_exit_point(image.objcopy_binary_words().expect("legacy wrap ROM image"))
}

pub fn contract_path(mode: SoundnessMode, name: &str) -> PathBuf {
    Path::new("generated_contracts")
        .join(mode.file_suffix())
        .join(name)
}

pub fn data_path(mode: SoundnessMode, name: &str) -> PathBuf {
    Path::new("debug_data").join(mode.file_suffix()).join(name)
}

pub const CALLDATA: &str = "single_tx_calldata.hex";
pub const CALLDATA_FIELDS: &str = "single_tx_calldata_fields.json";
/// The verified statement reported to the registry.
pub const VERIFIED_MARK: &str = "verified_mark.hex";

/// Generated sources relative to the L1 contract root. The merged project carries the
/// registry and Foundry tests; ignored negative projects build their verifiers for those tests.
pub const MERGED_VERIFIER: &str = "merged/src/GkrWhirVerifier.sol";

pub fn format_params(mode: SoundnessMode) -> verifier_evm::encoding::FormatParams {
    verifier_evm::encoding::FormatParams {
        setup_frontier_level: setup_frontier(mode).0,
    }
}
/// Setup frontier emitted by prover_pipeline::export_l1_wrap_setup_frontier.
pub fn setup_frontier(mode: SoundnessMode) -> (usize, Vec<[u32; 8]>) {
    let json: serde_json::Value = serde_json::from_reader(
        std::fs::File::open(data_path(mode, "setup_frontier.json")).expect("setup frontier"),
    )
    .expect("setup frontier JSON");
    let level = json["level"].as_u64().expect("frontier level") as usize;
    let nodes: Vec<[u32; 8]> = json["digests"]
        .as_array()
        .expect("frontier digests")
        .iter()
        .map(|d| {
            let hex = d.as_str().expect("hex digest");
            std::array::from_fn(|i| u32::from_str_radix(&hex[8 * i..8 * i + 8], 16).unwrap())
        })
        .collect();
    assert_eq!(nodes.len(), 1 << level, "frontier size");
    (level, nodes)
}

/// The calldata field map as committed JSON: `{gkr_bytes, fields: {name: {offset, length}}}`.
pub fn calldata_field_metadata(
    calldata: &verifier_evm::encoding::SingleTxCalldata,
    params: &verifier_evm::encoding::FormatParams,
) -> serde_json::Value {
    let fields: serde_json::Map<String, serde_json::Value> = calldata
        .fields
        .iter()
        .map(|(name, (offset, length))| {
            (
                name.clone(),
                serde_json::json!({ "offset": offset, "length": length }),
            )
        })
        .collect();
    let whir_rounds = (0..)
        .take_while(|r| calldata.fields.contains_key(&format!("whir_{r}_sumcheck")))
        .count();
    serde_json::json!({
        "gkr_bytes": calldata.gkr_bytes,
        "bytes": calldata.bytes.len(),
        "whir_rounds": whir_rounds,
        "digest_bytes": DIGEST_BYTES,
        "setup_frontier_level": params.setup_frontier_level,
        "fields": fields,
    })
}

#[derive(serde::Deserialize)]
pub struct Bundle {
    pub proof: Proof,
    pub operation_mode: OperationMode,
}
pub fn load_bundle(path: impl AsRef<Path>) -> Bundle {
    #[derive(serde::Deserialize)]
    struct Artifact {
        l1: Bundle,
    }
    let artifact: Artifact = proof_fixtures::read_file(path);
    artifact.l1
}
