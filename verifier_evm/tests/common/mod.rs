//! The canonical L1 wrap inputs shared by contract and calldata generation.
#![allow(dead_code)] // Each integration-test binary uses a different subset.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::{GKRProof, OperationMode};
use prover::gkr::prover_config::example_configs::l1_wrap_2p21;
use prover::gkr::prover_config::ProverConfig;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use std::path::{Path, PathBuf};
use trace_and_split::setups::program_setups::find_binary_exit_point;

pub type Circuit = GKRCircuitArtifact<Proth120>;
pub type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

pub const BUNDLE: &str = "../prover_pipeline/fixtures/l1_reference_2p21/l1_bundle.json";
pub const INITS_TEARDOWNS_TOP_BITS: &[u32] = &[0, 1];
pub const DIGEST_BYTES: usize = 25;

/// gkr.sol consumes monomial rounds, transcript-identical to the windowed prover schedule.
pub fn prover_config() -> ProverConfig {
    let mut config = l1_wrap_2p21::packed_prover_config(SecurityLevel::Sec100);
    config.same_size_sumcheck_schedule = prover::gkr::prover_config::naive_same_size_schedule();
    config
}
pub fn load() -> (Circuit, Proof, OperationMode) {
    let circuit = serde_json::from_reader(
        std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json",
        )
        .expect("circuit layout"),
    )
    .expect("deserialize circuit");
    let bundle = load_bundle(BUNDLE);
    (circuit, bundle.proof, bundle.operation_mode)
}
pub fn final_pc() -> u32 {
    let image = riscv_transpiler::elf::read_elf_from_path_with_rom(
        Path::new("../tools/gkr_verifier/full_statement_verifiers/fsv_unified_recursion_layer_sec_100_l1_feeder_wrap_special_opcodes_extension.elf"),
        riscv_transpiler::elf::ElfReadMode::Legacy,
        riscv_transpiler::common_constants::rom::L1_WRAP_ROM,
    )
    .expect("wrap FSV image");
    find_binary_exit_point(image.objcopy_binary_words().expect("legacy wrap ROM image"))
}

pub fn contract_path(name: &str) -> PathBuf {
    Path::new("generated_contracts/l1_wrap_2p21").join(name)
}
pub fn data_path(name: &str) -> PathBuf {
    Path::new("debug_data/l1_wrap_2p21").join(name)
}

/// Require a named rejection from a public encoder boundary.
pub fn assert_panics_with<T>(expected: &str, action: impl FnOnce() -> T + std::panic::UnwindSafe) {
    let Err(payload) = std::panic::catch_unwind(action) else {
        panic!("expected rejection");
    };
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
/// The verified statement reported to the registry.
pub const VERIFIED_MARK: &str = "verified_mark.hex";

/// Generated sources relative to the L1 contract root. The F1 project carries the
/// registry and Foundry tests; the negative project builds its verifier for those tests.
pub const MERGED_F1: &str = "merged_f1/src/GkrWhirVerifier.sol";
pub const F1_FRONTIER_CONTRACT: &str = "merged_f1/src/SetupFrontier.sol";
pub const F1_WRONG_FINAL_PC: &str = "negative/f1_wrong_final_pc/src/GkrWhirVerifier.sol";

pub fn f1_params() -> verifier_evm::encoding::FormatParams {
    verifier_evm::encoding::FormatParams {
        digest_bytes: DIGEST_BYTES,
        setup_frontier_level: setup_frontier().0,
    }
}
/// Setup frontier emitted by prover_pipeline::export_l1_wrap_setup_frontier.
pub fn setup_frontier() -> (usize, Vec<[u32; 8]>) {
    let json: serde_json::Value = serde_json::from_reader(
        std::fs::File::open(data_path("setup_frontier.json")).expect("setup frontier"),
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

/// The F1 field map as committed JSON: `{gkr_bytes, fields: {name: {offset, length}}}`.
pub fn f1_field_metadata(
    f1: &verifier_evm::encoding::SingleTxCalldata,
    params: &verifier_evm::encoding::FormatParams,
) -> serde_json::Value {
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
    let whir_rounds = (0..)
        .take_while(|r| f1.fields.contains_key(&format!("whir_{r}_sumcheck")))
        .count();
    serde_json::json!({
        "gkr_bytes": f1.gkr_bytes,
        "bytes": f1.bytes.len(),
        "whir_rounds": whir_rounds,
        "digest_bytes": params.digest_bytes,
        "setup_frontier_level": params.setup_frontier_level,
        "fields": fields,
    })
}

#[derive(serde::Deserialize)]
pub struct Bundle {
    pub proof: Proof,
    pub operation_mode: OperationMode,
    pub wrap: String,
}
pub fn load_bundle(path: impl AsRef<Path>) -> Bundle {
    let bundle: Bundle = serde_json::from_reader(std::fs::File::open(path).expect("L1 bundle"))
        .expect("typed L1 bundle");
    assert_eq!(bundle.wrap, "2p21");
    bundle
}
