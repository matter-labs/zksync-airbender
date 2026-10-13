//! Regenerates the on-chain verifier Solidity into `generated_contracts/` from the circuit
//! artifact. The Foundry project scaffolding (foundry.toml + the two-tx test) is committed
//! static; only the three verifier sources are (re)generated here.

mod common;

use common::production_prover_config;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
    EVM_PRODUCTION_TRACE_LEN_LOG2,
};
use prover::gkr::prover_config::{pow_bits, ProverConfig};
use std::path::Path;
use trace_and_split::setups::program_setups::find_binary_exit_point;

// Deployment parameters for the program being verified. These are properties of the *program +
// circuit*, NOT of any particular proof — verifier synthesis must never depend on proof/aux data.
// The verifier binds the statement to the terminal PC of the checked-in L1 feeder verifier binary
// (`feeder_exit_pc`); the external-challenges PoW difficulty is a verifier soundness knob.
const EXTERNAL_POW_BITS: u32 = 20;
// `fsv_unified_recursion_layer_sec_100_l1_feeder` (special-opcodes blake variant) — the merged-mode
// L1-feeder full-statement verifier whose execution the L1 proof attests (it verifies the final
// BabyBear recursion artifact).
const FEEDER_BINARY: &str =
    "../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.bin";

/// The registry address baked into both verifiers (they mark their committed
/// state to it). Default = the fixed address the local anvil harness etches
/// the registry at (`raw_tx_gas.sh`); real deployments override it via the
/// `REGISTRY_ADDRESS` env variable (set by `deploy.sh` AFTER deploying the
/// registry, since the address must exist before the verifiers generate).
const DEFAULT_REGISTRY_ADDRESS: &str = "0x00000000000000000000000000000000caFe0001";

fn feeder_exit_pc() -> u32 {
    let bytes = std::fs::read(FEEDER_BINARY).unwrap_or_else(|_| {
        panic!("Missing {FEEDER_BINARY} — run reproducible build script first");
    });
    assert!(
        bytes.len().is_multiple_of(4),
        "binary section not word-aligned"
    );
    let binary: Vec<u32> = bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    find_binary_exit_point(&binary)
}

/// The WHIR batching PoW difficulty, derived for the batched polynomials the WHIR run tests: the
/// packed `2^(trace + pack_log2)` columns.
fn whir_batch_pow_bits(circuit: &GKRCircuitArtifact<Proth120>, config: &ProverConfig) -> u32 {
    pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        EVM_PRODUCTION_TRACE_LEN_LOG2 + EVM_PRODUCTION_PACK_LOG2,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(circuit),
    )
}

#[test]
fn generate_contracts_into_dir() {
    let json = std::fs::read_to_string(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();

    let registry_address =
        std::env::var("REGISTRY_ADDRESS").unwrap_or_else(|_| DEFAULT_REGISTRY_ADDRESS.to_string());

    let prover_config = production_prover_config();
    let out = verifier_evm::generate_verifiers(
        &circuit,
        &prover_config,
        EVM_PRODUCTION_PACK_LOG2,
        EXTERNAL_POW_BITS,
        whir_batch_pow_bits(&circuit, &prover_config),
        feeder_exit_pc(),
        &registry_address,
    );

    let root = Path::new("generated_contracts");
    let write = |rel: &str, content: &str| {
        let p = root.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, content).unwrap();
        eprintln!("wrote {} ({} bytes)", p.display(), content.len());
    };

    write("gkr/src/GkrVerifier.sol", &out.gkr_sol);
    write("whir/src/WhirVerifier.sol", &out.whir_sol);
    write("two_tx/src/GkrWhirRegistry.sol", &out.registry_sol);
}

#[test]
fn regenerate_evm_verifier_stubs() {
    let json = std::fs::read_to_string(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();
    let exit_pc = feeder_exit_pc();

    // hardcoded to be substituted by external dependency
    let registry_address = "0x0000000000000000000000000000000000000000";

    let prover_config = production_prover_config();
    let out = verifier_evm::generate_verifiers(
        &circuit,
        &prover_config,
        EVM_PRODUCTION_PACK_LOG2,
        EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
        whir_batch_pow_bits(&circuit, &prover_config),
        exit_pc,
        registry_address,
    );

    let root = Path::new("generated_contracts");
    let write = |rel: &str, content: &str| {
        let p = root.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, content).unwrap();
        eprintln!("wrote {} ({} bytes)", p.display(), content.len());
    };

    write("gkr/src/GkrVerifierProduction.sol", &out.gkr_sol);
    write("whir/src/WhirVerifierProduction.sol", &out.whir_sol);
}
