//! Regenerates the on-chain verifier Solidity into `generated_contracts/` from the circuit
//! artifact. The Foundry project scaffolding (foundry.toml + the two-tx test) is committed
//! static; only the three verifier sources are (re)generated here.

mod common;

use common::{production_prover_config, PACK_LOG2};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
    EVM_PRODUCTION_TRACE_LEN_LOG2,
};
use std::path::Path;
use trace_and_split::setups::program_setups::find_binary_exit_point;

// Deployment parameters for the program being verified. These are properties of the *program +
// circuit*, NOT of any particular proof — verifier synthesis must never depend on proof/aux data.
// `EXPECTED_FINAL_PC` is the program's terminal PC the verifier binds the statement to; the two
// PoW difficulties are the verifier's soundness knobs. Update these when the program changes.
const WHIR_BATCH_POW_BITS: u32 = 11;
const EXTERNAL_POW_BITS: u32 = 20;
// Terminal PC of `fsv_unified_recursion_layer_sec_100_l1_feeder` (special-
// opcodes blake variant) — the merged-mode L1-feeder full-statement verifier
// whose execution the L1 proof attests (it verifies the final BabyBear
// recursion artifact). 0x001a3098 for the reproducible-build binaries.
const EXPECTED_FINAL_PC: u32 = 1716376;

/// The registry address baked into both verifiers (they mark their committed
/// state to it). Default = the fixed address the local anvil harness etches
/// the registry at (`raw_tx_gas.sh`); real deployments override it via the
/// `REGISTRY_ADDRESS` env variable (set by `deploy.sh` AFTER deploying the
/// registry, since the address must exist before the verifiers generate).
const DEFAULT_REGISTRY_ADDRESS: &str = "0x00000000000000000000000000000000caFe0001";

#[test]
fn generate_contracts_into_dir() {
    let json = std::fs::read_to_string(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();

    let registry_address =
        std::env::var("REGISTRY_ADDRESS").unwrap_or_else(|_| DEFAULT_REGISTRY_ADDRESS.to_string());

    let out = verifier_evm::generate_verifiers(
        &circuit,
        &production_prover_config(),
        PACK_LOG2,
        EXTERNAL_POW_BITS,
        WHIR_BATCH_POW_BITS,
        EXPECTED_FINAL_PC,
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
    use prover::gkr::prover_config::pow_bits;

    fn load_binary_section(path: &str) -> Vec<u32> {
        let bytes = std::fs::read(path).unwrap_or_else(|_| {
            panic!("Missing {path} — run reproducible build script first");
        });
        assert!(bytes.len() % 4 == 0, "binary section not word-aligned");
        bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
            .collect()
    }

    let json = std::fs::read_to_string(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();
    let binary = load_binary_section("../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.bin");
    let exit_pc = find_binary_exit_point(&binary);

    // hardcoded to be substituted by external dependency
    let registry_address = "0x0000000000000000000000000000000000000000";

    let prover_config = production_prover_config();
    let batched_proximity_pow_bits = pow_bits::batched_proximity_check_pow_bits(
        prover_config.security_level.security_bits(),
        EVM_PRODUCTION_TRACE_LEN_LOG2,
        prover_config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(&circuit),
    );

    let out = verifier_evm::generate_verifiers(
        &circuit,
        &prover_config,
        EVM_PRODUCTION_PACK_LOG2,
        EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
        batched_proximity_pow_bits,
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
