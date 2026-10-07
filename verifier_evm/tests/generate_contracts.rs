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
use std::path::Path;
use trace_and_split::setups::program_setups::find_binary_exit_point;

// Deployment parameters are properties of the *program + circuit*, never of a proof: the
// verifier binds the statement to the L1 feeder verifier's terminal PC (derived from the checked-in
// binary) and its PoW difficulties follow the production prover config.
const FEEDER_BINARY: &str = "../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.bin";
const LAYOUT: &str = "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json";

/// The registry address baked into both verifiers (they mark their committed
/// state to it). Default = the fixed address the local anvil harness etches
/// the registry at (`raw_tx_gas.sh`); real deployments override it via the
/// `REGISTRY_ADDRESS` env variable (set by `deploy.sh` AFTER deploying the
/// registry, since the address must exist before the verifiers generate).
const DEFAULT_REGISTRY_ADDRESS: &str = "0x00000000000000000000000000000000caFe0001";
const STUB_REGISTRY_ADDRESS: &str = "0x0000000000000000000000000000000000000000";

const TEST_PAIR: [&str; 3] = [
    "gkr/src/GkrVerifier.sol",
    "whir/src/WhirVerifier.sol",
    "two_tx/src/GkrWhirRegistry.sol",
];
const PRODUCTION_STUBS: [&str; 2] = [
    "gkr/src/GkrVerifierProduction.sol",
    "whir/src/WhirVerifierProduction.sol",
];

fn generate(registry_address: &str) -> verifier_evm::GeneratedContracts {
    use prover::gkr::prover_config::pow_bits;

    let circuit: GKRCircuitArtifact<Proth120> =
        serde_json::from_str(&std::fs::read_to_string(LAYOUT).unwrap()).unwrap();
    let bytes = std::fs::read(FEEDER_BINARY)
        .unwrap_or_else(|_| panic!("missing {FEEDER_BINARY}, run the reproducible build first"));
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
    let prover_config = production_prover_config();
    let batched_proximity_pow_bits = pow_bits::batched_proximity_check_pow_bits(
        prover_config.security_level.security_bits(),
        EVM_PRODUCTION_TRACE_LEN_LOG2,
        prover_config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(&circuit),
    );
    verifier_evm::generate_verifiers(
        &circuit,
        &prover_config,
        EVM_PRODUCTION_PACK_LOG2,
        EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
        batched_proximity_pow_bits,
        find_binary_exit_point(&binary),
        registry_address,
    )
}

fn sources(out: &verifier_evm::GeneratedContracts) -> [&str; 3] {
    [&out.gkr_sol, &out.whir_sol, &out.registry_sol]
}

fn write(rel: &str, content: &str) {
    let p = Path::new("generated_contracts").join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(&p, content).unwrap();
    eprintln!("wrote {} ({} bytes)", p.display(), content.len());
}

#[test]
#[ignore = "writes generated_contracts; build.sh runs it"]
fn generate_contracts_into_dir() {
    let registry_address =
        std::env::var("REGISTRY_ADDRESS").unwrap_or_else(|_| DEFAULT_REGISTRY_ADDRESS.to_string());
    let out = generate(&registry_address);
    for (rel, content) in TEST_PAIR.iter().zip(sources(&out)) {
        write(rel, content);
    }
}

#[test]
#[ignore = "writes generated_contracts; build.sh runs it"]
fn regenerate_evm_verifier_stubs() {
    let out = generate(STUB_REGISTRY_ADDRESS);
    for (rel, content) in PRODUCTION_STUBS.iter().zip(sources(&out)) {
        write(rel, content);
    }
}

#[test]
fn checked_in_contracts_are_current() {
    let test_pair = generate(DEFAULT_REGISTRY_ADDRESS);
    let stubs = generate(STUB_REGISTRY_ADDRESS);
    for (rel, content) in TEST_PAIR
        .iter()
        .zip(sources(&test_pair))
        .chain(PRODUCTION_STUBS.iter().zip(sources(&stubs)))
    {
        let checked_in = std::fs::read_to_string(Path::new("generated_contracts").join(rel))
            .unwrap_or_else(|_| panic!("missing generated_contracts/{rel}"));
        assert!(
            checked_in == content,
            "generated_contracts/{rel} is stale: rerun `cargo test -p verifier_evm --test generate_contracts -- --ignored`"
        );
    }
}
