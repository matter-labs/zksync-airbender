//! Regenerates the on-chain verifier Solidity into `generated_contracts/` from the circuit
//! artifact. The Foundry project scaffolding (foundry.toml + the two-tx test) is committed
//! static; only the three verifier sources are (re)generated here.

mod common;

use common::{Version, VERSIONS};
use field::Proth120;

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

fn generate(version: &Version, registry_address: &str) -> verifier_evm::GeneratedContracts {
    use prover::gkr::prover_config::pow_bits;

    let circuit = version.circuit();
    let config = version.prover_config();
    let lookup_pow_bits = pow_bits::lookup_challenges_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(&circuit),
    );
    let external_pow_bits = lookup_pow_bits.max(version.external_pow_floor);
    let batched_proximity_pow_bits = pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.trace_len_log2 + version.pack_log2,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(&circuit),
    );
    assert!(external_pow_bits <= 25 && batched_proximity_pow_bits <= 25);
    for bits in config
        .whir_schedule
        .whir_pow_schedule
        .iter()
        .copied()
        .chain([external_pow_bits, batched_proximity_pow_bits])
    {
        assert!(
            bits <= version.pow_cap,
            "{}: PoW {bits} exceeds {}",
            version.name,
            version.pow_cap
        );
    }
    let out = verifier_evm::generate_verifiers(
        &circuit,
        &config,
        version.pack_log2,
        external_pow_bits,
        batched_proximity_pow_bits,
        version.final_pc(),
        registry_address,
    );
    // Check the emitted verifier's gates, not just the arguments passed to it.
    assert_eq!(
        solidity_constant(&out.gkr_sol, "__TEMPLATE_EXTERNAL_POW_BITS"),
        external_pow_bits
    );
    assert_eq!(
        solidity_constant(&out.gkr_sol, "__TEMPLATE_WHIR_BATCH_POW_BITS"),
        batched_proximity_pow_bits
    );
    out
}

fn solidity_constant(source: &str, name: &str) -> u32 {
    let line = source
        .lines()
        .find(|line| line.contains(&format!("constant {name} ")))
        .unwrap();
    line.split_once('=')
        .unwrap()
        .1
        .split_once(';')
        .unwrap()
        .0
        .trim()
        .parse()
        .unwrap()
}

fn sources(out: &verifier_evm::GeneratedContracts) -> [&str; 3] {
    [&out.gkr_sol, &out.whir_sol, &out.registry_sol]
}

fn write(version: &Version, rel: &str, content: &str) {
    let p = version.contract_path(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(&p, content).unwrap();
    eprintln!("wrote {} ({} bytes)", p.display(), content.len());
}

#[test]
#[ignore = "writes versioned generated_contracts"]
fn generate_contracts_into_dir() {
    let registry_address =
        std::env::var("REGISTRY_ADDRESS").unwrap_or_else(|_| DEFAULT_REGISTRY_ADDRESS.to_string());
    for version in common::selected_versions() {
        let out = generate(&version, &registry_address);
        for (rel, content) in TEST_PAIR.iter().zip(sources(&out)) {
            write(&version, rel, content);
        }
    }
}

#[test]
#[ignore = "writes versioned generated_contracts"]
fn regenerate_evm_verifier_stubs() {
    for version in common::selected_versions() {
        let out = generate(&version, STUB_REGISTRY_ADDRESS);
        for (rel, content) in PRODUCTION_STUBS.iter().zip(sources(&out)) {
            write(&version, rel, content);
        }
    }
}

#[test]
fn checked_in_contracts_are_current() {
    for version in VERSIONS {
        let test_pair = generate(version, DEFAULT_REGISTRY_ADDRESS);
        let stubs = generate(version, STUB_REGISTRY_ADDRESS);
        for (rel, content) in TEST_PAIR
            .iter()
            .zip(sources(&test_pair))
            .chain(PRODUCTION_STUBS.iter().zip(sources(&stubs)))
        {
            let path = version.contract_path(rel);
            let checked_in = std::fs::read_to_string(&path)
                .unwrap_or_else(|_| panic!("missing {}", path.display()));
            assert!(
                checked_in == content,
                "{} is stale: rerun `cargo test -p verifier_evm --test generate_contracts -- --ignored`",
                path.display()
            );
        }
    }
}

#[test]
fn generator_accepts_trace21_and_rejects_mismatched_config() {
    // Synthetic geometry: real 2p21 artifacts receive their own descriptor
    // once generated. This exercises both generator admission checks now.
    let version = &common::L1_WRAP_2P22;
    let mut circuit = version.circuit();
    circuit.trace_len = 1 << 21;
    let mut config = version.prover_config();
    let generate = |config: &prover::gkr::prover_config::ProverConfig| {
        verifier_evm::generate_verifiers(
            &circuit,
            config,
            version.pack_log2,
            20,
            16,
            version.final_pc(),
            DEFAULT_REGISTRY_ADDRESS,
        )
    };
    assert!(std::panic::catch_unwind(|| generate(&config)).is_err());
    config.trace_len_log2 = 21;
    let out = generate(&config);
    assert_eq!(
        solidity_constant(&out.gkr_sol, "__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS"),
        21
    );
}
