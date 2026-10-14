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
    let prover::gkr::prover::CommitmentMode::MergedAndPackedMemoryAndWitness {
        pack_log2,
        external_challenges_pow_bits,
        final_pc,
        ..
    } = version.commitment_mode()
    else {
        panic!("{}: expected packed commitment mode", version.name);
    };
    assert_eq!(
        version.pack_log2, pack_log2,
        "descriptor packing must match proof aux"
    );
    assert_eq!(
        version.external_pow_floor, external_challenges_pow_bits,
        "descriptor external PoW floor must match proof aux"
    );
    assert_eq!(
        version.final_pc(),
        final_pc,
        "{}: descriptor exit PC must match proof aux",
        version.name
    );
    let lookup_pow_bits = pow_bits::lookup_challenges_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(&circuit),
    );
    let external_pow_bits = lookup_pow_bits.max(external_challenges_pow_bits);
    let batched_proximity_pow_bits = pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.trace_len_log2 + pack_log2,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(&circuit),
    );
    for (gate, bits) in [
        ("external challenges", external_pow_bits),
        ("WHIR batching", batched_proximity_pow_bits),
    ] {
        assert!(
            bits <= version.gkr_pow_cap,
            "{}: {gate} PoW {bits} exceeds GKR cap {}",
            version.name,
            version.gkr_pow_cap
        );
    }
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
        final_pc,
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
    use prover::definitions::SecurityLevel;
    use prover::gkr::prover_config::example_configs::l1_wrap_2p21;

    // The committed 2p21 layout and b' tuple are usable before a proof bundle
    // exists. Keep production descriptors tied to complete artifact bundles.
    let version = &common::L1_WRAP_2P22;
    let circuit = serde_json::from_str(include_str!(
        "../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
    ))
    .unwrap();
    let mut config = l1_wrap_2p21::packed_prover_config(SecurityLevel::Sec100);
    config.same_size_sumcheck_schedule = prover::gkr::prover_config::naive_same_size_schedule();
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
    assert!(std::panic::catch_unwind(|| generate(&version.prover_config())).is_err());
    let out = generate(&config);
    assert_eq!(
        solidity_constant(&out.gkr_sol, "__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS"),
        21
    );
    assert!(out.gkr_sol.contains("lt(k, 17)"));
    assert!(out
        .gkr_sol
        .contains("gkr_dr_final(ptr, fs, batching, eq(k, 16)"));
    assert!(!out.gkr_sol.contains("lt(k, 18)"));
    assert_eq!(solidity_constant(&out.whir_sol, "__TEMPLATE_WHIR_NZ"), 25);
    assert!(out
        .whir_sol
        .contains("let caps_off := add(64, mul(nz, 16))"));
    assert!(out.whir_sol.contains("if lt(add(mul(i, 2), 1), nz)"));
    assert!(out
        .whir_sol
        .contains("case 4 { fold := 3 q := 5 pow_bits := 17 qib := 28 vp := 8 cb := 20 }"));
    let mut bad_schedule = config.clone();
    bad_schedule.whir_schedule.whir_steps_lde_factors[0] *= 2;
    assert!(std::panic::catch_unwind(|| generate(&bad_schedule)).is_err());
    let mut bad_schedule = config.clone();
    bad_schedule.whir_schedule.whir_queries_schedule[0] = 51;
    assert!(std::panic::catch_unwind(|| generate(&bad_schedule)).is_err());
    config.sumcheck_explicit_output_size_log_2 = 3;
    assert!(std::panic::catch_unwind(|| generate(&config)).is_err());
}

#[test]
fn descriptor_rejects_aux_drift_and_excess_gkr_pow() {
    for version in [
        Version {
            pack_log2: 3,
            ..common::L1_WRAP_2P22
        },
        Version {
            external_pow_floor: 19,
            ..common::L1_WRAP_2P22
        },
        Version {
            gkr_pow_cap: 19,
            ..common::L1_WRAP_2P22
        },
    ] {
        assert!(std::panic::catch_unwind(|| generate(&version, DEFAULT_REGISTRY_ADDRESS)).is_err());
    }
}

#[test]
#[should_panic(expected = "descriptor exit PC must match proof aux")]
fn descriptor_rejects_aux_exit_pc_drift() {
    let version = Version {
        exit_pc: common::ExitPcSource::Frozen(0),
        ..common::L1_WRAP_2P22
    };
    generate(&version, DEFAULT_REGISTRY_ADDRESS);
}
