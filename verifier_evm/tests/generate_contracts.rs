//! Regenerates the on-chain verifier Solidity into `generated_contracts/` from the circuit
//! artifact. The Foundry project scaffolding (foundry.toml + the two-tx test) is committed
//! static; verifier sources and the wrong-final-PC control are (re)generated here.

mod common;

use common::Version;
use field::Proth120;

/// The registry address baked into both verifiers (they mark their committed
/// state to it). Default = the fixed address the local anvil harness etches
/// the registry at (`raw_tx_gas.sh`); real deployments override it via the
/// `REGISTRY_ADDRESS` env variable (set by `deploy.sh` AFTER deploying the
/// registry, since the address must exist before the verifiers generate).
const DEFAULT_REGISTRY_ADDRESS: &str = "0x00000000000000000000000000000000caFe0001";
const STUB_REGISTRY_ADDRESS: &str = "0x0000000000000000000000000000000000000000";
/// Where the single-tx harness etches the `SetupFrontier` data contract the F1 WHIR verifier reads.
const DEFAULT_FRONTIER_ADDRESS: &str = "0x000000000000000000000000000000005e7f0001";
const F1_FRONTIER_CONTRACT: &str = "single_tx/f1/frontier/src/SetupFrontier.sol";

const TEST_PAIR: [&str; 3] = [
    "gkr/src/GkrVerifier.sol",
    "whir/src/WhirVerifier.sol",
    "two_tx/src/GkrWhirRegistry.sol",
];
const PRODUCTION_STUBS: [&str; 2] = [
    "gkr/src/GkrVerifierProduction.sol",
    "whir/src/WhirVerifierProduction.sol",
];
/// Single-tx variants of the test pair for the `single_tx/harness` proxy; the
/// wrong-final-PC control's variant lives under the same prefix.
const SINGLE_TX: [&str; 2] = [
    "single_tx/gkr/src/GkrVerifier.sol",
    "single_tx/whir/src/WhirVerifier.sol",
];
const SINGLE_TX_PREFIX: &str = "single_tx/";
/// F1 single-tx verifiers (format F1, `verifier_evm::encoding`); the wrong-final-PC control's
/// variant lives under the same prefix.
const F1_PAIR: [&str; 2] = [
    "single_tx/f1/gkr/src/GkrVerifier.sol",
    "single_tx/f1/whir/src/WhirVerifier.sol",
];
const F1_PREFIX: &str = "single_tx/f1/";
const INSTRUMENTED_PREFIX: &str = "single_tx/instrumented/";
const F1_WRONG_SETUP_CAP: &str =
    "single_tx/f1/gkr_wrong_setup_cap/src/GkrVerifierWrongSetupCap.sol";

fn generate(version: &Version, registry_address: &str) -> verifier_evm::GeneratedContracts {
    render(version, registry_address, None)
}

// Preserve the valid proof/transcript and change only the verifier's expected PC.
fn generate_wrong_final_pc(
    version: &Version,
    registry_address: &str,
) -> verifier_evm::GeneratedContracts {
    render(version, registry_address, Some(version.final_pc() ^ 1))
}

fn render(
    version: &Version,
    registry_address: &str,
    negative_test_exit_pc: Option<u32>,
) -> verifier_evm::GeneratedContracts {
    version.require_bundle();
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
    let (external_pow_bits, batched_proximity_pow_bits) =
        derived_pow_bits(version, &circuit, &config);
    let out = verifier_evm::generate_verifiers(
        &circuit,
        &config,
        version.pack_log2,
        external_pow_bits,
        batched_proximity_pow_bits,
        negative_test_exit_pc.unwrap_or(final_pc),
        registry_address,
        version.digest_bytes,
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

// All PoW requirements depend on the layout/config, so validate pending versions
// even before their proof/aux bundle is exported.
fn derived_pow_bits(
    version: &Version,
    circuit: &common::Circuit,
    config: &prover::gkr::prover_config::ProverConfig,
) -> (u32, u32) {
    use prover::gkr::prover_config::pow_bits;
    let pack_log2 = version.pack_log2;
    let lookup_pow_bits = pow_bits::lookup_challenges_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(circuit),
    );
    let external_pow_bits = lookup_pow_bits.max(version.external_pow_floor);
    let batched_proximity_pow_bits = pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.trace_len_log2 + pack_log2,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(circuit),
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
    (external_pow_bits, batched_proximity_pow_bits)
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

fn generate_f1(
    version: &Version,
    final_pc: u32,
    flags: &[&str],
) -> verifier_evm::GeneratedContracts {
    let (_, proof, _) = version.load();
    let frontier = version.setup_frontier().map(|(_, nodes)| nodes);
    generate_f1_with_setup(
        version,
        final_pc,
        &proof.whir_proof.setup_commitment.commitment.cap.cap,
        frontier.as_deref(),
        flags,
    )
}

/// `setup_frontier`: `None` renders without a frontier (full setup paths to the cap).
fn generate_f1_with_setup(
    version: &Version,
    final_pc: u32,
    setup_cap: &[[u32; 8]],
    setup_frontier: Option<&[[u32; 8]]>,
    flags: &[&str],
) -> verifier_evm::GeneratedContracts {
    let circuit = version.circuit();
    let config = version.prover_config();
    let params = match setup_frontier {
        Some(_) => version.f1_params(),
        None => version
            .f1_params()
            .with_setup_frontier(config.cap_size.trailing_zeros() as usize),
    };
    let (external_pow_bits, batched_proximity_pow_bits) =
        derived_pow_bits(version, &circuit, &config);
    verifier_evm::generate_f1_verifiers(
        &circuit,
        &config,
        &params,
        external_pow_bits,
        batched_proximity_pow_bits,
        final_pc,
        setup_cap,
        setup_frontier.map(|nodes| (nodes, DEFAULT_FRONTIER_ADDRESS)),
        flags,
    )
}

/// `(relative path, source)` of every F1 render of `version`.
fn f1_sources(version: &Version) -> Vec<(String, String)> {
    let f1 = generate_f1(version, version.final_pc(), &[]);
    let mut out: Vec<(String, String)> = F1_PAIR
        .iter()
        .map(|rel| rel.to_string())
        .zip([f1.gkr_sol, f1.whir_sol])
        .collect();
    if let Some(source) = f1.setup_frontier_sol {
        out.push((F1_FRONTIER_CONTRACT.to_string(), source));
    }
    if let Some(rel) = version.wrong_final_pc_contract {
        out.push((
            format!("{F1_PREFIX}{rel}"),
            generate_f1(version, version.final_pc() ^ 1, &[]).gkr_sol,
        ));
    }
    // E8 control: the same GKR verifier pinned to another setup cap (one bit of the first digest);
    // a frontier cannot reduce to that cap, and the GKR verifier does not depend on it.
    let (_, proof, _) = version.load();
    let mut setup_cap = proof.whir_proof.setup_commitment.commitment.cap.cap.clone();
    setup_cap[0][0] ^= 1;
    out.push((
        F1_WRONG_SETUP_CAP.to_string(),
        generate_f1_with_setup(version, version.final_pc(), &setup_cap, None, &[]).gkr_sol,
    ));
    out
}

/// The oracle renders: v0 and F1 single-tx verifiers that log every keccak256 result.
fn instrumented_sources(version: &Version) -> Vec<(String, String)> {
    let v0 = generate(version, DEFAULT_REGISTRY_ADDRESS);
    let f1 = generate_f1(
        version,
        version.final_pc(),
        &[verifier_evm::generator::INSTRUMENTED],
    );
    [
        (
            "gkr_v0/src/GkrVerifier.sol",
            verifier_evm::instrument(&verifier_evm::single_tx_gkr(&v0.gkr_sol)),
        ),
        (
            "whir_v0/src/WhirVerifier.sol",
            verifier_evm::instrument(&verifier_evm::single_tx_whir(&v0.whir_sol)),
        ),
        ("gkr_f1/src/GkrVerifier.sol", f1.gkr_sol),
        ("whir_f1/src/WhirVerifier.sol", f1.whir_sol),
    ]
    .into_iter()
    .map(|(rel, src)| (format!("{INSTRUMENTED_PREFIX}{rel}"), src))
    .collect()
}

fn sources(out: &verifier_evm::GeneratedContracts) -> [&str; 3] {
    [&out.gkr_sol, &out.whir_sol, &out.registry_sol]
}

fn single_tx_sources(out: &verifier_evm::GeneratedContracts) -> [String; 2] {
    [
        verifier_evm::single_tx_gkr(&out.gkr_sol),
        verifier_evm::single_tx_whir(&out.whir_sol),
    ]
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
        for (rel, content) in SINGLE_TX.iter().zip(single_tx_sources(&out)) {
            write(&version, rel, &content);
        }
        for (rel, content) in f1_sources(&version)
            .into_iter()
            .chain(instrumented_sources(&version))
        {
            write(&version, &rel, &content);
        }
        if let Some(rel) = version.wrong_final_pc_contract {
            let wrong = generate_wrong_final_pc(&version, &registry_address).gkr_sol;
            write(&version, rel, &wrong);
            write(
                &version,
                &format!("{SINGLE_TX_PREFIX}{rel}"),
                &verifier_evm::single_tx_gkr(&wrong),
            );
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
    for version in common::available_versions("contract drift") {
        let test_pair = generate(version, DEFAULT_REGISTRY_ADDRESS);
        let stubs = generate(version, STUB_REGISTRY_ADDRESS);
        if let Some(rel) = version.wrong_final_pc_contract {
            let wrong = generate_wrong_final_pc(version, DEFAULT_REGISTRY_ADDRESS).gkr_sol;
            for (rel, expected) in [
                (rel.to_string(), wrong.clone()),
                (
                    format!("{SINGLE_TX_PREFIX}{rel}"),
                    verifier_evm::single_tx_gkr(&wrong),
                ),
            ] {
                let path = version.contract_path(&rel);
                let stored = std::fs::read_to_string(&path)
                    .expect("missing wrong-final-PC control verifier");
                assert_eq!(stored, expected, "{} is stale", path.display());
            }
        }
        for (rel, content) in f1_sources(version)
            .into_iter()
            .chain(instrumented_sources(version))
        {
            let path = version.contract_path(&rel);
            let checked_in = std::fs::read_to_string(&path)
                .unwrap_or_else(|_| panic!("missing {}", path.display()));
            assert!(
                checked_in == content,
                "{} is stale: rerun `cargo test -p verifier_evm --test generate_contracts -- --ignored`",
                path.display()
            );
        }
        let single_tx = single_tx_sources(&test_pair);
        for (rel, content) in TEST_PAIR
            .iter()
            .zip(sources(&test_pair))
            .chain(PRODUCTION_STUBS.iter().zip(sources(&stubs)))
            .chain(SINGLE_TX.iter().zip(single_tx.iter().map(String::as_str)))
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
    // The committed 2p21 layout and b' tuple are usable before a proof bundle
    // exists. Exercise its descriptor, including binary-derived exit PC, without
    // exporting verifier artifacts until the matching proof is available.
    let version = &common::L1_WRAP_2P21;
    let circuit = version.circuit();
    let mut config = version.prover_config();
    let (external_pow_bits, batching_pow_bits) = derived_pow_bits(version, &circuit, &config);
    assert_eq!((external_pow_bits, batching_pow_bits), (20, 16));
    let generate = |config: &prover::gkr::prover_config::ProverConfig| {
        verifier_evm::generate_verifiers(
            &circuit,
            config,
            version.pack_log2,
            external_pow_bits,
            batching_pow_bits,
            version.final_pc(),
            DEFAULT_REGISTRY_ADDRESS,
            version.digest_bytes,
        )
    };
    let mut mismatched_config = config.clone();
    mismatched_config.trace_len_log2 -= 1;
    assert!(std::panic::catch_unwind(|| generate(&mismatched_config)).is_err());
    let out = generate(&config);
    assert_eq!(
        solidity_constant(&out.gkr_sol, "__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS"),
        21
    );
    assert_eq!(config.sumcheck_explicit_output_size_log_2, 2);
    assert_eq!(solidity_constant(&out.gkr_sol, "GKR_OUT_LOG2"), 2);
    assert_eq!(solidity_constant(&out.gkr_sol, "GKR_OUT_LANES"), 4);
    assert_eq!(solidity_constant(&out.gkr_sol, "GKR_INIT_BYTES"), 640);
    assert!(out.gkr_sol.contains("lt(k, 19)"));
    assert!(out
        .gkr_sol
        .contains("gkr_dr_final(ptr, fs, batching, eq(k, 18)"));
    assert!(!out.gkr_sol.contains("lt(k, 17)"));
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
    for digest_bytes in [25, 32] {
        let out = verifier_evm::generate_verifiers(
            &circuit,
            &config,
            version.pack_log2,
            external_pow_bits,
            batching_pow_bits,
            version.final_pc(),
            DEFAULT_REGISTRY_ADDRESS,
            digest_bytes,
        );
        let mask = format!(
            "constant __TEMPLATE_DIGEST_MASK = 0x{}{};",
            "ff".repeat(digest_bytes),
            "00".repeat(32 - digest_bytes)
        );
        assert!(
            out.whir_sol.contains(&mask),
            "digest mask for {digest_bytes}"
        );
        assert_eq!(out.whir_sol.matches("__TEMPLATE_DIGEST_MASK)").count(), 3);
    }
    assert!(
        std::panic::catch_unwind(|| verifier_evm::generate_verifiers(
            &circuit,
            &config,
            version.pack_log2,
            external_pow_bits,
            batching_pow_bits,
            version.final_pc(),
            DEFAULT_REGISTRY_ADDRESS,
            24,
        ))
        .is_err()
    );
    for explicit_output_log2 in [1, 5] {
        config.sumcheck_explicit_output_size_log_2 = explicit_output_log2;
        assert!(std::panic::catch_unwind(|| generate(&config)).is_err());
    }
}

#[test]
fn descriptor_rejects_aux_drift_and_excess_gkr_pow() {
    for base in common::available_versions("descriptor aux drift") {
        for version in [
            Version {
                pack_log2: 3,
                ..*base
            },
            Version {
                external_pow_floor: 19,
                ..*base
            },
            Version {
                gkr_pow_cap: 19,
                ..*base
            },
        ] {
            assert!(
                std::panic::catch_unwind(|| generate(&version, DEFAULT_REGISTRY_ADDRESS)).is_err()
            );
        }
    }
}

#[test]
fn descriptor_rejects_aux_exit_pc_drift() {
    for base in common::available_versions("descriptor exit PC drift") {
        let version = Version {
            exit_pc: common::ExitPcSource::Frozen(0),
            ..*base
        };
        common::assert_panics_with("descriptor exit PC must match proof aux", || {
            generate(&version, DEFAULT_REGISTRY_ADDRESS)
        });
    }
}

#[test]
fn generator_rejects_inconsistent_base_oracle_geometry() {
    let version = common::L1_WRAP_2P21;
    let circuit = version.circuit();
    for field in ["lde_factor", "cap_size", "values_per_leaf"] {
        let mut config = version.prover_config();
        match field {
            "lde_factor" => config.lde_factor *= 2,
            "cap_size" => config.cap_size *= 2,
            "values_per_leaf" => config.base_oracles_values_per_leaf *= 2,
            _ => unreachable!(),
        }
        assert!(
            std::panic::catch_unwind(|| verifier_evm::generate_verifiers(
                &circuit,
                &config,
                version.pack_log2,
                20,
                16,
                version.final_pc(),
                DEFAULT_REGISTRY_ADDRESS,
                version.digest_bytes,
            ))
            .is_err(),
            "inconsistent base-oracle {field} accepted"
        );
    }
}

#[test]
fn wrong_final_pc_control_changes_only_the_expected_constant() {
    for version in common::available_versions("wrong final PC control") {
        let valid = generate(version, DEFAULT_REGISTRY_ADDRESS);
        let wrong = generate_wrong_final_pc(version, DEFAULT_REGISTRY_ADDRESS);
        assert_eq!(
            solidity_constant(&wrong.gkr_sol, "__TEMPLATE_EXPECTED_FINAL_PC"),
            version.final_pc() ^ 1
        );
        let differences: Vec<_> = valid
            .gkr_sol
            .lines()
            .zip(wrong.gkr_sol.lines())
            .filter(|(a, b)| a != b)
            .collect();
        assert_eq!(valid.gkr_sol.lines().count(), wrong.gkr_sol.lines().count());
        assert_eq!(differences.len(), 1);
        assert!(differences[0]
            .0
            .contains("constant __TEMPLATE_EXPECTED_FINAL_PC"));
        assert!(differences[0]
            .1
            .contains("constant __TEMPLATE_EXPECTED_FINAL_PC"));
        assert_eq!(valid.whir_sol, wrong.whir_sol);
        assert_eq!(valid.registry_sol, wrong.registry_sol);
    }
}

#[test]
fn single_tx_variants_change_only_the_handoff() {
    for version in common::available_versions("single-tx variants") {
        let two_tx = generate(version, DEFAULT_REGISTRY_ADDRESS);
        let [gkr, whir] = single_tx_sources(&two_tx);
        for (name, before, after, removed, added) in [
            ("GKR", &two_tx.gkr_sol, &gkr, 16, 11),
            ("WHIR", &two_tx.whir_sol, &whir, 14, 9),
        ] {
            let before: Vec<_> = before.lines().collect();
            let after: Vec<_> = after.lines().collect();
            let prefix = before
                .iter()
                .zip(&after)
                .take_while(|(a, b)| a == b)
                .count();
            let suffix = before[prefix..]
                .iter()
                .rev()
                .zip(after[prefix..].iter().rev())
                .take_while(|(a, b)| a == b)
                .count();
            assert_eq!(
                (
                    before.len() - prefix - suffix,
                    after.len() - prefix - suffix
                ),
                (removed, added),
                "{name}: single-tx edit spans unexpected lines"
            );
        }
        assert!(!gkr.contains("MARK_GKR_SELECTOR))"));
        assert!(gkr.contains("return(base, add(plen, 96))"));
        assert!(!whir.contains("MARK_WHIR_SELECTOR))"));
        assert!(whir.contains("return(0, 128)"));
    }
}

#[test]
fn f1_renders_read_calldata_only_in_the_decoders() {
    for version in common::available_versions("F1 calldata readers") {
        for (rel, source) in f1_sources(version) {
            // opcode uses, not identifiers such as `gate_calldataload`
            let readers = |src: &str| {
                ["calldataload(", "calldatacopy(", "calldatasize()"]
                    .iter()
                    .flat_map(|op| src.match_indices(op))
                    .filter(|(at, _)| {
                        !src[..*at]
                            .chars()
                            .next_back()
                            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                    })
                    .count()
            };
            if rel.contains("/gkr") {
                let start = source.find("// ── F1 decoder").expect("F1 decoder block");
                let end = start + source[start..].find("function f1_decode()").unwrap();
                let decode_end = end + source[end..].find("\n        }\n").unwrap();
                assert_eq!(
                    readers(&source[..start]) + readers(&source[decode_end..]),
                    0,
                    "{rel}: calldata read outside the F1 decoder"
                );
            }
        }
    }
}

#[test]
fn instrumented_renders_differ_only_by_the_log() {
    for version in common::available_versions("instrumented renders") {
        let production = generate_f1(version, version.final_pc(), &[]);
        let instrumented = generate_f1(
            version,
            version.final_pc(),
            &[verifier_evm::generator::INSTRUMENTED],
        );
        for (prod, inst) in [
            (&production.gkr_sol, &instrumented.gkr_sol),
            (&production.whir_sol, &instrumented.whir_sol),
        ] {
            assert!(
                !prod.contains("ilog_"),
                "production F1 render carries the log"
            );
            assert_eq!(&verifier_evm::instrument(prod), inst);
        }
    }
}

#[test]
fn f1_generator_rejects_a_profile_off_the_prover_config() {
    for version in common::available_versions("F1 profile vs config") {
        let (circuit, proof, _) = version.load();
        let config = version.prover_config();
        let setup_cap = &proof.whir_proof.setup_commitment.commitment.cap.cap;
        let frontier = version.setup_frontier();
        let generate = |params: &verifier_evm::encoding::FormatParams| {
            verifier_evm::generate_f1_verifiers(
                &circuit,
                &config,
                params,
                20,
                16,
                version.final_pc(),
                setup_cap,
                frontier
                    .as_ref()
                    .map(|(_, nodes)| (&nodes[..], DEFAULT_FRONTIER_ADDRESS)),
                &[],
            )
        };
        let mut params = version.f1_params();
        params.queries[0] -= 1;
        common::assert_panics_with("F1 profile differs from the prover config", || {
            generate(&params)
        });
        let mut params = version.f1_params();
        params.folds.swap(3, 4);
        common::assert_panics_with("F1 profile differs from the prover config", || {
            generate(&params)
        });
        let mut params = version.f1_params();
        params.pack_log2 = 3;
        assert!(std::panic::catch_unwind(|| generate(&params)).is_err());
        let params = version.f1_params();
        common::assert_panics_with("setup cap size", || {
            verifier_evm::generate_f1_verifiers(
                &circuit,
                &config,
                &params,
                20,
                16,
                version.final_pc(),
                &setup_cap[1..],
                frontier
                    .as_ref()
                    .map(|(_, nodes)| (&nodes[..], DEFAULT_FRONTIER_ADDRESS)),
                &[],
            )
        });
    }
}

#[test]
fn f1_generator_rejects_a_frontier_off_the_setup_cap() {
    for version in common::available_versions("F1 setup frontier binding") {
        let Some((_, mut nodes)) = version.setup_frontier() else {
            continue;
        };
        let (circuit, proof, _) = version.load();
        let config = version.prover_config();
        nodes[0][0] ^= 1;
        common::assert_panics_with(
            "the setup frontier does not reduce to the setup cap",
            || {
                verifier_evm::generate_f1_verifiers(
                    &circuit,
                    &config,
                    &version.f1_params(),
                    20,
                    16,
                    version.final_pc(),
                    &proof.whir_proof.setup_commitment.commitment.cap.cap,
                    Some((&nodes, DEFAULT_FRONTIER_ADDRESS)),
                    &[],
                )
            },
        );
    }
}
