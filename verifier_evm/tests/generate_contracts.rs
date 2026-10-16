//! Regenerates the merged on-chain verifier Solidity into the version's `generated_contracts/`
//! tree from the circuit artifact: the v0 and F1 `GkrWhirVerifier`s, the `SetupFrontier` data
//! contract, the negative controls and the instrumented oracle renders. The Foundry project
//! scaffolding (foundry.toml, the test registry and the tests) is committed static.

mod common;

use common::{
    Version, F1_FRONTIER_CONTRACT, F1_WRONG_FINAL_PC, F1_WRONG_SETUP_CAP, INSTRUMENTED_F1,
    INSTRUMENTED_V0, MERGED_F1, MERGED_V0,
};
use field::Proth120;
use verifier_evm::generator::INSTRUMENTED;

/// Where the F1 verifier reads its `SetupFrontier` data contract: the first contract the default
/// local deployer (anvil account 0, nonce 0) creates, so a plain local deployment lands there.
const DEFAULT_FRONTIER_ADDRESS: &str = "0x5FbDB2315678afecb367f032d93F642f64180aa3";

fn generate(version: &Version, flags: &[&str]) -> String {
    render(version, None, flags)
}

// Preserve the valid proof/transcript and change only the verifier's expected PC.
fn generate_wrong_final_pc(version: &Version) -> String {
    render(version, Some(version.final_pc() ^ 1), &[])
}

fn render(version: &Version, negative_test_exit_pc: Option<u32>, flags: &[&str]) -> String {
    version.require_bundle();
    let circuit = version.circuit();
    let config = version.prover_config();
    let final_pc = check_descriptor(version);
    let (external_pow_bits, batched_proximity_pow_bits) =
        derived_pow_bits(version, &circuit, &config);
    let out = verifier_evm::generate_verifier(
        &circuit,
        &config,
        version.pack_log2,
        external_pow_bits,
        batched_proximity_pow_bits,
        negative_test_exit_pc.unwrap_or(final_pc),
        version.inits_teardowns_top_bits,
        version.digest_bytes,
        flags,
    );
    // Check the emitted verifier's gates, not just the arguments passed to it.
    assert_eq!(
        solidity_constant(&out, "__TEMPLATE_EXTERNAL_POW_BITS"),
        external_pow_bits
    );
    assert_eq!(
        solidity_constant(&out, "__TEMPLATE_WHIR_BATCH_POW_BITS"),
        batched_proximity_pow_bits
    );
    out
}

/// The proof aux must match the descriptor (packing, external PoW floor, exit PC, top bits).
/// Returns the final PC.
fn check_descriptor(version: &Version) -> u32 {
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
    let (_, proof, _) = version.load();
    assert_eq!(
        version.inits_teardowns_top_bits,
        &proof.inits_and_teardowns_top_bits[..],
        "{}: descriptor inits/teardowns top bits must match the proof",
        version.name
    );
    final_pc
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

/// The value of a numeric `constant NAME = <literal expression>;` declaration.
fn solidity_constant(source: &str, name: &str) -> u32 {
    let line = source
        .lines()
        .find(|line| line.contains(&format!("constant {name} ")))
        .unwrap_or_else(|| panic!("no constant {name}"));
    let expr = line.split_once('=').unwrap().1.split_once(';').unwrap().0;
    eval_expr(expr)
}

/// Evaluates the generator's literal expressions (`32 * 7`, `1 << 2`, `(104 + 16 - 1) >> 4`).
fn eval_expr(expr: &str) -> u32 {
    let expr = expr.trim();
    if let Some(inner) = expr.strip_prefix('(').and_then(|e| e.strip_suffix(')')) {
        let mut depth = 0i32;
        let balanced = inner.chars().all(|c| {
            depth += match c {
                '(' => 1,
                ')' => -1,
                _ => 0,
            };
            depth >= 0
        });
        if balanced {
            return eval_expr(inner);
        }
    }
    // loosest binding first; the last top-level operator of a level is the root (left-assoc)
    for ops in [&["<<", ">>"][..], &["+", "-"], &["*"]] {
        let mut depth = 0i32;
        let mut split = None;
        let mut i = 0;
        while i < expr.len() {
            match expr.as_bytes()[i] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                _ if depth == 0 => {
                    if let Some(op) = ops.iter().find(|op| expr[i..].starts_with(**op)) {
                        split = Some((i, *op));
                        i += op.len();
                        continue;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        if let Some((at, op)) = split {
            let (l, r) = (eval_expr(&expr[..at]), eval_expr(&expr[at + op.len()..]));
            return match op {
                "<<" => l << r,
                ">>" => l >> r,
                "+" => l + r,
                "-" => l - r,
                _ => l * r,
            };
        }
    }
    expr.parse()
        .unwrap_or_else(|_| panic!("not a literal: {expr}"))
}

fn generate_f1(version: &Version, final_pc: u32, flags: &[&str]) -> verifier_evm::F1Contracts {
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
) -> verifier_evm::F1Contracts {
    let circuit = version.circuit();
    let config = version.prover_config();
    check_descriptor(version);
    let params = match setup_frontier {
        Some(_) => version.f1_params(),
        None => version
            .f1_params()
            .with_setup_frontier(config.cap_size.trailing_zeros() as usize),
    };
    let (external_pow_bits, batched_proximity_pow_bits) =
        derived_pow_bits(version, &circuit, &config);
    verifier_evm::generate_f1_verifier(
        &circuit,
        &config,
        &params,
        external_pow_bits,
        batched_proximity_pow_bits,
        final_pc,
        version.inits_teardowns_top_bits,
        setup_cap,
        setup_frontier.map(|nodes| (nodes, DEFAULT_FRONTIER_ADDRESS)),
        flags,
    )
}

/// `(relative path, source)` of every generated output of `version`.
fn generated_sources(version: &Version) -> Vec<(String, String)> {
    let mut out = vec![(MERGED_V0.to_string(), generate(version, &[]))];
    if let Some(rel) = version.wrong_final_pc_contract {
        out.push((rel.to_string(), generate_wrong_final_pc(version)));
    }
    let f1 = generate_f1(version, version.final_pc(), &[]);
    out.push((MERGED_F1.to_string(), f1.verifier_sol));
    if let Some(source) = f1.setup_frontier_sol {
        out.push((F1_FRONTIER_CONTRACT.to_string(), source));
    }
    out.push((
        F1_WRONG_FINAL_PC.to_string(),
        generate_f1(version, version.final_pc() ^ 1, &[]).verifier_sol,
    ));
    // E8 control: the F1 verifier pinned to another setup cap (one bit of the first digest), so
    // its transcript and setup commitment differ; a frontier cannot reduce to that cap.
    let (_, proof, _) = version.load();
    let mut setup_cap = proof.whir_proof.setup_commitment.commitment.cap.cap.clone();
    setup_cap[0][0] ^= 1;
    out.push((
        F1_WRONG_SETUP_CAP.to_string(),
        generate_f1_with_setup(version, version.final_pc(), &setup_cap, None, &[]).verifier_sol,
    ));
    // The oracle renders: v0 and F1 verifiers that log every transcript keccak256 result.
    out.push((
        INSTRUMENTED_V0.to_string(),
        generate(version, &[INSTRUMENTED]),
    ));
    out.push((
        INSTRUMENTED_F1.to_string(),
        generate_f1(version, version.final_pc(), &[INSTRUMENTED]).verifier_sol,
    ));
    out
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
    for version in common::selected_versions() {
        for (rel, content) in generated_sources(&version) {
            write(&version, &rel, &content);
        }
    }
}

#[test]
fn checked_in_contracts_are_current() {
    for version in common::available_versions("contract drift") {
        for (rel, content) in generated_sources(version) {
            let path = version.contract_path(&rel);
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
    // The committed 2p21 layout and tuple are usable before a proof bundle exists. Exercise its
    // descriptor, including binary-derived exit PC, without exporting verifier artifacts.
    let version = &common::L1_WRAP_2P21;
    let circuit = version.circuit();
    let mut config = version.prover_config();
    let (external_pow_bits, batching_pow_bits) = derived_pow_bits(version, &circuit, &config);
    assert_eq!((external_pow_bits, batching_pow_bits), (20, 16));
    let generate_with = |config: &prover::gkr::prover_config::ProverConfig, digest_bytes| {
        verifier_evm::generate_verifier(
            &circuit,
            config,
            version.pack_log2,
            external_pow_bits,
            batching_pow_bits,
            version.final_pc(),
            version.inits_teardowns_top_bits,
            digest_bytes,
            &[],
        )
    };
    let generate = |config: &prover::gkr::prover_config::ProverConfig| {
        generate_with(config, version.digest_bytes)
    };
    let mut mismatched_config = config.clone();
    mismatched_config.trace_len_log2 -= 1;
    assert!(std::panic::catch_unwind(|| generate(&mismatched_config)).is_err());
    let out = generate(&config);
    assert_eq!(config.sumcheck_explicit_output_size_log_2, 2);
    for (name, value) in [
        ("__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS", 21),
        ("__TEMPLATE_GKR_OUTPUT_LOG2", 2),
        ("__TEMPLATE_GKR_OUTPUT_EVALS", 4),
        ("__TEMPLATE_GKR_INIT_BYTES", 640),
        ("__TEMPLATE_GKR_DIM_REDUCE_LAYERS", 19),
        ("__TEMPLATE_WHIR_NZ", 24),
        ("__TEMPLATE_WHIR_MERGED_MW", 13),
        ("__TEMPLATE_WHIR_SETUP_MERGED", 2),
    ] {
        assert_eq!(solidity_constant(&out, name), value, "{name}");
    }
    assert!(out.contains("default { fold := 4 q := 5 pow_bits := 17 qib := 27 vp := 16 cb := 20 }"));
    let mut bad_schedule = config.clone();
    bad_schedule.whir_schedule.whir_steps_lde_factors[0] *= 2;
    assert!(std::panic::catch_unwind(|| generate(&bad_schedule)).is_err());
    for digest_bytes in [25, 32] {
        let out = generate_with(&config, digest_bytes);
        let mask = format!(
            "constant __TEMPLATE_DIGEST_MASK = 0x{}{};",
            "ff".repeat(digest_bytes),
            "00".repeat(32 - digest_bytes)
        );
        assert!(out.contains(&mask), "digest mask for {digest_bytes}");
        assert_eq!(out.matches("__TEMPLATE_DIGEST_MASK)").count(), 3);
    }
    assert!(std::panic::catch_unwind(|| generate_with(&config, 24)).is_err());
    for explicit_output_log2 in [0, 21] {
        config.sumcheck_explicit_output_size_log_2 = explicit_output_log2;
        assert!(std::panic::catch_unwind(|| generate(&config)).is_err());
    }
}

/// Pack 3: 13 memory+witness and 2 setup claims (10 = 8 + 2), the handoff scratch disjoint inside
/// the absorb region, the five-round schedule and the 2^7 tail, in both formats.
#[test]
fn generator_renders_pack3() {
    for version in common::available_versions("pack 3 render") {
        let v0 = generate(version, &[]);
        let f1 = generate_f1(version, version.final_pc(), &[]).verifier_sol;
        for source in [&v0, &f1] {
            for (name, value) in [
                ("__TEMPLATE_WHIR_PACK_LOG2", 3),
                ("__TEMPLATE_WHIR_PACK", 8),
                ("__TEMPLATE_WHIR_MERGED_MW", 13),
                ("__TEMPLATE_WHIR_SETUP_MERGED", 2),
                ("__TEMPLATE_WHIR_GCOUNT", 16),
                ("__TEMPLATE_WHIR_NZ", 24),
                ("__TEMPLATE_WHIR_RFIN", 7),
                ("__TEMPLATE_WHIR_NUM_ROUNDS", 5),
                ("__TEMPLATE_GKR_HANDOFF_MERGED_OFFSET", 96),
                ("__TEMPLATE_GKR_HANDOFF_FOLD_OFFSET", 576),
            ] {
                assert_eq!(solidity_constant(source, name), value, "{name}");
            }
            assert!(solidity_constant(source, "__TEMPLATE_GKR_ABS_BYTES") >= 576 + 8 * 32);
            for row in [
                "case 0 { fold := 1 q := 12 pow_bits := 30 qib := 30 vp := 2 cb := 7 }",
                "case 1 { fold := 4 q := 11 pow_bits := 27 qib := 27 vp := 16 cb := 8 }",
                "case 2 { fold := 4 q := 7 pow_bits := 30 qib := 27 vp := 16 cb := 12 }",
                "case 3 { fold := 4 q := 6 pow_bits := 20 qib := 27 vp := 16 cb := 16 }",
                "default { fold := 4 q := 5 pow_bits := 17 qib := 27 vp := 16 cb := 20 }",
            ] {
                assert!(source.contains(row), "missing `{row}`");
            }
        }
        assert!(f1.contains("function horner_128(x)"));
    }
}

#[test]
fn descriptor_rejects_aux_drift_and_excess_gkr_pow() {
    for base in common::available_versions("descriptor aux drift") {
        for version in [
            Version {
                pack_log2: base.pack_log2 - 1,
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
            Version {
                inits_teardowns_top_bits: &[1, 0],
                ..*base
            },
        ] {
            assert!(std::panic::catch_unwind(|| generate(&version, &[])).is_err());
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
            generate(&version, &[])
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
            std::panic::catch_unwind(|| verifier_evm::generate_verifier(
                &circuit,
                &config,
                version.pack_log2,
                20,
                16,
                version.final_pc(),
                version.inits_teardowns_top_bits,
                version.digest_bytes,
                &[],
            ))
            .is_err(),
            "inconsistent base-oracle {field} accepted"
        );
    }
}

/// The wrong-final-PC controls differ from their verifier only in the pinned PC.
#[test]
fn wrong_final_pc_controls_change_only_the_pinned_pc() {
    fn differences(valid: &str, control: &str) -> Vec<(String, String)> {
        assert_eq!(valid.lines().count(), control.lines().count());
        valid
            .lines()
            .zip(control.lines())
            .filter(|(a, b)| a != b)
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect()
    }
    for version in common::available_versions("wrong final PC controls") {
        let wrong = generate_wrong_final_pc(version);
        assert_eq!(
            solidity_constant(&wrong, "__TEMPLATE_EXPECTED_FINAL_PC"),
            version.final_pc() ^ 1
        );
        let diff = differences(&generate(version, &[]), &wrong);
        assert_eq!(diff.len(), 1);
        assert!(diff[0].0.contains("constant __TEMPLATE_EXPECTED_FINAL_PC"));
        assert!(diff[0].1.contains("constant __TEMPLATE_EXPECTED_FINAL_PC"));

        let diff = differences(
            &generate_f1(version, version.final_pc(), &[]).verifier_sol,
            &generate_f1(version, version.final_pc() ^ 1, &[]).verifier_sol,
        );
        assert_eq!(
            diff.len(),
            2,
            "F1: the PC constant and the decoder's pinned PC"
        );
        assert!(diff[0].0.contains("constant __TEMPLATE_EXPECTED_FINAL_PC"));
        assert!(diff[1].0.contains("// pinned final PC"));
    }
}

/// Calldata reads in the F1 render: the GKR half only in the decoder, the WHIR half from the
/// stream after the F1 GKR section.
#[test]
fn f1_gkr_half_reads_calldata_only_in_the_decoder() {
    for version in common::available_versions("F1 calldata readers") {
        let source = generate_f1(version, version.final_pc(), &[]).verifier_sol;
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
        let decoder = source.find("// ── F1 decoder").expect("F1 decoder block");
        let decode = decoder + source[decoder..].find("function f1_decode()").unwrap();
        let decoder_end = decode + source[decode..].find("\n        }\n").unwrap();
        let whir = source
            .find("        function sink2(a, b)")
            .expect("WHIR half");
        let whir_end = whir
            + source[whir..]
                .find("// SPILL OVERWRITE PREVENTION")
                .unwrap();
        assert!(decoder_end < whir);
        assert_eq!(
            readers(&source[..decoder])
                + readers(&source[decoder_end..whir])
                + readers(&source[whir_end..]),
            0,
            "calldata read outside the F1 decoder and the WHIR half"
        );
        assert!(readers(&source[whir..whir_end]) > 0);
    }
}

/// The instrumented renders log every non-Merkle keccak256 and return the statement with the
/// log instead of calling the registry.
#[test]
fn instrumented_renders_carry_the_log() {
    for version in common::available_versions("instrumented renders") {
        for (production, instrumented) in [
            (generate(version, &[]), generate(version, &[INSTRUMENTED])),
            (
                generate_f1(version, version.final_pc(), &[]).verifier_sol,
                generate_f1(version, version.final_pc(), &[INSTRUMENTED]).verifier_sol,
            ),
        ] {
            assert!(
                !production.contains("ilog_"),
                "production render carries the log"
            );
            assert_eq!(instrumented.matches("ilog_return(0, 96)").count(), 1);
            // calls in code, not in `//` comments (instrument leaves those alone)
            let code: String = production
                .lines()
                .map(|line| line.split("//").next().unwrap())
                .collect::<Vec<_>>()
                .join("\n");
            let keccaks = code.matches("keccak256(").count();
            let merkle = code.matches("keccak256(0, 64)").count()
                + code
                    .matches("keccak256(__TEMPLATE_WHIR_LEAF_PTR, mul(")
                    .count();
            assert_eq!(
                instrumented.matches("ilog_k(keccak256(").count(),
                keccaks - merkle
            );
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
        let generate = |params: &verifier_evm::encoding::FormatParams, setup_cap: &[[u32; 8]]| {
            verifier_evm::generate_f1_verifier(
                &circuit,
                &config,
                params,
                20,
                16,
                version.final_pc(),
                version.inits_teardowns_top_bits,
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
            generate(&params, setup_cap)
        });
        let mut params = version.f1_params();
        params.folds.swap(0, 1);
        common::assert_panics_with("F1 profile differs from the prover config", || {
            generate(&params, setup_cap)
        });
        common::assert_panics_with("setup cap size", || {
            generate(&version.f1_params(), &setup_cap[1..])
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
                verifier_evm::generate_f1_verifier(
                    &circuit,
                    &config,
                    &version.f1_params(),
                    20,
                    16,
                    version.final_pc(),
                    version.inits_teardowns_top_bits,
                    &proof.whir_proof.setup_commitment.commitment.cap.cap,
                    Some((&nodes, DEFAULT_FRONTIER_ADDRESS)),
                    &[],
                )
            },
        );
    }
}
