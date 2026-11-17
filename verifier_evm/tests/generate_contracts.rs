//! Regenerate the L1 wrap verifier and its ignored negative controls from the canonical bundle.
mod common;
use common::MERGED_VERIFIER;
use prover::gkr::prover_config::example_configs::l1_wrap;
use verifier_evm::generator::MAX_GKR_POW_BITS;

// CreateX deployCreate2 address for TestRegistry (factory/salt in deploy.sh).
// TestRegistry intentionally does not import the generated verifier, keeping its initcode stable.
const REGISTRY_ADDRESS: [u8; 20] = [
    0x78, 0xd5, 0x49, 0xf2, 0xa1, 0x40, 0x92, 0x3c, 0x51, 0x7c, 0x23, 0xb0, 0x08, 0xdf, 0xfe, 0x97,
    0x9b, 0x3c, 0x4e, 0x91,
];

/// The proof aux must match the pinned inputs (external PoW floor, exit PC, top bits).
/// Packing comes from the prover config.
/// Returns the final PC.
fn check_pinned_inputs() -> u32 {
    let (_, proof, operation_mode) = common::load();
    let prover::gkr::prover::OperationMode::SingleChunk {
        external_challenges_pow_bits,
        final_pc,
        ..
    } = operation_mode
    else {
        panic!("expected single-chunk operation mode");
    };
    assert_eq!(
        prover::gkr::prover_config::example_configs::l1_wrap::EXTERNAL_CHALLENGES_POW_BITS,
        external_challenges_pow_bits,
        "pinned external PoW floor must match proof aux"
    );
    assert_eq!(
        common::final_pc(),
        final_pc,
        "pinned exit PC must match proof aux"
    );
    assert_eq!(
        common::INITS_TEARDOWNS_TOP_BITS,
        &proof.inits_and_teardowns_top_bits[..],
        "pinned inits/teardowns top bits must match the proof"
    );
    final_pc
}

fn generate_wrap(pc: u32) -> verifier_evm::WrapContracts {
    let (circuit, proof, _) = common::load();
    let config = common::prover_config();
    check_pinned_inputs();
    let (_, nodes) = common::setup_frontier();
    verifier_evm::generate_wrap_verifier(
        &circuit,
        &config,
        &common::format_params(),
        pc,
        common::INITS_TEARDOWNS_TOP_BITS,
        &proof.whir_proof.setup_commitment.commitment.cap.cap,
        &nodes,
        REGISTRY_ADDRESS,
    )
}

fn generated_sources() -> Vec<(String, String)> {
    let pc = common::final_pc();
    let contracts = generate_wrap(pc);
    let wrong = generate_wrap(pc ^ 1);
    // Preserve the complete former data-contract runtime, including its leading STOP.
    // The code tail makes its placement independent of Solidity's metadata trailer.
    let source = &contracts.verifier_sol;
    assert!(!source.contains("SetupFrontier"));
    assert!(!source.contains("extcodecopy("));
    assert!(!source.contains("extcodehash("));
    assert!(source.contains("constructor()"));
    assert!(source.contains("sub(codesize(), __TEMPLATE_SETUP_DATA_BYTES)"));
    let data = hex::decode(
        source
            .split_once("hex\"")
            .unwrap()
            .1
            .split('"')
            .next()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(data.len(), 16_410);
    use sha3::{Digest, Keccak256};
    assert_eq!(
        hex::encode(Keccak256::digest(&data)),
        "f5e33e946c45cc936b514c2158e8ac6ce4085a320a7cbd8dde3d90d37b7301ed"
    );
    // The negative changes only the decoder's pinned PC word.
    assert_eq!(
        contracts.verifier_sol.lines().count(),
        wrong.verifier_sol.lines().count()
    );
    let differences: Vec<_> = contracts
        .verifier_sol
        .lines()
        .zip(wrong.verifier_sol.lines())
        .filter(|(a, b)| a != b)
        .collect();
    assert_eq!(differences.len(), 1);
    assert!(differences
        .iter()
        .all(|(a, b)| a.contains("// pinned final PC") && b.contains("// pinned final PC")));
    assert!(source.contains("address(0x0078d549f2a140923c517c23b008dffe979b3c4e91)"));
    assert!(!source.contains("abi.encode(registry_)"));
    assert!(source.contains("ptr := add(SEED_PTR(), __TEMPLATE_GKR_CACHE_OFFSET)"));
    assert!(source.contains("__TEMPLATE_GKR_CACHE_OFFSET         = 448;"));
    assert!(source.contains("__TEMPLATE_GKR_SEED_BYTES           = 32 * 34;"));
    let (circuit, proof, mode) = common::load();
    let config = common::prover_config();
    let common::pow::PowLeadingZeros {
        external,
        batching,
        queries,
        folding,
        ood,
    } = common::pow::leading_zeros(&circuit, &proof, &mode, &config);
    eprintln!("PoW leading zeros: external={external}, batching={batching}, queries={queries:?}, folding={folding:?}, OOD={ood:?}");
    let schedule = config.whir_schedule.queries_pow_bits_per_round();
    assert!(
        external < MAX_GKR_POW_BITS && batching < MAX_GKR_POW_BITS,
        "no room under the GKR PoW cap"
    );
    for (&zeros, &bits) in queries.iter().zip(&schedule) {
        assert!(zeros >= bits, "honest proof misses query PoW");
    }
    let mut negative = vec![
        ("wrong_final_pc".into(), wrong.verifier_sol),
        (
            "external_pow".into(),
            raised_difficulty(source, "__TEMPLATE_EXTERNAL_POW_BITS", external + 1),
        ),
        (
            "batching_pow".into(),
            raised_difficulty(source, "__TEMPLATE_WHIR_BATCH_POW_BITS", batching + 1),
        ),
    ];
    for (round, &zeros) in queries.iter().enumerate() {
        // Test-only text replacements may exceed the production cap, but must remain
        // representable by shr(sub(256, bits), digest). Cover the final default arm too.
        assert!(zeros < 256, "query PoW control cannot exceed 256 bits");
        let selector = if round + 1 == queries.len() {
            "default".to_owned()
        } else {
            format!("case {round}")
        };
        negative.push((
            format!("query_pow_{round}"),
            raised_query_difficulty(source, &selector, schedule[round], zeros + 1),
        ));
        if !folding[round].is_empty() {
            let zeros = *folding[round].iter().max().unwrap();
            let bits = if round == 0 {
                config.whir_schedule.base_round.folding_pow_bits
            } else {
                config.whir_schedule.internal_rounds[round - 1].folding_pow_bits
            };
            assert!(
                folding[round].iter().all(|&z| z >= bits),
                "honest proof misses folding PoW"
            );
            assert!(zeros < 256, "folding control cannot exceed 256 bits");
            negative.push((
                format!("folding_pow_{round}"),
                raised_round_difficulty(source, &selector, "fold_pow_bits", bits, zeros + 1),
            ));
        }
        if let Some(Some(zeros)) = ood.get(round) {
            // Round r commits intermediate oracle r+1; its OOD draw happens here.
            let bits = config.whir_schedule.internal_rounds[round].ood_pow_bits;
            assert!(*zeros >= bits, "honest proof misses OOD PoW");
            assert!(*zeros < 256, "OOD control cannot exceed 256 bits");
            negative.push((
                format!("ood_pow_{round}"),
                raised_round_difficulty(source, &selector, "ood_pow_bits", bits, zeros + 1),
            ));
        }
    }
    let mut files = Vec::new();
    // Share the compiler settings, omitting the main project's test file permissions.
    let foundry = include_str!("../generated_contracts/l1_wrap/merged/foundry.toml")
        .split("fs_permissions")
        .next()
        .unwrap();
    for (name, control) in negative {
        assert_one_changed_line(source, &control);
        files.push((format!("negative/{name}/src/GkrWhirVerifier.sol"), control));
        files.push((format!("negative/{name}/foundry.toml"), foundry.to_owned()));
    }
    files.push((MERGED_VERIFIER.into(), contracts.verifier_sol));
    files.push(("merged/MEMORY_LAYOUT.md".into(), contracts.memory_layout));
    files
}

// Controls use the real generator's complete output, changing exactly one difficulty.
// They intentionally cannot be produced through the production API's parameter guards.
fn assert_one_changed_line(source: &str, control: &str) {
    assert_eq!(source.lines().count(), control.lines().count());
    assert_eq!(
        source
            .lines()
            .zip(control.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
}

fn raised_difficulty(source: &str, name: &str, bits: u32) -> String {
    let line = source
        .lines()
        .find(|line| line.contains(&format!("constant {name} ")))
        .unwrap();
    let (prefix, rest) = line.split_once('=').unwrap();
    let (old, suffix) = rest.split_once(';').unwrap();
    assert!(
        bits > old.trim().parse::<u32>().unwrap(),
        "control must raise PoW"
    );
    source.replacen(line, &format!("{prefix}= {bits};{suffix}"), 1)
}

fn raised_query_difficulty(source: &str, selector: &str, old: u32, new: u32) -> String {
    raised_round_difficulty(source, selector, "pow_bits", old, new)
}

fn raised_round_difficulty(source: &str, selector: &str, name: &str, old: u32, new: u32) -> String {
    let line = source
        .lines()
        .find(|line| line.contains(&format!("{selector} {{ fold :=")))
        .unwrap();
    let target = format!(" {name} := {old}");
    assert_eq!(line.matches(&target).count(), 1);
    source.replacen(
        line,
        &line.replace(&target, &format!(" {name} := {new}")),
        1,
    )
}

#[test]
fn generator_rejects_invalid_inputs() {
    let (mut circuit, proof, _) = common::load();
    let config = common::prover_config();
    let (_, nodes) = common::setup_frontier();
    let params = common::format_params();
    let generate = |circuit: &common::Circuit,
                    config: &prover::gkr::prover_config::ProverConfig,
                    top: &[u32]| {
        verifier_evm::generate_wrap_verifier(
            circuit,
            config,
            &params,
            common::final_pc(),
            top,
            &proof.whir_proof.setup_commitment.commitment.cap.cap,
            &nodes,
            REGISTRY_ADDRESS,
        )
    };
    let rejects = |circuit: &common::Circuit,
                   config: &prover::gkr::prover_config::ProverConfig,
                   top: &[u32],
                   expected: &str| {
        let Err(panic) = std::panic::catch_unwind(|| generate(circuit, config, top)) else {
            panic!("generator accepted invalid inputs");
        };
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(message.contains(expected), "unexpected panic: {message}");
    };
    for top in [&[0, 0][..], &[1, 0], &[0, 256]] {
        rejects(&circuit, &config, top, "inits/teardowns top bits");
    }
    for bits in [l1_wrap::MAX_POW_BITS + 1, 257] {
        let mut config = config.clone();
        config.whir_schedule.base_round.queries_pow_bits = bits;
        rejects(
            &circuit,
            &config,
            common::INITS_TEARDOWNS_TOP_BITS,
            "query PoW",
        );
    }
    // A layout whose lookup requirement exceeds the GKR cap must fail at generation.
    circuit.num_generic_lookups = 1 << 32;
    rejects(
        &circuit,
        &config,
        common::INITS_TEARDOWNS_TOP_BITS,
        "external challenges PoW",
    );
}

fn write(rel: &str, content: &str) {
    let p = common::contract_path(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(&p, content).unwrap();
    eprintln!("wrote {} ({} bytes)", p.display(), content.len());
}

#[test]
#[ignore = "writes committed generated_contracts"]
fn generate_contracts_into_dir() {
    for (rel, content) in generated_sources() {
        write(&rel, &content);
    }
}
