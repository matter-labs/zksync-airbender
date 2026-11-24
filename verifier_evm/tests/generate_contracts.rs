//! Regenerate the L1 wrap verifier and its ignored negative controls from the canonical bundle.
mod common;
use common::MERGED_VERIFIER;
use prover::definitions::SoundnessMode;
use sha3::{Digest, Keccak256};

// CreateX deployCreate2 address for TestRegistry (factory/salt in deploy.sh).
// TestRegistry intentionally does not import the generated verifier, keeping its initcode stable.
const REGISTRY_ADDRESS: [u8; 20] = [
    0x78, 0xd5, 0x49, 0xf2, 0xa1, 0x40, 0x92, 0x3c, 0x51, 0x7c, 0x23, 0xb0, 0x08, 0xdf, 0xfe, 0x97,
    0x9b, 0x3c, 0x4e, 0x91,
];

/// The proof aux must match the pinned inputs (external PoW floor, exit PC, top bits).
/// Packing comes from the prover config.
/// Returns the final PC.
fn check_pinned_inputs(
    mode: SoundnessMode,
    proof: &common::Proof,
    operation_mode: &prover::gkr::prover::OperationMode,
) -> u32 {
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
        *external_challenges_pow_bits,
        "pinned external PoW floor must match proof aux"
    );
    assert_eq!(
        common::final_pc(mode),
        *final_pc,
        "pinned exit PC must match proof aux"
    );
    assert_eq!(
        common::INITS_TEARDOWNS_TOP_BITS,
        &proof.inits_and_teardowns_top_bits[..],
        "pinned inits/teardowns top bits must match the proof"
    );
    *final_pc
}

fn generated_sources(mode: SoundnessMode) -> Vec<(String, String)> {
    let (circuit, proof, operation_mode) = common::load(mode);
    let config = common::prover_config(mode);
    let pc = check_pinned_inputs(mode, &proof, &operation_mode);
    let (level, nodes) = common::setup_frontier(mode);
    let params = verifier_evm::encoding::FormatParams {
        setup_frontier_level: level,
    };
    let generate = |pc| {
        verifier_evm::generate_wrap_verifier(
            &circuit,
            &config,
            &params,
            pc,
            common::INITS_TEARDOWNS_TOP_BITS,
            &proof.whir_proof.setup_commitment.commitment.cap.cap,
            &nodes,
            REGISTRY_ADDRESS,
        )
    };
    let contracts = generate(pc);
    let wrong = generate(pc ^ 1);
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
    let data_hash = hex::encode(Keccak256::digest(&data));
    if mode == SoundnessMode::PessimisticConjecture {
        assert_eq!(data.len(), 29_210);
        assert_eq!(
            data_hash,
            "7024dc38fe6be11ae2b04cf75f6210dfdaeced21bde20b3e5836c01737528b85"
        );
    }
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
    let common::pow::PowLeadingZeros {
        external,
        batching,
        queries,
        folding,
        ood,
    } = common::pow::leading_zeros(&circuit, &proof, &operation_mode, &config);
    eprintln!("PoW leading zeros: external={external}, batching={batching}, queries={queries:?}, folding={folding:?}, OOD={ood:?}");
    let schedule = config.whir_schedule.queries_pow_bits_per_round();
    assert!(
        external < u64::BITS && batching < u64::BITS,
        "negative control needs a difficulty within the calldata nonce width"
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
        // The raised difficulty (zeros + 1) must fit the 64-bit calldata nonce width.
        // Cover the final default arm too.
        assert!(
            zeros < u64::BITS,
            "query PoW control cannot exceed the calldata nonce width"
        );
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
            assert!(
                zeros < u64::BITS,
                "folding PoW control cannot exceed the calldata nonce width"
            );
            negative.push((
                format!("folding_pow_{round}"),
                raised_round_difficulty(source, &selector, "fold_pow_bits", bits, zeros + 1),
            ));
        }
        if let Some(Some(zeros)) = ood.get(round) {
            // Round r commits intermediate oracle r+1; its OOD draw happens here.
            let bits = config.whir_schedule.internal_rounds[round].ood_pow_bits;
            assert!(*zeros >= bits, "honest proof misses OOD PoW");
            assert!(
                *zeros < u64::BITS,
                "OOD PoW control cannot exceed the calldata nonce width"
            );
            negative.push((
                format!("ood_pow_{round}"),
                raised_round_difficulty(source, &selector, "ood_pow_bits", bits, zeros + 1),
            ));
        }
    }
    let mut files = Vec::new();
    // Share the compiler settings, omitting the main project's test file permissions.
    let foundry = include_str!("forge/foundry.toml")
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
    let data_path = format!("../../../debug_data/{}", mode.file_suffix());
    let folds = config.whir_schedule.fold_steps();
    let padded_round = if folds.last() == Some(&5) {
        "_rejectsRunPad(_finalRound(\"_sumcheck\")); // fold 5: ten fields, then five folding nonces".into()
    } else {
        let round = (1..folds.len())
            .rfind(|&round| !(2 * folds[round] * 123).is_multiple_of(8))
            .expect("a padded internal WHIR sumcheck run");
        format!("_rejectsRunPad(\"whir_{round}_sumcheck\");")
    };
    let controls = include_str!("forge/Merged.t.sol")
        .replace("@CAP_SIZE@", &config.cap_size.to_string())
        .replace("@SETUP_HASH@", &data_hash)
        .replace("@PADDED_WHIR_ROUND@", &padded_round)
        .replace(
            "@SETUP_SIZE@",
            &format!("{}_{:03}", data.len() / 1000, data.len() % 1000),
        );
    files.extend([
        (
            "merged/foundry.toml".into(),
            include_str!("forge/foundry.toml").replace("@DATA@", &data_path),
        ),
        (
            "merged/src/TestRegistry.sol".into(),
            include_str!("forge/TestRegistry.sol").into(),
        ),
        (
            "merged/test/MergedBase.sol".into(),
            include_str!("forge/MergedBase.sol").replace("@DATA@", &data_path),
        ),
        ("merged/test/Merged.t.sol".into(), controls),
        (
            "merged/script/SendProof.s.sol".into(),
            include_str!("forge/SendProof.s.sol").replace("@DATA@", &data_path),
        ),
    ]);
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
    let mode = SoundnessMode::PessimisticConjecture;
    let (circuit, proof, _) = common::load(mode);
    let config = common::prover_config(mode);
    let (_, nodes) = common::setup_frontier(mode);
    let params = common::format_params(mode);
    let generate = |circuit: &common::Circuit,
                    config: &prover::gkr::prover_config::ProverConfig,
                    top: &[u32]| {
        verifier_evm::generate_wrap_verifier(
            circuit,
            config,
            &params,
            common::final_pc(mode),
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
    let mut high = config.clone();
    high.whir_schedule.base_round.queries_pow_bits = 64;
    high.whir_schedule.base_round.batching_pow_bits = Some(64);
    generate(&circuit, &high, common::INITS_TEARDOWNS_TOP_BITS);

    high.whir_schedule.base_round.queries_pow_bits = 65;
    rejects(
        &circuit,
        &high,
        common::INITS_TEARDOWNS_TOP_BITS,
        "query PoW",
    );
    high.whir_schedule.base_round.queries_pow_bits = 64;
    high.whir_schedule.base_round.batching_pow_bits = Some(65);
    rejects(
        &circuit,
        &high,
        common::INITS_TEARDOWNS_TOP_BITS,
        "WHIR batching PoW",
    );
}

fn write(mode: SoundnessMode, rel: &str, content: &str) {
    let p = common::contract_path(mode, rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(&p, content).unwrap();
    eprintln!("wrote {} ({} bytes)", p.display(), content.len());
}

#[test]
#[ignore = "writes committed generated_contracts"]
fn generate_contracts_into_dir() {
    for &mode in SoundnessMode::ALL {
        for (rel, content) in generated_sources(mode) {
            write(mode, &rel, &content);
        }
    }
}
