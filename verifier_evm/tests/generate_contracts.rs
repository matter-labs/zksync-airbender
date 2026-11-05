//! Regenerate the L1 wrap verifier and its wrong-final-PC control from the canonical bundle.
mod common;
use common::{F1_FRONTIER_CONTRACT, F1_WRONG_FINAL_PC, MERGED_F1};
use field::Proth120;

/// The proof aux must match the descriptor (external PoW floor, exit PC, top bits).
/// Packing comes from the prover config.
/// Returns the final PC.
fn check_descriptor() -> u32 {
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
        prover::gkr::prover_config::example_configs::l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
        external_challenges_pow_bits,
        "descriptor external PoW floor must match proof aux"
    );
    assert_eq!(
        common::final_pc(),
        final_pc,
        "descriptor exit PC must match proof aux"
    );
    assert_eq!(
        common::INITS_TEARDOWNS_TOP_BITS,
        &proof.inits_and_teardowns_top_bits[..],
        "descriptor inits/teardowns top bits must match the proof"
    );
    final_pc
}

// Enforce the layout/config PoW bounds before rendering.
fn derived_pow_bits(
    circuit: &common::Circuit,
    config: &prover::gkr::prover_config::ProverConfig,
) -> (u32, u32) {
    use prover::gkr::prover_config::pow_bits;
    let pack_log2 = config.pack_log2();
    let lookup_pow_bits = pow_bits::lookup_challenges_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(circuit),
    );
    let external_pow_bits = lookup_pow_bits.max(
        prover::gkr::prover_config::example_configs::l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
    );
    let batched_proximity_pow_bits = config.base_round().batching_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.whir_message_size_log2(),
        pow_bits::committed_base_oracle_columns(circuit, pack_log2, true),
    );
    for (gate, bits) in [
        ("external challenges", external_pow_bits),
        ("WHIR batching", batched_proximity_pow_bits),
    ] {
        assert!(bits <= 25, "{gate} PoW {bits} exceeds GKR cap 25");
    }
    for bits in config
        .whir_schedule
        .queries_pow_bits_per_round()
        .iter()
        .copied()
        .chain([external_pow_bits, batched_proximity_pow_bits])
    {
        assert!(bits <= 30, "PoW {bits} exceeds 30");
    }
    (external_pow_bits, batched_proximity_pow_bits)
}

fn generate_f1(pc: u32) -> verifier_evm::F1Contracts {
    let (circuit, proof, _) = common::load();
    let config = common::prover_config();
    check_descriptor();
    let (_, nodes) = common::setup_frontier();
    let (pow, _) = derived_pow_bits(&circuit, &config);
    verifier_evm::generate_f1_verifier(
        &circuit,
        &config,
        &common::f1_params(),
        pow,
        pc,
        common::INITS_TEARDOWNS_TOP_BITS,
        &proof.whir_proof.setup_commitment.commitment.cap.cap,
        &nodes,
    )
}

fn generated_sources() -> Vec<(String, String)> {
    let pc = common::final_pc();
    let f1 = generate_f1(pc);
    let wrong = generate_f1(pc ^ 1);
    // The negative changes only the pinned PC and the decoder's PC word.
    assert_eq!(
        f1.verifier_sol.lines().count(),
        wrong.verifier_sol.lines().count()
    );
    let differences: Vec<_> = f1
        .verifier_sol
        .lines()
        .zip(wrong.verifier_sol.lines())
        .filter(|(a, b)| a != b)
        .collect();
    assert_eq!(differences.len(), 2);
    assert!(differences.iter().all(|(a, b)| [
        "constant __TEMPLATE_EXPECTED_FINAL_PC",
        "// pinned final PC"
    ]
    .iter()
    .any(|tag| a.contains(tag) && b.contains(tag))));
    vec![
        (MERGED_F1.into(), f1.verifier_sol),
        (F1_FRONTIER_CONTRACT.into(), f1.setup_frontier_sol),
        (F1_WRONG_FINAL_PC.into(), wrong.verifier_sol),
    ]
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

#[test]
fn checked_in_contracts_are_current() {
    for (rel, content) in generated_sources() {
        let path = common::contract_path(&rel);
        let checked_in =
            std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("missing {}", path.display()));
        assert!(
                checked_in == content,
                "{} is stale: rerun `cargo test -p verifier_evm --test generate_contracts -- --ignored`",
                path.display()
            );
    }
}
