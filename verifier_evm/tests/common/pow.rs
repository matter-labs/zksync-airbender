//! Replay only transcript operations to measure the committed proof's PoW digests.
//! This is not another verifier: the generated contracts test acceptance and rejection.
use super::{Circuit, Proof};
use field::{Field, Proth120};
use prover::gkr::prover::OperationMode;
use prover::gkr::prover_config::ProverConfig;
use sha3::{Digest, Keccak256};
use transcript::{Keccak256Seed, Keccak256Transcript as Tr, Transcript};

fn draw(seed: &mut Keccak256Seed, n: usize) {
    Tr::draw_random_field_elements(seed, &mut vec![Proth120::ZERO; n]);
}

fn absorb(seed: &mut Keccak256Seed, values: &[Proth120]) {
    Tr::commit_extension_field_elements(seed, values);
}

fn pow(seed: &mut Keccak256Seed, nonce: u64) -> u32 {
    Tr::verify_pow(seed, nonce, 0);
    let mut zeros = 0;
    for byte in seed.0 {
        zeros += byte.leading_zeros();
        if byte != 0 {
            break;
        }
    }
    zeros
}

pub struct PowLeadingZeros {
    pub external: u32,
    pub batching: u32,
    pub queries: Vec<u32>,
    pub folding: Vec<Vec<u32>>,
    pub ood: Vec<Option<u32>>,
}

/// Leading-zero counts at every gated transcript draw.
pub fn leading_zeros(
    circuit: &Circuit,
    proof: &Proof,
    mode: &OperationMode,
    config: &ProverConfig,
) -> PowLeadingZeros {
    let replay = verifier_evm::encoding::replay_gkr_points(circuit, proof, mode, config);
    let preimage = verifier_evm::commit_seed_preimage(circuit, proof, mode);
    let mut seed = Keccak256Seed(Keccak256::digest(preimage).into());
    let external = pow(&mut seed, proof.lookup_challenges_pow_nonce);
    draw(
        &mut seed,
        prover::gkr::prover::GKRExternalChallenges::<Proth120, Proth120>::TOTAL_CHALLENGES + 2,
    );
    let output: Vec<_> = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|v| v[0].iter().chain(&v[1]))
        .copied()
        .collect();
    absorb(&mut seed, &output);
    draw(&mut seed, config.sumcheck_explicit_output_size_log_2);
    draw(&mut seed, 1);
    for layer in &replay.layers {
        let siv = &proof.sumcheck_intermediate_values[&layer.layer];
        for coefficients in &siv.internal_round_coefficients {
            absorb(&mut seed, coefficients.as_multilinear());
            draw(&mut seed, 1);
        }
        let values: Vec<_> = siv
            .final_step_evaluations
            .values()
            .flatten()
            .chain(siv.extra_evaluations_from_caching_relations.values())
            .copied()
            .collect();
        absorb(&mut seed, &values);
        draw(
            &mut seed,
            if layer.layer >= circuit.layers.len() {
                2
            } else {
                1
            },
        );
    }
    draw(&mut seed, config.pack_log2());
    let wp = &proof.whir_proof;
    let batching = pow(&mut seed, wp.batching_challenge_pow_nonce);
    draw(&mut seed, 1);
    assert_eq!(
        seed.0, replay.handoff_seed,
        "PoW replay differs at WHIR handoff"
    );

    let folds = config.whir_schedule.fold_steps();
    let queries = config.whir_schedule.queries_per_round();
    let nonces = wp.queries_pow_nonces();
    let mut query_zeros = Vec::new();
    let mut folding_zeros = Vec::new();
    let mut ood_zeros = Vec::new();
    for (r, &fold) in folds.iter().enumerate() {
        let polys = if r == 0 {
            &wp.base_sumcheck_polys
        } else {
            &wp.intermediate_whir_oracles[r - 1].sumcheck_polys
        };
        assert_eq!(polys.len(), fold);
        let folding_nonces = if r == 0 {
            &wp.base_folding_pow_nonces
        } else {
            &wp.intermediate_whir_oracles[r - 1].folding_pow_nonces
        };
        assert!(folding_nonces.is_empty() || folding_nonces.len() == fold);
        let mut zeros = Vec::new();
        for (step, poly) in polys.iter().enumerate() {
            absorb(&mut seed, poly);
            if !folding_nonces.is_empty() {
                zeros.push(pow(&mut seed, folding_nonces[step]));
            }
            draw(&mut seed, 1);
        }
        folding_zeros.push(zeros);
        if r + 1 < folds.len() {
            let oracle = &wp.intermediate_whir_oracles[r];
            let cap: Vec<_> = oracle
                .commitment
                .cap
                .cap
                .iter()
                .flatten()
                .copied()
                .collect();
            Tr::commit_u32_with_seed(&mut seed, &cap);
            assert_eq!(oracle.ood_samples.len(), 1);
            ood_zeros.push(oracle.ood_pow_nonce.map(|nonce| pow(&mut seed, nonce)));
            draw(&mut seed, 1);
            absorb(&mut seed, &oracle.ood_samples);
        } else {
            absorb(&mut seed, &wp.final_monomials);
        }
        query_zeros.push(pow(&mut seed, nonces[r]));
        // Match draw_query_bits' padded draw, including its skipped first word.
        let qib =
            config.whir_message_size_log2() + config.whir_schedule.base_lde_factor_log2() - fold;
        let words = ((queries[r] * qib).div_ceil(32) + 1).next_multiple_of(8);
        Tr::draw_randomness(&mut seed, &mut vec![0u32; words]);
        if r + 1 < folds.len() {
            draw(&mut seed, 1); // delinearization
        }
    }
    PowLeadingZeros {
        external,
        batching,
        queries: query_zeros,
        folding: folding_zeros,
        ood: ood_zeros,
    }
}
