//! GKR transcript replay: the per-round eq coordinates `z` and challenges `r` of every
//! sumcheck layer, in verifier processing order, from the proof's absorbed values.

use field::{Field, Proth120};
use prover::gkr::prover::{GKRExternalChallenges, OperationMode};
use prover::gkr::prover_config::ProverConfig;
use transcript::{Keccak256Seed, Keccak256Transcript, Transcript};

use crate::seed::{build_transcript_input, Circuit, Proof};

/// One sumcheck layer: round `i` binds against `z[i]` and draws `r[i]`.
#[derive(Clone, Debug)]
pub struct LayerPoints {
    /// The proof's layer index (dimension-reducing layers sit above the circuit layers).
    pub layer: usize,
    pub z: Vec<Proth120>,
    pub r: Vec<Proth120>,
}

#[derive(Clone, Debug)]
pub struct GkrReplay {
    /// Dimension-reducing layers (output → base), then circuit layers (top → 0).
    pub layers: Vec<LayerPoints>,
    /// The reconstructed seed after the WHIR batching draw.
    pub handoff_seed: [u8; 32],
    /// Base claim point followed by the physical-packing coordinates.
    pub handoff_point: Vec<Proth120>,
    /// The WHIR batching challenge reconstructed from the CPU transcript.
    pub batching_challenge: Proth120,
}

fn draw(seed: &mut Keccak256Seed, n: usize) -> Vec<Proth120> {
    let mut out = vec![Proth120::ZERO; n];
    Keccak256Transcript::draw_random_field_elements(seed, &mut out);
    out
}

fn absorb(seed: &mut Keccak256Seed, els: &[Proth120]) {
    Keccak256Transcript::commit_extension_field_elements(seed, els);
}

/// Dimension-reducing layer indices in processing order (output → base).
pub(crate) fn dim_reducing_layers(circuit: &Circuit, proof: &Proof) -> Vec<usize> {
    proof
        .sumcheck_intermediate_values
        .keys()
        .copied()
        .filter(|l| *l >= circuit.layers.len())
        .rev()
        .collect()
}

fn rounds(
    seed: &mut Keccak256Seed,
    proof: &Proof,
    layer: usize,
    point: &[Proth120],
) -> LayerPoints {
    let siv = &proof.sumcheck_intermediate_values[&layer];
    assert_eq!(
        siv.sumcheck_num_rounds,
        point.len(),
        "layer {layer}: rounds must match the claim point"
    );
    assert_eq!(siv.internal_round_coefficients.len(), point.len());
    let r = siv
        .internal_round_coefficients
        .iter()
        .map(|c| {
            absorb(seed, c.as_multilinear());
            draw(seed, 1)[0]
        })
        .collect();
    LayerPoints {
        layer,
        z: point.to_vec(),
        r,
    }
}

/// Replays the GKR transcript (one keccak per absorbed block and per draw) up to the WHIR
/// handoff. The reconstructed batching challenge must bind the base-oracle
/// evaluations to the first WHIR sumcheck claim; this is a transcript boundary
/// check, not full cryptographic verification.
pub fn replay_gkr_points(
    circuit: &Circuit,
    proof: &Proof,
    aux: &OperationMode,
    config: &ProverConfig,
) -> GkrReplay {
    assert!(
        matches!(aux, OperationMode::SingleChunk { .. }),
        "expected single-chunk operation mode"
    );
    assert!(
        config.pack_log2() > 0 && config.merged_memory_and_witness(),
        "expected packed merged prover config"
    );
    assert_eq!(
        1 << config.trace_len_log2,
        circuit.trace_len,
        "prover config trace differs from the circuit"
    );
    let mut seed = Keccak256Transcript::commit_initial_u32(&build_transcript_input(proof, aux));
    // The PoW digest becomes the seed; the difficulty is the verifier's check, not the replay's.
    Keccak256Transcript::verify_pow(&mut seed, proof.lookup_challenges_pow_nonce, 0);
    draw(
        &mut seed,
        GKRExternalChallenges::<Proth120, Proth120>::TOTAL_CHALLENGES + 2,
    );

    let output_evals: Vec<Proth120> = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|v| v[0].iter().chain(v[1].iter()))
        .copied()
        .collect();
    absorb(&mut seed, &output_evals);
    let explicit_output_log2 = proof
        .final_explicit_evaluations
        .values()
        .next()
        .expect("proof has no explicit outputs")[0]
        .len()
        .ilog2() as usize;
    let mut point = draw(&mut seed, explicit_output_log2);
    draw(&mut seed, 1); // batching

    let mut layers = Vec::new();
    for layer in dim_reducing_layers(circuit, proof) {
        let lp = rounds(&mut seed, proof, layer, &point);
        let lines: Vec<Proth120> = proof.sumcheck_intermediate_values[&layer]
            .final_step_evaluations
            .values()
            .flat_map(|v| {
                assert_eq!(v.len(), 2, "layer {layer}: expected [E; 2] LSB lines");
                v.iter().copied()
            })
            .collect();
        absorb(&mut seed, &lines);
        let r_last = draw(&mut seed, 2)[0]; // r_last, next batching
        point = std::iter::once(r_last)
            .chain(lp.r.iter().copied())
            .collect();
        layers.push(lp);
    }
    for layer in (0..circuit.layers.len()).rev() {
        let lp = rounds(&mut seed, proof, layer, &point);
        let siv = &proof.sumcheck_intermediate_values[&layer];
        let evals: Vec<Proth120> = siv
            .final_step_evaluations
            .values()
            .map(|v| {
                assert_eq!(v.len(), 1, "layer {layer}: expected one at-point eval");
                v[0]
            })
            .chain(
                siv.extra_evaluations_from_caching_relations
                    .values()
                    .copied(),
            )
            .collect();
        absorb(&mut seed, &evals);
        draw(&mut seed, 1); // next batching
        point = lp.r.clone();
        layers.push(lp);
    }

    point.extend(draw(&mut seed, config.pack_log2())); // packing coordinates
    Keccak256Transcript::verify_pow(&mut seed, proof.whir_proof.batching_challenge_pow_nonce, 0);
    let gamma = draw(&mut seed, 1)[0]; // WHIR batching
                                       // #584 removed the prover's optional handoff-seed snapshot. Bind the
                                       // reconstructed draw to the proof's first WHIR round instead.
    let wp = &proof.whir_proof;
    let mut power = Proth120::ONE;
    let mut claim = Proth120::ZERO;
    for value in wp
        .memory_commitment
        .evals
        .iter()
        .chain(&wp.witness_commitment.evals)
        .chain(&wp.setup_commitment.evals)
    {
        let mut term = *value;
        term.mul_assign(&power);
        claim.add_assign(&term);
        power.mul_assign(&gamma);
    }
    let [c0, c1, c2] = wp
        .base_sumcheck_polys
        .first()
        .expect("missing base WHIR sumcheck");
    let mut round_claim = *c0;
    round_claim.double();
    round_claim.add_assign(c1);
    round_claim.add_assign(c2);
    assert_eq!(
        claim, round_claim,
        "GKR transcript replay diverged from the WHIR batching claim"
    );
    GkrReplay {
        layers,
        handoff_seed: seed.0,
        handoff_point: point,
        batching_challenge: gamma,
    }
}
