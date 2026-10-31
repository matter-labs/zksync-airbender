use std::collections::BTreeMap;

use cs::definitions::{split_timestamp, GKRAddress};
use execution_prover::OperationMode;
use prover::definitions::GKRExternalChallenges;
use prover::field::{Field, Proth120};
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
use prover::gkr::prover::SumcheckRoundCoefficients;
use prover::gkr::prover_config::ProverConfig;
use prover::transcript::{Keccak256Seed, Keccak256Transcript, Transcript};

use super::ReferenceBundle;

pub(super) const M4_CHALLENGE_DRAWS: usize =
    GKRExternalChallenges::<Proth120, Proth120>::TOTAL_CHALLENGES + 2;

#[derive(Clone, Copy, Debug)]
pub(super) struct ReplayPowBits {
    pub(super) lookup: u32,
    pub(super) batched: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayedClaims {
    Ordered(Vec<Proth120>),
    ByAddress(BTreeMap<GKRAddress, Proth120>),
}

#[derive(Clone, Debug)]
pub(super) struct ReplayedSnapshot {
    pub(super) layer_idx: usize,
    pub(super) seed: [u8; 32],
    pub(super) claim_point: Vec<Proth120>,
    pub(super) batching_challenge: Proth120,
    pub(super) claims: ReplayedClaims,
}

#[derive(Clone, Debug)]
pub(super) struct ReplayedGkr {
    pub(super) m4_challenges: [Proth120; M4_CHALLENGE_DRAWS],
    pub(super) m4_seed: [u8; 32],
    pub(super) snapshots: Vec<ReplayedSnapshot>,
    pub(super) round_challenges: BTreeMap<usize, Vec<Proth120>>,
    pub(super) main0_seed: [u8; 32],
    pub(super) z: Vec<Proth120>,
    pub(super) extra: Vec<Proth120>,
    pub(super) evaluation_point: Vec<Proth120>,
    pub(super) batching_challenge: Proth120,
    pub(super) final_seed: [u8; 32],
}

fn commit(seed: &mut Keccak256Seed, values: &[Proth120]) {
    assert!(
        !values.is_empty(),
        "GKR replay never commits an empty slice"
    );
    commit_field_els::<Proth120, Proth120, Keccak256Transcript>(seed, values);
}

fn draw(seed: &mut Keccak256Seed, count: usize) -> Vec<Proth120> {
    draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(seed, count)
}

fn apply_pow(seed: &mut Keccak256Seed, nonce: u64, pow_bits: u32) {
    <Keccak256Transcript as Transcript<Proth120, Proth120>>::verify_pow(seed, nonce, pow_bits);
}

fn boundary_words(mode: &OperationMode) -> Vec<u32> {
    let OperationMode::SingleChunk {
        register_final_state,
        final_pc,
        final_timestamp,
        ..
    } = mode
    else {
        panic!("GKR replay requires OperationMode::SingleChunk");
    };
    let mut words = Vec::with_capacity(32 * 3 + 3);
    for register in register_final_state.iter() {
        let (low, high) = split_timestamp(register.last_access_timestamp);
        words.extend([register.value, low, high]);
    }
    let (low, high) = split_timestamp(*final_timestamp);
    words.extend([*final_pc, low, high]);
    words
}

fn interpolate(a: Proth120, b: Proth120, at: Proth120) -> Proth120 {
    let mut result = b;
    result.sub_assign(&a);
    result.mul_assign(&at);
    result.add_assign(&a);
    result
}

fn evaluate_at_point(values: &[Proth120], point: &[Proth120]) -> Proth120 {
    assert_eq!(
        values.len(),
        1usize << point.len(),
        "GKR replay explicit output length differs from the handoff point"
    );
    values
        .iter()
        .enumerate()
        .fold(Proth120::ZERO, |mut sum, (row, value)| {
            let weight = point
                .iter()
                .enumerate()
                .fold(Proth120::ONE, |mut weight, (bit, x)| {
                    let factor = if row & (1 << bit) == 0 {
                        let mut one_minus = Proth120::ONE;
                        one_minus.sub_assign(x);
                        one_minus
                    } else {
                        *x
                    };
                    weight.mul_assign(&factor);
                    weight
                });
            let mut term = *value;
            term.mul_assign(&weight);
            sum.add_assign(&term);
            sum
        })
}

pub(super) fn replay_gkr_challenges(
    bundle: &ReferenceBundle,
    config: &ProverConfig,
    pow: ReplayPowBits,
) -> ReplayedGkr {
    let proof = &bundle.proof;
    let whir = &proof.whir_proof;
    assert_ne!(
        whir.setup_commitment.num_columns, 0,
        "GKR replay requires a committed setup"
    );
    let mut words = boundary_words(&bundle.operation_mode);
    words.extend_from_slice(&proof.inits_and_teardowns_top_bits);
    flatten_merkle_caps_iter_into(
        [
            whir.setup_commitment.commitment.cap.clone(),
            whir.memory_commitment.commitment.cap.clone(),
        ]
        .into_iter(),
        &mut words,
    );
    let mut seed =
        <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(&words);
    apply_pow(&mut seed, proof.lookup_challenges_pow_nonce, pow.lookup);
    let m4_challenges: [Proth120; M4_CHALLENGE_DRAWS] = draw(&mut seed, M4_CHALLENGE_DRAWS)
        .try_into()
        .expect("GKR replay packed challenge count");
    let m4_seed = seed.0;

    let explicit: Vec<Proth120> = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|pair| pair.iter().flat_map(|values| values.iter().copied()))
        .collect();
    let final_log = proof
        .final_explicit_evaluations
        .values()
        .next()
        .expect("GKR replay requires an explicit output")[0]
        .len()
        .trailing_zeros() as usize;
    commit(&mut seed, &explicit);
    let mut handoff = draw(&mut seed, final_log + 1);
    let handoff_batching = handoff
        .pop()
        .expect("GKR replay handoff batching challenge");
    let initial_claims = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|pair| {
            pair.iter()
                .map(|values| evaluate_at_point(values, &handoff))
        })
        .collect();
    let top_layer = *proof
        .sumcheck_intermediate_values
        .keys()
        .next_back()
        .expect("GKR replay requires a backward layer");
    let mut snapshots = vec![ReplayedSnapshot {
        layer_idx: top_layer + 1,
        seed: seed.0,
        claim_point: handoff,
        batching_challenge: handoff_batching,
        claims: ReplayedClaims::Ordered(initial_claims),
    }];

    let mut round_challenges = BTreeMap::new();
    for (&layer_idx, layer) in proof.sumcheck_intermediate_values.iter().rev() {
        assert_eq!(
            layer.internal_round_coefficients.len(),
            layer.sumcheck_num_rounds,
            "GKR replay layer {layer_idx} round count"
        );
        let mut rounds = Vec::with_capacity(layer.sumcheck_num_rounds);
        for (round, coefficients) in layer.internal_round_coefficients.iter().enumerate() {
            let SumcheckRoundCoefficients::Multilinear(coefficients) = coefficients else {
                panic!("GKR replay layer {layer_idx} round {round} is not multilinear");
            };
            commit(&mut seed, coefficients);
            rounds.push(draw(&mut seed, 1)[0]);
        }
        let degree = layer
            .final_step_evaluations
            .values()
            .next()
            .expect("GKR replay layer must carry final evaluations")
            .len();
        assert!(
            layer
                .final_step_evaluations
                .values()
                .all(|values| values.len() == degree),
            "GKR replay layer {layer_idx} final evaluation degree is not uniform"
        );
        let (claim_point, batching_challenge, claims) = match degree {
            2 => {
                assert!(
                    layer.extra_evaluations_from_caching_relations.is_empty(),
                    "GKR replay dimension-reducing layer {layer_idx} carries extras"
                );
                let lines: Vec<Proth120> = layer
                    .final_step_evaluations
                    .values()
                    .flatten()
                    .copied()
                    .collect();
                commit(&mut seed, &lines);
                let [r_last, next_batching]: [Proth120; 2] = draw(&mut seed, 2)
                    .try_into()
                    .expect("GKR replay dimension-reducing boundary draws");
                let claims = layer
                    .final_step_evaluations
                    .iter()
                    .map(|(&address, values)| (address, interpolate(values[0], values[1], r_last)))
                    .collect();
                let claim_point = std::iter::once(r_last)
                    .chain(rounds.iter().copied())
                    .collect();
                (claim_point, next_batching, claims)
            }
            1 => {
                let mut values: Vec<Proth120> = layer
                    .final_step_evaluations
                    .values()
                    .map(|values| values[0])
                    .collect();
                values.extend(
                    layer
                        .extra_evaluations_from_caching_relations
                        .values()
                        .copied(),
                );
                commit(&mut seed, &values);
                let next_batching = draw(&mut seed, 1)[0];
                let mut claims: BTreeMap<GKRAddress, Proth120> = layer
                    .final_step_evaluations
                    .iter()
                    .map(|(&address, values)| (address, values[0]))
                    .collect();
                for (&address, &value) in &layer.extra_evaluations_from_caching_relations {
                    assert!(
                        claims.insert(address, value).is_none(),
                        "GKR replay layer {layer_idx} extra {address:?} duplicates a final evaluation"
                    );
                }
                (rounds.clone(), next_batching, claims)
            }
            _ => panic!("GKR replay layer {layer_idx} final evaluation degree {degree}"),
        };
        snapshots.push(ReplayedSnapshot {
            layer_idx,
            seed: seed.0,
            claim_point,
            batching_challenge,
            claims: ReplayedClaims::ByAddress(claims),
        });
        round_challenges.insert(layer_idx, rounds);
    }
    let last = snapshots.last().expect("GKR replay snapshots");
    assert_eq!(last.layer_idx, 0, "GKR replay must end at MAIN0");
    let main0_seed = last.seed;
    let z = last.claim_point.clone();

    let extra = draw(&mut seed, config.pack_log2());
    let evaluation_point: Vec<Proth120> = z.iter().chain(extra.iter()).copied().collect();
    apply_pow(&mut seed, whir.batching_challenge_pow_nonce, pow.batched);
    let batching_challenge = draw(&mut seed, 1)[0];
    ReplayedGkr {
        m4_challenges,
        m4_seed,
        snapshots,
        round_challenges,
        main0_seed,
        z,
        extra,
        evaluation_point,
        batching_challenge,
        final_seed: seed.0,
    }
}

impl ReplayedGkr {
    pub(super) fn assert_matches_bundle(&self, bundle: &ReferenceBundle) {
        let proof = &bundle.proof;
        let whir = &proof.whir_proof;
        assert_eq!(
            GKRExternalChallenges::<Proth120, Proth120>::from_slice(
                &self.m4_challenges
                    [..GKRExternalChallenges::<Proth120, Proth120>::TOTAL_CHALLENGES]
            ),
            proof.external_challenges,
            "GKR replay external challenges differ from the bundle"
        );
        assert_eq!(
            self.snapshots.len(),
            proof.sumcheck_intermediate_values.len() + 1,
            "GKR replay snapshot count"
        );
        let config = prover::gkr::prover_config::ProofProfile::L1Wrap
            .prover_config(21, prover::definitions::SecurityLevel::Sec100);
        let circuit: verifier_evm::seed::Circuit = serde_json::from_reader(
            std::fs::File::open(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
                "../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json",
            ))
            .unwrap(),
        )
        .unwrap();
        let cpu = verifier_evm::encoding::replay_gkr_points(
            &circuit,
            proof,
            &bundle.operation_mode,
            &config,
        );
        assert_eq!(
            self.evaluation_point, cpu.handoff_point,
            "CPU handoff evaluation point"
        );
        assert_eq!(
            self.batching_challenge, cpu.batching_challenge,
            "CPU handoff batching challenge"
        );
        assert_eq!(self.final_seed, cpu.handoff_seed, "CPU pre-WHIR seed");
        let mut seed = Keccak256Seed(cpu.handoff_seed);
        for poly in &whir.base_sumcheck_polys {
            commit(&mut seed, poly);
            draw(&mut seed, 1);
        }
        let oracle = whir
            .intermediate_whir_oracles
            .first()
            .expect("WHIR oracle 0");
        let mut cap_words = Vec::new();
        oracle.commitment.cap.add_into_buffer(&mut cap_words);
        Keccak256Transcript::commit_u32_with_seed(&mut seed, &cap_words);
        draw(
            &mut seed,
            config.whir_schedule.internal_rounds[0].num_ood_samples,
        );
        commit(&mut seed, &oracle.ood_samples);
        Keccak256Transcript::verify_pow(
            &mut seed,
            whir.base_queries_pow_nonce,
            config.whir_schedule.base_round.queries_pow_bits,
        );
    }
}
