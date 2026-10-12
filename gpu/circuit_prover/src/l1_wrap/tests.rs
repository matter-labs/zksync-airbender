use super::inputs::ALLOCATOR_BLOCK_BYTES;
use super::*;
use crate::proof::memory_policy::presets::l1_feeder;
use crate::proof::memory_policy::presets::INPUTS_RESERVE_BYTES;
use crate::upstream::OutputType;
use crate::upstream::{FinalRegisterValue, SecurityLevel, ROM_WORD_SIZE};
use cs::definitions::GKRAddress;
use gpu_gkr::proth120::proof_layout::M6ProofFields;
use gpu_prover_context::ProverContextConfig;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_whir::proth120::L1WhirProof;
use prover::definitions::GKRExternalChallenges;
use prover::gkr::prover::{SumcheckIntermediateProofValues, SumcheckRoundCoefficients};
use std::alloc::Global;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn panic_message(f: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a named panic");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| {
            payload
                .downcast_ref::<&str>()
                .map(|message| message.to_string())
        })
        .expect("panic payload is a message")
}

fn production_mode() -> CommitmentMode {
    CommitmentMode::MergedAndPackedMemoryAndWitness {
        pack_log2: EVM_PRODUCTION_PACK_LOG2,
        external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
        register_final_state: [FinalRegisterValue {
            value: 0,
            last_access_timestamp: 0,
        }; 32],
        final_pc: 0,
        final_timestamp: 0,
    }
}

#[test]
fn cpu_m8_l1_inputs_fit_reserve() {
    assert_eq!(
        ALLOCATOR_BLOCK_BYTES,
        1 << ProverContextConfig::default().allocator_block_log_size
    );
    let bytes = L1WrapInputs::<'static, Global>::phase_one_capacity_bytes(
        CircuitType::L1Wrap.get_domain_size(),
        ROM_WORD_SIZE,
    );
    let mib = 1 << 20;
    assert_eq!(bytes, (224 + 1 + 32 + 64 + 20 + 1) * mib);
    assert!(bytes <= INPUTS_RESERVE_BYTES);
}

#[test]
fn cpu_m8_l1_preflight() {
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(include_str!(
        "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .expect("committed Proth120 layout");
    let config = crate::config::prover_config(
        CircuitType::L1Wrap,
        ProofProfile::L1Wrap,
        SecurityLevel::Sec100,
    )
    .unwrap();
    assert_eq!(
        L1_WRAP_NTT_LOG_MAX_DOMAIN as usize,
        config.trace_len_log2
            + EVM_PRODUCTION_PACK_LOG2
            + config.lde_factor.trailing_zeros() as usize
    );
    assert_eq!(l1_wrap_batching_pow_bits(&config, &circuit), 11);
    validate_l1_wrap_preconditions(
        &config,
        &production_mode(),
        L1_WRAP_POLICY,
        L1_WRAP_NTT_LOG_MAX_DOMAIN,
    );
    let recompute = ProofMemoryPolicy {
        gkr: GkrMemoryPolicy::Recompute {
            value_layers: 1,
            cache_layers: 0,
        },
        ..L1_WRAP_POLICY
    };
    let standard = crate::config::prover_config(
        CircuitType::L1Wrap,
        ProofProfile::Standard,
        SecurityLevel::Sec100,
    )
    .unwrap();
    let mode_message = format!("L1Wrap requires CommitmentMode::MergedAndPackedMemoryAndWitness with pack_log2 {EVM_PRODUCTION_PACK_LOG2} and external_challenges_pow_bits {EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS}");
    let mut other_pack = production_mode();
    if let CommitmentMode::MergedAndPackedMemoryAndWitness { pack_log2, .. } = &mut other_pack {
        *pack_log2 -= 1;
    }
    let cases: [(&ProverConfig, CommitmentMode, ProofMemoryPolicy, u32, String); 6] = [
        (
            &config,
            production_mode(),
            recompute,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "L1Wrap does not support GkrMemoryPolicy::Recompute".to_string(),
        ),
        (
            &config,
            production_mode(),
            l1_feeder::POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            format!(
                "L1Wrap requires presets::l1_wrap::L1_WRAP_POLICY, got {:?}",
                l1_feeder::POLICY
            ),
        ),
        (
            &standard,
            production_mode(),
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "L1Wrap requires the ProofProfile::L1Wrap prover config".to_string(),
        ),
        (
            &config,
            CommitmentMode::MergedMemoryAndWitness,
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            mode_message.clone(),
        ),
        (
            &config,
            other_pack,
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            mode_message,
        ),
        (
            &config,
            production_mode(),
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN - 1,
            format!(
                "L1Wrap requires a Proth120 NTT context with log_max_domain {L1_WRAP_NTT_LOG_MAX_DOMAIN}, got {}",
                L1_WRAP_NTT_LOG_MAX_DOMAIN - 1
            ),
        ),
    ];
    for (config, mode, policy, log_max_domain, expected) in cases {
        assert_eq!(
            panic_message(|| validate_l1_wrap_preconditions(config, &mode, policy, log_max_domain)),
            expected
        );
    }
}

fn sentinel_m6_fields() -> M6ProofFields {
    let external = std::array::from_fn::<
        _,
        { GKRExternalChallenges::<Proth120, Proth120>::TOTAL_CHALLENGES },
        _,
    >(|index| Proth120(index as u128 + 1));
    let final_explicit_evaluations = BTreeMap::from([
        (
            OutputType::PermutationProduct,
            [vec![Proth120(21)], vec![Proth120(22)]],
        ),
        (
            OutputType::InitsAndTeardownsProduct,
            [
                vec![Proth120(23), Proth120(24)],
                vec![Proth120(25), Proth120(26)],
            ],
        ),
    ]);
    let sumcheck_intermediate_values = BTreeMap::from([(
        3,
        SumcheckIntermediateProofValues {
            sumcheck_num_rounds: 1,
            internal_round_coefficients: vec![SumcheckRoundCoefficients::Multilinear([
                Proth120(31),
                Proth120(32),
                Proth120(33),
                Proth120(34),
            ])],
            final_step_evaluations: BTreeMap::from([(
                GKRAddress::ScratchSpace(2),
                vec![Proth120(35), Proth120(36)],
            )]),
            extra_evaluations_from_caching_relations: BTreeMap::from([(
                GKRAddress::Cached {
                    layer: 1,
                    offset: 4,
                },
                Proth120(37),
            )]),
            _marker: PhantomData,
        },
    )]);
    M6ProofFields {
        external_challenges: GKRExternalChallenges::from_slice(&external),
        lookup_challenges_pow_nonce: 0x1122_3344_5566_7788,
        final_explicit_evaluations,
        sumcheck_intermediate_values,
        grand_product_accumulator_computed: Proth120(41),
        batched_proximity_check_pow_nonce: 0x8877_6655_4433_2211,
        merged_claims: ((51..58).map(Proth120).collect(), vec![Proth120(58)]),
        evaluation_point: (61..87).map(Proth120).collect(),
        batching_challenge: Proth120(91),
        intermediate_transcript_seed: [0xa5; 32],
    }
}

fn sentinel_whir() -> L1WhirProof {
    let mut whir = L1WhirProof {
        ood_samples: vec![Proth120(101), Proth120(102)],
        sumcheck_polys: vec![[Proth120(103), Proth120(104), Proth120(105)]],
        pow_nonces: vec![0x9988_7766_5544_3322],
        final_monomials: vec![Proth120(106), Proth120(107)],
        whir_schedule: ProofProfile::L1Wrap
            .prover_config(22, SecurityLevel::Sec100)
            .whir_schedule,
        batching_challenge: Some(Proth120(108)),
        original_evaluation_point: Some(vec![Proth120(109), Proth120(110)]),
        batched_opening: Some(Proth120(111)),
        ..Default::default()
    };
    whir.setup_commitment.num_columns = 1;
    whir.setup_commitment.evals = vec![Proth120(112)];
    whir.memory_commitment.num_columns = 2;
    whir.memory_commitment.evals = vec![Proth120(113), Proth120(114)];
    whir.witness_commitment.num_columns = 3;
    whir.witness_commitment.evals = vec![Proth120(115), Proth120(116), Proth120(117)];
    whir
}

#[test]
fn cpu_m8_l1_assembly() {
    let m6 = sentinel_m6_fields();
    let whir = sentinel_whir();
    let top_bits = vec![17, 23];
    let mut mode = production_mode();
    if let CommitmentMode::MergedAndPackedMemoryAndWitness {
        register_final_state,
        final_pc,
        final_timestamp,
        ..
    } = &mut mode
    {
        register_final_state[7].value = 0x1234_5678;
        register_final_state[7].last_access_timestamp = 0x1020_3040;
        *final_pc = 0x0506_0708;
        *final_timestamp = 0x5060_7080;
    }
    let result = assemble_l1_proof(m6.clone(), whir.clone(), top_bits.clone(), mode);
    let proof = result.proof;
    assert_eq!(proof.external_challenges, m6.external_challenges);
    assert_eq!(
        proof.final_explicit_evaluations,
        m6.final_explicit_evaluations
    );
    assert_eq!(
        serde_json::to_value(&proof.sumcheck_intermediate_values).unwrap(),
        serde_json::to_value(&m6.sumcheck_intermediate_values).unwrap(),
    );
    assert_eq!(
        serde_json::to_value(&proof.whir_proof).unwrap(),
        serde_json::to_value(&whir).unwrap()
    );
    assert_eq!(
        proof.grand_product_accumulator_computed,
        m6.grand_product_accumulator_computed
    );
    assert_eq!(
        proof.lookup_challenges_pow_nonce,
        m6.lookup_challenges_pow_nonce
    );
    assert_eq!(
        proof.batched_proximity_check_pow_nonce,
        m6.batched_proximity_check_pow_nonce
    );
    assert_eq!(proof.inits_and_teardowns_top_bits, top_bits);
    assert_eq!(
        proof.intermediate_transcript_seed,
        Some(m6.intermediate_transcript_seed)
    );
    assert_eq!(
        serde_json::to_value(result.commitment_mode).unwrap(),
        serde_json::to_value(mode).unwrap()
    );
}

#[test]
fn cpu_m8_l1_seed_provenance() {
    let m6 = sentinel_m6_fields();
    let pre_whir_seed = m6.intermediate_transcript_seed;
    let post_whir_seed = [0x5a; 32];
    let mut whir = sentinel_whir();
    whir.final_monomials = post_whir_seed
        .into_iter()
        .map(|value| Proth120(value as u128))
        .collect();
    let result = assemble_l1_proof(m6, whir, vec![17, 23], production_mode());
    assert_eq!(
        result.proof.intermediate_transcript_seed,
        Some(pre_whir_seed)
    );
    assert_ne!(
        result.proof.intermediate_transcript_seed,
        Some(post_whir_seed)
    );
}
