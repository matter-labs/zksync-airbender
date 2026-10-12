use super::inputs::ALLOCATOR_BLOCK_BYTES;
use super::*;
use crate::proof::memory_policy::presets::l1_feeder;
use crate::proof::memory_policy::presets::INPUTS_RESERVE_BYTES;
use crate::upstream::{FinalRegisterValue, SecurityLevel, ROM_WORD_SIZE};
use gpu_prover_context::ProverContextConfig;
use gpu_trace::witness::circuit_type::CircuitType;
use std::alloc::Global;
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
