mod inputs;
mod orchestration;
#[cfg(test)]
mod tests;

pub use inputs::L1WrapInputs;
pub use orchestration::{assemble_l1_proof, prove, GpuL1WrapProofJob};

use crate::proof::memory_policy::presets::l1_wrap::L1_WRAP_POLICY;
use crate::proof::memory_policy::{GkrMemoryPolicy, ProofMemoryPolicy};
use crate::upstream::{
    pow_bits, CommitmentMode, GKRCircuitArtifact, GKRProof, Keccak256MerkleTreeWithCap,
    ProofProfile, Proth120, ProverConfig, EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
    EVM_PRODUCTION_PACK_LOG2, EVM_PRODUCTION_TRACE_LEN_LOG2,
};

pub type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

pub const L1_WRAP_NTT_LOG_MAX_DOMAIN: u32 = 31;

pub fn validate_l1_wrap_preconditions(
    config: &ProverConfig,
    mode: &CommitmentMode,
    policy: ProofMemoryPolicy,
    log_max_domain: u32,
) {
    assert!(
        !matches!(policy.gkr, GkrMemoryPolicy::Recompute { .. }),
        "L1Wrap does not support GkrMemoryPolicy::Recompute"
    );
    assert!(
        policy == L1_WRAP_POLICY,
        "L1Wrap requires presets::l1_wrap::L1_WRAP_POLICY, got {policy:?}"
    );
    let expected =
        ProofProfile::L1Wrap.prover_config(EVM_PRODUCTION_TRACE_LEN_LOG2, config.security_level);
    assert!(
        config.trace_len_log2 == expected.trace_len_log2
            && config.lde_factor == expected.lde_factor
            && config.cap_size == expected.cap_size
            && config.base_oracles_values_per_leaf == expected.base_oracles_values_per_leaf
            && config.whir_schedule == expected.whir_schedule,
        "L1Wrap requires the ProofProfile::L1Wrap prover config"
    );
    assert!(
        matches!(
            mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2,
                external_challenges_pow_bits,
                ..
            } if *pack_log2 == EVM_PRODUCTION_PACK_LOG2
                && *external_challenges_pow_bits == EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS
        ),
        "L1Wrap requires CommitmentMode::MergedAndPackedMemoryAndWitness with pack_log2 {EVM_PRODUCTION_PACK_LOG2} and external_challenges_pow_bits {EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS}"
    );
    assert!(
        log_max_domain == L1_WRAP_NTT_LOG_MAX_DOMAIN,
        "L1Wrap requires a Proth120 NTT context with log_max_domain {L1_WRAP_NTT_LOG_MAX_DOMAIN}, got {log_max_domain}"
    );
}

pub fn l1_wrap_batching_pow_bits(
    config: &ProverConfig,
    circuit: &GKRCircuitArtifact<Proth120>,
) -> u32 {
    pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        circuit.trace_len.trailing_zeros() as usize + EVM_PRODUCTION_PACK_LOG2,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(circuit),
    )
}
