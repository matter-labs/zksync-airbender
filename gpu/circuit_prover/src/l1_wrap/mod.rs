mod geometry;
mod inputs;
mod orchestration;
#[cfg(test)]
mod tests;

pub use geometry::{l1_wrap_batching_pow_bits, L1WrapGeometry};
pub use inputs::L1WrapInputs;
pub use orchestration::{assemble_l1_proof, prove, GpuL1WrapProofJob};

use crate::proof::memory_policy::presets::l1_wrap::L1_WRAP_POLICY;
use crate::proof::memory_policy::{GkrMemoryPolicy, ProofMemoryPolicy};
use crate::upstream::{
    CommitmentMode, GKRProof, Keccak256MerkleTreeWithCap, ProofProfile, Proth120, ProverConfig,
};

pub type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

pub const L1_WRAP_NTT_LOG_MAX_DOMAIN: u32 = 31;

pub fn validate_l1_wrap_preconditions(
    geometry: &L1WrapGeometry,
    config: &ProverConfig,
    mode: &CommitmentMode,
    policy: ProofMemoryPolicy,
    log_max_domain: u32,
) {
    let circuit_type = geometry.circuit_type;
    assert!(
        !matches!(policy.gkr, GkrMemoryPolicy::Recompute { .. }),
        "L1Wrap does not support GkrMemoryPolicy::Recompute"
    );
    assert!(
        policy == L1_WRAP_POLICY,
        "L1Wrap requires presets::l1_wrap::L1_WRAP_POLICY, got {policy:?}"
    );
    let expected =
        ProofProfile::L1Wrap.prover_config(geometry.trace_log as usize, config.security_level);
    assert!(
        config.trace_len_log2 == expected.trace_len_log2
            && config.lde_factor == expected.lde_factor
            && config.cap_size == expected.cap_size
            && config.base_oracles_values_per_leaf == expected.base_oracles_values_per_leaf
            && config.whir_schedule == expected.whir_schedule,
        "{circuit_type:?} requires the ProofProfile::L1Wrap prover config"
    );
    let pack = geometry.pack_log2 as usize;
    let external = geometry.external_pow_bits;
    assert!(
        matches!(
            mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2,
                external_challenges_pow_bits,
                ..
            } if *pack_log2 == pack && *external_challenges_pow_bits == external
        ),
        "{circuit_type:?} requires CommitmentMode::MergedAndPackedMemoryAndWitness with pack_log2 {pack} and external_challenges_pow_bits {external}"
    );
    assert!(
        log_max_domain == L1_WRAP_NTT_LOG_MAX_DOMAIN,
        "L1Wrap requires a Proth120 NTT context with log_max_domain {L1_WRAP_NTT_LOG_MAX_DOMAIN}, got {log_max_domain}"
    );
}
