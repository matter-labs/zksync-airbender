mod constants;
mod geometry;
mod inputs;
mod orchestration;
#[cfg(test)]
mod tests;

pub use constants::L1WrapConstantsHost;
pub use geometry::{l1_wrap_batching_pow_bits, L1WrapGeometry};
pub use inputs::L1WrapInputs;
pub use orchestration::{assemble_l1_proof, prove, GpuL1WrapProofJob};

use crate::proof::memory_policy::presets::l1_wrap::L1_WRAP_POLICY;
use crate::proof::memory_policy::{GkrMemoryPolicy, ProofMemoryPolicy};
use crate::upstream::{
    GKRProof, Keccak256MerkleTreeWithCap, OperationMode, ProofProfile, Proth120, ProverConfig,
};

pub type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

pub const L1_WRAP_NTT_LOG_MAX_DOMAIN: u32 = 31;

pub fn validate_l1_wrap_preconditions(
    geometry: &L1WrapGeometry,
    config: &ProverConfig,
    mode: &OperationMode,
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
        config.commitment_mode == expected.commitment_mode
            && config.pack_log2() == expected.pack_log2()
            && config.trace_len_log2 == expected.trace_len_log2
            && config.lde_factor() == expected.lde_factor()
            && config.cap_size == expected.cap_size
            && config.base_oracles_values_per_leaf() == expected.base_oracles_values_per_leaf()
            && config.whir_schedule == expected.whir_schedule,
        "{circuit_type:?} requires the ProofProfile::L1Wrap prover config"
    );
    assert_eq!(
        geometry.pack_log2 as usize,
        config.pack_log2(),
        "L1Wrap geometry packing disagrees with the config"
    );
    assert_eq!(
        geometry.log_message as usize,
        config.whir_message_size_log2(),
        "L1Wrap geometry message size disagrees with the config"
    );
    let external = geometry.external_pow_bits;
    assert!(
        matches!(
            mode,
            OperationMode::SingleChunk {
                external_challenges_pow_bits,
                ..
            } if *external_challenges_pow_bits == external
        ),
        "{circuit_type:?} requires OperationMode::SingleChunk with external_challenges_pow_bits {external}"
    );
    assert!(
        log_max_domain == L1_WRAP_NTT_LOG_MAX_DOMAIN,
        "L1Wrap requires a Proth120 NTT context with log_max_domain {L1_WRAP_NTT_LOG_MAX_DOMAIN}, got {log_max_domain}"
    );
}
