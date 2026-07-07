//! Prover configuration policy.
//!
//! Maps a `CircuitType` + `SecurityLevel` to the canonical upstream
//! `ProverConfig`, and owns the GPU-supported-security-level contract. Lives in
//! the prover layer because `ProverConfig` is a `prove()` input (see
//! `proof/mod.rs`): `execution` calls down into this and threads the result
//! into `prove()`. The low `witness::circuit_type` enum stays a pure
//! domain type with no `ProverConfig`/`SecurityLevel` coupling.

use crate::primitives::field::BF;
use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, pow_bits, GKRCircuitArtifact,
    ProverConfig, SecurityLevel,
};
use crate::witness::circuit_type::CircuitType;

/// Security levels the GPU prover supports today.
pub const GPU_SUPPORTED_SECURITY_LEVELS: [SecurityLevel; 1] = [SecurityLevel::Sec80];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnsupportedGpuSecurityLevel {
    pub requested: SecurityLevel,
}

impl std::fmt::Display for UnsupportedGpuSecurityLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "GPU prover does not support security level {:?}; supported levels: {:?}",
            self.requested, GPU_SUPPORTED_SECURITY_LEVELS,
        )
    }
}

impl std::error::Error for UnsupportedGpuSecurityLevel {}

/// Canonical `ProverConfig` for `circuit_type` at `security_level`. Delegates to
/// the CPU's `config_for_security_level_under_pessimistic_conjecture` so GPU and
/// CPU agree on the production WHIR schedule. Only `Sec80` is supported on GPU.
pub fn prover_config(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> Result<ProverConfig, UnsupportedGpuSecurityLevel> {
    match security_level {
        SecurityLevel::Sec80 => Ok(prover_config_sec80(circuit_type)),
        other => Err(UnsupportedGpuSecurityLevel { requested: other }),
    }
}

fn prover_config_sec80(circuit_type: CircuitType) -> ProverConfig {
    let domain_size_log_2 = circuit_type.get_domain_size().trailing_zeros() as usize;
    // CPU's `example_configs` only defines schedules for {20, 22, 24}; collapse
    // 23 onto 24 to match the previous GPU mapping.
    let schedule_log_2 = match domain_size_log_2 {
        20 | 22 | 24 => domain_size_log_2,
        23 => 24,
        other => {
            panic!(
                "no Sec80 ProverConfig for circuit {circuit_type:?} (domain_size_log_2 = {other})"
            )
        }
    };
    config_for_security_level_under_pessimistic_conjecture(schedule_log_2, SecurityLevel::Sec80)
}

/// The GPU prover does not implement PoW grinding for the lookup-challenge or
/// batched-proximity-check challenges (unlike the WHIR proximity rounds, which
/// it *does* grind). Both bit counts are 0 at every security level the GPU
/// supports (`GPU_SUPPORTED_SECURITY_LEVELS` = [Sec80]), so the emitted proof's
/// `lookup_challenges_pow_nonce` / `batched_proximity_check_pow_nonce` are 0 —
/// identical to the CPU prover at Sec80.
///
/// The pow-bit counts are no longer stored on `ProverConfig`; they are derived
/// per-circuit from `security_level` (see `prover::gkr::prover_config::pow_bits`).
/// We re-derive them here from the config's *actual* `security_level` and assert
/// 0, so that adding a higher security level (where these grinds are non-zero)
/// without implementing them trips loudly here rather than silently emitting an
/// unsound proof carrying a 0 nonce.
pub(crate) fn assert_gpu_supported_pow_config(
    prover_config: &ProverConfig,
    compiled_circuit: &GKRCircuitArtifact<BF>,
) {
    let security_bits = prover_config.security_level.security_bits();
    let lookup_challenges_pow_bits = pow_bits::lookup_challenges_pow_bits(
        security_bits,
        pow_bits::lookup_identity_degree(compiled_circuit),
    );
    assert_eq!(
        lookup_challenges_pow_bits, 0,
        "GPU prover only supports lookup_challenges_pow_bits = 0 \
         (implement lookup-challenge PoW grinding to support this security level)",
    );
    let batched_proximity_check_pow_bits = pow_bits::batched_proximity_check_pow_bits(
        security_bits,
        compiled_circuit.trace_len.trailing_zeros() as usize,
        prover_config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(compiled_circuit),
    );
    assert_eq!(
        batched_proximity_check_pow_bits, 0,
        "GPU prover only supports batched_proximity_check_challenge_pow_bits = 0 \
         (implement batched-proximity PoW grinding to support this security level)",
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::circuit_type::UnrolledCircuitType;

    #[test]
    fn rejects_unsupported_security_level_in_prover_config() {
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
        let err = prover_config(circuit_type, SecurityLevel::Sec100).unwrap_err();
        assert_eq!(err.requested, SecurityLevel::Sec100);
    }
}
