//! Prover configuration policy.
//!
//! Maps a `CircuitType` + `SecurityLevel` to the canonical upstream
//! `ProverConfig`, and owns the GPU-supported-security-level contract. Lives in
//! the prover layer because `ProverConfig` is a `prove()` input (see
//! `proof/mod.rs`): `execution` calls down into this and threads the result
//! into `prove()`. The low `witness::circuit_type` enum stays a pure
//! domain type with no `ProverConfig`/`SecurityLevel` coupling.

use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, ProverConfig, SecurityLevel,
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

/// GPU prover doesn't yet implement PoW for lookup-challenge or
/// batched-proximity-check challenges; both `*_pow_bits` knobs must be 0.
pub(crate) fn assert_gpu_supported_pow_config(prover_config: &ProverConfig) {
    assert_eq!(
        prover_config.lookup_challenges_pow_bits, 0,
        "GPU prover only supports lookup_challenges_pow_bits = 0",
    );
    assert_eq!(
        prover_config.batched_proximity_check_challenge_pow_bits, 0,
        "GPU prover only supports batched_proximity_check_challenge_pow_bits = 0",
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
