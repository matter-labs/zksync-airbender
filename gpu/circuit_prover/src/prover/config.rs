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
use gpu_trace::witness::circuit_type::CircuitType;

/// Security levels the GPU prover supports.
pub const GPU_SUPPORTED_SECURITY_LEVELS: [SecurityLevel; 2] =
    [SecurityLevel::Sec80, SecurityLevel::Sec100];

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
/// CPU agree on the production WHIR schedule. Both `Sec80` and `Sec100` are
/// supported (the per-circuit lookup-challenge and WHIR-batching PoWs are ground
/// on device — see [`lookup_challenges_pow_bits`] / [`batched_proximity_check_pow_bits`]).
///
/// The `Result` is retained for API stability (`SecurityLevel` currently has no
/// unsupported variant, so both arms are `Ok`).
pub fn prover_config(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> Result<ProverConfig, UnsupportedGpuSecurityLevel> {
    Ok(config_for_supported_level(circuit_type, security_level))
}

fn config_for_supported_level(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> ProverConfig {
    let domain_size_log_2 = circuit_type.get_domain_size_log2();
    // CPU's `example_configs` only defines schedules for {20, 22, 24}; collapse
    // 23 onto 24 to match the previous GPU mapping.
    let schedule_log_2 = match domain_size_log_2 {
        20 | 22 | 24 => domain_size_log_2,
        23 => 24,
        other => {
            panic!(
                "no ProverConfig for circuit {circuit_type:?} at {security_level:?} \
                 (domain_size_log_2 = {other})"
            )
        }
    };
    config_for_security_level_under_pessimistic_conjecture(schedule_log_2 as usize, security_level)
}

/// PoW bit count for the lookup challenges (`lookup_alpha`, `lookup_additive`),
/// derived per-circuit from the config's `security_level` — matching the CPU
/// `draw_random_field_els_with_pow` site in `prover::gkr::prover`. 0 at Sec80,
/// non-zero at Sec100. Fed to the pow-aware lookup-challenge draw in
/// `proof/orchestration/stage1_forward.rs`.
pub(crate) fn lookup_challenges_pow_bits(
    prover_config: &ProverConfig,
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> u32 {
    pow_bits::lookup_challenges_pow_bits(
        prover_config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(compiled_circuit),
    )
}

/// PoW bit count for the WHIR base batching challenge, derived per-circuit from
/// the config's `security_level` — matching the CPU
/// `draw_random_field_els_with_pow` site. 0 at Sec80, non-zero at Sec100. Fed to
/// the pow-aware batching draw in `proof/orchestration/whir.rs`.
pub(crate) fn batched_proximity_check_pow_bits(
    prover_config: &ProverConfig,
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> u32 {
    pow_bits::batched_proximity_check_pow_bits(
        prover_config.security_level.security_bits(),
        compiled_circuit.trace_len.trailing_zeros() as usize,
        prover_config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(compiled_circuit),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use gpu_trace::witness::circuit_type::UnrolledCircuitType;

    #[test]
    fn builds_prover_config_for_all_supported_security_levels() {
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
        for &level in GPU_SUPPORTED_SECURITY_LEVELS.iter() {
            let cfg = prover_config(circuit_type, level).unwrap();
            assert_eq!(cfg.security_level, level);
        }
    }
}
