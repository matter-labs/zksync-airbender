//! Prover configuration policy.
//!
//! Maps a `CircuitType` + `SecurityLevel` to the canonical upstream
//! `ProverConfig`, and owns the GPU-supported-security-level contract. Lives in
//! the prover layer because `ProverConfig` is a `prove()` input (see
//! `proof/mod.rs`): `execution` calls down into this and threads the result
//! into `prove()`. The low `witness::circuit_type` enum stays a pure
//! domain type with no `ProverConfig`/`SecurityLevel` coupling.

use crate::upstream::{pow_bits, GKRCircuitArtifact, ProofProfile, ProverConfig, SecurityLevel};
use gpu_core::primitives::field::{BF, E4};
use gpu_trace::witness::circuit_type::CircuitType;

/// Security levels the GPU prover supports.
pub const GPU_SUPPORTED_SECURITY_LEVELS: [SecurityLevel; 1] = [SecurityLevel::Sec100];

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

/// Canonical `ProverConfig` for `circuit_type` under `profile` at
/// `security_level`. Delegates to the CPU's `ProofProfile::prover_config` so GPU
/// and CPU agree on the production WHIR schedule (the per-circuit
/// lookup-challenge and WHIR-batching PoWs are ground on device — see
/// [`lookup_challenges_pow_bits`] / [`batched_proximity_check_pow_bits`]).
///
/// The `Result` is retained for API stability (`SecurityLevel` currently has no
/// unsupported variant, so both arms are `Ok`).
pub fn prover_config(
    circuit_type: CircuitType,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> Result<ProverConfig, UnsupportedGpuSecurityLevel> {
    let domain_size_log_2 = circuit_type.get_domain_size_log2() as usize;
    Ok(profile.prover_config(domain_size_log_2, security_level))
}

/// PoW bit count for the lookup challenges (`lookup_alpha`, `lookup_additive`),
/// derived per-circuit from the config's `security_level` — matching the CPU
/// `draw_random_field_els_with_pow` site in `prover::gkr::prover`. Fed to the
/// pow-aware lookup-challenge draw in
/// `proof/orchestration/stage1_forward.rs`.
pub(crate) fn lookup_challenges_pow_bits(
    prover_config: &ProverConfig,
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> u32 {
    pow_bits::lookup_challenges_pow_bits::<BF, E4>(
        prover_config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(compiled_circuit),
    )
}

/// PoW bit count for the WHIR base batching challenge, derived per-circuit from
/// the config's `security_level` — matching the CPU
/// `draw_random_field_els_with_pow` site. Fed to the pow-aware batching draw in
/// `proof/orchestration/whir.rs`.
pub(crate) fn batched_proximity_check_pow_bits(
    prover_config: &ProverConfig,
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> u32 {
    pow_bits::batched_proximity_check_pow_bits::<BF, E4>(
        prover_config.security_level.security_bits(),
        compiled_circuit.trace_len.trailing_zeros() as usize,
        prover_config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(compiled_circuit),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::upstream::config_for_security_level_under_pessimistic_conjecture;
    use gpu_trace::witness::circuit_type::UnrolledCircuitType;

    #[test]
    fn builds_prover_config_for_all_supported_security_levels() {
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
        for &level in GPU_SUPPORTED_SECURITY_LEVELS.iter() {
            let cfg = prover_config(circuit_type, ProofProfile::Standard, level).unwrap();
            assert_eq!(cfg.security_level, level);
        }
    }

    #[test]
    fn cpu_m8_profile_configs() {
        use gpu_trace::witness::circuit_type::{
            DelegationCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
        };
        let geometry = |config: &ProverConfig| {
            (
                config.trace_len_log2,
                config.lde_factor,
                config.cap_size,
                config.base_oracles_values_per_leaf,
            )
        };
        for &level in GPU_SUPPORTED_SECURITY_LEVELS.iter() {
            let feeder = prover_config(
                CircuitType::Unrolled(UnrolledCircuitType::Unified22),
                ProofProfile::L1Feeder,
                level,
            )
            .unwrap();
            assert_eq!(geometry(&feeder), (22, 16, 16, 2));
            let wrap = prover_config(CircuitType::L1Wrap21, ProofProfile::L1Wrap, level).unwrap();
            assert_eq!(geometry(&wrap), (21, 512, 8, 2));
            assert_eq!(wrap.security_level, level);
            let circuits = DelegationCircuitType::get_all_delegation_types()
                .iter()
                .map(|&circuit| CircuitType::Delegation(circuit))
                .chain(
                    [
                        UnrolledCircuitType::InitsAndTeardowns,
                        UnrolledCircuitType::Memory(
                            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
                        ),
                        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly),
                        UnrolledCircuitType::NonMemory(
                            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
                        ),
                        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt),
                        UnrolledCircuitType::NonMemory(
                            UnrolledNonMemoryCircuitType::MulDivUnsigned,
                        ),
                        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary),
                        UnrolledCircuitType::Unified,
                        UnrolledCircuitType::Unified22,
                    ]
                    .map(CircuitType::Unrolled),
                );
            for circuit in circuits {
                let actual = prover_config(circuit, ProofProfile::Standard, level).unwrap();
                let expected = config_for_security_level_under_pessimistic_conjecture(
                    circuit.get_domain_size_log2() as usize,
                    level,
                );
                assert_eq!(
                    format!("{actual:?}"),
                    format!("{expected:?}"),
                    "{circuit:?}"
                );
            }
        }
    }

    #[test]
    fn unified_uses_its_canonical_schedule() {
        let circuit = CircuitType::Unrolled(UnrolledCircuitType::Unified);
        for &level in GPU_SUPPORTED_SECURITY_LEVELS.iter() {
            let actual = prover_config(circuit, ProofProfile::Standard, level).unwrap();
            let expected = config_for_security_level_under_pessimistic_conjecture(23, level);
            assert_eq!(actual.whir_schedule, expected.whir_schedule);
        }
    }
}
