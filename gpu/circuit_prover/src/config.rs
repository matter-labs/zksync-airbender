//! Prover configuration policy.
//!
//! Maps a `CircuitType` + `ProvingSelection` (security level and soundness
//! mode) to the canonical upstream `ProverConfig`, and owns the
//! GPU-supported-security-level contract. The
//! canonical configs include virtual packing, with independent physical
//! packing in the Blake compression default. The proof backend qualifies
//! separate physical-only configurations and the qualified merged Blake shape
//! through shared geometry admission.
//! Workers retain one resolved CPU config for setup and both request phases;
//! virtual defaults remain closed at that execution boundary. The qualified
//! physical merged Blake shape uses the same immutable config binding.
//! Lives in
//! the prover layer because `ProverConfig` is a `prove()` input (see
//! `proof/mod.rs`): `execution` calls down into this and threads the result
//! into `prove()`. The low `witness::circuit_type` enum stays a pure
//! domain type with no `ProverConfig`/`SecurityLevel` coupling.

use crate::upstream::{
    pow_bits, BaseCommitmentGeometry, ConfigSelectionError, GKRCircuitArtifact, ProofProfile,
    ProverConfig, ProvingSelection, SecurityLevel,
};
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

/// Canonical `ProverConfig` for `circuit_type` under `selection`, resolved from
/// the compiled circuit's committed columns. Delegates to the CPU resolver
/// (`CircuitType::try_prover_config_in_mode`) so GPU and CPU agree on the WHIR
/// schedule in every soundness mode (the per-circuit lookup-challenge and
/// WHIR-batching PoWs are ground on device — see [`lookup_challenges_pow_bits`] /
/// [`batched_proximity_check_pow_bits_for_geometry`] — and so are the
/// folding-challenge and OOD PoWs a schedule carries).
pub fn prover_config_for_selection(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    selection: ProvingSelection,
) -> Result<ProverConfig, ConfigSelectionError> {
    circuit_type.try_prover_config_in_mode(compiled_circuit, selection)
}

/// [`prover_config_for_selection`] for one declared `profile`: `Standard` resolves the
/// selected mode from the compiled columns; the L1 profiles use their special configs, which
/// exist only under `PessimisticConjecture` (deferred-scope `UnsupportedSpecialConfigMode`).
pub fn prover_config_for_profile_selection(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    profile: ProofProfile,
    selection: ProvingSelection,
) -> Result<ProverConfig, ConfigSelectionError> {
    match profile {
        ProofProfile::Standard => {
            prover_config_for_selection(circuit_type, compiled_circuit, selection)
        }
        l1 => l1.try_prover_config(circuit_type.get_domain_size_log2() as usize, selection),
    }
}

/// Pessimistic-conjecture `ProverConfig` for `circuit_type` at
/// `security_level`: the circuit definition's own config, equal to
/// [`prover_config_for_selection`] in that mode.
///
/// The `Result` is retained for API stability (`SecurityLevel` currently has no
/// unsupported variant, so both arms are `Ok`).
pub fn prover_config(
    circuit_type: CircuitType,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> Result<ProverConfig, UnsupportedGpuSecurityLevel> {
    Ok(if profile == ProofProfile::Standard {
        config_for_supported_level(circuit_type, security_level)
    } else {
        profile.prover_config(circuit_type.get_domain_size_log2() as usize, security_level)
    })
}

fn config_for_supported_level(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> ProverConfig {
    circuit_type.prover_config(security_level)
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

/// Override-aware batching over the preflight's single physical count authority.
pub(crate) fn batched_proximity_check_pow_bits_for_geometry(
    config: &ProverConfig,
    geometry: &BaseCommitmentGeometry,
) -> u32 {
    config.base_round().batching_pow_bits::<BF, E4>(
        config.security_level.security_bits(),
        geometry.message_size_log2(),
        geometry.total_physical_columns(),
    )
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod l1_profile_tests {
    use super::*;
    use gpu_trace::witness::circuit_type::UnrolledCircuitType;
    #[test]
    fn cpu_l1_profile_configs() {
        use gpu_trace::witness::circuit_type::{
            DelegationCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
        };
        let geometry = |config: &ProverConfig| {
            (
                config.trace_len_log2,
                config.lde_factor(),
                config.cap_size,
                config.base_oracles_values_per_leaf(),
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
            let feeder_a = prover_config(
                CircuitType::Unrolled(UnrolledCircuitType::Unified),
                ProofProfile::L1FeederA,
                level,
            )
            .unwrap();
            assert_eq!(geometry(&feeder_a), (23, 4, 4, 2));
            let wrap = prover_config(CircuitType::L1Wrap21, ProofProfile::L1Wrap, level).unwrap();
            assert_eq!(geometry(&wrap), (21, 128, 8, 2));
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
                let expected = circuit.prover_config(level);
                assert_eq!(
                    format!("{actual:?}"),
                    format!("{expected:?}"),
                    "{circuit:?}"
                );
            }
        }
    }
}
