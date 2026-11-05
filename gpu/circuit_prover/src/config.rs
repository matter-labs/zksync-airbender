//! Prover configuration policy.
//!
//! Maps a `CircuitType` + `ProvingSelection` (security level and soundness
//! mode) to the canonical upstream `ProverConfig`, and owns the
//! GPU-supported-security-level contract. The
//! canonical configs include virtual packing, with independent physical
//! packing in the Blake compression default. The proof backend admits
//! separate physical-only configurations and the merged Blake shape through
//! shared geometry admission.
//! Workers retain one resolved CPU config and its commitment geometry for
//! setup and both request phases; the canonical virtual defaults and the
//! physical merged Blake shape are admitted through that immutable binding.
//! Lives in
//! the prover layer because `ProverConfig` is a `prove()` input (see
//! `proof/mod.rs`): `execution` calls down into this and threads the result
//! into `prove()`. `witness::circuit_type::CircuitType` is the shared
//! `execution_prover_model` type: it resolves its own artifact-free
//! `ProverConfig` at a security level and the explicit-mode config from a
//! compiled circuit, and this module delegates to those resolvers.

use crate::upstream::{
    pow_bits, BaseCommitmentGeometry, GKRCircuitArtifact, ProofProfile, ProverConfig,
    ProvingSelection, SecurityLevel,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_trace::witness::circuit_type::CircuitType;

/// Security levels the GPU prover supports.
pub const GPU_SUPPORTED_SECURITY_LEVELS: [SecurityLevel; 1] = [SecurityLevel::Sec100];

/// Canonical `ProverConfig` for `circuit_type` under `profile` and `selection`. `Standard` is
/// resolved from the compiled circuit's committed columns; the L1 profiles use their special
/// configs ([`ProofProfile::prover_config`]), which exist only under `PessimisticConjecture`.
/// Delegates to the CPU resolvers (`CircuitType::prover_config_in_mode`) so GPU and CPU agree
/// on the WHIR schedule in every soundness mode (the per-circuit lookup-challenge and
/// WHIR-batching PoWs are ground on device — see [`lookup_challenges_pow_bits`] /
/// [`batched_proximity_check_pow_bits_for_geometry`] — and so are the
/// folding-challenge and OOD PoWs a schedule carries).
pub fn prover_config_for_selection(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    profile: ProofProfile,
    selection: ProvingSelection,
) -> ProverConfig {
    match profile {
        ProofProfile::Standard => circuit_type.prover_config_in_mode(compiled_circuit, selection),
        l1 => l1.prover_config(circuit_type.get_domain_size_log2() as usize, selection),
    }
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
        let geometry = |config: &ProverConfig| {
            (
                config.trace_len_log2,
                config.lde_factor(),
                config.cap_size,
                config.base_oracles_values_per_leaf(),
            )
        };
        for &level in GPU_SUPPORTED_SECURITY_LEVELS.iter() {
            let selection = ProvingSelection {
                security_level: level,
                soundness_mode: prover::definitions::SoundnessMode::PessimisticConjecture,
            };
            let resolve = |circuit: CircuitType, profile: ProofProfile| {
                profile.prover_config(circuit.get_domain_size_log2() as usize, selection)
            };
            let feeder = resolve(
                CircuitType::Unrolled(UnrolledCircuitType::Unified22),
                ProofProfile::L1Feeder,
            );
            assert_eq!(geometry(&feeder), (22, 16, 16, 2));
            let feeder_a = resolve(
                CircuitType::Unrolled(UnrolledCircuitType::Unified),
                ProofProfile::L1FeederA,
            );
            assert_eq!(geometry(&feeder_a), (23, 4, 4, 2));
            let wrap = resolve(CircuitType::L1Wrap21, ProofProfile::L1Wrap);
            assert_eq!(geometry(&wrap), (21, 128, 8, 2));
            assert_eq!(wrap.security_level, level);
        }
    }
}
