//! Prover configuration policy.
//!
//! Maps a `CircuitType` + `SecurityLevel` to the canonical upstream
//! `ProverConfig`, and owns the GPU-supported-security-level contract. The
//! canonical configs include virtual packing, with independent physical
//! packing in the Blake compression default. The proof backend qualifies
//! separate physical-only configurations and the qualified merged Blake shape
//! through shared geometry admission.
//! Workers retain one resolved CPU config for setup and both request phases;
//! virtual defaults and merged commitments remain closed at that execution boundary.
//! Lives in
//! the prover layer because `ProverConfig` is a `prove()` input (see
//! `proof/mod.rs`): `execution` calls down into this and threads the result
//! into `prove()`. The low `witness::circuit_type` enum stays a pure
//! domain type with no `ProverConfig`/`SecurityLevel` coupling.

use crate::upstream::{
    pow_bits, BaseCommitmentGeometry, GKRCircuitArtifact, ProverConfig, SecurityLevel,
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

/// Canonical `ProverConfig` for `circuit_type` at `security_level`. Delegates to
/// the CPU's `config_for_security_level_under_pessimistic_conjecture` so GPU and
/// CPU agree on the production WHIR schedule (the per-circuit lookup-challenge
/// and WHIR-batching PoWs are ground on device — see
/// [`lookup_challenges_pow_bits`] / [`batched_proximity_check_pow_bits_for_geometry`]).
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
    // the circuit definition's own config (`CircuitType::prover_config`)
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
