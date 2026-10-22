use crate::upstream::{ProverConfig, SecurityLevel};
use crate::{CommitmentMode, ExecutionKind, ProofProfile};
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::JitRunnerRam;

/// Commitments and proofs use the circuit's own config unless an L1 profile overrides it.
pub fn prover_config(
    circuit_type: CircuitType,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> ProverConfig {
    match profile {
        ProofProfile::Standard => circuit_type.prover_config(security_level),
        l1 => l1.prover_config(circuit_type.get_domain_size_log2() as usize, security_level),
    }
}

/// Unified executions take their mode from the selected circuit configuration.
/// Per-family unrolled executions only support separate commitments.
pub fn execution_commitment_mode(
    kind: ExecutionKind,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> CommitmentMode {
    match kind.unified_circuit() {
        Some(circuit) => prover_config(circuit, profile, security_level).commitment_mode,
        None => {
            assert_eq!(profile, ProofProfile::Standard);
            CommitmentMode::SeparateMemoryAndWitness
        }
    }
}

pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    fn execution_defaults() -> ExecutionProverConfiguration<Self>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration<C> {
    /// Shared host-work pool, also used for CPU proving; simulation and replay
    /// run on their own threads.
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_per_job_count: usize,
    /// Free blocks the cache is trimmed back towards; pressure relief, not a bound.
    pub min_free_host_allocators_per_job: usize,
    pub security_level: SecurityLevel,
    pub ram_config: JitRunnerRam,
    /// Simulate the field operations (MOPs) without the reduction of their inputs
    /// (`MopField::BabyBearAssumeCanonical`). It is only valid for the programs that never
    /// feed a non-canonical value into a field operation: the simulated execution diverges
    /// from the replayed one otherwise.
    pub assume_canonical_mop_inputs: bool,
    pub backend: C,
}

impl<C: BackendConfiguration> Default for ExecutionProverConfiguration<C> {
    fn default() -> Self {
        C::execution_defaults()
    }
}

#[cfg(test)]
mod l1_wrap_tests {
    use super::*;
    use crate::ExecutionKind;
    use ::prover::gkr::prover_config::example_configs::l1_wrap_2p21;
    use common_constants::rom::{L1_WRAP_ROM, REGULAR_ROM};

    #[test]
    fn execution_modes_resolve_the_selected_circuit_config() {
        for (kind, profile) in [
            (ExecutionKind::Unified, ProofProfile::Standard),
            (ExecutionKind::Unified, ProofProfile::L1FeederA),
            (ExecutionKind::Unified22, ProofProfile::L1Feeder),
            (ExecutionKind::L1Wrap21, ProofProfile::L1Wrap),
        ] {
            let circuit = kind.unified_circuit().unwrap();
            assert_eq!(
                execution_commitment_mode(kind, profile, SecurityLevel::Sec100),
                prover_config(circuit, profile, SecurityLevel::Sec100).commitment_mode,
            );
        }
        assert_eq!(
            execution_commitment_mode(
                ExecutionKind::Unified,
                ProofProfile::L1FeederA,
                SecurityLevel::Sec100
            ),
            CommitmentMode::MergedMemoryAndWitness,
        );
        assert_eq!(
            execution_commitment_mode(
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
                SecurityLevel::Sec100,
            ),
            CommitmentMode::SeparateMemoryAndWitness,
        );
    }

    #[test]
    fn unrolled_execution_rejects_l1_profiles() {
        for profile in [ProofProfile::L1Feeder, ProofProfile::L1FeederA] {
            assert!(std::panic::catch_unwind(|| execution_commitment_mode(
                ExecutionKind::Unrolled,
                profile,
                SecurityLevel::Sec100,
            ))
            .is_err());
        }
    }

    #[test]
    fn l1_wrap_identities_select_matching_config_and_rom() {
        let (kind, circuit) = (ExecutionKind::L1Wrap21, CircuitType::L1Wrap21);
        let expected = l1_wrap_2p21::packed_prover_config(SecurityLevel::Sec100);
        assert!(kind.is_l1_wrap() && !kind.is_unified());
        assert_eq!(kind.unified_circuit(), Some(circuit));
        assert_eq!(kind.rom(), L1_WRAP_ROM);
        assert_eq!(circuit.rom(), L1_WRAP_ROM);
        assert_eq!(circuit.get_domain_size_log2(), 21);
        let config = prover_config(circuit, ProofProfile::L1Wrap, SecurityLevel::Sec100);
        assert_eq!(config.trace_len_log2, 21);
        assert_eq!(config.lde_factor, expected.lde_factor);
        assert_eq!(config.whir_schedule, expected.whir_schedule);
        assert_eq!(config.pack_log2, expected.pack_log2);
        assert_eq!(config.commitment_mode, expected.commitment_mode);
        for kind in [
            ExecutionKind::Unrolled,
            ExecutionKind::Unified,
            ExecutionKind::Unified22,
        ] {
            assert!(!kind.is_l1_wrap());
            assert_eq!(kind.rom(), REGULAR_ROM);
        }
    }
}
