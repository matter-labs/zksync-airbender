use crate::upstream::{ProverConfig, SecurityLevel};
use crate::ProofProfile;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use riscv_transpiler::jit::JitRunnerRam;

/// Commitments and proofs must use the same geometry on both backends.
pub fn prover_config(
    circuit_type: CircuitType,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> ProverConfig {
    if profile == ProofProfile::L1Feeder {
        assert_eq!(
            circuit_type,
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            "ProofProfile::L1Feeder requires ExecutionKind::Unified"
        );
    }
    profile.prover_config(circuit_type.get_domain_size_log2() as usize, security_level)
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
