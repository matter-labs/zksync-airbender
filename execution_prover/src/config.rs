use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, ProverConfig, SecurityLevel,
};
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::JitRunnerRam;

/// Commitments and proofs must use the same geometry on both backends.
pub fn prover_config(circuit_type: CircuitType, security_level: SecurityLevel) -> ProverConfig {
    config_for_security_level_under_pessimistic_conjecture(
        circuit_type.get_domain_size_log2() as usize,
        security_level,
    )
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
    pub backend: C,
}

impl<C: BackendConfiguration> Default for ExecutionProverConfiguration<C> {
    fn default() -> Self {
        C::execution_defaults()
    }
}
