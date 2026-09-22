use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, ProverConfig, SecurityLevel,
};
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::MIN_HOST_TRACE_BLOCK_BYTES;
use riscv_transpiler::jit::JitRunnerRam;

/// Commitments and proofs must use the same geometry on both backends.
pub fn prover_config(circuit_type: CircuitType, security_level: SecurityLevel) -> ProverConfig {
    config_for_security_level_under_pessimistic_conjecture(
        circuit_type.get_domain_size_log2() as usize,
        security_level,
    )
}

pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    /// Shared defaults also depend on the backend.
    fn execution_defaults() -> ExecutionProverConfiguration<Self>;
    fn validate(&self);
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

impl<C: BackendConfiguration> ExecutionProverConfiguration<C> {
    pub fn validate(&self) {
        assert!(self.expected_concurrent_jobs > 0);
        assert!(self.replay_worker_threads_count > 0);
        assert!(self.host_allocators_per_job_count > 0);
        assert!(self.min_free_host_allocators_per_job <= self.host_allocators_per_job_count);
        let block_bytes = self.host_allocator_backing_allocation_size;
        assert!(
            block_bytes.is_power_of_two() && block_bytes >= MIN_HOST_TRACE_BLOCK_BYTES,
            "host trace blocks must be a power of two of at least {MIN_HOST_TRACE_BLOCK_BYTES} bytes"
        );
        self.backend.validate();
    }
}
