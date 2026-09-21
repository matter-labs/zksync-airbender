use crate::error::ExecutionProverError;
use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, ProverConfig, SecurityLevel,
};
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::MIN_HOST_TRACE_BLOCK_BYTES;
use riscv_transpiler::jit::JitRunnerRam;
use worker::Worker;

/// Commitments and proofs must use the same geometry on both backends.
pub fn prover_config(circuit_type: CircuitType, security_level: SecurityLevel) -> ProverConfig {
    config_for_security_level_under_pessimistic_conjecture(
        circuit_type.get_domain_size_log2() as usize,
        security_level,
    )
}

pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    const BACKEND_NAME: &'static str;

    /// Shared defaults also depend on the backend.
    fn execution_defaults() -> ExecutionProverConfiguration<Self>;
    fn validate(&self) -> Result<(), ExecutionProverError>;
    fn admission_limit(&self, expected_concurrent_jobs: usize) -> Option<usize>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration<C> {
    /// Shared host-work pool; simulation, replay and CPU proving have their own threads.
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
    pub fn validate(&self) -> Result<(), ExecutionProverError> {
        if self.expected_concurrent_jobs == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "expected_concurrent_jobs",
                "must be at least one",
            ));
        }
        for (field, threads) in [
            (
                "replay_worker_threads_count",
                Some(self.replay_worker_threads_count),
            ),
            ("max_thread_pool_threads", self.max_thread_pool_threads),
        ] {
            if let Some(threads) = threads {
                if !(1..=Worker::MAX_WORKER_SIZE).contains(&threads) {
                    return Err(ExecutionProverError::invalid_configuration(
                        field,
                        format!("must be between 1 and {}", Worker::MAX_WORKER_SIZE),
                    ));
                }
            }
        }
        if self.host_allocators_per_job_count == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocators_per_job_count",
                "must be at least one",
            ));
        }
        let block_bytes = self.host_allocator_backing_allocation_size;
        if !block_bytes.is_power_of_two()
            || block_bytes < MIN_HOST_TRACE_BLOCK_BYTES
            || std::alloc::Layout::from_size_align(block_bytes, 1).is_err()
        {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocator_backing_allocation_size",
                format!(
                    "must be a legal power-of-two allocation of at least {MIN_HOST_TRACE_BLOCK_BYTES} bytes"
                ),
            ));
        }
        if self.ram_config == JitRunnerRam::UninitPlaceholder {
            return Err(ExecutionProverError::invalid_configuration(
                "ram_config",
                "the placeholder RAM configuration cannot be used for execution",
            ));
        }
        self.total_host_allocators(0)?;
        if self.min_free_host_allocators_per_job > self.host_allocators_per_job_count {
            return Err(ExecutionProverError::invalid_configuration(
                "min_free_host_allocators_per_job",
                "the free-pool floor exceeds the whole pool",
            ));
        }
        if self
            .expected_concurrent_jobs
            .checked_add(1)
            .and_then(|entries| entries.checked_mul(self.replay_worker_threads_count))
            .and_then(|chunks| chunks.checked_mul(2))
            .is_none()
        {
            return Err(ExecutionProverError::invalid_configuration(
                "replay_worker_threads_count",
                "snapshot cache size overflows",
            ));
        }
        self.backend.validate()
    }

    pub fn admission_limit(&self) -> Option<usize> {
        self.backend.admission_limit(self.expected_concurrent_jobs)
    }

    pub(crate) fn total_host_allocators(
        &self,
        extra: usize,
    ) -> Result<usize, ExecutionProverError> {
        let total = self
            .expected_concurrent_jobs
            .checked_mul(self.host_allocators_per_job_count)
            .and_then(|blocks| blocks.checked_add(extra))
            .ok_or_else(|| {
                ExecutionProverError::invalid_configuration(
                    "host_allocators_per_job_count",
                    "total host block count overflows",
                )
            })?;
        total
            .checked_mul(self.host_allocator_backing_allocation_size)
            .ok_or_else(|| {
                ExecutionProverError::invalid_configuration(
                    "host_allocator_backing_allocation_size",
                    "total host pool size overflows",
                )
            })?;
        Ok(total)
    }
}

#[cfg(test)]
mod tests;
