//! The CPU half of the split execution configuration.
//!
//! Every thread count here sizes a *compute pool*, not the process: the
//! simulation and replay loops and the manager's own two threads sit outside
//! it, so a one-thread proving pool still means several OS threads.

use execution_prover::config::{BackendConfiguration, ExecutionProverConfiguration};
use execution_prover::ExecutionProverError;
use prover::definitions::SecurityLevel;
use riscv_transpiler::jit::JitRunnerRam;
use std::thread::available_parallelism;
use worker::Worker;

/// Kept out of the proving pool so the pipeline stays runnable while a proof
/// occupies the machine: the simulation loop, the replay loop and the auxiliary
/// host-work pool.
const RESERVED_THREADS: usize = 3;

const REPLAY_WORKER_THREADS: usize = 1;
const AUXILIARY_THREADS: usize = 1;
const EXPECTED_CONCURRENT_JOBS: usize = 1;

/// The block size the production publication bound was checked against. The
/// per-job count is derived from it and the configured RAM rather than written
/// down, because a literal silently goes stale when either changes.
const HOST_ALLOCATOR_BACKING_ALLOCATION_SIZE: usize = 1 << 26;

/// Baseline pool size, kept as headroom above the producer-progress reserve:
/// the trace cache gets `N - R_effective - 1` blocks, so a pool at exactly the
/// minimum would cache nothing and re-simulate for every prove pass.
const BASELINE_HOST_ALLOCATORS_PER_JOB: usize = 256;

/// Proving-pool size when the configuration does not pin one. A host smaller
/// than the reserve resolves to one proving thread, because a one-core host is
/// a legal, if slow, configuration.
fn default_proving_threads() -> usize {
    let parallelism = available_parallelism()
        .expect("host CPU quota must be readable to size the proving pool")
        .get();
    parallelism
        .saturating_sub(RESERVED_THREADS)
        .clamp(1, Worker::MAX_WORKER_SIZE)
}

/// CPU-specific configuration.
#[derive(Clone, Copy, Debug, Default)]
pub struct CpuBackendConfiguration {
    /// Threads one circuit request computes on. `None` resolves against the
    /// host at initialization, so a configuration built on one machine does not
    /// pin another machine's core count.
    pub proving_threads: Option<usize>,
}

impl CpuBackendConfiguration {
    pub(crate) fn resolved_proving_threads(&self) -> usize {
        self.proving_threads.unwrap_or_else(default_proving_threads)
    }
}

impl BackendConfiguration for CpuBackendConfiguration {
    const BACKEND_NAME: &'static str = "cpu";

    fn execution_defaults() -> ExecutionProverConfiguration<Self> {
        let mut configuration = ExecutionProverConfiguration {
            max_thread_pool_threads: Some(AUXILIARY_THREADS),
            expected_concurrent_jobs: EXPECTED_CONCURRENT_JOBS,
            replay_worker_threads_count: REPLAY_WORKER_THREADS,
            host_allocator_backing_allocation_size: HOST_ALLOCATOR_BACKING_ALLOCATION_SIZE,
            // Replaced below; the reserve depends on the two fields above.
            host_allocators_per_job_count: 0,
            security_level: SecurityLevel::Sec100,
            ram_config: JitRunnerRam::Medium,
            backend: Self::default(),
        };
        let minimum = configuration
            .minimum_host_allocators_per_job()
            .expect("CPU defaults must leave room for the producer-progress reserve");
        configuration.host_allocators_per_job_count = BASELINE_HOST_ALLOCATORS_PER_JOB.max(minimum);
        configuration
    }

    fn validate(&self) -> Result<(), ExecutionProverError> {
        let Some(threads) = self.proving_threads else {
            return Ok(());
        };
        if threads == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "backend.proving_threads",
                "must be at least one when set",
            ));
        }
        if threads > Worker::MAX_WORKER_SIZE {
            return Err(ExecutionProverError::invalid_configuration(
                "backend.proving_threads",
                format!(
                    "{threads} exceeds the maximum worker size {}",
                    Worker::MAX_WORKER_SIZE
                ),
            ));
        }
        Ok(())
    }

    /// One admitted execution per expected job: a request holds its whole trace
    /// ownership while it proves, so extra simultaneous callers would consume
    /// the credits the producers need to make progress.
    fn admission_limit(&self, expected_concurrent_jobs: usize) -> Option<usize> {
        Some(expected_concurrent_jobs)
    }
}

pub type CpuExecutionProverConfiguration = ExecutionProverConfiguration<CpuBackendConfiguration>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_are_valid() {
        let config = CpuExecutionProverConfiguration::default();
        config.validate().unwrap();
        assert!(
            config.host_allocators_per_job_count
                >= config.minimum_host_allocators_per_job().unwrap()
        );
    }

    #[test]
    fn illegal_proving_thread_counts_are_rejected() {
        for threads in [0, Worker::MAX_WORKER_SIZE + 1] {
            let mut config = CpuExecutionProverConfiguration::default();
            config.backend.proving_threads = Some(threads);
            assert!(config.validate().is_err());
        }
        let mut config = CpuExecutionProverConfiguration::default();
        config.backend.proving_threads = Some(Worker::MAX_WORKER_SIZE);
        config.validate().unwrap();
    }
}
