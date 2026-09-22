//! The CPU half of the split execution configuration.

use execution_prover::config::{BackendConfiguration, ExecutionProverConfiguration};
use prover::definitions::SecurityLevel;
use riscv_transpiler::jit::JitRunnerRam;

#[derive(Clone, Copy, Debug, Default)]
pub struct CpuBackendConfiguration {}

impl BackendConfiguration for CpuBackendConfiguration {
    fn execution_defaults() -> ExecutionProverConfiguration<Self> {
        ExecutionProverConfiguration {
            max_thread_pool_threads: None,
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 1,
            host_allocator_backing_allocation_size: 1 << 26,
            host_allocators_per_job_count: 256,
            min_free_host_allocators_per_job: 32,
            security_level: SecurityLevel::Sec100,
            ram_config: JitRunnerRam::Medium,
            backend: Self::default(),
        }
    }

    fn validate(&self) {}
}

pub type CpuExecutionProverConfiguration = ExecutionProverConfiguration<CpuBackendConfiguration>;
