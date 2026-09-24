use riscv_transpiler::jit::JitRunnerRam;

use crate::upstream::SecurityLevel;
use execution_prover::config::{BackendConfiguration, ExecutionProverConfiguration};
use gpu_circuit_prover::config::GPU_SUPPORTED_SECURITY_LEVELS;
use gpu_prover_context::ProverContextConfig;

#[derive(Clone, Copy, Debug)]
pub struct GpuBackendConfiguration {
    pub memory_preset: MemoryPreset,
    pub prover_context_config: ProverContextConfig,
    pub host_allocators_per_device_count: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MemoryPreset {
    /// Select the largest preset that fits after reserving context memory and slack.
    #[default]
    Auto,
    GiB30,
    GiB21,
}

impl GpuBackendConfiguration {
    pub(super) fn context_config(self) -> ProverContextConfig {
        let mut config = self.prover_context_config;
        config.inputs_reserve_bytes = crate::memory_policy::INPUTS_RESERVE_BYTES;
        let bytes: usize = match self.memory_preset {
            MemoryPreset::Auto => return config,
            MemoryPreset::GiB30 => 30 << 30,
            MemoryPreset::GiB21 => 21 << 30,
        };
        assert!(
            config.device_allocation_blocks_count.is_none(),
            "select a memory preset or an explicit arena block count, not both"
        );
        let block_size = 1usize
            .checked_shl(config.allocator_block_log_size)
            .expect("allocator_block_log_size must be less than usize::BITS");
        assert!(
            bytes.is_multiple_of(block_size),
            "memory preset arena must be aligned to the allocator block size"
        );
        config.device_allocation_blocks_count = Some(bytes / block_size);
        config
    }

    pub const fn supported_security_levels() -> &'static [SecurityLevel] {
        &GPU_SUPPORTED_SECURITY_LEVELS
    }
}

impl Default for GpuBackendConfiguration {
    fn default() -> Self {
        Self {
            memory_preset: MemoryPreset::Auto,
            prover_context_config: ProverContextConfig::default(),
            host_allocators_per_device_count: 128, // 8 GB
        }
    }
}

impl BackendConfiguration for GpuBackendConfiguration {
    fn execution_defaults() -> ExecutionProverConfiguration<Self> {
        ExecutionProverConfiguration {
            max_thread_pool_threads: None,
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 8,
            host_allocator_backing_allocation_size: 1 << 26, // 64 MB
            host_allocators_per_job_count: 256,              // 16 GB
            min_free_host_allocators_per_job: 32,            // 2 GB
            security_level: SecurityLevel::Sec100,
            ram_config: JitRunnerRam::Medium, // 1Gb
            backend: Self::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_memory_preset_configures_exact_arena() {
        for (preset, bytes) in [
            (MemoryPreset::Auto, None),
            (MemoryPreset::GiB21, Some(21usize << 30)),
            (MemoryPreset::GiB30, Some(30usize << 30)),
        ] {
            let config = GpuBackendConfiguration {
                memory_preset: preset,
                ..Default::default()
            }
            .context_config();
            assert_eq!(
                config
                    .device_allocation_blocks_count
                    .map(|blocks| blocks << config.allocator_block_log_size),
                bytes
            );
        }
        let mut config = GpuBackendConfiguration::default();
        config.prover_context_config.device_allocation_blocks_count = Some(22 << 10);
        assert_eq!(
            config.context_config().device_allocation_blocks_count,
            Some(22 << 10)
        );
        config.memory_preset = MemoryPreset::GiB21;
        assert!(std::panic::catch_unwind(|| config.context_config()).is_err());
    }
}
