//! The GPU specialization of the shared execution backend contract. The shared
//! orchestrator sees only the associated types.

use crate::errors::{extra_trace_blocks_for, GpuBackendError};
use crate::host_storage::{GpuTraceAllocator, LockedBoxedMemoryHolder, LockedBoxedTraceChunk};
use crate::precomputations::CircuitPrecomputations;
use crate::upstream::SecurityLevel;
use crate::workers::gpu_manager::GpuManager;
use era_cudart::device::get_device_count;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use execution_prover::backend::{CircuitPrecomputation, ExecutionBackend};
use execution_prover::config::{BackendConfiguration, ExecutionProverConfiguration};
use execution_prover::messages::WorkBatch;
use execution_prover::{CanonicalCircuitSetup, ExecutionProverError};
use execution_prover_model::circuit_type::CircuitType;
use gpu_circuit_prover::config::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};
use gpu_core::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover_context::ProverContextConfig;
use riscv_transpiler::jit::JitRunnerRam;
use std::sync::Arc;
use worker::Worker;

/// GPU-specific configuration.
#[derive(Clone, Copy, Debug)]
pub struct GpuBackendConfiguration {
    pub memory_preset: MemoryPreset,
    pub prover_context_config: ProverContextConfig,
    pub host_allocators_per_device_count: usize,
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

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MemoryPreset {
    /// Select the largest preset that fits after reserving context memory and slack.
    #[default]
    Auto,
    GiB30,
    GiB21,
}

impl GpuBackendConfiguration {
    fn context_config(self) -> ProverContextConfig {
        let mut config = self.prover_context_config;
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
}

impl BackendConfiguration for GpuBackendConfiguration {
    const BACKEND_NAME: &'static str = "gpu";

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

    fn validate(&self) -> Result<(), ExecutionProverError> {
        Ok(())
    }

    /// The staged manager already bounds in-flight work per device, so a
    /// second limiter here would only change pipeline behaviour.
    fn admission_limit(&self, _expected_concurrent_jobs: usize) -> Option<usize> {
        None
    }
}

/// The shared configuration is deliberately permissive about security levels;
/// restricting them is a backend decision.
fn validate_security_level(
    security_level: SecurityLevel,
) -> Result<(), UnsupportedGpuSecurityLevel> {
    if GPU_SUPPORTED_SECURITY_LEVELS.contains(&security_level) {
        Ok(())
    } else {
        Err(UnsupportedGpuSecurityLevel {
            requested: security_level,
        })
    }
}

impl CircuitPrecomputation for CircuitPrecomputations {
    fn compiled_circuit(
        &self,
    ) -> &Arc<crate::upstream::GKRCircuitArtifact<gpu_core::primitives::field::BF>> {
        self.gkr_programs.compiled_circuit()
    }

    fn setup_cap(&self) -> Option<crate::upstream::MerkleTreeCapVarLength> {
        self.setup_host.get_initialized().map(|setup_host| {
            crate::upstream::MerkleTreeCapVarLength {
                cap: setup_host.unified_tree_cap().to_vec(),
            }
        })
    }
}

pub struct GpuBackend {
    manager: GpuManager,
    /// `device_count * host_allocators_per_device_count`, checked once at
    /// startup so the shared accounting never sees an unchecked product.
    extra_trace_blocks: usize,
}

fn into_execution_error(error: GpuBackendError) -> ExecutionProverError {
    ExecutionProverError::backend_initialization(GpuBackendConfiguration::BACKEND_NAME, error)
}

impl ExecutionBackend for GpuBackend {
    type Configuration = GpuBackendConfiguration;
    type Allocator = GpuTraceAllocator;
    type Memory = LockedBoxedMemoryHolder;
    type Snapshot = LockedBoxedTraceChunk;
    type Precomputations = CircuitPrecomputations;

    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        _worker: Arc<Worker>,
    ) -> Result<Self, ExecutionProverError> {
        validate_security_level(config.security_level)
            .map_err(GpuBackendError::UnsupportedSecurityLevel)
            .map_err(into_execution_error)?;
        let device_count = get_device_count()
            .map_err(GpuBackendError::DeviceCountQuery)
            .map_err(into_execution_error)? as usize;
        if device_count == 0 {
            return Err(into_execution_error(GpuBackendError::NoDevices));
        }
        let extra_trace_blocks = extra_trace_blocks_for(
            device_count,
            config.backend.host_allocators_per_device_count,
        )
        .map_err(into_execution_error)?;
        // Blocks until every device worker has acknowledged its context.
        let manager = GpuManager::try_new(config.backend.context_config())
            .map_err(into_execution_error)?;
        Ok(Self {
            manager,
            extra_trace_blocks,
        })
    }

    fn allocate_trace_block(&self, bytes: usize) -> Result<Self::Allocator, ExecutionProverError> {
        let allocation = HostAllocation::alloc(bytes, CudaHostAllocFlags::DEFAULT)
            .map_err(|source| GpuBackendError::HostAllocation { bytes, source })
            .map_err(into_execution_error)?;
        Ok(GpuTraceAllocator::new(ConcurrentStaticHostAllocator::new(
            [allocation],
            bytes.trailing_zeros(),
        )))
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Result<Self::Memory, ExecutionProverError> {
        LockedBoxedMemoryHolder::try_new(ram).map_err(into_execution_error)
    }

    fn allocate_snapshot(&self) -> Result<Self::Snapshot, ExecutionProverError> {
        LockedBoxedTraceChunk::try_new().map_err(into_execution_error)
    }

    /// The per-device share of the host buffer pool, which the shared per-job
    /// accounting does not model.
    fn extra_trace_blocks(&self) -> usize {
        self.extra_trace_blocks
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
    ) -> Result<Self::Precomputations, ExecutionProverError> {
        let prover_config = gpu_circuit_prover::config::prover_config(circuit, security)
            .map_err(GpuBackendError::UnsupportedSecurityLevel)
            .map_err(into_execution_error)?;
        CircuitPrecomputations::from_canonical(
            circuit,
            setup,
            prover_config.lde_factor.trailing_zeros(),
            prover_config.base_oracles_values_per_leaf.trailing_zeros(),
            prover_config.cap_size.trailing_zeros(),
        )
        .map_err(GpuBackendError::Precomputation)
        .map_err(into_execution_error)
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        self.manager.send_batch(batch);
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
