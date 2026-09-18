use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use riscv_transpiler::jit::JitRunnerRam;
use riscv_transpiler::vm::SimpleTape;
use type_map::concurrent::TypeMap;

use crate::precomputations::CircuitPrecomputations;
use crate::upstream::SecurityLevel;
use gpu_circuit_prover::config::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};
use gpu_core::primitives::machine_type::MachineType;
use gpu_prover_context::ProverContextConfig;
use gpu_trace::witness::circuit_type::UnrolledCircuitType;

/// Specifies the execution mode for the prover.
///
/// - `Unrolled`: per-family circuits (split memory / non-memory / I&T).
/// - `Unified`: the reduced-machine unified circuit (single circuit family,
///   `MachineType::Reduced` only).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExecutionKind {
    Unrolled,
    Unified,
}

pub(super) struct BinaryHolder {
    pub(super) execution_kind: ExecutionKind,
    pub(super) machine_type: MachineType,
    pub(super) binary_image: Arc<Box<[u32]>>,
    pub(super) text_section: Arc<Box<[u32]>>,
    pub(super) cycles_bound: Option<u32>,
    pub(super) jit_cache: Arc<Mutex<TypeMap>>,
    pub(super) instruction_tape: Arc<SimpleTape>,
    pub(super) precomputations: HashMap<UnrolledCircuitType, CircuitPrecomputations>,
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration {
    pub memory_preset: MemoryPreset,
    pub prover_context_config: ProverContextConfig,
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_per_job_count: usize,
    pub host_allocators_per_device_count: usize,
    pub min_free_host_allocators_per_job: usize,
    pub security_level: SecurityLevel,
    pub ram_config: JitRunnerRam,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MemoryPreset {
    /// Select the largest preset that fits after reserving context memory and slack.
    #[default]
    Auto,
    GiB29,
    GiB21,
}

impl ExecutionProverConfiguration {
    pub(super) fn context_config(self) -> ProverContextConfig {
        let mut config = self.prover_context_config;
        let bytes: usize = match self.memory_preset {
            MemoryPreset::Auto => return config,
            MemoryPreset::GiB29 => 29 << 30,
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

    pub fn validate(self) -> Result<Self, UnsupportedGpuSecurityLevel> {
        if Self::supported_security_levels().contains(&self.security_level) {
            Ok(self)
        } else {
            Err(UnsupportedGpuSecurityLevel {
                requested: self.security_level,
            })
        }
    }
}

impl Default for ExecutionProverConfiguration {
    fn default() -> Self {
        Self {
            memory_preset: MemoryPreset::Auto,
            prover_context_config: ProverContextConfig::default(),
            max_thread_pool_threads: None,
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 8,
            host_allocator_backing_allocation_size: 1 << 26, // 64 MB
            host_allocators_per_job_count: 256,              // 16 GB
            host_allocators_per_device_count: 128,           // 8 GB
            min_free_host_allocators_per_job: 32,            // 2 GB
            security_level: SecurityLevel::Sec100,
            ram_config: JitRunnerRam::Medium, // 1Gb
        }
    }
}
