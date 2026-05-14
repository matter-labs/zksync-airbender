use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use riscv_transpiler::vm::SimpleTape;
use type_map::concurrent::TypeMap;

use crate::execution::precomputations::CircuitPrecomputations;
use crate::primitives::circuit_type::UnrolledCircuitType;
use crate::primitives::context::ProverContextConfig;
use crate::primitives::machine_type::MachineType;
use crate::upstream::SecurityLevel;

/// Specifies the execution mode for the prover.
///
/// - `Unrolled`: per-family circuits (split memory / non-memory / I&T).
/// - `Unified`: the reduced-machine unified circuit. Public surface is wired
///   up; GPU dispatch points panic with `unimplemented!()` until unified is
///   implemented.
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
    pub prover_context_config: ProverContextConfig,
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_per_job_count: usize,
    pub host_allocators_per_device_count: usize,
    pub min_free_host_allocators_per_job: usize,
    pub security_level: SecurityLevel,
}

impl Default for ExecutionProverConfiguration {
    fn default() -> Self {
        Self {
            prover_context_config: Default::default(),
            max_thread_pool_threads: None,
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 8,
            host_allocator_backing_allocation_size: 1 << 26, // 64 MB
            host_allocators_per_job_count: 256,              // 16 GB
            host_allocators_per_device_count: 128,           // 8 GB
            min_free_host_allocators_per_job: 32,            // 2 GB
            security_level: SecurityLevel::Sec80,
        }
    }
}
