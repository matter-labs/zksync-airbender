//! The CPU specialization of the shared execution backend contract.

use crate::config::CpuBackendConfiguration;
use crate::host_storage::{BoxedMemoryHolder, BoxedTraceChunk, CpuTraceAllocator};
use crate::jobs::CpuJobs;
use crate::manager::CpuManager;
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::SecurityLevel;
use execution_prover::backend::ExecutionBackend;
use execution_prover::config::{BackendConfiguration, ExecutionProverConfiguration};
use execution_prover::messages::WorkBatch;
use execution_prover::{CanonicalCircuitSetup, ExecutionProverError};
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::JitRunnerRam;
use std::sync::Arc;
use worker::Worker;

pub struct CpuBackend {
    /// Declared first so it drops first: the manager must drain and join before
    /// the pool its requests compute on goes away.
    manager: CpuManager<CpuTraceAllocator, CpuCircuitPrecomputations>,
    _proving_pool: Arc<Worker>,
}

impl ExecutionBackend for CpuBackend {
    type Configuration = CpuBackendConfiguration;
    type Allocator = CpuTraceAllocator;
    type Memory = BoxedMemoryHolder;
    type Snapshot = BoxedTraceChunk;
    type Precomputations = CpuCircuitPrecomputations;

    /// The shared auxiliary pool is deliberately unused: a request that
    /// occupied it would starve the setup, I&T and transcript work the
    /// orchestrator runs alongside the proof, so proving gets its own pool.
    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        _worker: Arc<Worker>,
    ) -> Result<Self, ExecutionProverError> {
        config.backend.validate()?;
        let proving_pool = Arc::new(Worker::new_with_num_threads(
            config.backend.resolved_proving_threads(),
        ));
        let manager =
            CpuManager::try_new(proving_pool.clone(), CpuJobs::default()).map_err(|error| {
                ExecutionProverError::backend_initialization(
                    CpuBackendConfiguration::BACKEND_NAME,
                    error,
                )
            })?;
        Ok(Self {
            manager,
            _proving_pool: proving_pool,
        })
    }

    fn allocate_trace_block(&self, bytes: usize) -> Result<Self::Allocator, ExecutionProverError> {
        Ok(CpuTraceAllocator::new(bytes))
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Result<Self::Memory, ExecutionProverError> {
        Ok(BoxedMemoryHolder::new(ram))
    }

    fn allocate_snapshot(&self) -> Result<Self::Snapshot, ExecutionProverError> {
        Ok(BoxedTraceChunk::default())
    }

    /// No per-device allowance to model: every CPU block is a per-job credit.
    fn extra_trace_blocks(&self) -> usize {
        0
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        _security: SecurityLevel,
    ) -> Result<Self::Precomputations, ExecutionProverError> {
        Ok(CpuCircuitPrecomputations::from_canonical(circuit, setup))
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        self.manager.send_batch(batch);
    }
}

pub type CpuExecutionProver = execution_prover::ExecutionProver<CpuBackend>;
