use crate::config::CpuBackendConfiguration;
use crate::host_storage::{BoxedMemoryHolder, BoxedTraceChunk};
use crate::manager::CpuManager;
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::SecurityLevel;
use execution_prover::backend::ExecutionBackend;
use execution_prover::config::ExecutionProverConfiguration;
use execution_prover::messages::WorkBatch;
use execution_prover::CanonicalCircuitSetup;
use execution_prover_model::allocator::CpuTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::JitRunnerRam;
use std::sync::Arc;
use worker::Worker;

pub struct CpuBackend {
    manager: CpuManager,
}

impl ExecutionBackend for CpuBackend {
    type Configuration = CpuBackendConfiguration;
    type Allocator = CpuTraceAllocator;
    type Memory = BoxedMemoryHolder;
    type Snapshot = BoxedTraceChunk;
    type Precomputations = CpuCircuitPrecomputations;

    fn initialize(
        _config: &ExecutionProverConfiguration<Self::Configuration>,
        worker: Arc<Worker>,
    ) -> Self {
        Self {
            manager: CpuManager::new(worker),
        }
    }

    fn allocate_trace_block(&self, bytes: usize) -> Self::Allocator {
        CpuTraceAllocator::new(bytes)
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory {
        BoxedMemoryHolder::new(ram)
    }

    fn allocate_snapshot(&self) -> Self::Snapshot {
        BoxedTraceChunk::default()
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        _security: SecurityLevel,
    ) -> Self::Precomputations {
        CpuCircuitPrecomputations::from_canonical(circuit, setup)
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        self.manager.send_batch(batch);
    }
}

pub type CpuExecutionProver = execution_prover::ExecutionProver<CpuBackend>;
