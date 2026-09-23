use crate::config::CpuBackendConfiguration;
use crate::manager::CpuManager;
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::SecurityLevel;
use execution_prover::backend::ExecutionBackend;
use execution_prover::config::ExecutionProverConfiguration;
use execution_prover::messages::WorkBatch;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::allocator::CpuTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::alloc::Global;
use std::sync::Arc;
use worker::Worker;

pub struct CpuBackend {
    manager: CpuManager,
}

impl ExecutionBackend for CpuBackend {
    type Configuration = CpuBackendConfiguration;
    type Allocator = CpuTraceAllocator;
    type Memory = Box<MemoryHolder>;
    type Snapshot = Box<TraceChunk>;
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
        MemoryHolder::allocate_zeroed(ram, Global)
    }

    fn allocate_snapshot(&self) -> Self::Snapshot {
        // SAFETY: `TraceChunk` is plain data; zeroing in place avoids moving
        // megabytes through the stack.
        unsafe { Box::<TraceChunk>::new_zeroed().assume_init() }
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
