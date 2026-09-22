//! Batch submission and completion between the orchestrator and a proving backend.

use crate::config::{BackendConfiguration, ExecutionProverConfiguration};
use crate::messages::WorkBatch;
use crate::setup::CanonicalCircuitSetup;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel, BF};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::ops::DerefMut;
use std::sync::Arc;
use worker::Worker;

pub trait CircuitPrecomputation: Clone + Send + Sync + 'static {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>>;

    /// Available after setup initialization. `None` means no setup columns.
    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength>;
}

/// Drop must drain accepted work and join workers before borrowed setup or
/// allocation owners are dropped.
pub trait ExecutionBackend: Send + Sync + Sized + 'static {
    type Configuration: BackendConfiguration;
    type Allocator: HostTraceAllocator;
    type Memory: DerefMut<Target = MemoryHolder> + Send + 'static;
    type Snapshot: DerefMut<Target = TraceChunk> + Send + 'static;
    type Precomputations: CircuitPrecomputation;

    /// Returns once the backend is ready to accept work.
    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        worker: Arc<Worker>,
    ) -> Self;

    fn allocate_trace_block(&self, bytes: usize) -> Self::Allocator;

    fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory;

    fn allocate_snapshot(&self) -> Self::Snapshot;

    /// Blocks beyond the per-job allowance, such as GPU per-device reserves.
    fn extra_trace_blocks(&self) -> usize;

    /// Must assert that compiled circuit geometry agrees with `circuit`.
    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
    ) -> Self::Precomputations;

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>);
}
