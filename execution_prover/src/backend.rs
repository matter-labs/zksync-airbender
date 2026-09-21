//! The contract between the shared orchestrator and a proving backend.
//!
//! The seam is batch submission and completion; how a backend executes a
//! request in between is its own business.

use crate::config::{BackendConfiguration, ExecutionProverConfiguration};
use crate::error::ExecutionProverError;
use crate::messages::WorkBatch;
use crate::setup::CanonicalCircuitSetup;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel, BF};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::ops::DerefMut;
use std::sync::Arc;
use worker::Worker;

/// The narrow view of a backend's per-circuit prepared state that the shared
/// code needs; everything else a backend prepares stays private to it.
pub trait CircuitPrecomputation: Clone + Send + Sync + 'static {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>>;

    /// The committed setup cap, available only after setup initialization has
    /// completed. `None` means this circuit genuinely has no setup columns, not
    /// that a RISC-V family has yet to be initialized.
    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength>;
}

/// A proving backend.
///
/// Dropping the backend must close admission, drain accepted work and join its
/// workers before any setup or allocation owner it borrowed is dropped — which
/// is why the orchestrator declares its backend field first.
pub trait ExecutionBackend: Send + Sync + Sized + 'static {
    type Configuration: BackendConfiguration;
    type Allocator: HostTraceAllocator;
    type Memory: DerefMut<Target = MemoryHolder> + Send + 'static;
    type Snapshot: DerefMut<Target = TraceChunk> + Send + 'static;
    type Precomputations: CircuitPrecomputation;

    /// Validate backend settings and finish manager startup. Returns only once
    /// the backend is ready to accept work.
    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        worker: Arc<Worker>,
    ) -> Result<Self, ExecutionProverError>;

    /// One finite host trace block. `bytes` is the configured backing size.
    fn allocate_trace_block(&self, bytes: usize) -> Result<Self::Allocator, ExecutionProverError>;

    /// Guest RAM for one simulation.
    fn allocate_memory(&self, ram: JitRunnerRam) -> Result<Self::Memory, ExecutionProverError>;

    /// One JIT trace chunk.
    fn allocate_snapshot(&self) -> Result<Self::Snapshot, ExecutionProverError>;

    /// Trace blocks the backend needs beyond the per-job allowance, for
    /// resources the shared code does not model (the GPU's per-device
    /// allowance). Zero for a backend with no such resources.
    fn extra_trace_blocks(&self) -> usize;

    /// Turn canonical setup inputs into backend state. Implementations assert
    /// that the compiled circuit's geometry agrees with `circuit`.
    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
    ) -> Result<Self::Precomputations, ExecutionProverError>;

    /// Accept a batch.
    ///
    /// Submission is infallible: a request that cannot be executed is reported
    /// as [`crate::messages::WorkerResult::BackendFailure`] on the batch's
    /// result channel, and
    /// that event must be emitted BEFORE the backend stops serving the batch.
    /// Dropping the result sender does not wake producers blocked on a free
    /// buffer or a snapshot channel, so without the event the orchestrator can
    /// neither cancel nor join them.
    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>);
}

#[cfg(test)]
mod tests;
