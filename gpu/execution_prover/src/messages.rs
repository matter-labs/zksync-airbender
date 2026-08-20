use crate::precomputations::CircuitPrecomputations;
use crate::A;
use common_constants::TimestampScalar;
use crossbeam_channel::{Receiver, Sender};
use fft::GoodAllocator;
use gpu_core::primitives::field::{BF, E4};
use gpu_trace::trace::tracing_data::TracingDataHost;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::InitsAndTeardownsTraceHost;

use crate::upstream::{
    DefaultTreeConstructor, FinalRegisterValue, GKRExternalChallenges, GKRProof,
    MerkleTreeCapVarLength, SecurityLevel,
};
use std::collections::BTreeSet;

pub(crate) struct InitsAndTeardownsData {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
}

pub(crate) struct TracingData<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub tracing_data: TracingDataHost<A>,
    pub participating_snapshot_indexes: BTreeSet<usize>,
}

#[derive(Clone)]
pub(crate) struct SimulationResult {
    pub final_register_values: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
}

// Short-lived channel message: one value is sent and dropped per worker
// event, so boxing `GpuWorkResult` to shrink the enum would trade a
// heap-alloc/dealloc on every send for a smaller stack footprint that never
// accumulates. Not worth it on this hot path.
#[allow(clippy::large_enum_variant)]
pub(crate) enum WorkerResult<A: GoodAllocator> {
    SnapshotProduced,
    InitsAndTeardownsData(InitsAndTeardownsData),
    TracingData(TracingData<A>),
    SimulationResult(SimulationResult),
    SnapshotReplayed(usize),
    GpuWorkResult(GpuWorkResult<A>),
}

pub(crate) struct MemoryCommitmentRequest<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: CircuitPrecomputations,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub security_level: SecurityLevel,
}

pub(crate) struct MemoryCommitmentResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub(crate) struct SetupInitializationRequest {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: CircuitPrecomputations,
    pub security_level: SecurityLevel,
}

pub(crate) struct SetupInitializationResult {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
}

pub(crate) struct ProofRequest<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: CircuitPrecomputations,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub external_challenges: GKRExternalChallenges<BF, E4>,
    /// Per-coset caps from this circuit's prior `commit_memory` (one entry
    /// per coset, in natural order). `prove()` builds a
    /// `GpuGKRMemoryTransfer` from these caps.
    pub memory_caps: Vec<MerkleTreeCapVarLength>,
    pub security_level: SecurityLevel,
}

pub(crate) struct ProofResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub proof: GKRProof<BF, E4, DefaultTreeConstructor>,
}

pub(crate) enum GpuWorkRequest<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentRequest<A>),
    Proof(ProofRequest<A>),
    SetupInitialization(SetupInitializationRequest),
}

impl<A: GoodAllocator> GpuWorkRequest<A> {
    pub fn batch_id(&self) -> u64 {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.batch_id,
            GpuWorkRequest::Proof(request) => request.batch_id,
            GpuWorkRequest::SetupInitialization(request) => request.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.circuit_type,
            GpuWorkRequest::Proof(request) => request.circuit_type,
            GpuWorkRequest::SetupInitialization(request) => request.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.sequence_id,
            GpuWorkRequest::Proof(request) => request.sequence_id,
            GpuWorkRequest::SetupInitialization(request) => request.sequence_id,
        }
    }
}

// Same rationale as `WorkerResult` above: this is a short-lived channel
// message, not a long-lived collection, so boxing `ProofResult` to shrink the
// enum would add a heap alloc per GPU-work result for no steady-state benefit.
#[allow(clippy::large_enum_variant)]
pub(crate) enum GpuWorkResult<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentResult<A>),
    Proof(ProofResult<A>),
    SetupInitialization(SetupInitializationResult),
}

impl<A: GoodAllocator> GpuWorkResult<A> {
    pub fn circuit_type(&self) -> CircuitType {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.circuit_type,
            GpuWorkResult::Proof(result) => result.circuit_type,
            GpuWorkResult::SetupInitialization(result) => result.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.sequence_id,
            GpuWorkResult::Proof(result) => result.sequence_id,
            GpuWorkResult::SetupInitialization(result) => result.sequence_id,
        }
    }
}

pub(crate) struct GpuWorkBatch {
    pub batch_id: u64,
    pub receiver: Receiver<GpuWorkRequest<A>>,
    pub sender: Sender<WorkerResult<A>>,
}
