use crate::upstream::{BF, E4};
use common_constants::TimestampScalar;
use crossbeam_channel::{Receiver, Sender};
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, TracingDataHost};
use fft::GoodAllocator;

use crate::upstream::{
    DefaultTreeConstructor, FinalRegisterValue, GKRExternalChallenges, GKRProof,
    MerkleTreeCapVarLength, SecurityLevel,
};
use std::collections::BTreeSet;

pub struct InitsAndTeardownsData<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
}

pub struct TracingData<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub tracing_data: TracingDataHost<A>,
    pub participating_snapshot_indexes: BTreeSet<usize>,
}

#[derive(Clone)]
pub struct SimulationResult {
    pub final_register_values: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
}

// Short-lived channel message: one value is sent and dropped per worker
// event, so boxing `WorkResult` to shrink the enum would trade a
// heap-alloc/dealloc on every send for a smaller stack footprint that never
// accumulates. Not worth it on this hot path.
#[allow(clippy::large_enum_variant)]
pub enum WorkerResult<A: GoodAllocator> {
    SnapshotProduced,
    InitsAndTeardownsData(InitsAndTeardownsData<A>),
    TracingData(TracingData<A>),
    SimulationResult(SimulationResult),
    SnapshotReplayed(usize),
    BackendWorkResult(WorkResult<A>),
}

pub struct MemoryCommitmentRequest<A: GoodAllocator, P> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: P,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub security_level: SecurityLevel,
}

pub struct MemoryCommitmentResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub struct SetupInitializationRequest<P> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: P,
    pub security_level: SecurityLevel,
}

pub struct SetupInitializationResult {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
}

pub struct ProofRequest<A: GoodAllocator, P> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: P,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub external_challenges: GKRExternalChallenges<BF, E4>,
    /// Per-coset caps from this circuit's prior `commit_memory` (one entry
    /// per coset, in natural order). The GPU backend builds a
    /// `GpuGKRMemoryTransfer` from these caps.
    pub memory_caps: Vec<MerkleTreeCapVarLength>,
    pub security_level: SecurityLevel,
}

pub struct ProofResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub proof: GKRProof<BF, E4, DefaultTreeConstructor>,
}

pub enum WorkRequest<A: GoodAllocator, P> {
    MemoryCommitment(MemoryCommitmentRequest<A, P>),
    Proof(ProofRequest<A, P>),
    SetupInitialization(SetupInitializationRequest<P>),
}

impl<A: GoodAllocator, P> WorkRequest<A, P> {
    pub fn batch_id(&self) -> u64 {
        match self {
            WorkRequest::MemoryCommitment(request) => request.batch_id,
            WorkRequest::Proof(request) => request.batch_id,
            WorkRequest::SetupInitialization(request) => request.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            WorkRequest::MemoryCommitment(request) => request.circuit_type,
            WorkRequest::Proof(request) => request.circuit_type,
            WorkRequest::SetupInitialization(request) => request.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            WorkRequest::MemoryCommitment(request) => request.sequence_id,
            WorkRequest::Proof(request) => request.sequence_id,
            WorkRequest::SetupInitialization(request) => request.sequence_id,
        }
    }
}

// Same rationale as `WorkerResult` above: this is a short-lived channel
// message, not a long-lived collection, so boxing `ProofResult` to shrink the
// enum would add a heap alloc per work result for no steady-state benefit.
#[allow(clippy::large_enum_variant)]
pub enum WorkResult<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentResult<A>),
    Proof(ProofResult<A>),
    SetupInitialization(SetupInitializationResult),
}

impl<A: GoodAllocator> WorkResult<A> {
    pub fn circuit_type(&self) -> CircuitType {
        match self {
            WorkResult::MemoryCommitment(result) => result.circuit_type,
            WorkResult::Proof(result) => result.circuit_type,
            WorkResult::SetupInitialization(result) => result.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            WorkResult::MemoryCommitment(result) => result.sequence_id,
            WorkResult::Proof(result) => result.sequence_id,
            WorkResult::SetupInitialization(result) => result.sequence_id,
        }
    }
}

pub struct WorkBatch<A: GoodAllocator, P> {
    pub batch_id: u64,
    pub receiver: Receiver<WorkRequest<A, P>>,
    pub sender: Sender<WorkerResult<A>>,
}
