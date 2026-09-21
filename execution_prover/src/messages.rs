//! The wire between the orchestrator, the simulation/replay workers and a
//! backend. Parameterised over the host trace allocator and the backend's
//! precomputation type; everything else describes the proving protocol.

use crate::upstream::{
    DefaultTreeConstructor, FinalRegisterValue, GKRExternalChallenges, GKRProof,
    MerkleTreeCapVarLength, SecurityLevel, BF, E4,
};
use common_constants::TimestampScalar;
use crossbeam_channel::{Receiver, Sender};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, TracingDataHost};
use std::collections::BTreeSet;

pub type ScheduledProof = GKRProof<BF, E4, DefaultTreeConstructor>;

pub struct InitsAndTeardownsData<A: HostTraceAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
}

pub struct TracingData<A: HostTraceAllocator> {
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

/// Why a simulation or replay thread stopped producing.
///
/// Without this event the collector waits forever: it closes its request
/// sender only once simulation reports done, and the backend retires a batch
/// only once that sender closes.
#[derive(Clone, Debug)]
pub struct ProducerFailure {
    pub batch_id: u64,
    pub reason: String,
}

/// Why a backend stopped serving a batch. Reported explicitly because
/// dropping a result sender does not wake a producer blocked on a free buffer
/// or a snapshot channel.
#[derive(Clone, Debug)]
pub struct BackendFailure {
    pub batch_id: u64,
    pub reason: String,
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

pub struct MemoryCommitmentRequest<A: HostTraceAllocator, P> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: P,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub security_level: SecurityLevel,
}

pub struct MemoryCommitmentResult<A: HostTraceAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    /// One cap per coset, in natural coset order.
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub struct ProofRequest<A: HostTraceAllocator, P> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: P,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub external_challenges: GKRExternalChallenges<BF, E4>,
    /// Per-coset caps from this circuit's prior memory commitment, in natural
    /// coset order.
    pub memory_caps: Vec<MerkleTreeCapVarLength>,
    pub security_level: SecurityLevel,
}

pub struct ProofResult<A: HostTraceAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub proof: ScheduledProof,
}

// Short-lived channel messages: one value is sent and dropped per event, so a
// boxed variant would buy a smaller footprint that never accumulates at the
// cost of a heap alloc on every send.
#[allow(clippy::large_enum_variant)]
pub enum WorkRequest<A: HostTraceAllocator, P> {
    MemoryCommitment(MemoryCommitmentRequest<A, P>),
    Proof(ProofRequest<A, P>),
    SetupInitialization(SetupInitializationRequest<P>),
}

impl<A: HostTraceAllocator, P> WorkRequest<A, P> {
    pub fn batch_id(&self) -> u64 {
        match self {
            Self::MemoryCommitment(request) => request.batch_id,
            Self::Proof(request) => request.batch_id,
            Self::SetupInitialization(request) => request.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            Self::MemoryCommitment(request) => request.circuit_type,
            Self::Proof(request) => request.circuit_type,
            Self::SetupInitialization(request) => request.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            Self::MemoryCommitment(request) => request.sequence_id,
            Self::Proof(request) => request.sequence_id,
            Self::SetupInitialization(request) => request.sequence_id,
        }
    }

    /// Request-kind label for logging.
    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::MemoryCommitment(_) => "memory commitment",
            Self::Proof(_) => "proof",
            Self::SetupInitialization(_) => "setup initialization",
        }
    }
}

#[allow(clippy::large_enum_variant)]
pub enum WorkResult<A: HostTraceAllocator> {
    MemoryCommitment(MemoryCommitmentResult<A>),
    Proof(ProofResult<A>),
    SetupInitialization(SetupInitializationResult),
}

impl<A: HostTraceAllocator> WorkResult<A> {
    pub fn batch_id(&self) -> u64 {
        match self {
            Self::MemoryCommitment(result) => result.batch_id,
            Self::Proof(result) => result.batch_id,
            Self::SetupInitialization(result) => result.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            Self::MemoryCommitment(result) => result.circuit_type,
            Self::Proof(result) => result.circuit_type,
            Self::SetupInitialization(result) => result.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            Self::MemoryCommitment(result) => result.sequence_id,
            Self::Proof(result) => result.sequence_id,
            Self::SetupInitialization(result) => result.sequence_id,
        }
    }
}

/// Everything the collector loop consumes: producer progress events plus
/// backend completions.
#[allow(clippy::large_enum_variant)]
pub enum WorkerResult<A: HostTraceAllocator> {
    InitsAndTeardownsData(InitsAndTeardownsData<A>),
    TracingData(TracingData<A>),
    SimulationResult(SimulationResult),
    SnapshotReplayed(usize),
    BackendWorkResult(WorkResult<A>),
    BackendFailure(BackendFailure),
    ProducerFailure(ProducerFailure),
}

/// One batch handed to a backend: where its requests arrive and where its
/// completions go.
pub struct WorkBatch<A: HostTraceAllocator, P> {
    pub batch_id: u64,
    pub receiver: Receiver<WorkRequest<A, P>>,
    pub sender: Sender<WorkerResult<A>>,
}
