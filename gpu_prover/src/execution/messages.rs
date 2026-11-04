use crate::circuit_type::CircuitType;
use crate::execution::precomputations::CircuitPrecomputations;
use crate::execution::A;
use crate::prover::tracing_data::TracingDataHost;
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use crossbeam_channel::{Receiver, Sender};
use cs::definitions::TimestampScalar;
use fft::GoodAllocator;
use prover::definitions::ExternalChallenges;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use std::collections::BTreeSet;
use trace_and_split::FinalRegisterValue;

pub struct InitsAndTeardownsData<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
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

pub enum WorkerResult<A: GoodAllocator> {
    SnapshotProduced,
    InitsAndTeardownsData(InitsAndTeardownsData<A>),
    TracingData(TracingData<A>),
    SimulationResult(SimulationResult),
    SnapshotReplayed(usize),
    GpuWorkResult(GpuWorkResult<A>),
}

pub struct MemoryCommitmentRequest<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: CircuitPrecomputations,
    pub inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
}

pub struct MemoryCommitmentResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub struct ProofRequest<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: CircuitPrecomputations,
    pub inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub external_challenges: ExternalChallenges,
}

pub struct ProofResult<A: GoodAllocator> {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
    pub proof: UnrolledModeProof,
}

/// Asks a GPU worker to build (or reuse) the setup Merkle trees of one circuit and
/// hand back their caps. No trace is involved: the trees are a pure function of the
/// circuit's setup trace, so the result is memoized in the shared
/// `CircuitPrecomputations` and the first proof of that circuit reuses it.
pub struct SetupCapsRequest {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub precomputations: CircuitPrecomputations,
}

pub struct SetupCapsResult {
    pub batch_id: u64,
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub merkle_tree_caps: Vec<MerkleTreeCapVarLength>,
}

pub enum GpuWorkRequest<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentRequest<A>),
    Proof(ProofRequest<A>),
    SetupCaps(SetupCapsRequest),
}

impl<A: GoodAllocator> GpuWorkRequest<A> {
    pub fn batch_id(&self) -> u64 {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.batch_id,
            GpuWorkRequest::Proof(request) => request.batch_id,
            GpuWorkRequest::SetupCaps(request) => request.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.circuit_type,
            GpuWorkRequest::Proof(request) => request.circuit_type,
            GpuWorkRequest::SetupCaps(request) => request.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.sequence_id,
            GpuWorkRequest::Proof(request) => request.sequence_id,
            GpuWorkRequest::SetupCaps(request) => request.sequence_id,
        }
    }

    pub fn precomputations(&self) -> &CircuitPrecomputations {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => &request.precomputations,
            GpuWorkRequest::Proof(request) => &request.precomputations,
            GpuWorkRequest::SetupCaps(request) => &request.precomputations,
        }
    }

    pub fn inits_and_teardowns(&self) -> Option<&ShuffleRamInitsAndTeardownsHost<A>> {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.inits_and_teardowns.as_ref(),
            GpuWorkRequest::Proof(request) => request.inits_and_teardowns.as_ref(),
            GpuWorkRequest::SetupCaps(_) => None,
        }
    }

    pub fn tracing_data(&self) -> Option<&TracingDataHost<A>> {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.tracing_data.as_ref(),
            GpuWorkRequest::Proof(request) => request.tracing_data.as_ref(),
            GpuWorkRequest::SetupCaps(_) => None,
        }
    }
}

pub enum GpuWorkResult<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentResult<A>),
    Proof(ProofResult<A>),
    SetupCaps(SetupCapsResult),
}

impl<A: GoodAllocator> GpuWorkResult<A> {
    pub fn circuit_type(&self) -> CircuitType {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.circuit_type,
            GpuWorkResult::Proof(result) => result.circuit_type,
            GpuWorkResult::SetupCaps(result) => result.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.sequence_id,
            GpuWorkResult::Proof(result) => result.sequence_id,
            GpuWorkResult::SetupCaps(result) => result.sequence_id,
        }
    }
}

pub struct GpuWorkBatch {
    pub batch_id: u64,
    pub receiver: Receiver<GpuWorkRequest<A>>,
    pub sender: Sender<WorkerResult<A>>,
}
