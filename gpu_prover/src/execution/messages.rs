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
    SnapshotProduced(usize),
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

pub enum GpuWorkRequest<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentRequest<A>),
    Proof(ProofRequest<A>),
}

impl<A: GoodAllocator> GpuWorkRequest<A> {
    pub fn batch_id(&self) -> u64 {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.batch_id,
            GpuWorkRequest::Proof(request) => request.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.circuit_type,
            GpuWorkRequest::Proof(request) => request.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => request.sequence_id,
            GpuWorkRequest::Proof(request) => request.sequence_id,
        }
    }

    pub fn precomputations(&self) -> &CircuitPrecomputations {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => &request.precomputations,
            GpuWorkRequest::Proof(request) => &request.precomputations,
        }
    }

    pub fn inits_and_teardowns(&self) -> &Option<ShuffleRamInitsAndTeardownsHost<A>> {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => &request.inits_and_teardowns,
            GpuWorkRequest::Proof(request) => &request.inits_and_teardowns,
        }
    }

    pub fn tracing_data(&self) -> &Option<TracingDataHost<A>> {
        match self {
            GpuWorkRequest::MemoryCommitment(request) => &request.tracing_data,
            GpuWorkRequest::Proof(request) => &request.tracing_data,
        }
    }
}

pub enum GpuWorkResult<A: GoodAllocator> {
    MemoryCommitment(MemoryCommitmentResult<A>),
    Proof(ProofResult<A>),
}

impl<A: GoodAllocator> GpuWorkResult<A> {
    pub fn batch_id(&self) -> u64 {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.batch_id,
            GpuWorkResult::Proof(result) => result.batch_id,
        }
    }

    pub fn circuit_type(&self) -> CircuitType {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.circuit_type,
            GpuWorkResult::Proof(result) => result.circuit_type,
        }
    }

    pub fn sequence_id(&self) -> usize {
        match self {
            GpuWorkResult::MemoryCommitment(result) => result.sequence_id,
            GpuWorkResult::Proof(result) => result.sequence_id,
        }
    }

    pub fn inits_and_teardowns(&self) -> &Option<ShuffleRamInitsAndTeardownsHost<A>> {
        match self {
            GpuWorkResult::MemoryCommitment(result) => &result.inits_and_teardowns,
            GpuWorkResult::Proof(result) => &result.inits_and_teardowns,
        }
    }

    pub fn tracing_data(&self) -> &Option<TracingDataHost<A>> {
        match self {
            GpuWorkResult::MemoryCommitment(result) => &result.tracing_data,
            GpuWorkResult::Proof(result) => &result.tracing_data,
        }
    }
}

pub struct GpuWorkBatch {
    pub batch_id: u64,
    pub receiver: Receiver<GpuWorkRequest<A>>,
    pub sender: Sender<WorkerResult<A>>,
}
