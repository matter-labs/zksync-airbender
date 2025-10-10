use super::gpu_worker::{GpuWorkResult, MemoryCommitmentResult, ProofResult};
use crate::circuit_type::CircuitType;
use crate::execution::snapshotter::SplitSnapshot;
use crate::prover::tracing_data::TracingDataHost;
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use fft::GoodAllocator;
use std::collections::HashSet;
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
    pub participating_snapshot_indexes: HashSet<usize>,
}

pub enum WorkerResult<A: GoodAllocator> {
    InitsAndTeardownsData(InitsAndTeardownsData<A>),
    TracingData(TracingData<A>),
    SimulationResult {
        cycles_count: usize,
        final_register_values: [FinalRegisterValue; 32],
    },
    SnapshotReplayed(usize),
    GpuWorkResult(GpuWorkResult<A>),
}
