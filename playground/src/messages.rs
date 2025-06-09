use crate::cpu_worker::{CyclesChunk, SetupAndTeardownChunk};
use crate::gpu_worker::MemoryCommitmentResult;
use fft::GoodAllocator;
use prover::tracers::delegation::DelegationWitness;
use std::collections::HashMap;
use trace_and_split::FinalRegisterValue;

pub enum WorkerResult<A: GoodAllocator> {
    SetupAndTeardownChunk(SetupAndTeardownChunk<A>),
    RAMTracingResult {
        chunks_traced_count: usize,
        final_register_values: [FinalRegisterValue; 32],
    },
    CyclesChunk(CyclesChunk<A>),
    CyclesTracingResult {
        chunks_traced_count: usize,
    },
    DelegationWitness(DelegationWitness<A>),
    DelegationTracingResult {
        delegation_chunks_counts: HashMap<u16, usize>,
    },
    MemoryCommitment(MemoryCommitmentResult<A>),
}
