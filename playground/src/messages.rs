use fft::GoodAllocator;
use prover::ShuffleRamSetupAndTeardown;
use std::alloc::Global;

pub struct GpuMemoryCommitmentRequest {}

pub struct GpuMemoryCommitmentResponse {}

pub struct GpuProofRequest {}

pub struct GpuProofResponse {}

pub enum GpuTaskRequest {
    MemoryCommitment(GpuMemoryCommitmentRequest),
    Proof(GpuProofRequest),
}

pub enum GpuTaskResponse {
    MemoryCommitment(GpuMemoryCommitmentResponse),
    Proof(GpuProofResponse),
}

pub struct GenerateMainTrace<A: GoodAllocator = Global> {
    chunk_index: u32,
    inits_and_teardowns: Option<ShuffleRamSetupAndTeardown<A>>,
}

pub struct GenerateDelegationTraces {}

pub struct Yield;
