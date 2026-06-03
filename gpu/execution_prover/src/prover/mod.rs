//! `ExecutionProver` orchestrator. Channel `send` / `recv` calls use `.unwrap()`
//! by convention: channel teardown indicates the worker pool was dropped before
//! results were collected — a programming bug worth panicking on. Other
//! fallible operations use `.expect("…")` with a specific message.

mod binary;
mod cache;
mod config;
mod lifecycle;
mod non_determinism_wrapper;
mod pipeline;
mod proof_artifacts;
mod result;

pub use circuit_prover::UnsupportedGpuSecurityLevel;
pub use config::{ExecutionKind, ExecutionProverConfiguration};
pub use result::{CommitMemoryResult, ProveResult};

/// Opaque handle to a binary registered with the `ExecutionProver`. Returned by
/// [`ExecutionProver::add_binary`]; required to identify the binary in
/// `commit_memory` / `commit_memory_and_prove`. Cannot be fabricated by
/// callers, which converts what was previously a runtime
/// "binary key not found" panic into a compile-time guarantee.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinaryHandle(usize);

use cache::{TraceCache, TraceCacheEntry};
use config::BinaryHolder;
use non_determinism_wrapper::NonDeterminismWrapper;
use result::ExecutionProverResult;

use crate::messages::{
    GpuWorkBatch, GpuWorkRequest, GpuWorkResult, InitsAndTeardownsData, MemoryCommitmentRequest,
    MemoryCommitmentResult, ProofRequest, ProofResult, SimulationResult, TracingData, WorkerResult,
};
use crate::precomputations::{
    build_unrolled_circuit_precomputation, get_common_precomputations_for_all,
    CircuitPrecomputations,
};
use crate::tracing::{SplitTracingType, UnifiedTracingType};
use crate::workers::cpu::{run_replayer, run_simulator};
use crate::workers::gpu_manager::GpuManager;
use crate::workers::simulation_runner::{LockedBoxedMemoryHolder, LockedBoxedTraceChunk};
use crate::A;
use circuit_prover::prover::trace::tracing_data::TracingDataHost;
use circuit_prover::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use circuit_prover::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use common_constants::TimestampScalar;
use crossbeam_channel::{unbounded, Receiver, Sender};
use crossbeam_utils::sync::WaitGroup;
use era_cudart::device::get_device_count;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::machine_type::MachineType;
use itertools::Itertools;
use log::{debug, info, trace, warn};

use crate::upstream::{
    FinalRegisterValue, GKRExternalChallenges, MerkleTreeCapVarLength, Transcript,
};
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::{
    FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use riscv_transpiler::vm::{NonDeterminismCSRSource, SimpleTape};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::Instant;
use type_map::concurrent::TypeMap;
use verifier_common::MEMORY_DELEGATION_POW_BITS;
use worker::Worker;

pub struct ExecutionProver {
    configuration: ExecutionProverConfiguration,
    gpu_manager: GpuManager,
    worker: Arc<Worker>,
    memory_holders_cache: Arc<Mutex<Vec<LockedBoxedMemoryHolder>>>,
    trace_chunks_cache: Arc<Mutex<Vec<Vec<LockedBoxedTraceChunk>>>>,
    binary_holders: BTreeMap<usize, BinaryHolder>,
    next_binary_id: usize,
    common_precomputations: BTreeMap<CircuitType, CircuitPrecomputations>,
    free_allocators_sender: Sender<A>,
    free_allocators_receiver: Receiver<A>,
}

#[cfg(test)]
mod tests;
