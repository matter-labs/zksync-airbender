//! `ExecutionProver` orchestrator. Channel `send` / `recv` calls use `.unwrap()`
//! by convention: channel teardown indicates the worker pool was dropped before
//! results were collected — a programming bug worth panicking on. Other
//! fallible operations use `.expect("…")` with a specific message.

mod artifacts;
mod binary;
mod cache;
mod config;
mod lifecycle;
mod non_determinism_wrapper;
mod pipeline;
mod proof_artifacts;
mod result;
mod setup_init;

pub use artifacts::{ProgramArtifacts, RiscvFamilyArtifact};
pub use config::ExecutionKind;
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
use setup_init::request_setup_initialization;

use crate::backend::{CircuitPrecomputation, ExecutionBackend};
use crate::config::ExecutionProverConfiguration;
use crate::messages::{
    InitsAndTeardownsData, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest,
    ProofResult, SimulationResult, TracingData, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use crate::setup::{build_common_setups, build_unrolled_setup};
use crate::tracing::{SplitTracingType, UnifiedTracingType};
use crate::upstream::{BF, E4};
use crate::workers::simulation::{run_replayer, run_simulator};
use crate::workers::spawn_abort_on_panic;
use common_constants::TimestampScalar;
use crossbeam_channel::{unbounded, Receiver, Sender};
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::trace::InitsAndTeardownsTraceHost;
use execution_prover_model::trace::TracingDataHost;
use execution_prover_model::MachineType;
use itertools::Itertools;
use log::{debug, info, trace};

use crate::upstream::{
    Blake2sTranscript, FinalRegisterValue, GKRExternalChallenges, MerkleTreeCapVarLength,
};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::{
    FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use riscv_transpiler::vm::{NonDeterminismCSRSource, SimpleTape};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::Instant;
use type_map::concurrent::TypeMap;
use verifier_common::MEMORY_DELEGATION_POW_BITS;
use worker::Worker;

pub struct ExecutionProver<B: ExecutionBackend> {
    configuration: ExecutionProverConfiguration<B::Configuration>,
    // Field order is load-bearing: `backend` must be declared (and thus
    // dropped) before the precomputation maps so workers finish before the
    // setup hosts drop.
    backend: B,
    worker: Arc<Worker>,
    memory_holders_sender: Sender<B::Memory>,
    memory_holders_receiver: Receiver<B::Memory>,
    trace_chunk_sets_sender: Sender<Vec<B::Snapshot>>,
    trace_chunk_sets_receiver: Receiver<Vec<B::Snapshot>>,
    binary_holders: BTreeMap<usize, BinaryHolder<B>>,
    next_binary_id: usize,
    common_precomputations: BTreeMap<CircuitType, B::Precomputations>,
    free_allocators_sender: Sender<B::Allocator>,
    free_allocators_receiver: Receiver<B::Allocator>,
}
