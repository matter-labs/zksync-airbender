//! The `ExecutionProver` orchestrator: binary registration, the
//! simulation/replay pipeline, the trace cache, the two-pass commit/prove
//! protocol, result ordering and program artifacts. What a backend does with a
//! circuit request is behind [`crate::backend::ExecutionBackend`].

mod admission;
mod artifacts;
mod binary;
mod cache;
mod config;
mod lifecycle;
mod non_determinism_wrapper;
pub(crate) mod pipeline;
mod proof_artifacts;
mod result;
mod setup_init;

pub use artifacts::{ProgramArtifacts, RiscvFamilyArtifact};
pub use config::ExecutionKind;
pub use result::{CommitMemoryResult, ProveResult};

/// Opaque handle to a registered binary, returned by
/// [`ExecutionProver::add_binary`]. It cannot be fabricated, and it belongs to
/// the instance that issued it — it is not portable between instances.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinaryHandle(usize);

use admission::{Admission, AdmissionPermit};
use cache::{TraceCache, TraceCacheEntry};
use config::BinaryHolder;
use non_determinism_wrapper::NonDeterminismWrapper;
use result::ExecutionProverResult;
use setup_init::request_setup_initialization;

use crate::backend::{CircuitPrecomputation, ExecutionBackend};
use crate::config::ExecutionProverConfiguration;
use crate::error::ExecutionProverError;
use crate::messages::{
    InitsAndTeardownsData, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest,
    ProofResult, SimulationResult, TracingData, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use crate::setup::{build_common_setups, build_unified_setup, build_unrolled_setup};
use crate::tracing::{SplitTracingType, UnifiedTracingType};
use crate::upstream::{BF, E4};
use crate::workers::cancellation::{CancelOnPanic, Cancellation};
use crate::workers::simulation::{run_replayer, run_simulator};
use common_constants::TimestampScalar;
use crossbeam_channel::{unbounded, Receiver, Sender};
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, TracingDataHost};
use execution_prover_model::MachineType;
use itertools::Itertools;
use log::{debug, info, trace};

use crate::upstream::{
    Blake2sTranscript, FinalRegisterValue, GKRExternalChallenges, MerkleTreeCapVarLength,
    SecurityLevel,
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
    // Field order is load-bearing and must not be reordered: dropping the
    // backend closes admission, drains accepted work and joins its workers, so
    // it has to happen before the precomputations and buffer pool those workers
    // are still borrowing.
    backend: B,
    configuration: ExecutionProverConfiguration<B::Configuration>,
    worker: Arc<Worker>,
    memory_holders_cache: Arc<Mutex<Vec<B::Memory>>>,
    trace_chunks_cache: Arc<Mutex<Vec<Vec<B::Snapshot>>>>,
    /// At most `expected_concurrent_jobs` executions in flight, when the
    /// backend asks for a limit. `None` leaves the backend's own concurrency
    /// envelope in charge.
    admission: Option<Admission>,
    /// Trace blocks one execution's cache may hold: `N - R_effective - 1`.
    cache_quota_blocks: usize,
    binary_holders: BTreeMap<usize, BinaryHolder<B>>,
    next_binary_id: usize,
    common_precomputations: BTreeMap<CircuitType, B::Precomputations>,
    free_allocators_sender: Sender<B::Allocator>,
    free_allocators_receiver: Receiver<B::Allocator>,
    /// Set once a backend failure has terminated a batch.
    ///
    /// A backend that abandons consumed requests takes their input owners with
    /// it, so the pool cannot be made whole and the backend cannot serve
    /// another batch. The instance is marked terminal instead and every later
    /// call fails before allocating or spawning anything.
    terminal_failure: Mutex<Option<String>>,
    // Test seams. Each is asserted by a test that has no other way to observe
    // the behaviour it covers; see the accessors in `lifecycle.rs`.
    #[cfg(any(test, feature = "test_utils"))]
    peak_cached_blocks: std::sync::atomic::AtomicUsize,
    #[cfg(any(test, feature = "test_utils"))]
    simulations_started: std::sync::atomic::AtomicUsize,
    #[cfg(any(test, feature = "test_utils"))]
    cache_hits: std::sync::atomic::AtomicUsize,
    #[cfg(any(test, feature = "test_utils"))]
    released_work_requests: std::sync::atomic::AtomicUsize,
}
