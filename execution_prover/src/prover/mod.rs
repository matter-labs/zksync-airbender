//! `ExecutionProver` orchestrator. Channel `send` / `recv` calls use `.unwrap()`
//! by convention: channel teardown indicates the worker pool was dropped before
//! results were collected — a programming bug worth panicking on. Other
//! fallible operations use `.expect("…")` with a specific message.

mod baby_bear;
mod binary;
mod cache;
mod config;
mod lifecycle;
mod non_determinism_wrapper;
mod proth120;
mod setup_init;
mod simulation;

pub use baby_bear::artifacts::{ProgramArtifacts, RiscvFamilyArtifact};
pub use baby_bear::result::{CommitMemoryResult, ProveResult};
pub use config::ExecutionKind;
pub use proth120::{L1Proof, L1WrapResult};

/// Opaque handle to a binary registered with the `ExecutionProver`. Returned by
/// [`ExecutionProver::add_binary_variants`]; required to identify the binary in
/// `commit_memory` / `commit_memory_and_prove`. Cannot be fabricated by
/// callers, which converts what was previously a runtime
/// "binary key not found" panic into a compile-time guarantee.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinaryHandle(usize);

use cache::{TraceCache, TraceCacheEntry};
use config::BinaryHolder;
use setup_init::{request_setup_initialization, PendingSetupInitialization};

use crate::backend::ExecutionBackend;
use crate::config::ExecutionProverConfiguration;
use crate::messages::{SimulationResult, WorkBatch, WorkRequest, WorkResult, WorkerResult};
use crate::tracing::{SplitTracingType, UnifiedTracingType};
use crate::workers::simulation::{run_replayer, run_simulator};
use crate::workers::spawn_abort_on_panic;
use crate::ProofProfile;
use crossbeam_channel::{unbounded, Receiver, Sender};
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use execution_prover_model::trace::InitsAndTeardownsTraceHost;
use execution_prover_model::trace::TracingDataHost;
use execution_prover_model::MachineType;
use itertools::Itertools;
use log::{info, trace};
use riscv_transpiler::vm::{NonDeterminismCSRSource, SimpleTape};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::Instant;
use type_map::concurrent::TypeMap;
use worker::Worker;

pub struct ExecutionProver<B: ExecutionBackend> {
    configuration: ExecutionProverConfiguration<B::Configuration>,
    host_pool_allocation: Option<JoinHandle<()>>,
    // Drain the backend before dropping pending setup result receivers.
    backend: Arc<B>,
    pending_setup_initializations: Vec<PendingSetupInitialization<B::Allocator>>,
    worker: Arc<Worker>,
    memory_holders_sender: Sender<B::Memory>,
    memory_holders_receiver: Receiver<B::Memory>,
    trace_chunk_sets_sender: Sender<Vec<B::Snapshot>>,
    trace_chunk_sets_receiver: Receiver<Vec<B::Snapshot>>,
    binary_holders: BTreeMap<usize, BinaryHolder<B>>,
    next_binary_id: usize,
    l1_whir_schedule: Option<::prover::gkr::prover_config::WhirSchedule>,
    /// The BabyBear delegation and inits-and-teardowns circuits every binary shares.
    common_precomputations: BTreeMap<CircuitType, B::Precomputations>,
    free_allocators_sender: Sender<B::Allocator>,
    free_allocators_receiver: Receiver<B::Allocator>,
}
