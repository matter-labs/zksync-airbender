//! Shared simulation/replay, trace caching and commit/prove orchestration.

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

/// Handle to a binary registered with this prover instance.
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
    // Join backend workers before dropping the owners they may still borrow.
    backend: B,
    configuration: ExecutionProverConfiguration<B::Configuration>,
    worker: Arc<Worker>,
    memory_holders_cache: Arc<Mutex<Vec<B::Memory>>>,
    trace_chunks_cache: Arc<Mutex<Vec<Vec<B::Snapshot>>>>,
    admission: Option<Admission>,
    /// Trace blocks one execution's cache may hold: `N - reserve - 1`.
    cache_quota_blocks: usize,
    binary_holders: BTreeMap<usize, BinaryHolder<B>>,
    next_binary_id: usize,
    common_precomputations: BTreeMap<CircuitType, B::Precomputations>,
    free_allocators_sender: Sender<B::Allocator>,
    free_allocators_receiver: Receiver<B::Allocator>,
    // Failed batches can lose pooled blocks, so this instance cannot be reused.
    terminal_failure: Mutex<Option<String>>,
}
