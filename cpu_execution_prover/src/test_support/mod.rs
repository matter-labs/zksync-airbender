use crate::config::{CpuBackendConfiguration, CpuExecutionProverConfiguration};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    CommitmentMode, Field, GKRExternalChallenges, GKRFullWitnessTrace, L1WrapSetup, Proth120,
    SecurityLevel, NUM_PERMUTATION_ARGUMENT_KEY_PARTS,
};
use crossbeam_channel::{unbounded, Sender};
use execution_prover::backend::ExecutionBackend;
use execution_prover::config::ExecutionProverConfiguration;
use execution_prover::messages::{
    L1WrapProofRequest, L1WrapProofResult, SetupInitializationResult, WorkBatch, WorkRequest,
    WorkResult, WorkerResult,
};
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover::{
    ExecutionKind, ExecutionProver, L1Proof, L1WrapResult, MachineType, ProofProfile,
};
use execution_prover_model::allocator::CpuTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, UnrolledUnifiedTraceHost};
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use riscv_transpiler::vm::FlatResponsesSource;
use std::alloc::Global;
use std::any::Any;
use std::marker::PhantomData;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use worker::Worker;

#[doc(hidden)]
pub use crate::jobs::expand_inits_and_teardowns;

const FIXTURE_BATCH_ID: u64 = 0;

type Callback = Box<dyn for<'a> FnOnce(L1WrapFixture<'a>) -> Box<dyn Any + Send> + Send>;
type CaptureOutcome = Result<Box<dyn Any + Send>, Box<dyn Any + Send>>;

pub struct L1WrapFixture<'a> {
    pub circuit_type: CircuitType,
    pub setup: &'a L1WrapSetup,
    pub tracing_data: &'a UnrolledUnifiedTraceHost<CpuTraceAllocator>,
    pub inits_and_teardowns: &'a InitsAndTeardownsTraceHost<CpuTraceAllocator>,
    pub commitment_mode: CommitmentMode,
    pub worker: &'a Worker,
}

impl L1WrapFixture<'_> {
    pub fn evaluate_witness(&self) -> GKRFullWitnessTrace<Proth120, Global, Global> {
        crate::jobs::evaluate_witness(
            self.circuit_type,
            self.setup,
            self.inits_and_teardowns,
            self.tracing_data,
            self.worker,
        )
    }
}

pub fn with_l1_wrap_fixture<R, F>(
    configuration: CpuExecutionProverConfiguration,
    binary: Vec<u32>,
    text: Vec<u32>,
    nd_words: Vec<u32>,
    cycles_bound: Option<u32>,
    callback: F,
) -> R
where
    F: for<'a> FnOnce(L1WrapFixture<'a>) -> R + Send + 'static,
    R: Send + 'static,
{
    with_l1_wrap_fixture_for(
        ExecutionKind::L1Wrap21,
        configuration,
        binary,
        text,
        nd_words,
        cycles_bound,
        callback,
    )
}

pub fn with_l1_wrap_fixture_for<R, F>(
    execution_kind: ExecutionKind,
    configuration: CpuExecutionProverConfiguration,
    binary: Vec<u32>,
    text: Vec<u32>,
    nd_words: Vec<u32>,
    cycles_bound: Option<u32>,
    callback: F,
) -> R
where
    F: for<'a> FnOnce(L1WrapFixture<'a>) -> R + Send + 'static,
    R: Send + 'static,
{
    let mut prover = ExecutionProver::<CaptureBackend>::with_configuration(configuration);
    let (sender, receiver) = unbounded();
    prover.backend().install(
        Box::new(move |fixture: L1WrapFixture<'_>| {
            Box::new(callback(fixture)) as Box<dyn Any + Send>
        }),
        sender,
    );
    let handle = prover.add_binary(
        execution_kind,
        MachineType::Reduced,
        binary,
        text,
        cycles_bound,
        &[ProofProfile::L1Wrap],
    );
    prover.prove_l1_wrap(
        FIXTURE_BATCH_ID,
        &handle,
        FlatResponsesSource::new_with_reads(nd_words),
    );
    drop(prover);
    let mut outcomes: Vec<CaptureOutcome> = receiver.into_iter().collect();
    assert_eq!(
        outcomes.len(),
        1,
        "capture backend must run the L1Wrap callback exactly once"
    );
    match outcomes.pop().unwrap() {
        Ok(value) => *value
            .downcast::<R>()
            .unwrap_or_else(|_| panic!("capture callback returned an unexpected type")),
        Err(payload) => resume_unwind(payload),
    }
}

#[derive(Default)]
struct CaptureState {
    callback: Option<Callback>,
    result: Option<Sender<CaptureOutcome>>,
}

struct CaptureBackend {
    worker: Arc<Worker>,
    state: Arc<Mutex<CaptureState>>,
    batches: Mutex<Vec<JoinHandle<()>>>,
}

impl CaptureBackend {
    fn install(&self, callback: Callback, result: Sender<CaptureOutcome>) {
        let mut state = self.state.lock().unwrap();
        assert!(
            state.callback.is_none() && state.result.is_none(),
            "capture backend already has an installed callback"
        );
        state.callback = Some(callback);
        state.result = Some(result);
    }
}

impl Drop for CaptureBackend {
    fn drop(&mut self) {
        let mut panicked = false;
        for thread in self.batches.get_mut().unwrap().drain(..) {
            panicked |= thread.join().is_err();
        }
        if !std::thread::panicking() {
            assert!(!panicked, "capture backend consumer thread panicked");
        }
    }
}

impl ExecutionBackend for CaptureBackend {
    type Configuration = CpuBackendConfiguration;
    type Allocator = CpuTraceAllocator;
    type Memory = Box<MemoryHolder>;
    type Snapshot = Box<TraceChunk>;
    type Precomputations = CpuCircuitPrecomputations;

    fn initialize(
        _config: &ExecutionProverConfiguration<Self::Configuration>,
        worker: Arc<Worker>,
    ) -> Self {
        Self {
            worker,
            state: Default::default(),
            batches: Mutex::new(Vec::new()),
        }
    }

    fn allocate_trace_block(&self, bytes: usize) -> Self::Allocator {
        CpuTraceAllocator::new(bytes)
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory {
        MemoryHolder::allocate_zeroed(ram, Global)
    }

    fn allocate_snapshot(&self) -> Self::Snapshot {
        unsafe { Box::<TraceChunk>::new_zeroed().assume_init() }
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        _security: SecurityLevel,
        profiles: &[ProofProfile],
    ) -> Self::Precomputations {
        CpuCircuitPrecomputations::from_canonical(circuit, setup, profiles)
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        let worker = Arc::clone(&self.worker);
        let state = Arc::clone(&self.state);
        let thread = std::thread::spawn(move || serve(batch, &worker, &state));
        self.batches.lock().unwrap().push(thread);
    }
}

fn serve(
    batch: WorkBatch<CpuTraceAllocator, CpuCircuitPrecomputations>,
    worker: &Worker,
    state: &Mutex<CaptureState>,
) {
    for request in batch.receiver {
        let result = match request {
            WorkRequest::SetupInitialization(request) => {
                WorkResult::SetupInitialization(SetupInitializationResult {
                    batch_id: request.batch_id,
                    circuit_type: request.circuit_type,
                    sequence_id: request.sequence_id,
                })
            }
            WorkRequest::L1WrapProof(request) => {
                WorkResult::L1WrapProof(capture(request, worker, state))
            }
            WorkRequest::MemoryCommitment(_) | WorkRequest::Proof(_) => {
                panic!("capture backend accepts only SetupInitialization and L1WrapProof")
            }
        };
        batch
            .sender
            .send(WorkerResult::BackendWorkResult(result))
            .expect("capture backend result channel closed before the batch retired");
    }
}

fn capture(
    request: L1WrapProofRequest<CpuTraceAllocator, CpuCircuitPrecomputations>,
    worker: &Worker,
    state: &Mutex<CaptureState>,
) -> L1WrapProofResult<CpuTraceAllocator> {
    let CaptureState { callback, result } = std::mem::take(&mut *state.lock().unwrap());
    let (Some(callback), Some(result)) = (callback, result) else {
        panic!("capture backend received an L1WrapProof without an installed callback")
    };
    let fixture = L1WrapFixture {
        circuit_type: request.circuit_type,
        setup: &request.precomputations.l1_wrap().setup,
        tracing_data: &request.tracing_data,
        inits_and_teardowns: &request.inits_and_teardowns,
        commitment_mode: request.commitment_mode,
        worker,
    };
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        worker.pool.install(|| callback(fixture))
    }));
    result
        .send(outcome)
        .expect("capture outcome receiver dropped before the L1Wrap callback finished");
    L1WrapProofResult {
        batch_id: request.batch_id,
        circuit_type: request.circuit_type,
        inits_and_teardowns: request.inits_and_teardowns,
        tracing_data: request.tracing_data,
        result: L1WrapResult {
            proof: dummy_proof(),
            commitment_mode: request.commitment_mode,
        },
    }
}

fn dummy_proof() -> L1Proof {
    L1Proof {
        external_challenges: GKRExternalChallenges {
            permutation_argument_linearization_challenges: [Proth120::ZERO;
                NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1],
            permutation_argument_additive_part: Proth120::ZERO,
            _marker: PhantomData,
        },
        final_explicit_evaluations: Default::default(),
        sumcheck_intermediate_values: Default::default(),
        whir_proof: Default::default(),
        grand_product_accumulator_computed: Default::default(),
        inits_and_teardowns_top_bits: Vec::new(),
        lookup_challenges_pow_nonce: 0,
        batched_proximity_check_pow_nonce: 0,
        intermediate_transcript_seed: None,
    }
}

#[cfg(test)]
mod tests;
