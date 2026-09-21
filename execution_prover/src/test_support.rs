//! Device-free backends for exercising the orchestrator contract.
//!
//! [`FakeBackend`] allocates from the global heap and merely REPORTS a block
//! capacity, so it cannot show pool exhaustion; [`finite_pool`] adds blocks
//! that own their bytes for the tests that need to. Neither proves.

use crate::backend::{CircuitPrecomputation, ExecutionBackend};
use crate::config::{BackendConfiguration, ExecutionProverConfiguration};
use crate::error::ExecutionProverError;
use crate::messages::{
    BackendFailure, InitsAndTeardownsData, MemoryCommitmentResult, SetupInitializationResult,
    TracingData, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use crate::setup::CanonicalCircuitSetup;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel, BF};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::sync::{Arc, Mutex};
use worker::Worker;

pub(crate) const FAKE_BLOCK_BYTES: usize = 1 << 20;

/// Heap-backed stand-in for a finite trace block: it forwards to the unbounded
/// global heap and only reports a capacity, so nothing it is used in can show
/// exhaustion, blocking or recycling. See [`finite_pool`] for those.
#[derive(Clone, Copy, Debug, Default)]
pub struct FakeTraceAllocator;

unsafe impl Allocator for FakeTraceAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        Global.deallocate(ptr, layout)
    }
}

impl fft::GoodAllocator for FakeTraceAllocator {}

impl HostTraceAllocator for FakeTraceAllocator {
    fn capacity(&self) -> usize {
        FAKE_BLOCK_BYTES
    }
}

pub struct FakeMemory(Box<MemoryHolder>);

impl Deref for FakeMemory {
    type Target = MemoryHolder;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for FakeMemory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct FakeSnapshot(Box<TraceChunk>);

impl Deref for FakeSnapshot {
    type Target = TraceChunk;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for FakeSnapshot {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Clone)]
pub struct FakePrecomputations {
    compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
}

impl CircuitPrecomputation for FakePrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.compiled_circuit
    }

    /// Neither backend commits a setup, so neither has a cap.
    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength> {
        None
    }
}

/// Join handles for the per-batch service threads, shared by both backends.
///
/// `submit` MUST be asynchronous: the orchestrator submits a batch before it
/// sends a single request, so a `submit` that drained its receiver inline
/// would block forever with nothing to drain. Dropping joins them, matching
/// the backend contract's drain-then-drop ordering.
#[derive(Default)]
struct BatchThreads(Mutex<Vec<std::thread::JoinHandle<()>>>);

impl BatchThreads {
    fn spawn(&self, name: String, body: impl FnOnce() + Send + 'static) {
        let handle = std::thread::Builder::new()
            .name(name)
            .spawn(body)
            .expect("failed to start a backend batch thread");
        self.0
            .lock()
            .expect("backend batch-handle mutex poisoned")
            .push(handle);
    }
}

impl Drop for BatchThreads {
    fn drop(&mut self) {
        let handles =
            std::mem::take(&mut *self.0.lock().expect("backend batch-handle mutex poisoned"));
        for handle in handles {
            let _ = handle.join();
        }
    }
}

fn fake_memory(ram: JitRunnerRam) -> Result<FakeMemory, ExecutionProverError> {
    Ok(FakeMemory(MemoryHolder::allocate_zeroed::<_>(
        ram,
        Default::default(),
    )))
}

fn zeroed_trace_chunk() -> Box<TraceChunk> {
    // SAFETY: the chunk is filled by the JIT before any read; `TraceChunk` is
    // plain data with no drop glue.
    unsafe { Box::<TraceChunk>::new_zeroed().assume_init() }
}

/// Both backends keep only the compiled circuit, and assert the geometry
/// agreement a real backend's `prepare` asserts.
fn fake_precomputations(
    circuit: CircuitType,
    setup: CanonicalCircuitSetup,
) -> Result<FakePrecomputations, ExecutionProverError> {
    assert_eq!(
        setup.compiled_circuit().trace_len,
        circuit.get_domain_size(),
        "compiled circuit trace_len disagrees with CircuitType geometry for {circuit:?}"
    );
    Ok(FakePrecomputations {
        compiled_circuit: Arc::new(setup.into_backend_inputs().compiled_circuit),
    })
}

/// Serve one request: setup initialisation and memory commitments complete,
/// and a proof request reports a failure because neither backend proves.
///
/// Reported rather than `unimplemented!()`: panicking in the batch thread
/// drops the sender and the collector meets a bare disconnect, which is a
/// different failure mode from the one under test. `None` ends the batch.
fn serve_request<A: HostTraceAllocator, P>(
    backend: &'static str,
    request: WorkRequest<A, P>,
    sender: &crossbeam_channel::Sender<WorkerResult<A>>,
) -> Option<WorkResult<A>> {
    match request {
        WorkRequest::SetupInitialization(request) => {
            Some(WorkResult::SetupInitialization(SetupInitializationResult {
                batch_id: request.batch_id,
                circuit_type: request.circuit_type,
                sequence_id: request.sequence_id,
            }))
        }
        WorkRequest::MemoryCommitment(request) => {
            let merkle_tree_caps =
                canonical_empty_caps(request.circuit_type, request.security_level);
            Some(WorkResult::MemoryCommitment(MemoryCommitmentResult {
                batch_id: request.batch_id,
                circuit_type: request.circuit_type,
                sequence_id: request.sequence_id,
                inits_and_teardowns: request.inits_and_teardowns,
                tracing_data: request.tracing_data,
                merkle_tree_caps,
            }))
        }
        WorkRequest::Proof(request) => {
            let _ = sender.send(WorkerResult::BackendFailure(BackendFailure {
                batch_id: request.batch_id,
                reason: format!("the {backend} backend serves no proof requests"),
            }));
            None
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FakeBackendConfiguration {
    /// When set, `initialize` fails with this message, so the
    /// initialization-error path can be exercised.
    pub fail_initialization_with: Option<&'static str>,
    /// When set, backend validation rejects with this message.
    pub reject_validation_with: Option<&'static str>,
    /// When set, the backend reports a failure instead of serving the Nth
    /// non-setup request, abandoning it and everything queued behind it.
    /// Setup initialization is always served, so construction completes.
    pub fail_after_requests: Option<usize>,
    /// Serve this many non-setup requests, then queue a late producer event,
    /// CLOSE the request channel, and only then report the failure — so the
    /// collector meets the closed channel while dispatching work rebuilt from
    /// the late event, before the failure that explains it.
    pub close_requests_before_failure_after: Option<usize>,
    /// Close the request receiver as soon as THIS submitted batch arrives,
    /// before reading anything, then report a failure.
    ///
    /// Zero-based, per backend INSTANCE, and the census includes setup
    /// batches: 0 is the constructor's, 1 is `add_binary`'s, 2 is a commit
    /// pass and 3 a prove pass. So `seed_from_cache`'s disconnect is `Some(3)`
    /// and `Some(1)` would fire during registration.
    pub close_requests_on_submit: Option<usize>,
}

impl BackendConfiguration for FakeBackendConfiguration {
    const BACKEND_NAME: &'static str = "fake";

    fn execution_defaults() -> ExecutionProverConfiguration<Self> {
        let mut configuration = ExecutionProverConfiguration {
            max_thread_pool_threads: Some(1),
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 1,
            host_allocator_backing_allocation_size: FAKE_BLOCK_BYTES,
            host_allocators_per_job_count: 0,
            min_free_host_allocators_per_job: 1,
            security_level: SecurityLevel::Sec100,
            ram_config: JitRunnerRam::Tiny,
            backend: Self {
                fail_initialization_with: None,
                reject_validation_with: None,
                fail_after_requests: None,
                close_requests_before_failure_after: None,
                close_requests_on_submit: None,
            },
        };
        // Derived, not guessed: the reserve depends on the block size and RAM
        // above. The blocks are zero-sized handles over `Global`, so a large
        // count costs nothing until rows are written.
        configuration.host_allocators_per_job_count = configuration
            .minimum_host_allocators_per_job()
            .expect("the fake backend's own geometry must admit a budget");
        configuration
    }

    fn validate(&self) -> Result<(), ExecutionProverError> {
        match self.reject_validation_with {
            Some(reason) => Err(ExecutionProverError::invalid_configuration(
                "backend", reason,
            )),
            None => Ok(()),
        }
    }

    fn admission_limit(&self, expected_concurrent_jobs: usize) -> Option<usize> {
        Some(expected_concurrent_jobs)
    }
}

pub struct FakeBackend {
    fail_after_requests: Option<usize>,
    close_requests_before_failure_after: Option<usize>,
    close_requests_on_submit: Option<usize>,
    /// Batches submitted to THIS backend, so the injection needs no
    /// process-global state and no suite serialization.
    submits: std::sync::atomic::AtomicUsize,
    batches: BatchThreads,
}

impl ExecutionBackend for FakeBackend {
    type Configuration = FakeBackendConfiguration;
    type Allocator = FakeTraceAllocator;
    type Memory = FakeMemory;
    type Snapshot = FakeSnapshot;
    type Precomputations = FakePrecomputations;

    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        _worker: Arc<Worker>,
    ) -> Result<Self, ExecutionProverError> {
        if let Some(reason) = config.backend.fail_initialization_with {
            return Err(ExecutionProverError::backend_initialization(
                Self::Configuration::BACKEND_NAME,
                reason,
            ));
        }
        Ok(Self {
            fail_after_requests: config.backend.fail_after_requests,
            close_requests_before_failure_after: config.backend.close_requests_before_failure_after,
            close_requests_on_submit: config.backend.close_requests_on_submit,
            submits: std::sync::atomic::AtomicUsize::new(0),
            batches: BatchThreads::default(),
        })
    }

    fn allocate_trace_block(&self, _bytes: usize) -> Result<Self::Allocator, ExecutionProverError> {
        Ok(FakeTraceAllocator)
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Result<Self::Memory, ExecutionProverError> {
        fake_memory(ram)
    }

    fn allocate_snapshot(&self) -> Result<Self::Snapshot, ExecutionProverError> {
        Ok(FakeSnapshot(zeroed_trace_chunk()))
    }

    fn extra_trace_blocks(&self) -> usize {
        0
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        _security: SecurityLevel,
    ) -> Result<Self::Precomputations, ExecutionProverError> {
        fake_precomputations(circuit, setup)
    }

    /// Services the batch on its own thread.
    ///
    /// With `fail_after_requests` set, the thread reports a failure once that
    /// many non-setup requests have been served and stops reading, abandoning
    /// the request it held and everything queued behind it — as a device
    /// worker that dies mid-batch does. Producers are still running, so their
    /// events keep arriving and exercise the post-failure release path.
    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        let WorkBatch {
            batch_id,
            receiver,
            sender,
        } = batch;
        let fail_after_requests = self.fail_after_requests;
        let close_requests_before_failure_after = self.close_requests_before_failure_after;
        // Per-backend ordinal; see `close_requests_on_submit` for the census.
        let submit_index = self
            .submits
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if self.close_requests_on_submit == Some(submit_index) {
            // SYNCHRONOUS on purpose: dropping the receiver inside the spawned
            // thread would let the caller's seeding succeed before the close
            // landed. Closing here guarantees the very next send fails.
            drop(receiver);
            let _ = sender.send(WorkerResult::BackendFailure(BackendFailure {
                batch_id,
                reason: "fake backend refused batch at submit".to_string(),
            }));
            return;
        }
        self.batches
            .spawn(format!("fake-backend-{batch_id}"), move || {
                let mut served = 0usize;
                // Held in an `Option` so an injection can close it mid-batch; a
                // plain `for request in receiver` would own it to the end.
                let mut receiver = Some(receiver);
                while let Some(request) = receiver.as_ref().and_then(|r| r.recv().ok()) {
                    assert_eq!(request.batch_id(), batch_id);
                    if !matches!(request, WorkRequest::SetupInitialization(_)) {
                        if fail_after_requests == Some(served) {
                            inject_failure_then_late_event(batch_id, request, &sender);
                            return;
                        }
                        if close_requests_before_failure_after == Some(served) {
                            close_requests_then_inject_late_event_and_fail(
                                batch_id,
                                request,
                                &sender,
                                &mut receiver,
                            );
                            return;
                        }
                        served += 1;
                    }
                    let Some(result) = serve_request("fake", request, &sender) else {
                        return;
                    };
                    // Gated so a test can hold completions back and make the
                    // finite block pool bite; a no-op unless armed.
                    result_gate::wait_for_permit();
                    if sender
                        .send(WorkerResult::BackendWorkResult(result))
                        .is_err()
                    {
                        return;
                    }
                }
            });
    }
}

/// Report the failure, then hand the collector a late producer event built
/// from the request being abandoned, which makes the post-failure release
/// branch reachable deterministically. Both messages go on the SAME sender,
/// so FIFO guarantees the failure is observed first.
fn inject_failure_then_late_event<A: HostTraceAllocator, P>(
    batch_id: u64,
    request: WorkRequest<A, P>,
    sender: &crossbeam_channel::Sender<WorkerResult<A>>,
) {
    let late = late_event_from(request);
    // Gated like a completion, so a test can hold a FAILING execution in
    // flight too — otherwise it releases its slot before a waiter can be
    // observed blocking behind it.
    result_gate::wait_for_permit();
    sender
        .send(WorkerResult::BackendFailure(BackendFailure {
            batch_id,
            reason: "fake backend failed".to_string(),
        }))
        .expect("collector must still be listening");
    sender
        .send(late)
        .expect("collector must still be draining after a failure");
}

/// Close the request channel FIRST, then queue a late producer event, then
/// report the failure: the collector rebuilds work from the event and
/// dispatches into a channel whose receiver is already gone, all before the
/// failure explaining it arrives.
///
/// The close must come first. FIFO on `sender` orders the event against the
/// failure but says nothing about the receiver's lifetime, so sending the
/// event first would let the dispatch succeed and the `SendError` never
/// happen.
fn close_requests_then_inject_late_event_and_fail<A: HostTraceAllocator, P>(
    batch_id: u64,
    request: WorkRequest<A, P>,
    sender: &crossbeam_channel::Sender<WorkerResult<A>>,
    receiver: &mut Option<crossbeam_channel::Receiver<WorkRequest<A, P>>>,
) {
    let late = late_event_from(request);
    // Gone before the collector can learn there is anything to dispatch.
    *receiver = None;
    sender
        .send(late)
        .expect("collector must still be draining before the failure");
    sender
        .send(WorkerResult::BackendFailure(BackendFailure {
            batch_id,
            reason: "fake backend failed".to_string(),
        }))
        .expect("collector must still be listening");
}

/// Build a producer event from a request's own trace owners; nothing is
/// fabricated or cloned. An empty `participating_snapshot_indexes` is
/// correct — the request reached the backend, so its data is ready.
fn late_event_from<A: HostTraceAllocator, P>(request: WorkRequest<A, P>) -> WorkerResult<A> {
    let (circuit_type, sequence_id, inits_and_teardowns, tracing_data) = match request {
        WorkRequest::MemoryCommitment(request) => (
            request.circuit_type,
            request.sequence_id,
            request.inits_and_teardowns,
            request.tracing_data,
        ),
        WorkRequest::Proof(request) => (
            request.circuit_type,
            request.sequence_id,
            request.inits_and_teardowns,
            request.tracing_data,
        ),
        WorkRequest::SetupInitialization(_) => {
            unreachable!("setup requests are served before any failure")
        }
    };
    let is_inits_and_teardowns = matches!(
        circuit_type,
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
    );
    match tracing_data {
        Some(tracing_data) if !is_inits_and_teardowns => WorkerResult::TracingData(TracingData {
            circuit_type,
            sequence_id,
            tracing_data,
            participating_snapshot_indexes: std::collections::BTreeSet::new(),
        }),
        _ => WorkerResult::InitsAndTeardownsData(InitsAndTeardownsData {
            circuit_type,
            sequence_id,
            inits_and_teardowns,
        }),
    }
}

/// Holds every backend completion until a test opens the gate.
///
/// Process-global, matching the spawn-injection seam: `BackendConfiguration`
/// is `Copy`, so a shared handle cannot live in the configuration.
///
/// With completions withheld no trace block ever returns, so a producer must
/// eventually block on the pool — the condition a liveness test has to observe
/// before it can claim that a completion is what resumes production.
pub mod result_gate {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Condvar, Mutex};

    /// Guarded rather than atomic so `open` cannot land between a waiter's
    /// check and its park, which would lose the notification.
    static ARMED: Mutex<bool> = Mutex::new(false);
    static OPENED: Condvar = Condvar::new();
    static SERVED: AtomicUsize = AtomicUsize::new(0);

    /// Withhold every completion until `open` is called.
    pub fn arm() {
        *ARMED.lock().expect("result gate mutex poisoned") = true;
        SERVED.store(0, Ordering::SeqCst);
    }

    /// Let everything through and stop gating.
    pub fn open() {
        *ARMED.lock().expect("result gate mutex poisoned") = false;
        OPENED.notify_all();
    }

    pub fn clear() {
        open();
        SERVED.store(0, Ordering::SeqCst);
    }

    /// Completions actually delivered so far.
    pub fn served() -> usize {
        SERVED.load(Ordering::SeqCst)
    }

    /// Called by a backend before each completion.
    pub(super) fn wait_for_permit() {
        let mut armed = ARMED.lock().expect("result gate mutex poisoned");
        while *armed {
            armed = OPENED.wait(armed).expect("result gate mutex poisoned");
        }
        drop(armed);
        SERVED.fetch_add(1, Ordering::SeqCst);
    }
}

/// Caps of the shape the protocol expects: one per coset, each
/// `cap_size / lde_factor` digests, all zero. `Vec::new()` would pass the
/// collector and then be rejected at cap conversion or transcript assembly.
fn canonical_empty_caps(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> Vec<crate::upstream::MerkleTreeCapVarLength> {
    let config = crate::config::prover_config(circuit_type, security_level);
    let digests_per_coset = config.cap_size / config.lde_factor;
    (0..config.lde_factor)
        .map(|_| crate::upstream::MerkleTreeCapVarLength {
            cap: vec![[0u32; 8]; digests_per_coset],
        })
        .collect()
}

/// Partial-startup failure injection, process-global.
pub use crate::prover::pipeline::spawn_injection::{
    clear as clear_spawn_injection, fail_replay_spawn_after,
};

/// Cumulative waits on each finite pool, for liveness tests that must observe
/// a producer genuinely blocked rather than merely slow.
pub use crate::workers::cancellation::waits;

/// A backend whose trace blocks own their bytes.
///
/// A block is one fixed region: it refuses a request larger than that region,
/// refuses a second concurrent request, and frees the region when the pool
/// drops. Handing the same block out twice or overrunning one is an observable
/// counter rather than silent corruption, which [`FakeTraceAllocator`] cannot
/// offer because it forwards to `Global`.
pub mod finite_pool {
    use super::{
        fake_memory, fake_precomputations, result_gate, serve_request, zeroed_trace_chunk,
        BatchThreads, FakeMemory, FakePrecomputations,
    };
    use crate::backend::ExecutionBackend;
    use crate::config::{BackendConfiguration, ExecutionProverConfiguration};
    use crate::error::ExecutionProverError;
    use crate::messages::{WorkBatch, WorkRequest, WorkerResult};
    use crate::setup::CanonicalCircuitSetup;
    use crate::upstream::SecurityLevel;
    use execution_prover_model::allocator::HostTraceAllocator;
    use execution_prover_model::circuit_type::CircuitType;
    use riscv_transpiler::jit::{JitRunnerRam, TraceChunk};
    use std::alloc::{alloc_zeroed, dealloc, AllocError, Allocator, Layout};
    use std::ptr::NonNull;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use worker::Worker;

    /// Exactly `MIN_ALIGN` on this target, and deliberately not more: Rust's
    /// `alloc_zeroed` reaches `calloc` only while the alignment fits in
    /// `MIN_ALIGN` and otherwise falls back to `alloc` plus a `memset`, which
    /// would write a pool of 64 MiB blocks front to back at construction
    /// instead of leaving it on untouched zero pages. Every trace row type
    /// aligns to at most 8; `allocate` rejects anything stricter.
    const BLOCK_ALIGNMENT: usize = 16;

    /// Smallest legal block: the largest aligned unit in
    /// `host_trace_row_layouts()` is one 1024-item page of 8-byte i&t
    /// timestamps, and `chunk_into_blocks` asserts a block holds one.
    const MINIMUM_REAL_BLOCK_BYTES: usize = 8192;

    /// Process-global counters, for the same reason [`result_gate`] is:
    /// `BackendConfiguration` is `Copy`, so a shared handle cannot travel in
    /// the configuration. Tests that read these serialize with each other.
    pub mod stats {
        use std::sync::atomic::{AtomicUsize, Ordering};

        pub(super) static LIVE: AtomicUsize = AtomicUsize::new(0);
        pub(super) static PEAK_LIVE: AtomicUsize = AtomicUsize::new(0);
        pub(super) static DOUBLE_USE: AtomicUsize = AtomicUsize::new(0);
        pub(super) static OVER_CAPACITY: AtomicUsize = AtomicUsize::new(0);
        pub(super) static REQUESTS_RECEIVED: AtomicUsize = AtomicUsize::new(0);

        /// Block regions handed out and not yet released.
        pub fn live_blocks() -> usize {
            LIVE.load(Ordering::SeqCst)
        }

        /// High-water mark of [`live_blocks`].
        pub fn peak_live_blocks() -> usize {
            PEAK_LIVE.load(Ordering::SeqCst)
        }

        /// Times a block was asked for a second region while one was out,
        /// i.e. two owners held the same block at once.
        pub fn double_use_errors() -> usize {
            DOUBLE_USE.load(Ordering::SeqCst)
        }

        /// Times a request exceeded a block's real capacity.
        pub fn over_capacity_errors() -> usize {
            OVER_CAPACITY.load(Ordering::SeqCst)
        }

        /// Requests the backend has taken off the channel, counted BEFORE it
        /// waits on the result gate: what tells a test that the producers
        /// published something before they blocked.
        pub fn requests_received() -> usize {
            REQUESTS_RECEIVED.load(Ordering::SeqCst)
        }

        /// Reset the cumulative counters. `LIVE` is a live census rather than
        /// a counter, so zeroing it would hide a leak.
        pub fn reset() {
            PEAK_LIVE.store(LIVE.load(Ordering::SeqCst), Ordering::SeqCst);
            DOUBLE_USE.store(0, Ordering::SeqCst);
            OVER_CAPACITY.store(0, Ordering::SeqCst);
            REQUESTS_RECEIVED.store(0, Ordering::SeqCst);
        }
    }

    /// One block's owned region.
    #[derive(Debug)]
    struct Block {
        region: NonNull<u8>,
        capacity: usize,
        /// Whether the region is currently handed out. A block serves exactly
        /// one live allocation: producers create one `Vec` per block and never
        /// grow it.
        handed_out: AtomicBool,
    }

    // SAFETY: the region is owned exclusively by this `Block` for its whole
    // life, and every access to it goes through `handed_out`.
    unsafe impl Send for Block {}
    unsafe impl Sync for Block {}

    impl Drop for Block {
        fn drop(&mut self) {
            // SAFETY: allocated in `FiniteTraceAllocator::with_capacity` with
            // exactly this layout and never reallocated.
            unsafe {
                dealloc(
                    self.region.as_ptr(),
                    Layout::from_size_align(self.capacity, BLOCK_ALIGNMENT).unwrap(),
                );
            }
        }
    }

    /// A trace block backed by real memory it owns.
    ///
    /// `Clone` shares the block, which is what recycling needs:
    /// `ChunkedTraceHolder::into_allocators` clones the allocator out of a
    /// `Vec` that is then dropped, and the clone goes back into the pool.
    #[derive(Clone, Debug, Default)]
    pub struct FiniteTraceAllocator {
        /// `None` only for the `Default` that `GoodAllocator` requires, and
        /// never a usable block: it reports zero capacity, so a producer that
        /// reached one trips `process_snapshot`'s `assert_ne!(diff, 0)`.
        block: Option<Arc<Block>>,
    }

    impl FiniteTraceAllocator {
        pub fn with_capacity(capacity: usize) -> Self {
            assert!(
                capacity >= MINIMUM_REAL_BLOCK_BYTES,
                "a {capacity}-byte block cannot hold one aligned i&t page"
            );
            let layout = Layout::from_size_align(capacity, BLOCK_ALIGNMENT)
                .expect("a finite block layout must be legal");
            // SAFETY: non-zero size, legal layout.
            let region = unsafe { alloc_zeroed(layout) };
            let region = NonNull::new(region).expect("finite block backing allocation failed");
            Self {
                block: Some(Arc::new(Block {
                    region,
                    capacity,
                    handed_out: AtomicBool::new(false),
                })),
            }
        }
    }

    unsafe impl Allocator for FiniteTraceAllocator {
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            let Some(block) = self.block.as_ref() else {
                return Err(AllocError);
            };
            if layout.size() > block.capacity || layout.align() > BLOCK_ALIGNMENT {
                stats::OVER_CAPACITY.fetch_add(1, Ordering::SeqCst);
                return Err(AllocError);
            }
            if block.handed_out.swap(true, Ordering::SeqCst) {
                stats::DOUBLE_USE.fetch_add(1, Ordering::SeqCst);
                return Err(AllocError);
            }
            let live = stats::LIVE.fetch_add(1, Ordering::SeqCst) + 1;
            stats::PEAK_LIVE.fetch_max(live, Ordering::SeqCst);
            Ok(NonNull::slice_from_raw_parts(block.region, block.capacity))
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
            let block = self
                .block
                .as_ref()
                .expect("a default FiniteTraceAllocator never hands out a region");
            assert_eq!(
                ptr, block.region,
                "a finite block was asked to free a region it does not own"
            );
            block.handed_out.store(false, Ordering::SeqCst);
            stats::LIVE.fetch_sub(1, Ordering::SeqCst);
        }
    }

    impl fft::GoodAllocator for FiniteTraceAllocator {}

    impl HostTraceAllocator for FiniteTraceAllocator {
        fn capacity(&self) -> usize {
            self.block.as_ref().map_or(0, |block| block.capacity)
        }
    }

    /// A snapshot chunk that a test can hold inside the replayer.
    ///
    /// The snapshot pool is replenished by the replayers rather than by
    /// backend completions, so [`result_gate`] cannot reach it; parking a
    /// replayer while it holds a chunk is what makes its exhaustion
    /// deliberate. The hook is in `Deref`/`DerefMut` because that is the first
    /// thing `run_replayer` does with a chunk, and it fires only on a replay
    /// thread — parking the simulator would stop the pool being drawn down.
    pub struct FiniteSnapshot(Box<TraceChunk>);

    impl std::ops::Deref for FiniteSnapshot {
        type Target = TraceChunk;
        fn deref(&self) -> &Self::Target {
            replay_gate::park_if_replaying();
            &self.0
        }
    }

    impl std::ops::DerefMut for FiniteSnapshot {
        fn deref_mut(&mut self) -> &mut Self::Target {
            replay_gate::park_if_replaying();
            &mut self.0
        }
    }

    /// Holds replay threads inside the chunk they are working on.
    ///
    /// Process-global, like [`result_gate`], and for the same reason.
    pub mod replay_gate {
        use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
        use std::sync::{Condvar, Mutex};

        /// Thread-name prefix `spawn_simulation_workers` gives its replay
        /// threads; matching on it keeps the simulator running.
        const REPLAY_THREAD_PREFIX: &str = "ab-replay-";

        static ARMED: AtomicBool = AtomicBool::new(false);
        static PARKED: AtomicUsize = AtomicUsize::new(0);
        static RELEASED: Mutex<bool> = Mutex::new(false);
        static WOKEN: Condvar = Condvar::new();

        /// Park every replay thread that touches its chunk from now on.
        pub fn arm() {
            *RELEASED.lock().expect("replay gate mutex poisoned") = false;
            PARKED.store(0, Ordering::SeqCst);
            ARMED.store(true, Ordering::SeqCst);
        }

        /// Let the held replayers go and stop parking new ones.
        pub fn release() {
            ARMED.store(false, Ordering::SeqCst);
            *RELEASED.lock().expect("replay gate mutex poisoned") = true;
            WOKEN.notify_all();
        }

        pub fn clear() {
            release();
            PARKED.store(0, Ordering::SeqCst);
        }

        /// Cumulative entries into the park: what tells a test a replayer is
        /// genuinely holding a chunk rather than merely scheduled.
        pub fn parked() -> usize {
            PARKED.load(Ordering::SeqCst)
        }

        pub(super) fn park_if_replaying() {
            if !ARMED.load(Ordering::SeqCst) {
                return;
            }
            let on_replay_thread = std::thread::current()
                .name()
                .is_some_and(|name| name.starts_with(REPLAY_THREAD_PREFIX));
            if !on_replay_thread {
                return;
            }
            PARKED.fetch_add(1, Ordering::SeqCst);
            let mut released = RELEASED.lock().expect("replay gate mutex poisoned");
            while !*released {
                released = WOKEN.wait(released).expect("replay gate mutex poisoned");
            }
        }
    }

    /// Declared block size the producer budget is computed from, deliberately
    /// much larger than the real capacity below.
    const DECLARED_BLOCK_BYTES: usize = 1 << 30;

    #[derive(Clone, Copy, Debug)]
    pub struct FiniteBackendConfiguration {
        /// Bytes each block really owns, which a test may set BELOW the
        /// declared size.
        ///
        /// A pool of `N = R + 1` blocks at the declared size is large enough
        /// for any workload by construction — that is what the budget proves —
        /// so exhausting it honestly needs ~7.6 GiB of trace held at once.
        /// Under-funding a block is the only way to bring exhaustion into
        /// reach, and it demonstrates the MECHANISM only: the sufficiency of
        /// the production budget is arithmetic, proven in `tracing/budget.rs`.
        pub real_block_capacity_bytes: usize,
    }

    impl BackendConfiguration for FiniteBackendConfiguration {
        const BACKEND_NAME: &'static str = "finite";

        fn execution_defaults() -> ExecutionProverConfiguration<Self> {
            let mut configuration = ExecutionProverConfiguration {
                max_thread_pool_threads: Some(1),
                expected_concurrent_jobs: 1,
                replay_worker_threads_count: 1,
                host_allocator_backing_allocation_size: DECLARED_BLOCK_BYTES,
                host_allocators_per_job_count: 0,
                min_free_host_allocators_per_job: 1,
                security_level: SecurityLevel::Sec100,
                // The `hashed_fibonacci` fixture's guest stack top is around
                // 68 MiB; see `failure_drain.rs`.
                ram_config: JitRunnerRam::Medium,
                backend: Self {
                    real_block_capacity_bytes: MINIMUM_REAL_BLOCK_BYTES,
                },
            };
            configuration.host_allocators_per_job_count = configuration
                .minimum_host_allocators_per_job()
                .expect("the finite backend's own geometry must admit a budget");
            configuration
        }

        fn validate(&self) -> Result<(), ExecutionProverError> {
            if self.real_block_capacity_bytes < MINIMUM_REAL_BLOCK_BYTES {
                return Err(ExecutionProverError::invalid_configuration(
                    "backend",
                    format!(
                        "a {}-byte block cannot hold one aligned i&t page",
                        self.real_block_capacity_bytes
                    ),
                ));
            }
            Ok(())
        }

        fn admission_limit(&self, expected_concurrent_jobs: usize) -> Option<usize> {
            Some(expected_concurrent_jobs)
        }
    }

    pub struct FiniteBackend {
        real_block_capacity_bytes: usize,
        batches: BatchThreads,
    }

    impl ExecutionBackend for FiniteBackend {
        type Configuration = FiniteBackendConfiguration;
        type Allocator = FiniteTraceAllocator;
        type Memory = FakeMemory;
        type Snapshot = FiniteSnapshot;
        type Precomputations = FakePrecomputations;

        fn initialize(
            config: &ExecutionProverConfiguration<Self::Configuration>,
            _worker: Arc<Worker>,
        ) -> Result<Self, ExecutionProverError> {
            Ok(Self {
                real_block_capacity_bytes: config.backend.real_block_capacity_bytes,
                batches: BatchThreads::default(),
            })
        }

        /// `bytes` is the DECLARED size the budget was computed from; the
        /// block really owns `real_block_capacity_bytes`.
        fn allocate_trace_block(
            &self,
            _bytes: usize,
        ) -> Result<Self::Allocator, ExecutionProverError> {
            Ok(FiniteTraceAllocator::with_capacity(
                self.real_block_capacity_bytes,
            ))
        }

        fn allocate_memory(&self, ram: JitRunnerRam) -> Result<Self::Memory, ExecutionProverError> {
            fake_memory(ram)
        }

        fn allocate_snapshot(&self) -> Result<Self::Snapshot, ExecutionProverError> {
            Ok(FiniteSnapshot(zeroed_trace_chunk()))
        }

        fn extra_trace_blocks(&self) -> usize {
            0
        }

        fn prepare(
            &self,
            circuit: CircuitType,
            setup: CanonicalCircuitSetup,
            _security: SecurityLevel,
        ) -> Result<Self::Precomputations, ExecutionProverError> {
            fake_precomputations(circuit, setup)
        }

        fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
            let WorkBatch {
                batch_id,
                receiver,
                sender,
            } = batch;
            self.batches
                .spawn(format!("finite-backend-{batch_id}"), move || {
                    for request in receiver {
                        assert_eq!(request.batch_id(), batch_id);
                        // Counted before the gate: a test needs to know work
                        // REACHED the backend, which is what makes opening the
                        // gate able to return credits.
                        if !matches!(request, WorkRequest::SetupInitialization(_)) {
                            stats::REQUESTS_RECEIVED.fetch_add(1, Ordering::SeqCst);
                        }
                        let Some(result) = serve_request("finite", request, &sender) else {
                            return;
                        };
                        result_gate::wait_for_permit();
                        if sender
                            .send(WorkerResult::BackendWorkResult(result))
                            .is_err()
                        {
                            return;
                        }
                    }
                });
        }
    }
}

/// Producer-level unit tests for how one stream's snapshot delta maps onto
/// finite block credits.
///
/// This is NOT the plan's negative control and must not be read as one. It does
/// not run the JIT or `SimulationRunner`, so it never exercises
/// `ContextImpl::MAX_CYCLES_PER_SNAPSHOT`; its two cases feed DIFFERENT row
/// counts to the same producer rather than running one workload under two
/// checkpoint settings; it leaves the result channel unserved, which
/// manufactures the stall instead of letting one arise from an exhausted pool
/// under real publication and credit return; and it reaches cancellation
/// through `process_snapshot`'s own `Option` return, not through the callback
/// stop path that crosses the non-unwinding JIT ABI.
///
/// What it does earn its place for: it pins the arithmetic the budget is built
/// on against the real producer loop and real finite blocks, at consistent
/// sizes — a delta larger than `P_s + S_s` exhausts the pool and parks the
/// producer, a delta of `L` fits the reserve with no wait at all, and the
/// one-stream reserve agrees with `tracing::budget`.
///
/// Blocks here are only ever reserved, never written — there is no tracer to
/// fill them — so a 1 GiB pool of them costs no resident memory.
#[cfg(test)]
mod producer_allocation {
    use super::finite_pool::FiniteTraceAllocator;
    use crate::messages::WorkerResult;
    use crate::tracing::TracingDataProducer;
    use crate::workers::cancellation::{waits, Cancellation};
    use crossbeam_channel::unbounded;
    use execution_prover_model::circuit_type::{
        CircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };
    use riscv_transpiler::jit::{
        max_cycles_between_snapshots, DEFAULT_MAX_CYCLES_PER_SNAPSHOT,
        MAX_COUNTER_INCREMENT_PER_CYCLE,
    };
    use riscv_transpiler::witness::NonMemoryOpcodeTracingDataWithTimestamp;
    use std::collections::VecDeque;
    use std::time::{Duration, Instant};

    type Row = NonMemoryOpcodeTracingDataWithTimestamp;

    /// Reported and owned alike, unlike the mechanism harness: the reserve below
    /// is computed from this number and the blocks really are this big.
    const BLOCK_BYTES: usize = 64 << 20;

    const CIRCUIT: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
    ));

    /// `P_s + S_s + 1` for this one stream, at this block size.
    fn reserve_for_one_stream() -> usize {
        let rows_per_block = BLOCK_BYTES / size_of::<Row>();
        let domain = CIRCUIT.get_domain_size();
        let length = max_cycles_between_snapshots(DEFAULT_MAX_CYCLES_PER_SNAPSHOT)
            * MAX_COUNTER_INCREMENT_PER_CYCLE;
        let partial = domain.div_ceil(rows_per_block);
        let snapshot = length.div_ceil(rows_per_block) + length.div_ceil(domain) + 1;
        partial + snapshot + 1
    }

    fn checkpointed_snapshot_rows() -> usize {
        max_cycles_between_snapshots(DEFAULT_MAX_CYCLES_PER_SNAPSHOT)
            * MAX_COUNTER_INCREMENT_PER_CYCLE
    }

    struct Harness {
        producer: Option<TracingDataProducer<Row, FiniteTraceAllocator>>,
        cancellation: Cancellation,
        // Held so published results keep their blocks, exactly as an unserved
        // backend request would: nothing drains this.
        _results: crossbeam_channel::Receiver<WorkerResult<FiniteTraceAllocator>>,
        _free: crossbeam_channel::Sender<FiniteTraceAllocator>,
    }

    fn harness(pool: usize) -> Harness {
        let (free_sender, free_receiver) = unbounded();
        for _ in 0..pool {
            free_sender
                .send(FiniteTraceAllocator::with_capacity(BLOCK_BYTES))
                .unwrap();
        }
        let (results_sender, results_receiver) = unbounded();
        let cancellation = Cancellation::new();
        let producer = TracingDataProducer::<Row, _>::new(
            CIRCUIT,
            free_receiver,
            results_sender,
            cancellation.token(),
        );
        Harness {
            producer: Some(producer),
            cancellation,
            _results: results_receiver,
            _free: free_sender,
        }
    }

    fn await_condition(what: &str, mut condition: impl FnMut() -> bool) {
        let deadline = Instant::now() + Duration::from_secs(120);
        while !condition() {
            assert!(Instant::now() < deadline, "timed out waiting for {what}");
            std::thread::yield_now();
        }
    }

    /// With the checkpoint disabled, one snapshot's delta outruns the reserve
    /// and the producer parks with nothing left to publish.
    ///
    /// The block is OBSERVED before anything is cancelled. That ordering is the
    /// requirement: a run that was cancelled first would show only that
    /// cancellation works, not that the wait it interrupted ever happened.
    /// Cancellation then travels back as a value through the same non-unwinding
    /// stop path `receive_trace` relies on, which is why `process_snapshot`
    /// returns an `Option` rather than panicking.
    #[test]
    fn cpu_a_delta_beyond_the_reserve_parks_the_producer() {
        let _observation = waits::observation_guard();
        let pool = reserve_for_one_stream();
        let mut harness = harness(pool);
        let mut producer = harness.producer.take().unwrap();
        // What an unbounded interval permits: several whole circuits in one
        // snapshot. Each boundary publishes into a channel nobody serves, so
        // not one block ever comes back.
        let rows = 4 * CIRCUIT.get_domain_size();
        let before = waits::trace_block_waits();

        let worker = std::thread::spawn(move || {
            let mut ranges = VecDeque::new();
            let outcome = producer.process_snapshot(0, 0, rows, &mut ranges);
            // Ranges borrow the chunks; drop them before the producer so the
            // blocks are released in the order the pipeline releases them.
            drop(ranges);
            outcome
        });

        await_condition("the producer to park on an empty trace-block pool", || {
            waits::trace_block_waits() > before
        });

        harness.cancellation.cancel();
        let outcome = worker.join().expect("the producer thread must not panic");
        assert_eq!(
            outcome, None,
            "a cancelled producer must give up as a value, not by panicking"
        );
    }

    /// The same pool and the same stream, with the delta the checkpoint bounds
    /// it to, completes without ever parking.
    #[test]
    fn cpu_a_delta_of_l_fits_the_reserve_without_waiting() {
        let _observation = waits::observation_guard();
        let pool = reserve_for_one_stream();
        let mut harness = harness(pool);
        let mut producer = harness.producer.take().unwrap();
        let rows = checkpointed_snapshot_rows();
        assert!(
            rows < 4 * CIRCUIT.get_domain_size(),
            "the bounded delta must be the smaller of the two, or the two halves \
             differ by something other than the checkpoint"
        );
        let before = waits::trace_block_waits();

        let mut ranges = VecDeque::new();
        let outcome = producer.process_snapshot(0, 0, rows, &mut ranges);

        assert_eq!(outcome, Some(()), "a checkpointed snapshot must complete");
        assert_eq!(
            waits::trace_block_waits(),
            before,
            "the reserve did not cover one checkpointed snapshot"
        );
        drop(ranges);
        let _ = harness;
    }

    /// The reserve this reproduction is sized from, so a change to the budget or
    /// to the row type shows up here rather than silently moving the goalposts.
    #[test]
    fn cpu_the_one_stream_reserve_is_what_the_budget_says() {
        let inputs = crate::tracing::budget::ProducerBudgetInputs::new(
            crate::ExecutionKind::Unrolled,
            crate::MachineType::FullUnsigned,
            BLOCK_BYTES,
            riscv_transpiler::jit::JitRunnerRam::Medium.ram_size(),
        );
        let budget = crate::tracing::budget::ProducerBudget::compute(&inputs).unwrap();
        assert!(
            reserve_for_one_stream() < budget.reserve_blocks,
            "one stream's reserve must be a fraction of the whole-execution one"
        );
    }
}

/// The plan's negative control, driven through the real JIT.
///
/// Both arms run the SAME bytecode with the SAME cycle bound against the SAME
/// pool. The only difference is `run_simulator`'s `SNAPSHOT_INTERVAL` const:
/// `0` leaves `ContextImpl::MAX_CYCLES_PER_SNAPSHOT` at `None`, the fixed
/// interval is what production passes. Real JIT, real replay, real publication,
/// real credit return — the consumer returns a trace's blocks under the same
/// rule the collector uses.
///
/// WHY A REGISTER-ONLY LOOP. The guest is `addi x1, x1, 1; jal x0, -4` — no
/// loads, no stores, no delegations. A workload that touches memory fills trace
/// chunks on its own, so it publishes for reasons that have nothing to do with
/// the checkpoint, and a disabled arm that then failed to stall would be a
/// fixture result indistinguishable from a real finding. With no memory trace a
/// chunk cannot fill incidentally, so publication in the enabled arm is
/// attributable to the checkpoint and to nothing else.
///
/// WHY THE RUN IS AS LONG AS IT IS, derived rather than tuned. Credits come
/// back only when a circuit is published, and a circuit is published only at a
/// circuit boundary or at finalize. A run crossing no boundary publishes
/// nothing mid-run in EITHER arm, so both arms hold the whole run and are
/// indistinguishable. The run must therefore cross one boundary:
///
/// * the loop emits one `AddSubLui` row and one `BranchSlt` row per iteration,
///   at one counter increment per cycle, so an iteration is 2 cycles;
/// * `AddSubLuiAuipcMop` has `D = 2^24` rows, so it crosses after `2^24`
///   iterations, i.e. `2^25` cycles;
/// * with `q = BLOCK_BYTES / size_of::<NonMemoryOpcodeTracingDataWithTimestamp>()`
///   rows per block, the two streams hold `2 * ceil(2^24 / q)` blocks at that
///   point, which is what [`POOL_BLOCKS`] is derived from.
///
/// At the boundary the enabled arm's contributing snapshots have already been
/// replayed, so the circuit dispatches and its blocks return. The disabled arm
/// is still inside one snapshot, so the same circuit is undispatchable
/// (`pipeline/results.rs` gates on `participating_snapshot_indexes`), its
/// blocks cannot come back, and the producer parks on an empty pool. That is a
/// hard deadlock, which is why this arm is cancelled rather than waited out.
#[cfg(test)]
mod jit_snapshot_control {
    use super::finite_pool::FiniteTraceAllocator;
    use crate::messages::{TracingData, WorkerResult};
    use crate::tracing::SplitTracingType;
    use crate::workers::cancellation::{waits, Cancellation};
    use crate::workers::simulation::{run_replayer, run_simulator};
    use execution_prover_model::circuit_type::{
        CircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };
    use execution_prover_model::MachineType;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
    use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
    use riscv_transpiler::jit::{
        JitRunnerRam, MemoryHolder, TraceChunk, DEFAULT_MAX_CYCLES_PER_SNAPSHOT,
    };
    use riscv_transpiler::vm::SimpleTape;
    use riscv_transpiler::witness::NonMemoryOpcodeTracingDataWithTimestamp;
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use std::time::{Duration, Instant};
    use type_map::concurrent::TypeMap;
    use worker::Worker;

    /// `addi x1, x1, 1` then `jal x0, -4`. Register-only by construction: it
    /// never touches memory, so it emits no memory rows and fills no trace
    /// chunk on its own.
    const REGISTER_ONLY_LOOP: [u32; 2] = [0x0010_8093, 0xffdf_f06f];

    /// Reported to the producer and owned by the allocator alike.
    const BLOCK_BYTES: usize = 1 << 20;
    const RAM: JitRunnerRam = JitRunnerRam::Tiny;
    const SIMULATOR_STACK: usize = 64 << 20;
    /// Bounded so a hang fails loudly instead of looking like CI trouble.
    const JOIN_TIMEOUT: Duration = Duration::from_secs(600);
    const STALL_TIMEOUT: Duration = Duration::from_secs(600);

    fn rows_per_block() -> usize {
        BLOCK_BYTES / size_of::<NonMemoryOpcodeTracingDataWithTimestamp>()
    }

    fn add_sub_domain() -> usize {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        ))
        .get_domain_size()
    }

    /// Blocks the two streams hold when `AddSubLui` reaches its boundary, plus
    /// one snapshot's appends and the one block that guarantees progress.
    fn pool_blocks() -> usize {
        let per_stream = add_sub_domain().div_ceil(rows_per_block());
        let snapshot = (DEFAULT_MAX_CYCLES_PER_SNAPSHOT as usize).div_ceil(rows_per_block()) + 2;
        2 * per_stream + snapshot + 1
    }

    /// Past the boundary with room, so the enabled arm publishes a circuit and
    /// then finishes, while the disabled arm has to keep allocating well beyond
    /// what the pool has left.
    ///
    /// The margin is derived, not padded. At the boundary the pool has
    /// `pool_blocks() - 2 * ceil(2^24 / q)` blocks left, about 55 here. The
    /// enabled arm gets its two circuits back and sails through; the disabled
    /// arm keeps them and must allocate `2 * ceil(margin_cycles / 2 / q)` more.
    /// One interval of margin would need ~52 blocks against those ~55 — too
    /// close to tell a stall from a finish — so four intervals are used, which
    /// needs ~208 and cannot be met.
    fn cycles_bound() -> u32 {
        (2 * add_sub_domain() + 4 * (DEFAULT_MAX_CYCLES_PER_SNAPSHOT as usize)) as u32
    }

    /// How an arm is brought to a stop.
    #[derive(Clone, Copy)]
    enum Stop {
        /// Let it finish by itself. Only valid for a bounded run.
        Natural,
        /// Wait for the circular wait, then cancel. The stalled arm.
        WhenStalled,
    }

    struct Report {
        completed: bool,
        stalled: bool,
        pool_blocks: usize,
        blocks_returned: usize,
        waits_observed: usize,
        /// Snapshots the replayer finished, and traces the consumer released.
        /// An arm that "did not stall" proves nothing unless it actually
        /// published, replayed and returned credits; these are that evidence.
        snapshots_replayed: usize,
        traces_released: usize,
    }

    /// Cancels and joins whatever is still running, on every exit path.
    struct Running {
        cancellation: Option<Cancellation>,
        handles: Vec<std::thread::JoinHandle<()>>,
    }

    impl Running {
        /// Wait for every thread within `JOIN_TIMEOUT`.
        ///
        /// `cancel_first` is the stalled arm, which is deadlocked by
        /// construction and can only be stopped. The other arm must be allowed
        /// to finish on its own — cancelling it would make "did not stall"
        /// trivially true while proving nothing, which is exactly the failure
        /// this method had on its first run.
        ///
        /// `JoinHandle::join` has no timed form, so the bound is on the
        /// completion signal; once every thread has signalled, the joins
        /// themselves cannot block. A bound that expires cancels so the joins
        /// can return, then fails loudly rather than hanging.
        fn finish(
            mut self,
            done: &crossbeam_channel::Receiver<()>,
            expected: usize,
            cancel_first: bool,
        ) {
            if cancel_first {
                if let Some(cancellation) = self.cancellation.take() {
                    cancellation.cancel();
                }
            }
            let deadline = Instant::now() + JOIN_TIMEOUT;
            for _ in 0..expected {
                let left = deadline.saturating_duration_since(Instant::now());
                if done.recv_timeout(left).is_err() {
                    if let Some(cancellation) = self.cancellation.take() {
                        cancellation.cancel();
                    }
                    panic!("a worker did not finish within {JOIN_TIMEOUT:?}");
                }
            }
            for handle in std::mem::take(&mut self.handles) {
                handle.join().expect("a worker panicked");
            }
        }
    }

    impl Drop for Running {
        fn drop(&mut self) {
            // Only reached when `finish` was skipped, i.e. an assertion already
            // failed. Cancel so the joins below can return at all.
            if let Some(cancellation) = self.cancellation.take() {
                cancellation.cancel();
            }
            for handle in std::mem::take(&mut self.handles) {
                let _ = handle.join();
            }
        }
    }

    /// Run one arm. `SNAPSHOT_INTERVAL` of 0 disables the checkpoint.
    fn drive<const SNAPSHOT_INTERVAL: u32>(
        program: &[u32],
        bound: Option<u32>,
        stop: Stop,
    ) -> Report {
        let pool = pool_blocks();
        let text: Vec<u32> = program.to_vec();
        let preprocessed = preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
        let tape = Arc::new(SimpleTape::new(&preprocessed));
        let binary_image = Arc::new(text.clone().into_boxed_slice());
        let text_section = Arc::new(text.into_boxed_slice());

        let (free_sender, free_receiver) = crossbeam_channel::unbounded::<FiniteTraceAllocator>();
        for _ in 0..pool {
            free_sender
                .send(FiniteTraceAllocator::with_capacity(BLOCK_BYTES))
                .unwrap();
        }
        let (results_sender, results_receiver) = crossbeam_channel::unbounded();
        let (snapshot_sender, snapshot_receiver) = crossbeam_channel::unbounded();
        let (chunk_sender, chunk_receiver) = crossbeam_channel::unbounded::<Box<TraceChunk>>();
        for _ in 0..2 {
            // SAFETY: the JIT fills a chunk before any read; `TraceChunk` is
            // plain data with no drop glue.
            chunk_sender
                .send(unsafe { Box::<TraceChunk>::new_zeroed().assume_init() })
                .unwrap();
        }
        let (done_sender, done_receiver) = crossbeam_channel::unbounded::<()>();
        let abort = Arc::new(AtomicBool::new(false));
        let cancellation = Cancellation::new();
        // Traces the consumer holds because a snapshot they belong to has not
        // been replayed. Non-zero with an empty pool IS the circular wait, as
        // an explicit state rather than a timing heuristic.
        let undispatchable = Arc::new(AtomicUsize::new(0));
        let simulation_finished = Arc::new(AtomicBool::new(false));
        let snapshots_replayed = Arc::new(AtomicUsize::new(0));
        let traces_released = Arc::new(AtomicUsize::new(0));

        // BEFORE anything is launched: a baseline taken after the simulator
        // starts can miss the very wait it is looking for.
        let baseline_waits = waits::trace_block_waits();

        let mut running = Running {
            cancellation: Some(cancellation),
            handles: Vec::with_capacity(3),
        };
        let token = running.cancellation.as_ref().unwrap().token();

        running.handles.push({
            let free_sender = free_sender.clone();
            let undispatchable = undispatchable.clone();
            let simulation_finished = simulation_finished.clone();
            let snapshots_replayed = snapshots_replayed.clone();
            let traces_released = traces_released.clone();
            let done_sender = done_sender.clone();
            std::thread::Builder::new()
                .name("ab-consumer-control".to_string())
                .spawn(move || {
                    let mut replayed: BTreeSet<usize> = BTreeSet::new();
                    let mut waiting: BTreeMap<
                        (CircuitType, usize),
                        TracingData<FiniteTraceAllocator>,
                    > = BTreeMap::new();
                    let release = |data: TracingData<FiniteTraceAllocator>,
                                   sender: &crossbeam_channel::Sender<FiniteTraceAllocator>,
                                   released: &AtomicUsize| {
                        for allocator in data.tracing_data.into_allocators() {
                            let _ = sender.send(allocator);
                        }
                        released.fetch_add(1, Ordering::SeqCst);
                    };
                    for result in results_receiver {
                        match result {
                            WorkerResult::TracingData(data) => {
                                if data.participating_snapshot_indexes.is_subset(&replayed) {
                                    release(data, &free_sender, &traces_released);
                                } else {
                                    waiting.insert((data.circuit_type, data.sequence_id), data);
                                }
                            }
                            WorkerResult::SnapshotReplayed(index) => {
                                replayed.insert(index);
                                snapshots_replayed.fetch_add(1, Ordering::SeqCst);
                                let ready: Vec<_> = waiting
                                    .iter()
                                    .filter(|(_, d)| {
                                        d.participating_snapshot_indexes.is_subset(&replayed)
                                    })
                                    .map(|(key, _)| *key)
                                    .collect();
                                for key in ready {
                                    release(
                                        waiting.remove(&key).unwrap(),
                                        &free_sender,
                                        &traces_released,
                                    );
                                }
                            }
                            WorkerResult::InitsAndTeardownsData(data) => {
                                if let Some(trace) = data.inits_and_teardowns {
                                    for allocator in trace.into_allocators() {
                                        let _ = free_sender.send(allocator);
                                    }
                                }
                            }
                            WorkerResult::SimulationResult(_) => {
                                simulation_finished.store(true, Ordering::SeqCst)
                            }
                            _ => {}
                        }
                        undispatchable.store(waiting.len(), Ordering::SeqCst);
                    }
                    let _ = done_sender.send(());
                })
                .unwrap()
        });

        running.handles.push({
            let results_sender = results_sender.clone();
            let chunk_sender = chunk_sender.clone();
            let abort = abort.clone();
            let token = token.clone();
            let done_sender = done_sender.clone();
            std::thread::Builder::new()
                .name("ab-replay-control-0".to_string())
                .spawn(move || {
                    run_replayer::<SplitTracingType, FiniteTraceAllocator, _>(
                        1,
                        0,
                        tape,
                        snapshot_receiver,
                        chunk_sender,
                        results_sender,
                        abort,
                        token,
                    );
                    let _ = done_sender.send(());
                })
                .unwrap()
        });

        running.handles.push({
            let chunk_sender = chunk_sender.clone();
            // A CLONE, with the original kept alive in this frame until after
            // the joins. The simulator finishes first, and if it owned the only
            // receiver its exit would close the channel under the replayer,
            // which then panics returning the chunk it just replayed. The
            // pipeline keeps the original for the same reason.
            let chunk_receiver = chunk_receiver.clone();
            let results_sender = results_sender.clone();
            let free_receiver = free_receiver.clone();
            let abort = abort.clone();
            let done_sender = done_sender.clone();
            std::thread::Builder::new()
                .name("ab-simulator-control".to_string())
                .stack_size(SIMULATOR_STACK)
                .spawn(move || {
                    let mut memory_holder: Box<MemoryHolder> =
                        MemoryHolder::allocate_zeroed(RAM, Default::default());
                    let worker = Worker::new_with_num_threads(1);
                    run_simulator::<_, SplitTracingType, _, _, _, SNAPSHOT_INTERVAL>(
                        1,
                        MachineType::FullUnsigned,
                        binary_image,
                        text_section,
                        bound,
                        Arc::new(Mutex::new(TypeMap::new())),
                        &mut memory_holder,
                        Arc::new(Mutex::new(Some(QuasiUARTSource::new_with_reads(vec![])))),
                        chunk_sender,
                        chunk_receiver,
                        snapshot_sender,
                        results_sender,
                        free_receiver,
                        abort,
                        token,
                        &worker,
                        RAM,
                    );
                    let _ = done_sender.send(());
                })
                .unwrap()
        });

        // This frame's copies must go or the consumer never sees its channel
        // close and the bounded wait below expires for the wrong reason.
        drop(results_sender);
        drop(chunk_sender);
        drop(done_sender);

        let (stalled, cancel_first) = match stop {
            Stop::Natural => (false, false),
            Stop::WhenStalled => (
                await_stall(&free_sender, &undispatchable, baseline_waits),
                true,
            ),
        };
        let waits_observed = waits::trace_block_waits() - baseline_waits;
        running.finish(&done_receiver, 3, cancel_first);

        Report {
            completed: simulation_finished.load(Ordering::SeqCst),
            stalled,
            pool_blocks: pool,
            blocks_returned: free_sender.len(),
            waits_observed,
            snapshots_replayed: snapshots_replayed.load(Ordering::SeqCst),
            traces_released: traces_released.load(Ordering::SeqCst),
        }
    }

    /// The explicit circular-wait state: a producer has waited, no credit is
    /// available, and the consumer is holding a trace it cannot dispatch.
    ///
    /// Not a settle timer. All three conditions are states rather than
    /// elapsed-time guesses, and together they say the run cannot make progress
    /// on its own: the only thing that could free a block is the publication
    /// that the unreplayed snapshot is blocking.
    fn await_stall(
        free_sender: &crossbeam_channel::Sender<FiniteTraceAllocator>,
        undispatchable: &AtomicUsize,
        baseline_waits: usize,
    ) -> bool {
        let deadline = Instant::now() + STALL_TIMEOUT;
        loop {
            let waited = waits::trace_block_waits() > baseline_waits;
            let starved = free_sender.is_empty();
            let blocked_publication = undispatchable.load(Ordering::SeqCst) > 0;
            if waited && starved && blocked_publication {
                return true;
            }
            if Instant::now() >= deadline {
                return false;
            }
            std::thread::yield_now();
        }
    }

    /// Both arms, same workload, same pool; only the interval differs.
    #[test]
    #[ignore = "multi-GiB and multi-minute: run explicitly when the box is clear"]
    fn cpu_without_the_checkpoint_publication_blocks_and_with_it_the_same_workload_completes() {
        let _observation = waits::observation_guard();
        println!(
            "derived: rows/block {}, pool {} blocks ({} MiB), cycles bound {}",
            rows_per_block(),
            pool_blocks(),
            (pool_blocks() * BLOCK_BYTES) >> 20,
            cycles_bound()
        );

        let enabled = drive::<DEFAULT_MAX_CYCLES_PER_SNAPSHOT>(
            &REGISTER_ONLY_LOOP,
            Some(cycles_bound()),
            Stop::Natural,
        );
        println!(
            "enabled : completed={} waits={} returned {}/{} snapshots_replayed={} traces_released={}",
            enabled.completed,
            enabled.waits_observed,
            enabled.blocks_returned,
            enabled.pool_blocks,
            enabled.snapshots_replayed,
            enabled.traces_released
        );
        assert!(
            enabled.completed,
            "the checkpointed arm did not finish, so the pool is too small to tell the \
             arms apart rather than the checkpoint being what makes the difference"
        );
        assert_eq!(
            enabled.blocks_returned, enabled.pool_blocks,
            "the checkpointed arm did not return every credit"
        );
        // "Did not stall" is not the claim. The enabled arm has to have done
        // the work: snapshots replayed and traces released mid-run are what
        // say publication and credit return actually happened.
        assert!(
            enabled.snapshots_replayed > 1,
            "the checkpointed arm replayed {} snapshots, so the checkpoint did not \
             chop the run up at all",
            enabled.snapshots_replayed
        );
        assert!(
            enabled.traces_released > 0,
            "the checkpointed arm released no trace, so nothing was published"
        );

        let disabled = drive::<0>(&REGISTER_ONLY_LOOP, Some(cycles_bound()), Stop::WhenStalled);
        println!(
            "disabled: stalled={} completed={} waits={}",
            disabled.stalled, disabled.completed, disabled.waits_observed
        );
        assert!(
            disabled.stalled,
            "the unchecked arm never reached the circular wait: no credit free, a \
             producer waiting and an undispatchable trace held. That would be a finding \
             about the budget, not about this test — one unbounded snapshot would not \
             outrun the reserve for this workload"
        );
        assert!(
            !disabled.completed,
            "the unchecked arm published a simulation result, so it was not deadlocked"
        );
    }
}
