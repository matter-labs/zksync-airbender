mod cache_seed;
mod results;

use super::*;
use cache_seed::seed_from_cache;

/// The simulator recurses through the JIT's trace callbacks and the replayers
/// walk deep witness structures, so these threads get an explicit stack.
const SIMULATION_THREAD_STACK_SIZE: usize = 64 << 20;

/// Test seam: a real spawn failure needs the process to be out of threads or
/// memory, which a test cannot provoke without damaging the rest of the run.
#[cfg(any(test, feature = "test_utils"))]
pub mod spawn_injection {
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// Replay spawns still permitted before the next one fails.
    /// `usize::MAX` means no injection.
    static ALLOWED_REPLAY_SPAWNS: AtomicUsize = AtomicUsize::new(usize::MAX);

    /// Let `successes` replay spawns through, then fail every later one.
    ///
    /// Process-global, so a test using it must own its process.
    pub fn fail_replay_spawn_after(successes: usize) {
        ALLOWED_REPLAY_SPAWNS.store(successes, Ordering::SeqCst);
    }

    /// Restore normal spawning.
    pub fn clear() {
        ALLOWED_REPLAY_SPAWNS.store(usize::MAX, Ordering::SeqCst);
    }

    pub(super) fn should_fail() -> bool {
        let mut current = ALLOWED_REPLAY_SPAWNS.load(Ordering::SeqCst);
        loop {
            if current == usize::MAX {
                return false;
            }
            if current == 0 {
                return true;
            }
            match ALLOWED_REPLAY_SPAWNS.compare_exchange(
                current,
                current - 1,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return false,
                Err(observed) => current = observed,
            }
        }
    }
}

/// Spawn a replay thread, honouring the test-only failure injection.
fn spawn_replay_thread(
    builder: std::thread::Builder,
    body: impl FnOnce() + Send + 'static,
) -> std::io::Result<std::thread::JoinHandle<()>> {
    #[cfg(any(test, feature = "test_utils"))]
    if spawn_injection::should_fail() {
        // As a real spawn failure does, so the channel clones the body
        // captured are released on this path too.
        drop(body);
        return Err(std::io::Error::other(
            "injected replay-thread spawn failure",
        ));
    }
    builder.spawn(body)
}

/// Handles for one batch's simulation and replay threads, and the cancellation
/// that wakes them.
///
/// Joining is not optional: the threads return their memory holder and trace
/// chunks to the caches on the way out, and the next batch's simulator pops
/// them straight back. Dropping a `JoinHandle` detaches the thread instead, so
/// `Drop` cancels and joins on any path that leaves without joining.
pub(super) struct SimulationThreads<T: Send + 'static> {
    threads: Vec<std::thread::JoinHandle<()>>,
    cancellation: Cancellation,
    /// The spawning frame's own handle on the trace-chunk free list, held here
    /// rather than in a local so releasing it is part of the guard.
    ///
    /// The simulator's final drain — `free_trace_chunks_receiver.iter()` —
    /// ends when the LAST sender closes and does not consult the cancellation
    /// token, so joining while still holding this deadlocks the joiner against
    /// the thread it is joining.
    free_trace_chunks_sender: Option<Sender<T>>,
}

impl<T: Send + 'static> SimulationThreads<T> {
    /// Wake every producer blocked on a buffer, a chunk or a snapshot.
    pub(super) fn cancel(&mut self) {
        self.cancellation.cancel();
    }

    /// Close this frame's trace-chunk sender so the simulator's final drain can
    /// terminate. Idempotent.
    pub(super) fn release_startup_owners(&mut self) {
        self.free_trace_chunks_sender = None;
    }

    /// Join every thread and hand back the first panic payload instead of
    /// raising it, so the caller can decide which failure to report.
    ///
    /// Every handle is joined even after one reports a panic: returning early
    /// would detach the rest, leaving them holding cache entries the next
    /// batch needs.
    pub(super) fn join_capturing(mut self) -> Option<Box<dyn std::any::Any + Send>> {
        self.join_all()
    }

    fn join_all(&mut self) -> Option<Box<dyn std::any::Any + Send>> {
        // Unconditional: a join can only complete once the simulator's drain
        // has, and that drain waits on this sender.
        self.release_startup_owners();
        let mut first_panic = None;
        for thread in std::mem::take(&mut self.threads) {
            if let Err(payload) = thread.join() {
                if first_panic.is_none() {
                    first_panic = Some(payload);
                }
            }
        }
        first_panic
    }
}

impl<T: Send + 'static> Drop for SimulationThreads<T> {
    fn drop(&mut self) {
        if self.threads.is_empty() {
            return;
        }
        // Reached only when the caller left without joining, i.e. a panic is
        // already unwinding. Their panics are swallowed rather than aborting
        // the process with a double panic.
        self.cancellation.cancel();
        let _ = self.join_all();
    }
}
use results::{
    dispatch_backend_requests, maybe_close_request_sender_after_progress, RequestContext,
    ResultAccumulator,
};

impl<B: ExecutionBackend> ExecutionProver<B> {
    pub(super) fn get_result(
        &self,
        proving: bool,
        cache: &mut Option<TraceCache<B::Allocator>>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: Arc<Mutex<Option<impl NonDeterminismCSRSource + Send + 'static>>>,
        pow_challenge: u64,
        external_challenges: Option<GKRExternalChallenges<BF, E4>>,
        proof_caps: BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
    ) -> ExecutionProverResult {
        if let Some(cache) = cache.as_ref() {
            if proving {
                assert!(cache.simulation_result.is_some());
            } else {
                assert!(cache.is_not_initialized());
            }
        }
        self.ensure_usable();
        assert!(proving ^ external_challenges.is_none());
        let binary_holder = &self.binary_holders[&binary_key];
        let (work_results_sender, work_results_receiver) = unbounded();
        let (work_requests_sender, work_requests_receiver) = unbounded();
        let work_batch = WorkBatch {
            batch_id,
            receiver: work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        trace!("BATCH[{batch_id}] PROVER sending work batch to backend");
        self.backend.submit(work_batch);
        let cache_seed = seed_from_cache(
            self,
            binary_holder,
            proving,
            cache,
            batch_id,
            external_challenges.as_ref(),
            &proof_caps,
            &work_requests_sender,
        );
        let mut sent_requests_count = cache_seed.sent_requests_count;
        let requests_served_from_cache = cache_seed.requests_served_from_cache;
        let trivial_unified_inits_and_teardowns = cache_seed.trivial_unified_inits_and_teardowns;
        let mut work_requests_sender = Some(work_requests_sender);
        let execution_kind = binary_holder.execution_kind;
        let machine_type = binary_holder.machine_type;
        let abort = Arc::new(AtomicBool::new(false));
        let mut acc = ResultAccumulator::<B::Allocator>::new();
        let mut backend_failure_signaled = false;
        // Distinct from `acc.failure`: the disconnect can be observed before
        // the failure event that explains it arrives, and no event may come.
        let mut backend_stopped_accepting = false;
        acc.pending_requests_count = cache_seed.pending_requests_count;
        acc.trivial_unified_inits_and_teardowns_count =
            cache_seed.trivial_unified_inits_and_teardowns_count;
        let mut abort_signaled = if let Some(cache) = cache.as_ref() {
            if proving && cache.total_requests_count == sent_requests_count {
                work_requests_sender = None;
                acc.simulation_result = cache.simulation_result.clone();
                true
            } else {
                false
            }
        } else {
            false
        };
        // A cached-seed disconnect is known BEFORE any producer exists, so
        // none are spawned: spawning and immediately cancelling risks a spawn
        // failure of its own, which would mask the queued `BackendFailure`.
        let mut simulation_threads = if abort_signaled || cache_seed.backend_stopped {
            debug!(
                "BATCH[{batch_id}] all proof requests have been served from cache, skipping simulation"
            );
            None
        } else {
            Some(self.spawn_simulation_workers(
                batch_id,
                binary_holder,
                non_determinism_source,
                &work_results_sender,
                &abort,
                Cancellation::new(),
            ))
        };
        drop(work_results_sender);

        // Nothing to cancel here, only collector state to initialise.
        // Draining continues so the backend's own failure event is consumed
        // and the ORIGINAL reason reaches the caller.
        if cache_seed.backend_stopped {
            backend_stopped_accepting = true;
            backend_failure_signaled = true;
            work_requests_sender = None;
        }

        let request_context = RequestContext {
            proving,
            batch_id,
            binary_holder,
            external_challenges: external_challenges.as_ref(),
            proof_caps: &proof_caps,
        };
        for sequence_id in trivial_unified_inits_and_teardowns {
            let data = InitsAndTeardownsData {
                circuit_type: CircuitType::Unrolled(UnrolledCircuitType::Unified),
                sequence_id,
                inits_and_teardowns: None,
            };
            acc.unpaired_unified_inits_and_teardowns
                .insert(sequence_id, data);
        }
        match execution_kind {
            ExecutionKind::Unrolled => {
                let non_memory =
                    UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .iter()
                        .map(|t| t.get_family_idx());
                let memory =
                    UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .iter()
                        .map(|t| t.get_family_idx());
                for family_idx in non_memory.chain(memory) {
                    acc.circuit_families_memory_caps
                        .insert(family_idx, BTreeMap::new());
                    acc.circuit_families_proofs
                        .insert(family_idx, BTreeMap::new());
                }
            }
            ExecutionKind::Unified => {
                let family_idx = UnrolledCircuitType::Unified.get_family_idx();
                acc.circuit_families_memory_caps
                    .insert(family_idx, BTreeMap::new());
                acc.circuit_families_proofs
                    .insert(family_idx, BTreeMap::new());
            }
        }

        for work_result in work_results_receiver {
            let work_requests = acc.handle_work_result(self, cache, work_result, &request_context);
            if backend_failure_signaled {
                // The request channel is already closed, so dispatching would
                // unwrap a `None` sender; see `release_work_requests`.
                self.release_work_requests(work_requests);
                continue;
            }
            let backend_stopped = dispatch_backend_requests(
                self,
                &requests_served_from_cache,
                work_requests,
                &work_requests_sender,
                &mut acc.pending_requests_count,
                &mut sent_requests_count,
            );
            if backend_stopped {
                // Keep draining: the failure event is normally queued behind
                // the results still in flight, and consuming it is what makes
                // the reported reason the ORIGINAL one.
                backend_stopped_accepting = true;
            }
            if acc.failure.is_some() || backend_stopped {
                backend_failure_signaled = true;
                debug!("BATCH[{batch_id}] PROVER backend reported a failure, cancelling producers");
                // Order matters: waking the producers first lets them release
                // the result senders whose liveness this loop depends on.
                if let Some(threads) = simulation_threads.as_mut() {
                    threads.cancel();
                }
                work_requests_sender = None;
            }
            maybe_close_request_sender_after_progress::<B>(
                cache,
                &mut work_requests_sender,
                sent_requests_count,
                &mut abort_signaled,
                &mut acc.simulation_result,
                &acc.uninitialized_tracing_data,
                &acc.unpaired_unified_inits_and_teardowns,
                &acc.unpaired_unified_tracing_data,
                &abort,
                proving,
                batch_id,
            );
        }

        let failure = acc.failure.take().or_else(|| {
            // A reported reason always wins: by this point the whole results
            // channel has been drained, so any queued `BackendFailure` is
            // already in `acc.failure`.
            backend_stopped_accepting.then(|| {
                "the backend stopped accepting work without reporting a failure".to_string()
            })
        });
        // Captured rather than re-raised: a producer panic is usually the
        // consequence of the first recorded failure, which is the informative
        // one. Re-raised below only if nothing else failed.
        let producer_panic = simulation_threads
            .take()
            .and_then(|threads| threads.join_capturing());

        // Only a clean run accounts for every dispatched request: a failing
        // backend abandons what it had in flight and sends no completion, so
        // asserting here would replace the reported failure.
        if !backend_failure_signaled {
            assert_eq!(acc.pending_requests_count, 0);
        }
        if backend_failure_signaled {
            // Dropped, not recycled: recycling asserts unique `Arc` ownership
            // and a backend that abandoned consumed requests may still hold
            // reader references, so `into_allocators` could panic over the top
            // of the real failure. The pool cannot be made whole anyway.
            drop(std::mem::take(&mut acc.uninitialized_tracing_data));
            drop(std::mem::take(
                &mut acc.unpaired_unified_inits_and_teardowns,
            ));
            drop(std::mem::take(&mut acc.unpaired_unified_tracing_data));
        } else if abort_signaled {
            std::mem::take(&mut acc.uninitialized_tracing_data)
                .into_values()
                .for_each(|data| {
                    self.free_tracing_data(data.tracing_data);
                });
            std::mem::take(&mut acc.unpaired_unified_inits_and_teardowns)
                .into_values()
                .for_each(|data| {
                    if let Some(inits_and_teardowns) = data.inits_and_teardowns {
                        self.free_inits_and_teardowns(inits_and_teardowns);
                    }
                });
            std::mem::take(&mut acc.unpaired_unified_tracing_data)
                .into_values()
                .for_each(|data| {
                    self.free_tracing_data(data.tracing_data);
                });
        } else {
            assert!(acc.uninitialized_tracing_data.is_empty());
            assert!(acc.unpaired_unified_inits_and_teardowns.is_empty());
            assert!(acc.unpaired_unified_tracing_data.is_empty());
        }
        if backend_failure_signaled {
            // As above: release by dropping.
            if let Some(cache) = cache.as_mut() {
                drop(std::mem::take(&mut cache.entries));
            }
        }

        // Raised only after every owner above has been released, so the unwind
        // cannot skip that release.
        if let Some(reason) = failure {
            self.mark_terminal(&reason);
            panic!("BATCH[{batch_id}] execution failed: {reason}");
        }
        if let Some(payload) = producer_panic {
            std::panic::resume_unwind(payload);
        }

        if let Some(cache) = cache.as_mut() {
            if proving {
                assert!(cache.is_empty())
            } else {
                cache.total_requests_count = sent_requests_count;
                cache.trivial_unified_inits_and_teardowns_count =
                    acc.trivial_unified_inits_and_teardowns_count;
                cache.simulation_result = acc.simulation_result.clone();
            }
        }
        assemble_result(acc, proving, pow_challenge, binary_key)
    }

    /// Drop work requests that will never be submitted, releasing their
    /// traces. Failure path only.
    ///
    /// The owners are DROPPED, not recycled: `into_allocators` asserts unique
    /// `Arc` ownership, and a late or refused request can share its chunks
    /// with a live cache entry — tripping that would replace the backend's
    /// original error with a uniqueness panic. Not returning the credits is
    /// correct: the instance is terminal and producers are woken by
    /// cancellation, not by credits.
    fn release_work_requests(
        &self,
        work_requests: VecDeque<WorkRequest<B::Allocator, B::Precomputations>>,
    ) {
        for request in work_requests {
            #[cfg(any(test, feature = "test_utils"))]
            self.released_work_requests
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            match request {
                WorkRequest::MemoryCommitment(request) => {
                    drop(request.inits_and_teardowns);
                    drop(request.tracing_data);
                }
                WorkRequest::Proof(request) => {
                    drop(request.inits_and_teardowns);
                    drop(request.tracing_data);
                }
                WorkRequest::SetupInitialization(_) => {}
            }
        }
    }

    /// Start the simulator and `replay_worker_threads_count` replay workers on
    /// dedicated, named OS threads.
    ///
    /// Dedicated, not pooled: these loops block on channels for most of their
    /// life, so a shared pool smaller than `1 + replayers` would have nothing
    /// left to run the work they are waiting for. The shared `Worker` stays
    /// for genuinely parallel auxiliary work the simulator calls into.
    ///
    /// The returned handle must be joined before the caller returns, and
    /// cancelled first if the batch is torn down early — a producer blocked on
    /// a free buffer will not observe a dropped result sender.
    fn spawn_simulation_workers<ND: NonDeterminismCSRSource + Send + 'static>(
        &self,
        batch_id: u64,
        binary_holder: &BinaryHolder<B>,
        non_determinism_source: Arc<Mutex<Option<ND>>>,
        work_results_sender: &Sender<WorkerResult<B::Allocator>>,
        abort: &Arc<AtomicBool>,
        cancellation: Cancellation,
    ) -> SimulationThreads<B::Snapshot> {
        let replayers_count = self.configuration.replay_worker_threads_count;
        let execution_kind = binary_holder.execution_kind;
        let machine_type = binary_holder.machine_type;
        let (split_snapshot_sender, split_snapshot_receiver) = unbounded();
        let (unified_snapshot_sender, unified_snapshot_receiver) = unbounded();
        let (free_trace_chunks_sender, free_trace_chunks_receiver) = unbounded();
        // Owns handles from the moment each is spawned, so a later spawn
        // failure unwinds through `SimulationThreads::drop` instead of
        // detaching the ones already running.
        let mut threads = SimulationThreads {
            threads: Vec::with_capacity(replayers_count + 1),
            cancellation,
            free_trace_chunks_sender: Some(free_trace_chunks_sender),
        };
        let free_trace_chunks_sender = threads
            .free_trace_chunks_sender
            .as_ref()
            .expect("just set")
            .clone();

        #[cfg(any(test, feature = "test_utils"))]
        self.simulations_started
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        trace!("BATCH[{batch_id}] PROVER starting SIMULATOR thread");
        {
            let memory_holders_cache = self.memory_holders_cache.clone();
            let trace_chunks_cache = self.trace_chunks_cache.clone();
            let free_trace_chunks_sender = free_trace_chunks_sender.clone();
            let free_allocators_receiver = self.free_allocators_receiver.clone();
            let binary_image = binary_holder.binary_image.clone();
            let text_section = binary_holder.text_section.clone();
            let cycles_bound = binary_holder.cycles_bound;
            let jit_cache = binary_holder.jit_cache.clone();
            let non_determinism_source = non_determinism_source.clone();
            let work_results_sender = work_results_sender.clone();
            let abort = abort.clone();
            let worker = self.worker.clone();
            let ram_config = self.configuration.ram_config;
            let token = threads.cancellation.token();
            let handle = std::thread::Builder::new()
                .name(format!("ab-simulator-{batch_id}"))
                .stack_size(SIMULATION_THREAD_STACK_SIZE)
                .spawn(move || {
                    // A simulator panic would otherwise leave every replayer
                    // blocked on a snapshot that will never arrive, and the
                    // collector blocked behind this thread's result sender.
                    let guard = CancelOnPanic::new(
                        token.clone(),
                        work_results_sender.clone(),
                        batch_id,
                        "simulator",
                    );
                    let mut memory_holder = {
                        let mut cache = memory_holders_cache
                            .lock()
                            .expect("ExecutionProver memory-holders cache mutex poisoned");
                        cache
                            .pop()
                            .expect("memory-holders cache is sized for the admitted job count")
                    };
                    let chunks = {
                        let mut cache = trace_chunks_cache
                            .lock()
                            .expect("ExecutionProver trace-chunks cache mutex poisoned");
                        cache
                            .pop()
                            .expect("trace-chunks cache is sized for the admitted job count")
                    };
                    for chunk in chunks {
                        free_trace_chunks_sender.send(chunk).expect(
                            "ExecutionProver trace-chunk free list closed while seeding replay workers",
                        );
                    }
                    let free_trace_chunks_receiver_clone = free_trace_chunks_receiver.clone();
                    match execution_kind {
                        ExecutionKind::Unrolled => run_simulator::<_, SplitTracingType, _, _, _, { riscv_transpiler::jit::DEFAULT_MAX_CYCLES_PER_SNAPSHOT }>(
                            batch_id,
                            machine_type,
                            binary_image,
                            text_section,
                            cycles_bound,
                            jit_cache,
                            &mut memory_holder,
                            non_determinism_source,
                            free_trace_chunks_sender,
                            free_trace_chunks_receiver,
                            split_snapshot_sender,
                            work_results_sender,
                            free_allocators_receiver,
                            abort,
                            token,
                            &worker,
                            ram_config,
                        ),
                        ExecutionKind::Unified => run_simulator::<_, UnifiedTracingType, _, _, _, { riscv_transpiler::jit::DEFAULT_MAX_CYCLES_PER_SNAPSHOT }>(
                            batch_id,
                            machine_type,
                            binary_image,
                            text_section,
                            cycles_bound,
                            jit_cache,
                            &mut memory_holder,
                            non_determinism_source,
                            free_trace_chunks_sender,
                            free_trace_chunks_receiver,
                            unified_snapshot_sender,
                            work_results_sender,
                            free_allocators_receiver,
                            abort,
                            token,
                            &worker,
                            ram_config,
                        ),
                    };
                    memory_holders_cache
                        .lock()
                        .expect("ExecutionProver memory-holders cache mutex poisoned")
                        .push(memory_holder);
                    // Every chunk comes back, including on the cancelled
                    // path: the next batch's simulator pops this whole set.
                    let trace_chunks = free_trace_chunks_receiver_clone.iter().collect_vec();
                    trace_chunks_cache
                        .lock()
                        .expect("ExecutionProver trace-chunks cache mutex poisoned")
                        .push(trace_chunks);
                    guard.disarm();
                })
                .expect("failed to start the simulator thread");
            threads.threads.push(handle);
        }

        trace!("BATCH[{batch_id}] PROVER starting REPLAY threads");
        for worker_id in 0..replayers_count {
            let instruction_tape = binary_holder.instruction_tape.clone();
            let split_snapshot_receiver = split_snapshot_receiver.clone();
            let free_trace_chunks_sender = free_trace_chunks_sender.clone();
            let unified_snapshot_receiver = unified_snapshot_receiver.clone();
            let work_results_sender = work_results_sender.clone();
            let abort = abort.clone();
            let token = threads.cancellation.token();
            let builder = std::thread::Builder::new()
                .name(format!("ab-replay-{batch_id}-{worker_id}"))
                .stack_size(SIMULATION_THREAD_STACK_SIZE);
            let handle = spawn_replay_thread(builder, move || {
                // A replay panic would otherwise leave the simulator blocked
                // on the trace chunk this thread was holding.
                let guard = CancelOnPanic::new(
                    token.clone(),
                    work_results_sender.clone(),
                    batch_id,
                    "replay",
                );
                match execution_kind {
                    ExecutionKind::Unrolled => run_replayer::<SplitTracingType, _, _>(
                        batch_id,
                        worker_id,
                        instruction_tape,
                        split_snapshot_receiver,
                        free_trace_chunks_sender,
                        work_results_sender,
                        abort,
                        token,
                    ),
                    ExecutionKind::Unified => run_replayer::<UnifiedTracingType, _, _>(
                        batch_id,
                        worker_id,
                        instruction_tape,
                        unified_snapshot_receiver,
                        free_trace_chunks_sender,
                        work_results_sender,
                        abort,
                        token,
                    ),
                };
                guard.disarm();
            })
            .expect("failed to start a replay thread");
            threads.threads.push(handle);
        }
        drop(free_trace_chunks_sender);
        threads.release_startup_owners();
        threads
    }

    pub(super) fn commit_memory_inner(
        &self,
        cache: &mut Option<TraceCache<B::Allocator>>,
        batch_id: u64,
        handle: BinaryHandle,
        non_determinism_source: Arc<Mutex<Option<impl NonDeterminismCSRSource + Send + 'static>>>,
    ) -> CommitMemoryResult {
        let binary_key = handle.0;
        info!(
            "BATCH[{batch_id}] PROVER producing memory commitments for binary with key {binary_key:?}"
        );
        let timer = Instant::now();
        let mut result = self
            .get_result(
                false,
                cache,
                batch_id,
                binary_key,
                non_determinism_source,
                0,
                None,
                BTreeMap::new(),
            )
            .into_memory_commitment_result();
        result.binary_handle = handle;
        let elapsed = timer.elapsed().as_secs_f64();
        info!(
            "BATCH[{batch_id}] PROVER produced memory commitments for binary with key {binary_key:?} in {elapsed:.3}s"
        );
        result
    }

    pub(super) fn prove_inner(
        &self,
        cache: &mut Option<TraceCache<B::Allocator>>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: Arc<Mutex<Option<impl NonDeterminismCSRSource + Send + 'static>>>,
        pow_challenge: u64,
        external_challenges: GKRExternalChallenges<BF, E4>,
        proof_caps: BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
    ) -> ProveResult {
        info!("BATCH[{batch_id}] PROVER producing proofs for binary with key {binary_key:?}");
        let timer = Instant::now();
        let result = self
            .get_result(
                true,
                cache,
                batch_id,
                binary_key,
                non_determinism_source,
                pow_challenge,
                Some(external_challenges),
                proof_caps,
            )
            .into_proof_result();
        let elapsed = timer.elapsed().as_secs_f64();
        info!(
            "BATCH[{batch_id}] PROVER produced proofs for binary with key {binary_key:?} in {elapsed:.3}s"
        );
        result
    }
}

/// `{key: {sequence_id: value}}` collapsed to `{key: [value]}` in sequence
/// order, which is what both result shapes carry.
fn flatten_by_sequence<K: Ord, V>(per_key: BTreeMap<K, BTreeMap<usize, V>>) -> BTreeMap<K, Vec<V>> {
    per_key
        .into_iter()
        .map(|(key, per_sequence)| (key, per_sequence.into_values().collect()))
        .collect()
}

/// Fold the collected [`ResultAccumulator`] into the final result.
fn assemble_result<A: execution_prover_model::allocator::HostTraceAllocator>(
    acc: ResultAccumulator<A>,
    proving: bool,
    pow_challenge: u64,
    binary_key: usize,
) -> ExecutionProverResult {
    let ResultAccumulator {
        trivial_unified_inits_and_teardowns_count,
        inits_and_teardowns_top_bits,
        simulation_result,
        circuit_families_memory_caps,
        inits_and_teardowns_memory_caps,
        delegation_circuits_memory_caps,
        circuit_families_proofs,
        inits_and_teardowns_proofs,
        delegation_circuits_proofs,
        ..
    } = acc;
    let SimulationResult {
        final_register_values,
        final_pc,
        final_timestamp,
    } = simulation_result.expect("simulation result must be present before get_result returns");
    if proving {
        let circuit_families_proofs = flatten_by_sequence(circuit_families_proofs);
        let inits_and_teardowns_proofs = inits_and_teardowns_proofs.into_values().collect_vec();
        let delegation_circuits_proofs = flatten_by_sequence(delegation_circuits_proofs);
        // Unified mode: real inits-and-teardowns circuits are the trailing
        // ones; everything before the trivial count is a dummy marker. Every
        // sequence_id, trivial or real, goes through the same
        // `WorkResult::Proof` insert, so the subtraction cannot underflow.
        let num_unified_it_circuits = circuit_families_proofs
            .get(&UnrolledCircuitType::Unified.get_family_idx())
            .map(|unified_proofs| {
                assert!(
                    unified_proofs.len() >= trivial_unified_inits_and_teardowns_count,
                    "unified proof count {} below trivial i&t count {}",
                    unified_proofs.len(),
                    trivial_unified_inits_and_teardowns_count
                );
                (unified_proofs.len() - trivial_unified_inits_and_teardowns_count) as u32
            });
        let result = ProveResult {
            register_final_values: final_register_values,
            final_pc,
            final_timestamp,
            circuit_families_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs: delegation_circuits_proofs,
            pow_challenge,
            num_unified_it_circuits,
        };
        ExecutionProverResult::Prove(result)
    } else {
        let circuit_families_memory_caps = flatten_by_sequence(circuit_families_memory_caps);
        let inits_and_teardowns_memory_caps =
            inits_and_teardowns_memory_caps.into_values().collect_vec();
        let delegation_circuits_memory_caps = flatten_by_sequence(delegation_circuits_memory_caps);
        let result = CommitMemoryResult {
            final_register_values,
            final_pc,
            final_timestamp,
            circuit_families_memory_caps,
            inits_and_teardowns_memory_caps,
            delegation_circuits_memory_caps,
            num_trivial_unified_circuits: trivial_unified_inits_and_teardowns_count,
            inits_and_teardowns_top_bits,
            binary_handle: BinaryHandle(binary_key),
        };
        ExecutionProverResult::CommitMemory(result)
    }
}
