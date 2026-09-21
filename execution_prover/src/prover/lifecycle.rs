use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Construct with the backend's default configuration. Not `Default`:
    /// this starts the backend, a thread pool, the simulation caches, the
    /// setup precomputations and the host buffer pool.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
            .expect("the default ExecutionProverConfiguration must be valid")
    }

    pub fn with_configuration(
        configuration: ExecutionProverConfiguration<B::Configuration>,
    ) -> Result<Self, ExecutionProverError> {
        // Before anything is allocated, so an invalid configuration costs no
        // backend resources.
        configuration.validate()?;

        let worker = if let Some(thread_pool_threads_count) = configuration.max_thread_pool_threads
        {
            Worker::new_with_num_threads(thread_pool_threads_count)
        } else {
            Worker::new()
        };
        info!(
            "PROVER thread pool with {} threads created",
            worker.num_cores
        );
        let worker = Arc::new(worker);

        // Before the caches, precomputations and buffer pool below: a backend
        // that cannot initialize must say so in seconds, not after minutes of
        // setup construction.
        let backend = B::initialize(&configuration, Arc::clone(&worker))?;

        // The extra block allowance is a runtime value (it depends on the
        // device count), so shared validation cannot see it. Folded in here,
        // still before anything is allocated.
        let host_allocators_count = total_host_allocators(&configuration, &backend)?;

        let simulator_cache_entries_count = configuration.expected_concurrent_jobs + 1;
        info!("PROVER creating memory holders cache with {simulator_cache_entries_count} entries");
        let memory_holders_cache = (0..simulator_cache_entries_count)
            .map(|_| backend.allocate_memory(configuration.ram_config))
            .collect::<Result<Vec<_>, _>>()?;
        let memory_holders_cache = Arc::new(Mutex::new(memory_holders_cache));

        let trace_chunks_count = configuration.replay_worker_threads_count * 2;
        info!(
            "PROVER creating trace chunks cache with {simulator_cache_entries_count} x {trace_chunks_count} entries"
        );
        let trace_chunks_cache = (0..simulator_cache_entries_count)
            .map(|_| {
                (0..trace_chunks_count)
                    .map(|_| backend.allocate_snapshot())
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let trace_chunks_cache = Arc::new(Mutex::new(trace_chunks_cache));

        let binary_holders = BTreeMap::new();
        info!("PROVER generating common precomputations");
        let common_precomputations =
            build_common_precomputations(&backend, &worker, configuration.security_level)?;
        let pending_setup_initialization = request_setup_initialization(
            &backend,
            configuration.security_level,
            common_precomputations
                .iter()
                .map(|(circuit_type, precomputations)| (*circuit_type, precomputations.clone()))
                .collect(),
        );

        info!(
            "PROVER initializing {} host buffers with {} MB per buffer",
            host_allocators_count,
            configuration.host_allocator_backing_allocation_size >> 20
        );
        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        for _ in 0..host_allocators_count {
            let allocator = backend
                .allocate_trace_block(configuration.host_allocator_backing_allocation_size)?;
            free_allocators_sender
                .send(allocator)
                .expect("ExecutionProver allocator pool channel closed during initialization");
        }

        pending_setup_initialization.wait();
        info!("PROVER initialized");
        let cache_quota_blocks = configuration.cache_quota_blocks()?;
        let admission = configuration.admission_limit().map(Admission::new);
        debug!("PROVER trace cache quota is {cache_quota_blocks} blocks per execution");
        Ok(Self {
            backend,
            configuration,
            worker,
            memory_holders_cache,
            trace_chunks_cache,
            admission,
            cache_quota_blocks,
            binary_holders,
            next_binary_id: 0,
            common_precomputations,
            free_allocators_sender,
            free_allocators_receiver,
            terminal_failure: Mutex::new(None),
            #[cfg(any(test, feature = "test_utils"))]
            peak_cached_blocks: std::sync::atomic::AtomicUsize::new(0),
            #[cfg(any(test, feature = "test_utils"))]
            simulations_started: std::sync::atomic::AtomicUsize::new(0),
            #[cfg(any(test, feature = "test_utils"))]
            cache_hits: std::sync::atomic::AtomicUsize::new(0),
            #[cfg(any(test, feature = "test_utils"))]
            released_work_requests: std::sync::atomic::AtomicUsize::new(0),
        })
    }

    /// Fail immediately if a previous batch terminated this instance, before
    /// any allocation or thread spawn.
    pub(super) fn ensure_usable(&self) {
        // Copy out and release the lock BEFORE panicking: unwinding with the
        // guard alive poisons the mutex, and every later call would report the
        // poison instead of the saved first failure.
        let reason = self
            .terminal_failure
            .lock()
            .expect("terminal-failure mutex poisoned")
            .clone();
        if let Some(reason) = reason {
            panic!("this ExecutionProver is unusable after a backend failure: {reason}");
        }
    }

    /// Take an execution slot, if the backend asked for a limit.
    ///
    /// The terminal check runs TWICE on purpose: once before queueing, so a
    /// dead instance rejects without making the caller wait, and once after
    /// acquiring, because the execution that held the slot may be the one that
    /// killed the backend. `AdmissionPermit::drop` returns the slot on the
    /// panic path the second check takes.
    pub(super) fn admit(&self) -> Option<AdmissionPermit<'_>> {
        self.ensure_usable();
        let permit = self.admission.as_ref().map(Admission::acquire);
        self.ensure_usable();
        permit
    }

    /// Largest number of blocks the trace cache has RETAINED at once, sampled
    /// after eviction so `peak <= quota` holds.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn peak_cached_blocks(&self) -> usize {
        self.peak_cached_blocks
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Blocks this execution's trace cache may hold.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn cache_quota_blocks(&self) -> usize {
        self.cache_quota_blocks
    }

    /// Execution slots free right now, when the backend asked for a limit.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn available_execution_slots(&self) -> Option<usize> {
        self.admission.as_ref().map(Admission::available)
    }

    /// Execution slots taken since construction, cumulative. A final free
    /// count cannot tell one acquisition from two released in between.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn execution_slot_acquisitions(&self) -> usize {
        self.admission.as_ref().map_or(0, Admission::acquisitions)
    }

    /// Callers that have entered the blocking wait for a slot, cumulative.
    /// The only way to tell a blocked caller from a merely slow one.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn execution_slot_wait_entries(&self) -> usize {
        self.admission.as_ref().map_or(0, Admission::entered_wait)
    }

    /// Proof requests dispatched from traces the cache already held. The
    /// backend still proves them; what the cache saved is the re-simulation.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn cache_hits(&self) -> usize {
        self.cache_hits.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Simulations started since construction: what shows that a blocked
    /// caller spawned no producers and took no buffers.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn simulations_started(&self) -> usize {
        self.simulations_started
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    pub(super) fn mark_terminal(&self, reason: &str) {
        let mut terminal = self
            .terminal_failure
            .lock()
            .expect("terminal-failure mutex poisoned");
        // The first failure is the informative one; later ones are its
        // consequences.
        if terminal.is_none() {
            *terminal = Some(reason.to_string());
        }
    }

    /// Whether a backend failure has terminated this instance.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn is_terminal(&self) -> bool {
        self.terminal_failure
            .lock()
            .expect("terminal-failure mutex poisoned")
            .is_some()
    }

    /// Common, binary-independent precomputations, keyed by circuit type.
    /// Whether the constructor initialized each family's setup is not
    /// otherwise observable.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn common_precomputations(&self) -> &BTreeMap<CircuitType, B::Precomputations> {
        &self.common_precomputations
    }

    /// As above, for the setups `add_binary` initializes.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn binary_precomputations(
        &self,
        binary_id: usize,
    ) -> &HashMap<UnrolledCircuitType, B::Precomputations> {
        &self
            .binary_holders
            .get(&binary_id)
            .expect("no binary is registered under this id")
            .precomputations
    }

    /// How many requests were released rather than dispatched after a failure.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn released_work_requests(&self) -> usize {
        self.released_work_requests
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Blocks currently available in the trace pool.
    #[cfg(any(test, feature = "test_utils"))]
    pub fn available_trace_blocks(&self) -> usize {
        self.free_allocators_sender.len()
    }

    pub(super) fn free_inits_and_teardowns(
        &self,
        inits_and_teardowns: InitsAndTeardownsTraceHost<B::Allocator>,
    ) {
        for allocator in inits_and_teardowns.into_allocators() {
            self.free_allocators_sender.send(allocator).expect(
                "ExecutionProver allocator return channel closed during init/teardown free",
            );
        }
    }

    pub(super) fn free_tracing_data(&self, tracing_data: TracingDataHost<B::Allocator>) {
        for allocator in tracing_data.into_allocators() {
            self.free_allocators_sender
                .send(allocator)
                .expect("ExecutionProver allocator return channel closed during tracing-data free");
        }
    }

    pub(super) fn free_traces(
        &self,
        inits_and_teardowns: Option<InitsAndTeardownsTraceHost<B::Allocator>>,
        tracing_data: Option<TracingDataHost<B::Allocator>>,
    ) {
        if let Some(inits_and_teardowns) = inits_and_teardowns {
            self.free_inits_and_teardowns(inits_and_teardowns);
        }
        if let Some(tracing_data) = tracing_data {
            self.free_tracing_data(tracing_data);
        }
    }

    /// Hold the cache to its block quota, returning evicted credits.
    ///
    /// A hard bound, and what keeps caching from starving production. Unlike
    /// [`Self::trim_cache`], which reacts to the observed free count and is
    /// opportunistic only.
    pub(super) fn enforce_cache_quota(&self, cache: &mut TraceCache<B::Allocator>) {
        for entry in cache.evict_to_fit(self.cache_quota_blocks) {
            trace!(
                "PROVER evicting cached {:?}[{}] to stay within the {} block cache quota",
                entry.circuit_type,
                entry.sequence_id,
                self.cache_quota_blocks
            );
            self.free_traces(entry.inits_and_teardowns, entry.tracing_data);
        }
        // AFTER eviction: sampling before would record the pre-eviction
        // high-water mark, which exceeds the quota by up to one whole entry.
        #[cfg(any(test, feature = "test_utils"))]
        self.peak_cached_blocks
            .fetch_max(cache.block_count(), std::sync::atomic::Ordering::Relaxed);
    }

    pub(super) fn trim_cache(&self, cache: &mut TraceCache<B::Allocator>) {
        let entries = &mut cache.entries;
        let min = self.configuration.min_free_host_allocators_per_job
            * self.configuration.expected_concurrent_jobs;
        while self.free_allocators_sender.len() < min && !entries.is_empty() {
            let evicted_entry = entries.pop_front().unwrap();
            let TraceCacheEntry {
                inits_and_teardowns,
                tracing_data,
                ..
            } = evicted_entry;
            self.free_traces(inits_and_teardowns, tracing_data);
        }
    }
}

/// Total host trace blocks, with the backend's extra allowance folded in.
/// Checked arithmetic: a wrap here builds an undersized pool, which surfaces
/// much later as a producer that never resumes.
fn total_host_allocators<B: ExecutionBackend>(
    configuration: &ExecutionProverConfiguration<B::Configuration>,
    backend: &B,
) -> Result<usize, ExecutionProverError> {
    let extra = backend.extra_trace_blocks();
    let total = configuration
        .expected_concurrent_jobs
        .checked_mul(configuration.host_allocators_per_job_count)
        .and_then(|per_job| per_job.checked_add(extra))
        .ok_or_else(|| {
            ExecutionProverError::invalid_configuration(
                "host_allocators_per_job_count",
                format!(
                    "expected_concurrent_jobs * host_allocators_per_job_count + {extra} backend blocks overflows"
                ),
            )
        })?;
    total
        .checked_mul(configuration.host_allocator_backing_allocation_size)
        .ok_or_else(|| {
            ExecutionProverError::invalid_configuration(
                "host_allocator_backing_allocation_size",
                format!(
                    "{total} blocks of {} bytes overflows the address space",
                    configuration.host_allocator_backing_allocation_size
                ),
            )
        })?;
    Ok(total)
}

/// Prepare every binary-independent circuit's backend state.
fn build_common_precomputations<B: ExecutionBackend>(
    backend: &B,
    worker: &Worker,
    security_level: SecurityLevel,
) -> Result<BTreeMap<CircuitType, B::Precomputations>, ExecutionProverError> {
    let mut out = BTreeMap::new();
    for (circuit_type, setup) in build_common_setups(worker) {
        let precomputations = backend.prepare(circuit_type, setup, security_level)?;
        out.insert(circuit_type, precomputations);
    }
    Ok(out)
}
