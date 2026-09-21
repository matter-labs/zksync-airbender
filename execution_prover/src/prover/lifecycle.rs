use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Starts workers and allocates prover resources.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
            .expect("the default ExecutionProverConfiguration must be valid")
    }

    pub fn with_configuration(
        configuration: ExecutionProverConfiguration<B::Configuration>,
    ) -> Result<Self, ExecutionProverError> {
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

        // Detect unavailable backend resources before expensive setup construction.
        let backend = B::initialize(&configuration, Arc::clone(&worker))?;

        // Device-dependent reserves are known only after backend initialization.
        let host_allocators_count =
            configuration.total_host_allocators(backend.extra_trace_blocks())?;

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
        let admission = configuration.admission_limit().map(Admission::new);
        Ok(Self {
            backend,
            configuration,
            worker,
            memory_holders_cache,
            trace_chunks_cache,
            admission,
            binary_holders,
            next_binary_id: 0,
            common_precomputations,
            free_allocators_sender,
            free_allocators_receiver,
            terminal_failure: Mutex::new(None),
        })
    }

    pub(super) fn ensure_usable(&self) {
        // Release the lock before panicking to preserve the original error.
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

    pub(super) fn trim_cache(&self, cache: &mut TraceCache<B::Allocator>) {
        let min = self.configuration.min_free_host_allocators_per_job
            * self.configuration.expected_concurrent_jobs;
        while self.free_allocators_sender.len() < min && !cache.entries.is_empty() {
            let entry = cache.entries.pop_front().unwrap();
            trace!(
                "PROVER evicting cached {:?}[{}] to refill the free pool",
                entry.circuit_type,
                entry.sequence_id
            );
            self.free_traces(entry.inits_and_teardowns, entry.tracing_data);
        }
    }
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
