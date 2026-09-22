use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
    }

    pub fn with_configuration(
        configuration: ExecutionProverConfiguration<B::Configuration>,
    ) -> Self {
        configuration.validate();

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

        let backend = B::initialize(&configuration, Arc::clone(&worker));

        let simulator_cache_entries_count = configuration.expected_concurrent_jobs + 1;
        info!("PROVER creating memory holders cache with {simulator_cache_entries_count} entries");
        let (memory_holders_sender, memory_holders_receiver) = unbounded();
        // Each holder is a zeroed guest RAM registered with the backend; the
        // registrations are slow and independent, so they run side by side.
        std::thread::scope(|scope| {
            for _ in 0..simulator_cache_entries_count {
                let memory_holders_sender = memory_holders_sender.clone();
                let backend = &backend;
                let ram_config = configuration.ram_config;
                scope.spawn(move || {
                    memory_holders_sender
                        .send(backend.allocate_memory(ram_config))
                        .unwrap()
                });
            }
        });

        let trace_chunks_count = configuration.replay_worker_threads_count * 2;
        info!(
            "PROVER creating trace chunks cache with {simulator_cache_entries_count} x {trace_chunks_count} entries"
        );
        let (trace_chunk_sets_sender, trace_chunk_sets_receiver) = unbounded();
        for _ in 0..simulator_cache_entries_count {
            let chunks: Vec<_> = (0..trace_chunks_count)
                .map(|_| backend.allocate_snapshot())
                .collect();
            trace_chunk_sets_sender.send(chunks).unwrap();
        }

        let binary_holders = BTreeMap::new();
        info!("PROVER generating common precomputations");
        let common_precomputations: BTreeMap<_, _> = build_common_setups(&worker)
            .into_iter()
            .map(|(circuit_type, setup)| {
                let precomputations =
                    backend.prepare(circuit_type, setup, configuration.security_level);
                (circuit_type, precomputations)
            })
            .collect();
        let pending_setup_initialization = request_setup_initialization(
            &backend,
            configuration.security_level,
            common_precomputations
                .iter()
                .map(|(circuit_type, precomputations)| (*circuit_type, precomputations.clone()))
                .collect(),
        );

        let host_allocators_count = configuration.expected_concurrent_jobs
            * configuration.host_allocators_per_job_count
            + backend.extra_trace_blocks();
        info!(
            "PROVER initializing {} host buffers with {} MB per buffer",
            host_allocators_count,
            configuration.host_allocator_backing_allocation_size >> 20
        );
        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        for _ in 0..host_allocators_count {
            free_allocators_sender
                .send(
                    backend
                        .allocate_trace_block(configuration.host_allocator_backing_allocation_size),
                )
                .unwrap();
        }

        pending_setup_initialization.wait();
        info!("PROVER initialized");
        Self {
            backend,
            configuration,
            worker,
            memory_holders_sender,
            memory_holders_receiver,
            trace_chunk_sets_sender,
            trace_chunk_sets_receiver,
            binary_holders,
            next_binary_id: 0,
            common_precomputations,
            free_allocators_sender,
            free_allocators_receiver,
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
