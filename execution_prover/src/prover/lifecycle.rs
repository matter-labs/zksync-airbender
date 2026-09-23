use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
    }

    pub fn with_configuration(
        configuration: ExecutionProverConfiguration<B::Configuration>,
    ) -> Self {
        let ExecutionProverConfiguration {
            max_thread_pool_threads,
            expected_concurrent_jobs,
            replay_worker_threads_count,
            host_allocator_backing_allocation_size,
            host_allocators_per_job_count,
            min_free_host_allocators_per_job: _,
            security_level,
            ram_config,
            backend: _,
        } = configuration;
        let worker = if let Some(thread_pool_threads_count) = max_thread_pool_threads {
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
        let simulator_cache_entries_count = expected_concurrent_jobs + 1;
        info!("PROVER creating memory holders cache with {simulator_cache_entries_count} entries");
        let (memory_holders_sender, memory_holders_receiver) = unbounded();
        // Each holder is a zeroed guest RAM registered with the backend; the
        // registrations are slow and independent, so they run side by side.
        std::thread::scope(|scope| {
            for _ in 0..simulator_cache_entries_count {
                let memory_holders_sender = memory_holders_sender.clone();
                let backend = &backend;
                scope.spawn(move || {
                    memory_holders_sender
                        .send(backend.allocate_memory(ram_config))
                        .unwrap()
                });
            }
        });
        let trace_chunks_count = replay_worker_threads_count * 2;
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
                (
                    circuit_type,
                    backend.prepare(circuit_type, setup, security_level),
                )
            })
            .collect();
        let pending_setup_initialization = request_setup_initialization(
            &backend,
            security_level,
            common_precomputations
                .iter()
                .map(|(circuit_type, precomputations)| (*circuit_type, precomputations.clone()))
                .collect(),
        );
        let host_allocators_count =
            expected_concurrent_jobs * host_allocators_per_job_count + backend.extra_trace_blocks();
        let host_allocation_size = host_allocator_backing_allocation_size;
        info!(
            "PROVER initializing {} host buffers with {} MB per buffer",
            host_allocators_count,
            host_allocation_size >> 20
        );
        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        for _ in 0..host_allocators_count {
            free_allocators_sender
                .send(backend.allocate_trace_block(host_allocation_size))
                .expect("ExecutionProver allocator pool channel closed during initialization");
        }
        pending_setup_initialization.wait();
        info!("PROVER initialized");
        Self {
            configuration,
            backend,
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
