use super::*;

impl ExecutionProver {
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
            .expect("default ExecutionProverConfiguration must use a supported GPU security level")
    }

    pub fn with_configuration(
        configuration: ExecutionProverConfiguration,
    ) -> Result<Self, UnsupportedGpuSecurityLevel> {
        // The JIT simulator picks the MOP (Zimop) prime field from
        // `RISCV_MOP_FIELD` at each build, DEFAULTING TO M31
        // (`riscv_transpiler::jit::impls::mop_field`). This prover stack is
        // BabyBear end to end — the replay worker replays with
        // `gpu_core::primitives::field::BF` (= BabyBearField, workers/cpu.rs)
        // and the GKR circuits' MOP tables are BabyBear — so an M31-JIT
        // simulation silently diverges from the traced witness on any
        // mop-bearing binary. The per-circuit proofs stay self-consistent and
        // the divergence only surfaces as a global memory-permutation closure
        // failure in the full-statement verifier. Pin the JIT field before any
        // worker thread can build jitted code.
        std::env::set_var("RISCV_MOP_FIELD", "babybear");
        let configuration = configuration.validate()?;
        let ExecutionProverConfiguration {
            prover_context_config,
            max_thread_pool_threads,
            expected_concurrent_jobs,
            replay_worker_threads_count,
            host_allocator_backing_allocation_size,
            host_allocators_per_job_count,
            host_allocators_per_device_count,
            min_free_host_allocators_per_job: _,
            security_level,
        } = configuration;
        let device_count = get_device_count().expect("CUDA device count query failed") as usize;
        assert_ne!(device_count, 0, "no CUDA capable devices found");
        let gpu_wait_group = WaitGroup::new();
        let gpu_manager = GpuManager::new(gpu_wait_group.clone(), prover_context_config);
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
        let simulator_cache_entries_count = expected_concurrent_jobs + 1;
        info!("PROVER creating memory holders cache with {simulator_cache_entries_count} entries");
        let memory_holders_cache = (0..simulator_cache_entries_count)
            .into_par_iter()
            .map(|_| LockedBoxedMemoryHolder::new())
            .collect();
        let memory_holders_cache = Arc::new(Mutex::new(memory_holders_cache));
        let trace_chunks_count = replay_worker_threads_count * 2;
        info!(
            "PROVER creating trace chunks cache with {simulator_cache_entries_count} x {trace_chunks_count} entries"
        );
        let trace_chunks_cache = (0..simulator_cache_entries_count)
            .into_par_iter()
            .map(|_| {
                (0..trace_chunks_count)
                    .into_par_iter()
                    .map(|_| LockedBoxedTraceChunk::new())
                    .collect()
            })
            .collect();
        let trace_chunks_cache = Arc::new(Mutex::new(trace_chunks_cache));
        let binary_holders = BTreeMap::new();
        info!("PROVER generating common precomputations");
        let common_precomputations = get_common_precomputations_for_all(&worker, security_level);
        let host_allocators_count = expected_concurrent_jobs * host_allocators_per_job_count
            + device_count * host_allocators_per_device_count;
        let host_allocation_size = host_allocator_backing_allocation_size;
        let host_allocation_log_chunk_size = host_allocation_size.trailing_zeros();
        info!(
            "PROVER initializing {} host buffers with {} MB per buffer",
            host_allocators_count,
            host_allocation_size >> 20
        );
        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        let free_allocators_sender_ref = &free_allocators_sender;
        (0..host_allocators_count).into_par_iter().for_each(|_| {
            let allocation =
                HostAllocation::alloc(host_allocation_size, CudaHostAllocFlags::DEFAULT)
                    .expect("pinned host allocation for ExecutionProver pool failed");
            let allocator = A::new([allocation], host_allocation_log_chunk_size);
            free_allocators_sender_ref
                .send(allocator)
                .expect("ExecutionProver allocator pool channel closed during initialization");
        });
        gpu_wait_group.wait();
        info!("PROVER initialized");
        Ok(Self {
            configuration,
            gpu_manager,
            worker,
            memory_holders_cache,
            trace_chunks_cache,
            binary_holders,
            next_binary_id: 0,
            common_precomputations,
            free_allocators_sender,
            free_allocators_receiver,
        })
    }

    pub(super) fn free_inits_and_teardowns(&self, inits_and_teardowns: InitsAndTeardownsTraceHost) {
        for allocator in inits_and_teardowns.into_allocators() {
            self.free_allocators_sender.send(allocator).expect(
                "ExecutionProver allocator return channel closed during init/teardown free",
            );
        }
    }

    pub(super) fn free_tracing_data(&self, tracing_data: TracingDataHost<A>) {
        for allocator in tracing_data.into_allocators() {
            self.free_allocators_sender
                .send(allocator)
                .expect("ExecutionProver allocator return channel closed during tracing-data free");
        }
    }

    pub(super) fn free_traces(
        &self,
        inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
        tracing_data: Option<TracingDataHost<A>>,
    ) {
        if let Some(inits_and_teardowns) = inits_and_teardowns {
            self.free_inits_and_teardowns(inits_and_teardowns);
        }
        if let Some(tracing_data) = tracing_data {
            self.free_tracing_data(tracing_data);
        }
    }

    pub(super) fn trim_cache(&self, cache: &mut TraceCache) {
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
