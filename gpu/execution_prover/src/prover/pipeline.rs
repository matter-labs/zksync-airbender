mod cache_seed;
mod results;

use super::*;
use cache_seed::seed_from_cache;
use results::{
    dispatch_gpu_requests, handle_work_result, maybe_close_gpu_sender_after_progress,
    RequestContext,
};

impl ExecutionProver {
    pub(super) fn get_result(
        &self,
        proving: bool,
        cache: &mut Option<TraceCache>,
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
        assert!(proving ^ external_challenges.is_none());
        let replayers_count = self.configuration.replay_worker_threads_count;
        let binary_holder = &self.binary_holders[&binary_key];
        let (work_results_sender, work_results_receiver) = unbounded();
        let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
        let (split_snapshot_sender, split_snapshot_receiver) = unbounded();
        let (unified_snapshot_sender, unified_snapshot_receiver) = unbounded();
        let gpu_work_batch = GpuWorkBatch {
            batch_id,
            receiver: gpu_work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        trace!("BATCH[{batch_id}] PROVER sending work batch to GPU manager");
        self.gpu_manager.send_batch(gpu_work_batch);
        let cache_seed = seed_from_cache(
            self,
            binary_holder,
            proving,
            cache,
            batch_id,
            external_challenges.as_ref(),
            &proof_caps,
            &gpu_work_requests_sender,
        );
        let mut pending_requests_count = cache_seed.pending_requests_count;
        let mut sent_requests_count = cache_seed.sent_requests_count;
        let requests_served_from_cache = cache_seed.requests_served_from_cache;
        let mut trivial_unified_inits_and_teardowns_count =
            cache_seed.trivial_unified_inits_and_teardowns_count;
        let trivial_unified_inits_and_teardowns = cache_seed.trivial_unified_inits_and_teardowns;
        let mut gpu_work_requests_sender = Some(gpu_work_requests_sender);
        let execution_kind = binary_holder.execution_kind;
        let machine_type = binary_holder.machine_type;
        let abort = Arc::new(AtomicBool::new(false));
        let mut simulation_result = None;
        let mut abort_signaled = if let Some(cache) = cache.as_ref() {
            if proving && cache.total_requests_count == sent_requests_count {
                gpu_work_requests_sender = None;
                simulation_result = cache.simulation_result.clone();
                true
            } else {
                false
            }
        } else {
            false
        };
        if abort_signaled {
            debug!(
                "BATCH[{batch_id}] all proof requests have been served from cache, skipping simulation"
            );
        } else {
            trace!("BATCH[{batch_id}] PROVER spawning SIMULATOR worker");
            let (free_trace_chunks_sender, free_trace_chunks_receiver) = unbounded();
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
                self.worker.pool.spawn(move || {
                    let mut memory_holder = {
                        let mut cache = memory_holders_cache
                            .lock()
                            .expect("ExecutionProver memory-holders cache mutex poisoned");
                        if cache.is_empty() {
                            drop(cache);
                            warn!("BATCH[{batch_id}] PROVER memory holders cache is empty, creating a new memory holder");
                            LockedBoxedMemoryHolder::new()
                        } else {
                            cache.pop().unwrap()
                        }
                    };
                    let trace_chunks_count = replayers_count * 2;
                    {
                        let mut cache = trace_chunks_cache
                            .lock()
                            .expect("ExecutionProver trace-chunks cache mutex poisoned");
                        let chunks = if cache.is_empty() {
                            drop(cache);
                            warn!("BATCH[{batch_id}] PROVER trace chunks cache is empty, creating a new set of trace chunks");
                            (0..trace_chunks_count)
                                .into_par_iter()
                                .map(|_| LockedBoxedTraceChunk::new())
                                .collect()
                        } else {
                            cache.pop().unwrap()
                        };
                        for chunk in chunks {
                            free_trace_chunks_sender.send(chunk).expect(
                                "ExecutionProver trace-chunk free list closed while seeding replay workers",
                            );
                        }
                    }
                    let free_trace_chunks_receiver_clone = free_trace_chunks_receiver.clone();
                    match execution_kind {
                        ExecutionKind::Unrolled => run_simulator::<_, SplitTracingType>(
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
                            &worker,
                        ),
                        ExecutionKind::Unified => run_simulator::<_, UnifiedTracingType>(
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
                            &worker,
                        ),
                    };
                    memory_holders_cache
                        .lock()
                        .expect("ExecutionProver memory-holders cache mutex poisoned")
                        .push(memory_holder);
                    let trace_chunks = free_trace_chunks_receiver_clone.iter().collect_vec();
                    assert_eq!(trace_chunks.len(), trace_chunks_count);
                    trace_chunks_cache
                        .lock()
                        .expect("ExecutionProver trace-chunks cache mutex poisoned")
                        .push(trace_chunks);
                });
            }
            trace!("BATCH[{batch_id}] PROVER spawning REPLAY workers");
            for worker_id in 0..replayers_count {
                let instruction_tape = binary_holder.instruction_tape.clone();
                let split_snapshot_receiver = split_snapshot_receiver.clone();
                let free_trace_chunks_sender = free_trace_chunks_sender.clone();
                let unified_snapshot_receiver = unified_snapshot_receiver.clone();
                let work_results_sender = work_results_sender.clone();
                let abort = abort.clone();
                self.worker.pool.spawn(move || match execution_kind {
                    ExecutionKind::Unrolled => run_replayer::<SplitTracingType>(
                        batch_id,
                        worker_id,
                        instruction_tape,
                        split_snapshot_receiver,
                        free_trace_chunks_sender,
                        work_results_sender,
                        abort,
                    ),
                    ExecutionKind::Unified => run_replayer::<UnifiedTracingType>(
                        batch_id,
                        worker_id,
                        instruction_tape,
                        unified_snapshot_receiver,
                        free_trace_chunks_sender,
                        work_results_sender,
                        abort,
                    ),
                });
            }
            drop(free_trace_chunks_sender);
        }
        drop(split_snapshot_receiver);
        drop(unified_snapshot_receiver);
        drop(work_results_sender);

        let request_context = RequestContext {
            proving,
            batch_id,
            binary_holder,
            external_challenges: external_challenges.as_ref(),
            proof_caps: &proof_caps,
        };
        let mut uninitialized_tracing_data = BTreeMap::new();
        let mut uninitialized_tracing_data_key_by_snapshot_index = BTreeMap::new();
        let mut processed_snapshots = BTreeSet::<usize>::new();
        let mut unpaired_unified_inits_and_teardowns = BTreeMap::new();
        let mut unpaired_unified_tracing_data = BTreeMap::new();
        let mut circuit_families_memory_caps = BTreeMap::new();
        let mut inits_and_teardowns_memory_caps = BTreeMap::new();
        let mut delegation_circuits_memory_caps = BTreeMap::new();
        let mut circuit_families_proofs = BTreeMap::new();
        let mut inits_and_teardowns_proofs = BTreeMap::new();
        let mut delegation_circuits_proofs = BTreeMap::new();
        for sequence_id in trivial_unified_inits_and_teardowns {
            let data = InitsAndTeardownsData {
                circuit_type: CircuitType::Unrolled(UnrolledCircuitType::Unified),
                sequence_id,
                inits_and_teardowns: None,
            };
            unpaired_unified_inits_and_teardowns.insert(sequence_id, data);
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
                    circuit_families_memory_caps.insert(family_idx, BTreeMap::new());
                    circuit_families_proofs.insert(family_idx, BTreeMap::new());
                }
            }
            ExecutionKind::Unified => {
                let family_idx = UnrolledCircuitType::Unified.get_family_idx();
                circuit_families_memory_caps.insert(family_idx, BTreeMap::new());
                circuit_families_proofs.insert(family_idx, BTreeMap::new());
            }
        }

        for work_result in work_results_receiver {
            let gpu_work_requests = handle_work_result(
                self,
                cache,
                work_result,
                &request_context,
                &mut pending_requests_count,
                &mut trivial_unified_inits_and_teardowns_count,
                &mut processed_snapshots,
                &mut uninitialized_tracing_data,
                &mut uninitialized_tracing_data_key_by_snapshot_index,
                &mut unpaired_unified_inits_and_teardowns,
                &mut unpaired_unified_tracing_data,
                &mut simulation_result,
                &mut circuit_families_memory_caps,
                &mut inits_and_teardowns_memory_caps,
                &mut delegation_circuits_memory_caps,
                &mut circuit_families_proofs,
                &mut inits_and_teardowns_proofs,
                &mut delegation_circuits_proofs,
            );
            dispatch_gpu_requests(
                self,
                &requests_served_from_cache,
                gpu_work_requests,
                &gpu_work_requests_sender,
                &mut pending_requests_count,
                &mut sent_requests_count,
            );
            maybe_close_gpu_sender_after_progress(
                cache,
                &mut gpu_work_requests_sender,
                sent_requests_count,
                &mut abort_signaled,
                &mut simulation_result,
                &uninitialized_tracing_data,
                &unpaired_unified_inits_and_teardowns,
                &unpaired_unified_tracing_data,
                &abort,
                proving,
                batch_id,
            );
        }

        assert_eq!(pending_requests_count, 0);
        if abort_signaled {
            uninitialized_tracing_data.into_values().for_each(|data| {
                self.free_tracing_data(data.tracing_data);
            });
            unpaired_unified_inits_and_teardowns
                .into_values()
                .for_each(|data| {
                    if let Some(inits_and_teardowns) = data.inits_and_teardowns {
                        self.free_inits_and_teardowns(inits_and_teardowns);
                    }
                });
            unpaired_unified_tracing_data
                .into_values()
                .for_each(|data| {
                    self.free_tracing_data(data.tracing_data);
                });
        } else {
            assert!(uninitialized_tracing_data.is_empty());
            assert!(unpaired_unified_inits_and_teardowns.is_empty());
            assert!(unpaired_unified_tracing_data.is_empty());
        }
        if let Some(cache) = cache.as_mut() {
            if proving {
                assert!(cache.is_empty())
            } else {
                cache.total_requests_count = sent_requests_count;
                cache.trivial_unified_inits_and_teardowns_count =
                    trivial_unified_inits_and_teardowns_count;
                cache.simulation_result = simulation_result.clone();
            }
        }
        let SimulationResult {
            final_register_values,
            final_pc,
            final_timestamp,
        } = simulation_result.expect("simulation result must be present before get_result returns");
        if proving {
            let circuit_families_proofs = circuit_families_proofs
                .into_iter()
                .map(|(i, v)| (i, v.into_values().collect_vec()))
                .collect();
            let inits_and_teardowns_proofs = inits_and_teardowns_proofs
                .into_iter()
                .map(|(_, v)| v)
                .collect_vec();
            let delegation_circuits_proofs = delegation_circuits_proofs
                .into_iter()
                .map(|(i, v)| (i, v.into_values().collect_vec()))
                .collect();
            let circuit_families_proofs: BTreeMap<_, Vec<_>> = circuit_families_proofs;
            // Unified mode: real inits-and-teardowns circuits are the trailing
            // ones; everything before `trivial_unified_inits_and_teardowns_count`
            // is a dummy marker.
            let num_unified_it_circuits = circuit_families_proofs
                .get(&UnrolledCircuitType::Unified.get_family_idx())
                .map(|unified_proofs| {
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
            let circuit_families_memory_caps = circuit_families_memory_caps
                .into_iter()
                .map(|(i, v)| (i, v.into_values().collect_vec()))
                .collect();
            let inits_and_teardowns_memory_caps = inits_and_teardowns_memory_caps
                .into_iter()
                .map(|(_, v)| v)
                .collect_vec();
            let delegation_circuits_memory_caps = delegation_circuits_memory_caps
                .into_iter()
                .map(|(i, v)| (i, v.into_values().collect_vec()))
                .collect();
            let result = CommitMemoryResult {
                final_register_values,
                final_pc,
                final_timestamp,
                circuit_families_memory_caps,
                inits_and_teardowns_memory_caps,
                delegation_circuits_memory_caps,
                binary_handle: BinaryHandle(binary_key),
            };
            ExecutionProverResult::CommitMemory(result)
        }
    }

    pub(super) fn commit_memory_inner(
        &self,
        cache: &mut Option<TraceCache>,
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
        cache: &mut Option<TraceCache>,
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
