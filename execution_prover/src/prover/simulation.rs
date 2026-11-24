//! The simulator and replay workers that trace an execution for both the
//! BabyBear pipeline and the Proth120 wrap.

use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Spawn the simulator worker plus `replay_worker_threads_count` replay
    /// workers onto their own threads. Owns the snapshot / free-trace-chunk
    /// channels for the duration of the spawn; the workers keep their own
    /// clones, so the originals are dropped here once every worker is queued.
    pub(super) fn spawn_simulation_workers<ND: NonDeterminismCSRSource + Send + 'static>(
        &self,
        batch_id: u64,
        binary_holder: &BinaryHolder<B>,
        non_determinism_source: ND,
        work_results_sender: &Sender<WorkerResult<B::Allocator>>,
        abort: &Arc<AtomicBool>,
    ) -> Receiver<ND> {
        let (non_determinism_sender, non_determinism_receiver) = crossbeam_channel::bounded(1);
        let unified_circuit = binary_holder
            .execution_kind
            .unified_circuit_in_mode(self.configuration.soundness_mode)
            .unwrap_or(CircuitType::Unrolled(UnrolledCircuitType::Unified));
        let replayers_count = self.configuration.replay_worker_threads_count;
        let execution_kind = binary_holder.execution_kind;
        let machine_type = binary_holder.machine_type;
        let (split_snapshot_sender, split_snapshot_receiver) = unbounded();
        let (unified_snapshot_sender, unified_snapshot_receiver) = unbounded();
        trace!("BATCH[{batch_id}] PROVER spawning SIMULATOR worker");
        let (free_trace_chunks_sender, free_trace_chunks_receiver) = unbounded();
        {
            let memory_holders_sender = self.memory_holders_sender.clone();
            let memory_holders_receiver = self.memory_holders_receiver.clone();
            let trace_chunk_sets_sender = self.trace_chunk_sets_sender.clone();
            let trace_chunk_sets_receiver = self.trace_chunk_sets_receiver.clone();
            let free_trace_chunks_sender = free_trace_chunks_sender.clone();
            let free_allocators_receiver = self.free_allocators_receiver.clone();
            let binary_image = binary_holder.binary_image.clone();
            let text_section = binary_holder.text_section.clone();
            let cycles_bound = if binary_holder.execution_kind.is_l1_wrap() {
                let limit = unified_circuit.get_domain_size() as u32 + 1;
                Some(binary_holder.cycles_bound.unwrap_or(limit).min(limit))
            } else {
                binary_holder.cycles_bound
            };
            let jit_cache = binary_holder.jit_cache.clone();
            let work_results_sender = work_results_sender.clone();
            let abort = abort.clone();
            let worker = self.worker.clone();
            let ram_config = self.configuration.ram_config;
            let assume_canonical_mop_inputs = self.configuration.assume_canonical_mop_inputs;
            spawn_abort_on_panic(format!("ab-simulator-{batch_id}"), move || {
                let mut memory_holder = memory_holders_receiver
                    .recv()
                    .expect("ExecutionProver memory holders channel closed");
                let trace_chunks_count = replayers_count * 2;
                let chunks = trace_chunk_sets_receiver
                    .recv()
                    .expect("ExecutionProver trace chunks channel closed");
                for chunk in chunks {
                    free_trace_chunks_sender.send(chunk).expect(
                        "ExecutionProver trace-chunk free list closed while seeding replay workers",
                    );
                }
                let free_trace_chunks_receiver_clone = free_trace_chunks_receiver.clone();
                match execution_kind {
                    ExecutionKind::Unrolled => run_simulator::<_, SplitTracingType, _, _, _>(
                        batch_id,
                        machine_type,
                        unified_circuit,
                        binary_image,
                        text_section,
                        cycles_bound,
                        jit_cache,
                        &mut memory_holder,
                        non_determinism_source,
                        non_determinism_sender,
                        free_trace_chunks_sender,
                        free_trace_chunks_receiver,
                        split_snapshot_sender,
                        work_results_sender,
                        free_allocators_receiver,
                        abort,
                        &worker,
                        ram_config,
                        assume_canonical_mop_inputs,
                    ),
                    ExecutionKind::Unified | ExecutionKind::Unified22 | ExecutionKind::L1Wrap => {
                        run_simulator::<_, UnifiedTracingType, _, _, _>(
                            batch_id,
                            machine_type,
                            unified_circuit,
                            binary_image,
                            text_section,
                            cycles_bound,
                            jit_cache,
                            &mut memory_holder,
                            non_determinism_source,
                            non_determinism_sender,
                            free_trace_chunks_sender,
                            free_trace_chunks_receiver,
                            unified_snapshot_sender,
                            work_results_sender,
                            free_allocators_receiver,
                            abort,
                            &worker,
                            ram_config,
                            assume_canonical_mop_inputs,
                        )
                    }
                };
                memory_holders_sender
                    .send(memory_holder)
                    .expect("ExecutionProver memory holders channel closed");
                let trace_chunks = free_trace_chunks_receiver_clone.iter().collect_vec();
                assert_eq!(trace_chunks.len(), trace_chunks_count);
                trace_chunk_sets_sender
                    .send(trace_chunks)
                    .expect("ExecutionProver trace chunks channel closed");
            });
        }
        trace!("BATCH[{batch_id}] PROVER spawning REPLAY workers");
        let rom = unified_circuit.rom();
        for worker_id in 0..replayers_count {
            let instruction_tape = binary_holder.instruction_tape.clone();
            let split_snapshot_receiver = split_snapshot_receiver.clone();
            let free_trace_chunks_sender = free_trace_chunks_sender.clone();
            let unified_snapshot_receiver = unified_snapshot_receiver.clone();
            let work_results_sender = work_results_sender.clone();
            let abort = abort.clone();
            let name = format!("ab-replay-{batch_id}-{worker_id}");
            spawn_abort_on_panic(name, move || match execution_kind {
                ExecutionKind::Unrolled => run_replayer::<SplitTracingType, _, _>(
                    batch_id,
                    worker_id,
                    rom,
                    instruction_tape,
                    split_snapshot_receiver,
                    free_trace_chunks_sender,
                    work_results_sender,
                    abort,
                ),
                ExecutionKind::Unified | ExecutionKind::Unified22 | ExecutionKind::L1Wrap => {
                    run_replayer::<UnifiedTracingType, _, _>(
                        batch_id,
                        worker_id,
                        rom,
                        instruction_tape,
                        unified_snapshot_receiver,
                        free_trace_chunks_sender,
                        work_results_sender,
                        abort,
                    )
                }
            });
        }
        drop(free_trace_chunks_sender);
        non_determinism_receiver
    }
}
