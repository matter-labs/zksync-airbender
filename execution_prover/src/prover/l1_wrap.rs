use super::*;
use crate::messages::L1WrapProofRequest;
use crate::workers::simulation::assert_l1_wrap_geometry;
use ::prover::field::Proth120;
use ::prover::gkr::prover::GKRProof;
use ::prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
};
use ::prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::{UnrolledTracingDataHost, UnrolledUnifiedTraceHost};

pub type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

#[derive(Clone, Debug)]
pub struct L1WrapResult {
    pub proof: L1Proof,
    pub commitment_mode: CommitmentMode,
}

struct L1WrapTrace<A: HostTraceAllocator> {
    tracing_data: UnrolledUnifiedTraceHost<A>,
    inits_and_teardowns: InitsAndTeardownsTraceHost<A>,
    simulation: SimulationResult,
}

fn collect_l1_wrap_trace<A: HostTraceAllocator>(
    results: impl IntoIterator<Item = WorkerResult<A>>,
) -> L1WrapTrace<A> {
    let mut traces = Vec::new();
    let mut inits = Vec::new();
    let mut simulation = None;
    let mut replayed = BTreeSet::new();
    for result in results {
        match result {
            WorkerResult::SnapshotProduced => {}
            WorkerResult::TracingData(data) => traces.push(data),
            WorkerResult::InitsAndTeardownsData(data) => inits.push(data),
            WorkerResult::SimulationResult(result) => {
                assert!(
                    simulation.replace(result).is_none(),
                    "duplicate L1Wrap simulation result"
                );
            }
            WorkerResult::SnapshotReplayed(index) => {
                assert!(replayed.insert(index), "duplicate L1Wrap replay completion");
            }
            WorkerResult::BackendWorkResult(_) => {
                panic!("unexpected backend result during L1Wrap tracing")
            }
        }
    }
    assert!(
        traces
            .iter()
            .all(|data| !matches!(data.circuit_type, CircuitType::Delegation(_))),
        "L1Wrap does not support delegation calls"
    );
    assert_l1_wrap_geometry(traces.len(), inits.len());
    let trace = traces.pop().unwrap();
    assert_eq!(
        trace.circuit_type,
        CircuitType::L1Wrap,
        "L1Wrap requires its own trace geometry"
    );
    assert_eq!(
        trace.sequence_id, 0,
        "L1Wrap needs exactly one unified chunk"
    );
    assert!(
        trace.participating_snapshot_indexes.is_subset(&replayed),
        "L1Wrap trace has unfinished replay snapshots"
    );
    let TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(tracing_data)) =
        trace.tracing_data
    else {
        panic!("L1Wrap requires a unified trace");
    };
    assert!(
        tracing_data.len() <= CircuitType::L1Wrap.get_domain_size(),
        "L1Wrap needs exactly one unified chunk"
    );
    let inits = inits.pop().unwrap();
    assert_eq!(
        inits.circuit_type,
        CircuitType::L1Wrap,
        "L1Wrap requires its own I&T geometry"
    );
    assert_eq!(
        inits.sequence_id, 0,
        "L1Wrap touched more than one inits/teardowns instance"
    );
    let inits_and_teardowns = inits
        .inits_and_teardowns
        .expect("L1Wrap requires inits/teardowns data");
    assert_eq!(
        inits_and_teardowns.top_bits.len(),
        CircuitType::L1Wrap.get_num_inits_and_teardowns_sets(),
        "L1Wrap requires two inits/teardowns sets"
    );
    L1WrapTrace {
        tracing_data,
        inits_and_teardowns,
        simulation: simulation.expect("L1Wrap simulation did not complete"),
    }
}

impl<B: ExecutionBackend> ExecutionProver<B> {
    pub fn prove_l1_wrap<ND: NonDeterminismCSRSource + Send + 'static>(
        &self,
        batch_id: u64,
        handle: &BinaryHandle,
        non_determinism: ND,
    ) -> L1WrapResult {
        let holder = &self.binary_holders[&handle.0];
        assert_eq!(
            holder.execution_kind,
            ExecutionKind::L1Wrap,
            "prove_l1_wrap requires ExecutionKind::L1Wrap"
        );
        assert_eq!(
            holder.profiles,
            [ProofProfile::L1Wrap],
            "ExecutionKind::L1Wrap requires exactly ProofProfile::L1Wrap"
        );
        let (sender, receiver) = unbounded();
        self.spawn_simulation_workers(
            batch_id,
            holder,
            Arc::new(Mutex::new(Some(non_determinism))),
            &sender,
            &Arc::new(AtomicBool::new(false)),
        );
        drop(sender);
        let trace = collect_l1_wrap_trace(receiver);
        self.prove_l1_wrap_trace(batch_id, holder, trace)
    }

    fn prove_l1_wrap_trace(
        &self,
        batch_id: u64,
        holder: &BinaryHolder<B>,
        trace: L1WrapTrace<B::Allocator>,
    ) -> L1WrapResult {
        let commitment_mode = CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2: EVM_PRODUCTION_PACK_LOG2,
            external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
            final_pc: trace.simulation.final_pc,
            final_timestamp: trace.simulation.final_timestamp,
            register_final_state: trace.simulation.final_register_values,
        };
        let (request_sender, request_receiver) = unbounded();
        let (result_sender, result_receiver) = unbounded();
        self.backend.submit(WorkBatch {
            batch_id,
            receiver: request_receiver,
            sender: result_sender,
        });
        request_sender
            .send(WorkRequest::L1WrapProof(L1WrapProofRequest {
                batch_id,
                precomputations: holder
                    .l1_wrap_precomputations
                    .as_ref()
                    .expect("L1Wrap setup was not registered")
                    .clone(),
                inits_and_teardowns: trace.inits_and_teardowns,
                tracing_data: trace.tracing_data,
                commitment_mode,
            }))
            .expect("backend rejected L1Wrap proof request");
        drop(request_sender);
        let mut output = None;
        for result in result_receiver {
            let WorkerResult::BackendWorkResult(WorkResult::L1WrapProof(result)) = result else {
                panic!("unexpected backend result during L1Wrap proving");
            };
            assert_eq!(
                result.batch_id, batch_id,
                "L1Wrap result has wrong batch ID"
            );
            assert_eq!(
                result.result.commitment_mode, commitment_mode,
                "L1Wrap result changed commitment-mode boundary state"
            );
            self.free_traces(
                Some(result.inits_and_teardowns),
                Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(
                    result.tracing_data,
                ))),
            );
            assert!(
                output.replace(result.result).is_none(),
                "duplicate L1Wrap proof result"
            );
        }
        output.expect("backend terminated before producing the L1Wrap proof")
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::test_support::{TestBackend, TestConfiguration, TestPrecomputations, PROFILES};
    use execution_prover_model::allocator::CpuTraceAllocator;
    use execution_prover_model::trace::ChunkedTraceHolder;

    fn events() -> Vec<WorkerResult<CpuTraceAllocator>> {
        vec![
            WorkerResult::TracingData(TracingData {
                circuit_type: CircuitType::L1Wrap,
                sequence_id: 0,
                tracing_data: TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(
                    ChunkedTraceHolder { chunks: vec![] },
                )),
                participating_snapshot_indexes: BTreeSet::from([0, 2]),
            }),
            WorkerResult::InitsAndTeardownsData(InitsAndTeardownsData {
                circuit_type: CircuitType::L1Wrap,
                sequence_id: 0,
                inits_and_teardowns: Some(InitsAndTeardownsTraceHost {
                    page_indices: ChunkedTraceHolder { chunks: vec![] },
                    values_packed: ChunkedTraceHolder { chunks: vec![] },
                    timestamps_packed: ChunkedTraceHolder { chunks: vec![] },
                    top_bits: vec![0, 1],
                }),
            }),
            WorkerResult::SimulationResult(SimulationResult {
                final_pc: 42,
                final_timestamp: 100,
                final_register_values: [FinalRegisterValue {
                    value: 0,
                    last_access_timestamp: 0,
                }; 32],
            }),
            WorkerResult::SnapshotReplayed(2),
            WorkerResult::SnapshotReplayed(0),
        ]
    }

    #[test]
    fn delayed_out_of_order_replay_is_drained_before_consuming_trace() {
        let trace = collect_l1_wrap_trace(events());
        assert_eq!(trace.simulation.final_pc, 42);
        assert_eq!(trace.inits_and_teardowns.top_bits, [0, 1]);
    }

    #[test]
    #[should_panic(expected = "L1Wrap trace has unfinished replay snapshots")]
    fn missing_replay_is_rejected() {
        let mut events = events();
        events.pop();
        collect_l1_wrap_trace(events);
    }

    #[test]
    #[should_panic(expected = "L1Wrap needs exactly one unified chunk")]
    fn multiple_chunks_are_rejected() {
        let trace = events().remove(0);
        let mut events = events();
        events.push(trace);
        collect_l1_wrap_trace(events);
    }

    #[test]
    #[should_panic(expected = "L1Wrap touched more than one inits/teardowns instance")]
    fn multiple_it_instances_are_rejected() {
        let extra = events().remove(1);
        let mut events = events();
        events.push(extra);
        collect_l1_wrap_trace(events);
    }

    #[test]
    #[should_panic(expected = "L1Wrap does not support delegation calls")]
    fn delegation_calls_are_rejected() {
        let mut events = events();
        let WorkerResult::TracingData(trace) = &mut events[0] else {
            unreachable!()
        };
        trace.circuit_type = CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression);
        collect_l1_wrap_trace(events);
    }

    fn light_prover() -> ExecutionProver<TestBackend> {
        let mut configuration = ExecutionProverConfiguration::<TestConfiguration>::default();
        configuration.host_allocators_per_job_count = 8;
        configuration.host_allocator_backing_allocation_size = 64 << 10;
        let worker = Arc::new(Worker::new_with_num_threads(1));
        let backend = TestBackend::initialize(&configuration, worker.clone());
        let (memory_holders_sender, memory_holders_receiver) = unbounded();
        memory_holders_sender
            .send(backend.allocate_memory(configuration.ram_config))
            .unwrap();
        let (trace_chunk_sets_sender, trace_chunk_sets_receiver) = unbounded();
        trace_chunk_sets_sender
            .send(vec![
                backend.allocate_snapshot(),
                backend.allocate_snapshot(),
            ])
            .unwrap();
        let (free_allocators_sender, free_allocators_receiver) = unbounded();
        for _ in 0..configuration.host_allocators_per_job_count {
            free_allocators_sender
                .send(
                    backend
                        .allocate_trace_block(configuration.host_allocator_backing_allocation_size),
                )
                .unwrap();
        }
        let program = vec![0x0001_2083, 0xffdf_f06f];
        let tape = SimpleTape::new(&preprocess_bytecode::<ReducedMachineDecoderConfig, true>(
            &program,
        ));
        let holder = BinaryHolder {
            execution_kind: ExecutionKind::L1Wrap,
            profiles: vec![ProofProfile::L1Wrap],
            machine_type: MachineType::Reduced,
            binary_image: Arc::new(program.clone().into_boxed_slice()),
            text_section: Arc::new(program.into_boxed_slice()),
            cycles_bound: Some(32),
            jit_cache: Default::default(),
            instruction_tape: Arc::new(tape),
            precomputations: HashMap::new(),
            l1_wrap_precomputations: Some(TestPrecomputations(None)),
        };
        ExecutionProver {
            configuration,
            backend,
            worker,
            memory_holders_sender,
            memory_holders_receiver,
            trace_chunk_sets_sender,
            trace_chunk_sets_receiver,
            binary_holders: BTreeMap::from([(0, holder)]),
            next_binary_id: 1,
            common_precomputations: BTreeMap::new(),
            free_allocators_sender,
            free_allocators_receiver,
        }
    }

    #[test]
    fn single_pass_wrap_reuses_batch_id_and_returns_the_allocator_pool() {
        const BATCH: u64 = 9104;
        let prover = light_prover();
        for _ in 0..2 {
            let result = prover.prove_l1_wrap(
                BATCH,
                &BinaryHandle(0),
                riscv_transpiler::vm::FlatResponsesSource::new_with_reads(vec![]),
            );
            let CommitmentMode::MergedAndPackedMemoryAndWitness {
                final_timestamp,
                pack_log2,
                external_challenges_pow_bits,
                ..
            } = result.commitment_mode
            else {
                panic!("wrong mode")
            };
            assert_eq!(
                final_timestamp,
                common_constants::INITIAL_TIMESTAMP + 32 * common_constants::TIMESTAMP_STEP
            );
            assert_eq!(pack_log2, EVM_PRODUCTION_PACK_LOG2);
            assert_eq!(
                external_challenges_pow_bits,
                EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS
            );
            assert_eq!(prover.free_allocators_receiver.len(), 8);
        }
        let records = PROFILES.lock().unwrap();
        let wraps: Vec<_> = records
            .iter()
            .filter(|(batch, ..)| *batch == BATCH)
            .copied()
            .collect();
        assert_eq!(
            wraps,
            vec![(BATCH, CircuitType::L1Wrap, true, ProofProfile::L1Wrap); 2]
        );
    }

    #[test]
    #[should_panic(expected = "program_artifacts is not defined for ExecutionKind::L1Wrap")]
    fn baby_bear_artifacts_are_rejected_for_l1_wrap() {
        light_prover().program_artifacts(&BinaryHandle(0), ProofProfile::L1Wrap);
    }
}
