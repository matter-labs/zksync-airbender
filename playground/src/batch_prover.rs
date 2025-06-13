use crate::cpu_worker::{
    get_cpu_worker_func, CpuWorkerMode, CyclesChunk, NonDeterminism, SetupAndTeardownChunk,
};
use crate::gpu_manager::{GpuManager, GpuWorkBatch};
use crate::gpu_worker::{
    GpuWorkRequest, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest, ProofResult,
};
use crate::messages::WorkerResult;
use crate::precomputations::CircuitPrecomputationsHost;
use crate::tracer::CycleTracingData;
use crossbeam_channel::{unbounded, Sender};
use fft::GoodAllocator;
use field::{Field, Mersenne31Field, Mersenne31Quartic};
use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::circuit_type::{CircuitType, DelegationCircuitType, MainCircuitType};
use gpu_prover::prover::context::{MemPoolProverContext, ProverContext};
use gpu_prover::prover::tracing_data::TracingDataHost;
use gpu_prover::witness::trace_delegation::DelegationTraceHost;
use gpu_prover::witness::trace_main::MainTraceHost;
use log::info;
use prover::definitions::{ExternalChallenges, ExternalDelegationArgumentChallenges};
use prover::tracers::delegation::DelegationWitness;
use prover::ShuffleRamSetupAndTeardown;
use rayon::ThreadPool;
use risc_v_simulator::cycle::{
    IMStandardIsaConfig, IMWithoutSignedMulDivIsaConfig, IWithoutByteAccessIsaConfig,
    IWithoutByteAccessIsaConfigWithDelegation,
};
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;
use trace_and_split::setups;
use worker::Worker;

type BF = Mersenne31Field;
type A = ConcurrentStaticHostAllocator;

const CPU_WORKERS_COUNT: usize = 6;
const CYCLES_TRACING_WORKERS_COUNT: usize = CPU_WORKERS_COUNT - 2;

struct Binary {
    circuit_type: MainCircuitType,
    bytecode: Arc<Box<[u32]>>,
    precomputations: CircuitPrecomputationsHost<A>,
}

pub struct GpuBatchProver<'a, K: Display + Eq + Hash> {
    gpu_manager: GpuManager<MemPoolProverContext<'a>>,
    worker: Worker,
    binaries: HashMap<K, Binary>,
    delegation_circuits_precomputations:
        HashMap<DelegationCircuitType, CircuitPrecomputationsHost<A>>,
}

impl<K: Display + Eq + Hash> GpuBatchProver<'_, K> {
    pub fn new(
        host_allocations_count: usize,
        log_host_allocation_size: usize,
        scope: &rayon::Scope,
    ) -> Self {
        let gpu_manager = GpuManager::new(host_allocations_count, log_host_allocation_size, scope);
        gpu_manager.wait_for_initialization();
        let worker = Worker::new();
        info!(
            "GPU BATCH PROVER thread pool for {} logical cores created",
            worker.num_cores
        );
        info!("GPU BATCH PROVER producing precomputations for delegation circuits");
        let delegation_circuits_precomputations =
            setups::all_delegation_circuits_precomputations(&worker)
                .into_iter()
                .map(|(id, p)| (DelegationCircuitType::from(id as u16), p.into()))
                .collect();
        info!("GPU BATCH PROVER produced precomputations for delegation circuits");
        Self {
            gpu_manager,
            worker,
            binaries: HashMap::new(),
            delegation_circuits_precomputations,
        }
    }

    pub fn add_binary(
        &mut self,
        key: K,
        circuit_type: MainCircuitType,
        bytecode: impl Into<Box<[u32]>>,
    ) {
        let bytecode = Arc::new(bytecode.into());
        info!(
            "GPU BATCH PROVER producing precomputations for circuit type: {:?}",
            circuit_type
        );
        let precomputations = Self::get_precomputations(circuit_type, &bytecode, &self.worker);
        info!(
            "GPU BATCH PROVER produced precomputations for circuit type {:?}",
            circuit_type
        );
        let binary = Binary {
            circuit_type,
            bytecode,
            precomputations,
        };
        self.binaries.insert(key, binary);
    }

    pub fn get_results(
        &self,
        proving: bool,
        binary_key: K,
        num_instances_upper_bound: usize,
        non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
        external_challenges: Option<ExternalChallenges>,
    ) {
        if proving {
            assert!(external_challenges.is_some());
        }
        let binary = &self.binaries[&binary_key];
        let trace_len = binary.precomputations.compiled_circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let cycles_per_circuit = trace_len - 1;
        let (free_setup_and_teardowns_sender, free_setup_and_teardowns_receiver) = unbounded();
        let gpu_workers_count = self.gpu_manager.get_workers_count();
        for _ in 0..(1 + gpu_workers_count) * 3 {
            let mut lazy_init_data = Vec::with_capacity_in(cycles_per_circuit, A::default());
            unsafe {
                lazy_init_data.set_len(cycles_per_circuit);
            }
            let message = ShuffleRamSetupAndTeardown { lazy_init_data };
            free_setup_and_teardowns_sender.send(message).unwrap();
        }
        let (free_cycle_tracing_data_sender, free_cycle_tracing_data_receiver) = unbounded();
        for _ in 0..(CYCLES_TRACING_WORKERS_COUNT + gpu_workers_count) * 3 {
            let message = CycleTracingData::with_cycles_capacity(cycles_per_circuit);
            free_cycle_tracing_data_sender.send(message).unwrap();
        }
        let mut free_delegation_witness_senders = HashMap::new();
        let mut free_delegation_witness_receivers = HashMap::new();

        for (&id, factory) in &Self::get_delegation_factories(binary.circuit_type) {
            let (sender, receiver) = unbounded();
            for _ in 0..2 {
                sender.send(factory()).unwrap();
            }
            free_delegation_witness_senders.insert(id, sender);
            free_delegation_witness_receivers.insert(id, receiver);
        }
        info!("channels are initialized");
        info!("go!");
        let (work_results_sender, worker_results_receiver) = unbounded();
        info!("spawning CPU workers");
        let non_determinism_source = Arc::new(non_determinism_source);
        let mut cpu_worker_id = 0;
        let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
            free_setup_and_teardowns: free_setup_and_teardowns_receiver.clone(),
        };
        self.spawn_cpu_worker(
            binary.circuit_type,
            cpu_worker_id,
            num_instances_upper_bound,
            binary.bytecode.clone(),
            non_determinism_source.clone(),
            ram_tracing_mode,
            work_results_sender.clone(),
        );
        cpu_worker_id += 1;
        for split_index in 0..CYCLES_TRACING_WORKERS_COUNT {
            let ram_tracing_mode = CpuWorkerMode::TraceCycles {
                split_count: CYCLES_TRACING_WORKERS_COUNT,
                split_index,
                free_cycle_tracing_data: free_cycle_tracing_data_receiver.clone(),
            };
            self.spawn_cpu_worker(
                binary.circuit_type,
                cpu_worker_id,
                num_instances_upper_bound,
                binary.bytecode.clone(),
                non_determinism_source.clone(),
                ram_tracing_mode,
                work_results_sender.clone(),
            );
            cpu_worker_id += 1;
        }
        let delegation_mode = CpuWorkerMode::TraceDelegations {
            free_delegation_witnesses: free_delegation_witness_receivers.clone(),
        };
        self.spawn_cpu_worker(
            binary.circuit_type,
            cpu_worker_id,
            num_instances_upper_bound,
            binary.bytecode.clone(),
            non_determinism_source.clone(),
            delegation_mode,
            work_results_sender.clone(),
        );
        info!("CPU workers spawned");
        let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
        let gpu_work_batch = GpuWorkBatch {
            receiver: gpu_work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        self.gpu_manager.send_batch(gpu_work_batch);
        drop(work_results_sender);
        let mut final_main_chunks_count = None;
        let mut final_register_values = None;
        let mut final_delegation_chunks_counts = None;
        let mut main_memory_commitments = vec![];
        let mut delegation_memory_commitments = HashMap::new();
        let mut main_proofs = vec![];
        let mut delegation_proofs = HashMap::new();
        let mut setup_and_teardown_chunks = HashMap::new();
        let mut cycles_chunks = HashMap::new();
        let mut delegation_work_sender = Some(gpu_work_requests_sender.clone());
        let send_main_work_request =
            move |circuit_sequence: usize,
                  setup_and_teardown_chunk: Option<ShuffleRamSetupAndTeardown<_>>,
                  cycles_chunk: CycleTracingData<_>| {
                if proving {
                    info!("sending main circuit proof request for chunk {circuit_sequence}");
                } else {
                    info!(
                    "sending main circuit memory commitment request for chunk {circuit_sequence}"
                );
                }
                let setup_and_teardown = setup_and_teardown_chunk.map(|chunk| chunk.into());
                let trace = MainTraceHost {
                    cycles_traced: cycles_chunk.per_cycle_data.len(),
                    cycle_data: Arc::new(cycles_chunk.per_cycle_data),
                    num_cycles_chunk_size: cycles_per_circuit,
                };
                let tracing_data = TracingDataHost::Main {
                    setup_and_teardown,
                    trace,
                };
                let request = if proving {
                    let proof_request = ProofRequest {
                        circuit_type: CircuitType::Main(binary.circuit_type),
                        circuit_sequence,
                        precomputations: binary.precomputations.clone(),
                        tracing_data,
                        external_challenges: external_challenges.unwrap(),
                    };
                    GpuWorkRequest::Proof(proof_request)
                } else {
                    let memory_commitment_request = MemoryCommitmentRequest {
                        circuit_type: CircuitType::Main(binary.circuit_type),
                        circuit_sequence,
                        precomputations: binary.precomputations.clone(),
                        tracing_data,
                    };
                    GpuWorkRequest::MemoryCommitment(memory_commitment_request)
                };
                gpu_work_requests_sender.send(request).unwrap();
            };
        let mut send_main_work_request = Some(send_main_work_request);
        let mut main_work_requests_count = 0;
        for result in worker_results_receiver {
            match result {
                WorkerResult::SetupAndTeardownChunk(chunk) => {
                    let SetupAndTeardownChunk {
                        index,
                        chunk: setup_and_teardown_chunk,
                    } = chunk;
                    info!("received setup and teardown chunk {index}");
                    if let Some(cycles_chunk) = cycles_chunks.remove(&index) {
                        let send = send_main_work_request.as_ref().unwrap();
                        send(index, setup_and_teardown_chunk, cycles_chunk);
                        main_work_requests_count += 1;
                    } else {
                        setup_and_teardown_chunks.insert(index, setup_and_teardown_chunk);
                    }
                }
                WorkerResult::RAMTracingResult {
                    chunks_traced_count,
                    final_register_values: values,
                } => {
                    info!("received RAM tracing result with final register values, chunks traced: {chunks_traced_count}");
                    let previous_count = final_main_chunks_count.replace(chunks_traced_count);
                    assert!(previous_count.is_none_or(|v| v == chunks_traced_count));
                    final_register_values = Some(values);
                }
                WorkerResult::CyclesChunk(chunk) => {
                    let CyclesChunk { index, data } = chunk;
                    info!("received cycles chunk {index}");
                    if let Some(setup_and_teardown_chunk) = setup_and_teardown_chunks.remove(&index)
                    {
                        let send = send_main_work_request.as_ref().unwrap();
                        send(index, setup_and_teardown_chunk, data);
                        main_work_requests_count += 1;
                    } else {
                        cycles_chunks.insert(index, data);
                    }
                }
                WorkerResult::CyclesTracingResult {
                    chunks_traced_count,
                } => {
                    info!("received cycles tracing result, chunks traced: {chunks_traced_count}");
                    let previous_count = final_main_chunks_count.replace(chunks_traced_count);
                    assert!(previous_count.is_none_or(|v| v == chunks_traced_count));
                }
                WorkerResult::DelegationWitness(witness) => {
                    let id = witness.delegation_type;
                    info!("received delegation witnesses for delegation id {id}");
                    let circuit_type = CircuitType::from_delegation_type(id);
                    let precomputations = self.delegation_circuits_precomputations
                        [&DelegationCircuitType::from(id)]
                        .clone();
                    let tracing_data = TracingDataHost::Delegation(witness.into());
                    let request = if proving {
                        info!("sending delegation proof request for delegation id {id}");
                        let proof_request = ProofRequest {
                            circuit_type,
                            circuit_sequence: 0,
                            precomputations,
                            tracing_data,
                            external_challenges: external_challenges.unwrap(),
                        };
                        GpuWorkRequest::Proof(proof_request)
                    } else {
                        info!(
                            "sending delegation memory commitment request for delegation id {id}"
                        );
                        let memory_commitment_request = MemoryCommitmentRequest {
                            circuit_type,
                            circuit_sequence: 0,
                            precomputations,
                            tracing_data,
                        };
                        GpuWorkRequest::MemoryCommitment(memory_commitment_request)
                    };
                    delegation_work_sender
                        .as_ref()
                        .unwrap()
                        .send(request)
                        .unwrap();
                }
                WorkerResult::DelegationTracingResult {
                    delegation_chunks_counts,
                } => {
                    for (id, count) in delegation_chunks_counts.iter() {
                        info!("received delegation tracing result for delegation id {id}, chunks traced: {count}");
                    }
                    final_delegation_chunks_counts = Some(delegation_chunks_counts);
                    info!("sent all delegation memory commitment requests");
                    delegation_work_sender = None;
                }
                WorkerResult::MemoryCommitment(commitment) => {
                    assert!(!proving);
                    let MemoryCommitmentResult {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        merkle_tree_caps,
                    } = commitment;
                    match tracing_data {
                        TracingDataHost::Main {
                            setup_and_teardown,
                            trace,
                        } => {
                            info!(
                            "received memory commitment for main circuit type: {:?} circuit sequence: {}",
                            circuit_type, circuit_sequence
                        );
                            if let Some(setup_and_teardown) = setup_and_teardown {
                                let lazy_init_data =
                                    Arc::into_inner(setup_and_teardown.lazy_init_data).unwrap();
                                let setup_and_teardown =
                                    ShuffleRamSetupAndTeardown { lazy_init_data };
                                info!("returning free setup and teardown");
                                free_setup_and_teardowns_sender
                                    .send(setup_and_teardown)
                                    .unwrap();
                            }
                            let mut per_cycle_data = Arc::into_inner(trace.cycle_data).unwrap();
                            per_cycle_data.clear();
                            let cycle_tracing_data = CycleTracingData { per_cycle_data };
                            info!("returning free cycle tracing data");
                            free_cycle_tracing_data_sender
                                .send(cycle_tracing_data)
                                .unwrap();
                            main_memory_commitments.push((circuit_sequence, merkle_tree_caps));
                        }
                        TracingDataHost::Delegation(witness) => {
                            info!(
                                "received memory commitment for delegation circuit type: {:?}",
                                circuit_type
                            );
                            let DelegationTraceHost {
                                num_requests,
                                num_register_accesses_per_delegation,
                                num_indirect_reads_per_delegation,
                                num_indirect_writes_per_delegation,
                                base_register_index,
                                delegation_type,
                                indirect_accesses_properties,
                                write_timestamp,
                                register_accesses,
                                indirect_reads,
                                indirect_writes,
                            } = witness;
                            let mut write_timestamp = Arc::into_inner(write_timestamp).unwrap();
                            write_timestamp.clear();
                            let mut register_accesses = Arc::into_inner(register_accesses).unwrap();
                            register_accesses.clear();
                            let mut indirect_reads = Arc::into_inner(indirect_reads).unwrap();
                            indirect_reads.clear();
                            let mut indirect_writes = Arc::into_inner(indirect_writes).unwrap();
                            indirect_writes.clear();
                            let witness = DelegationWitness {
                                num_requests,
                                num_register_accesses_per_delegation,
                                num_indirect_reads_per_delegation,
                                num_indirect_writes_per_delegation,
                                base_register_index,
                                delegation_type,
                                indirect_accesses_properties,
                                write_timestamp,
                                register_accesses,
                                indirect_reads,
                                indirect_writes,
                            };
                            info!("returning free delegation tracing data");
                            free_delegation_witness_senders
                                .get(&DelegationCircuitType::from(delegation_type))
                                .unwrap()
                                .send(witness)
                                .unwrap();
                            delegation_memory_commitments
                                .entry(delegation_type)
                                .or_insert_with(Vec::new)
                                .push(merkle_tree_caps);
                        }
                    }
                }
                WorkerResult::Proof(proof) => {
                    assert!(proving);
                    let ProofResult {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        proof,
                    } = proof;
                    match tracing_data {
                        TracingDataHost::Main {
                            setup_and_teardown,
                            trace,
                        } => {
                            info!(
                                "received proof for main circuit type: {:?} circuit sequence: {}",
                                circuit_type, circuit_sequence
                            );
                            if let Some(setup_and_teardown) = setup_and_teardown {
                                let lazy_init_data =
                                    Arc::into_inner(setup_and_teardown.lazy_init_data).unwrap();
                                let setup_and_teardown =
                                    ShuffleRamSetupAndTeardown { lazy_init_data };
                                info!("returning free setup and teardown");
                                free_setup_and_teardowns_sender
                                    .send(setup_and_teardown)
                                    .unwrap();
                            }
                            let mut per_cycle_data = Arc::into_inner(trace.cycle_data).unwrap();
                            per_cycle_data.clear();
                            let cycle_tracing_data = CycleTracingData { per_cycle_data };
                            info!("returning free cycle tracing data");
                            free_cycle_tracing_data_sender
                                .send(cycle_tracing_data)
                                .unwrap();
                            main_proofs.push((circuit_sequence, proof));
                        }
                        TracingDataHost::Delegation(witness) => {
                            info!(
                                "received memory commitment for delegation circuit type: {:?}",
                                circuit_type
                            );
                            let DelegationTraceHost {
                                num_requests,
                                num_register_accesses_per_delegation,
                                num_indirect_reads_per_delegation,
                                num_indirect_writes_per_delegation,
                                base_register_index,
                                delegation_type,
                                indirect_accesses_properties,
                                write_timestamp,
                                register_accesses,
                                indirect_reads,
                                indirect_writes,
                            } = witness;
                            let mut write_timestamp = Arc::into_inner(write_timestamp).unwrap();
                            write_timestamp.clear();
                            let mut register_accesses = Arc::into_inner(register_accesses).unwrap();
                            register_accesses.clear();
                            let mut indirect_reads = Arc::into_inner(indirect_reads).unwrap();
                            indirect_reads.clear();
                            let mut indirect_writes = Arc::into_inner(indirect_writes).unwrap();
                            indirect_writes.clear();
                            let witness = DelegationWitness {
                                num_requests,
                                num_register_accesses_per_delegation,
                                num_indirect_reads_per_delegation,
                                num_indirect_writes_per_delegation,
                                base_register_index,
                                delegation_type,
                                indirect_accesses_properties,
                                write_timestamp,
                                register_accesses,
                                indirect_reads,
                                indirect_writes,
                            };
                            info!("returning free delegation tracing data");
                            free_delegation_witness_senders
                                .get(&DelegationCircuitType::from(delegation_type))
                                .unwrap()
                                .send(witness)
                                .unwrap();
                            delegation_proofs
                                .entry(delegation_type)
                                .or_insert_with(Vec::new)
                                .push(proof);
                        }
                    }
                }
            };
            if send_main_work_request.is_none() {
                continue;
            }
            if let Some(count) = final_main_chunks_count {
                if main_work_requests_count == count {
                    info!("sent all main memory commitment requests");
                    send_main_work_request = None;
                }
            }
        }
        let final_main_chunks_count = final_main_chunks_count.unwrap();
        assert_ne!(final_main_chunks_count, 0);
        let _final_register_values = final_register_values.as_ref().unwrap();
        if proving {
            assert_eq!(main_proofs.len(), final_main_chunks_count);
            for (id, count) in final_delegation_chunks_counts.unwrap() {
                assert_eq!(count, delegation_proofs.get(&id).unwrap().len());
            }
        } else {
            assert_eq!(main_memory_commitments.len(), final_main_chunks_count);
            for (id, count) in final_delegation_chunks_counts.unwrap() {
                assert_eq!(count, delegation_memory_commitments.get(&id).unwrap().len());
            }
        }
        assert!(send_main_work_request.is_none());
        assert!(delegation_work_sender.is_none());
        assert!(setup_and_teardown_chunks.is_empty());
        assert!(cycles_chunks.is_empty());
    }
    // pub fn prove<C: ProverContext>(
    //     &self,
    //     gpu_manager: &GpuManager<C>,
    //     binary: Arc<Box<[u32]>>,
    //     main_circuit_type: MainCircuitType,
    //     main_circuit_precomputations: CircuitPrecomputationsHost<C::HostAllocator>,
    //     delegation_circuits_precomputations: HashMap<
    //         DelegationCircuitType,
    //         CircuitPrecomputationsHost<C::HostAllocator>,
    //     >,
    //     delegation_factories: HashMap<
    //         DelegationCircuitType,
    //         Box<dyn Fn() -> DelegationWitness<C::HostAllocator>>,
    //     >,
    // ) {
    //     get_results(
    //         gpu_manager,
    //         &binary,
    //         main_circuit_type,
    //         &main_circuit_precomputations,
    //         &delegation_circuits_precomputations,
    //         &delegation_factories,
    //     );
    // }
    fn get_precomputations<A: GoodAllocator>(
        circuit_type: MainCircuitType,
        bytecode: &[u32],
        worker: &Worker,
    ) -> CircuitPrecomputationsHost<A> {
        match circuit_type {
            MainCircuitType::FinalReducedRiscVMachine => {
                setups::get_final_reduced_riscv_circuit_setup(&bytecode, worker).into()
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                setups::get_riscv_without_signed_mul_div_circuit_setup(&bytecode, worker).into()
            }
            MainCircuitType::ReducedRiscVMachine => {
                setups::get_reduced_riscv_circuit_setup(&bytecode, worker).into()
            }
            MainCircuitType::RiscVCycles => {
                setups::get_main_riscv_circuit_setup(&bytecode, worker).into()
            }
        }
    }

    fn get_delegation_factories<A: GoodAllocator>(
        circuit_type: MainCircuitType,
    ) -> HashMap<DelegationCircuitType, Box<dyn Fn() -> DelegationWitness<A>>> {
        let factories = match circuit_type {
            MainCircuitType::FinalReducedRiscVMachine => {
                setups::delegation_factories_for_machine::<IWithoutByteAccessIsaConfig, A>()
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                setups::delegation_factories_for_machine::<IMWithoutSignedMulDivIsaConfig, A>()
            }
            MainCircuitType::ReducedRiscVMachine => setups::delegation_factories_for_machine::<
                IWithoutByteAccessIsaConfigWithDelegation,
                A,
            >(),
            MainCircuitType::RiscVCycles => {
                setups::delegation_factories_for_machine::<IMStandardIsaConfig, A>()
            }
        };
        factories
            .into_iter()
            .map(|(id, factory)| (DelegationCircuitType::from(id), factory))
            .collect()
    }

    fn spawn_cpu_worker(
        &self,
        circuit_type: MainCircuitType,
        worker_id: usize,
        num_main_chunks_upper_bound: usize,
        binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
        non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
        mode: CpuWorkerMode<A>,
        results: Sender<WorkerResult<A>>,
    ) {
        match circuit_type {
            MainCircuitType::FinalReducedRiscVMachine => {
                let func = get_cpu_worker_func::<IWithoutByteAccessIsaConfig, _>(
                    worker_id,
                    num_main_chunks_upper_bound,
                    binary,
                    non_determinism,
                    mode,
                    results,
                );
                self.worker.pool.spawn(func);
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                let func = get_cpu_worker_func::<IWithoutByteAccessIsaConfig, _>(
                    worker_id,
                    num_main_chunks_upper_bound,
                    binary,
                    non_determinism,
                    mode,
                    results,
                );
                self.worker.pool.spawn(func);
            }
            MainCircuitType::ReducedRiscVMachine => {
                let func = get_cpu_worker_func::<IWithoutByteAccessIsaConfigWithDelegation, _>(
                    worker_id,
                    num_main_chunks_upper_bound,
                    binary,
                    non_determinism,
                    mode,
                    results,
                );
                self.worker.pool.spawn(func);
            }
            MainCircuitType::RiscVCycles => {
                let func = get_cpu_worker_func::<IMStandardIsaConfig, _>(
                    worker_id,
                    num_main_chunks_upper_bound,
                    binary,
                    non_determinism,
                    mode,
                    results,
                );
                self.worker.pool.spawn(func);
            }
        }
    }
}
