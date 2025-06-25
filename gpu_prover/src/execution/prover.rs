use super::cpu_worker::{
    get_cpu_worker_func, CpuWorkerMode, CyclesChunk, NonDeterminism, SetupAndTeardownChunk,
};
use super::gpu_manager::{GpuManager, GpuWorkBatch};
use super::gpu_worker::{
    GpuWorkRequest, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest, ProofResult,
};
use super::messages::WorkerResult;
use super::precomputations::CircuitPrecomputationsHost;
use super::tracer::CycleTracingData;
use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::circuit_type::{CircuitType, DelegationCircuitType, MainCircuitType};
use crate::cudart::device::get_device_count;
use crate::prover::context::MemPoolProverContext;
use crate::prover::context::ProverContext;
use crate::prover::tracing_data::TracingDataHost;
use crate::witness::trace_delegation::DelegationTraceHost;
use crate::witness::trace_main::MainTraceHost;
use crossbeam_channel::{unbounded, Receiver, Sender};
use crossbeam_utils::sync::WaitGroup;
use cs::definitions::TimestampData;
use fft::GoodAllocator;
use itertools::Itertools;
use log::{info, trace};
use prover::definitions::{ExternalChallenges, LazyInitAndTeardown};
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Proof;
use prover::risc_v_simulator::abstractions::tracer::{
    RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData,
};
use prover::risc_v_simulator::cycle::{
    IMStandardIsaConfig, IMWithoutSignedMulDivIsaConfig, IWithoutByteAccessIsaConfig,
    IWithoutByteAccessIsaConfigWithDelegation,
};
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::SingleCycleTracingData;
use prover::ShuffleRamSetupAndTeardown;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;
use std::time::Instant;
use trace_and_split::{
    fs_transform_for_memory_and_delegation_arguments, setups, FinalRegisterValue,
};
use worker::Worker;

type A = ConcurrentStaticHostAllocator;

const CPU_WORKERS_COUNT: usize = 6;
const CYCLES_TRACING_WORKERS_COUNT: usize = CPU_WORKERS_COUNT - 2;

/// Represents an executable binary that can be proven by the prover
///
///  # Fields
/// * `key`: unique identifier for the binary, can be for example a &str or usize, anything that implements Clone, Debug, Eq, and Hash
/// * `circuit_type`: the type of the circuit this binary is for, one of the values from the `MainCircuitType` enumeration
/// * `bytecode`: the bytecode of the binary, can be a Vec<u32> or any other type that can be converted into Box<[u32]>
///
#[derive(Clone)]
pub struct ExecutableBinary<K: Clone + Debug + Eq + Hash, B: Into<Box<[u32]>>> {
    pub key: K,
    pub circuit_type: MainCircuitType,
    pub bytecode: B,
}

struct BinaryHolder {
    circuit_type: MainCircuitType,
    bytecode: Arc<Box<[u32]>>,
    precomputations: CircuitPrecomputationsHost<A>,
}

pub struct ExecutionProver<'a, K: Debug + Eq + Hash> {
    gpu_manager: GpuManager<MemPoolProverContext<'a>>,
    worker: Worker,
    wait_group: Option<WaitGroup>,
    binaries: HashMap<K, BinaryHolder>,
    delegation_circuits_precomputations:
        HashMap<DelegationCircuitType, CircuitPrecomputationsHost<A>>,
    free_setup_and_teardowns_sender: Sender<ShuffleRamSetupAndTeardown<A>>,
    free_setup_and_teardowns_receiver: Receiver<ShuffleRamSetupAndTeardown<A>>,
    free_cycle_tracing_data_sender: Sender<CycleTracingData<A>>,
    free_cycle_tracing_data_receiver: Receiver<CycleTracingData<A>>,
    free_delegation_witness_senders: HashMap<DelegationCircuitType, Sender<DelegationWitness<A>>>,
    free_delegation_witness_receivers:
        HashMap<DelegationCircuitType, Receiver<DelegationWitness<A>>>,
}

impl<K: Clone + Debug + Eq + Hash> ExecutionProver<'_, K> {
    ///  Creates a new instance of `ExecutionProver`.
    ///
    /// # Arguments
    ///
    /// * `max_concurrent_batches`: maximum number of concurrent batches that the prover allocates host buffers for, this is a soft limit, the prover will work with more batches if needed, but it can stall certain operations for some time
    /// * `binaries`: a vector of executable binaries that the prover can work with, each binary must have a unique key
    ///
    /// returns: an instance of `ExecutionProver` that can be used to generate memory commitments and proofs for the provided binaries, it is supposed to be a Singleton instance
    ///
    pub fn new(
        max_concurrent_batches: usize,
        binaries: Vec<ExecutableBinary<K, impl Into<Box<[u32]>>>>,
    ) -> Self {
        assert_ne!(max_concurrent_batches, 0);
        assert!(!binaries.is_empty());
        let device_count = get_device_count().unwrap() as usize;
        let max_num_cycles = binaries
            .iter()
            .map(|b| Self::get_num_cycles(b.circuit_type))
            .max()
            .unwrap();
        fn delegation_witness_size(witness: DelegationWitness) -> usize {
            witness.write_timestamp.capacity() * size_of::<TimestampData>()
                + witness.register_accesses.capacity()
                    * size_of::<RegisterOrIndirectReadWriteData>()
                + witness.indirect_reads.capacity() * size_of::<RegisterOrIndirectReadData>()
                + witness.indirect_writes.capacity() * size_of::<RegisterOrIndirectReadWriteData>()
        }
        let combined_bytes_for_delegation_traces = binaries
            .iter()
            .map(|b| Self::get_delegation_factories(b.circuit_type).into_iter())
            .flatten()
            .unique_by(|(t, _)| *t)
            .map(|(_, factory)| delegation_witness_size(factory()))
            .sum::<usize>();
        let setup_and_teardowns_count =
            max_concurrent_batches * CYCLES_TRACING_WORKERS_COUNT + device_count * 2;
        let setups_and_teardowns_bytes_needed =
            setup_and_teardowns_count * max_num_cycles * size_of::<LazyInitAndTeardown>();
        let cycles_tracing_data_count =
            max_concurrent_batches * CYCLES_TRACING_WORKERS_COUNT + device_count * 2;
        let cycles_tracing_data_bytes_needed =
            cycles_tracing_data_count * max_num_cycles * size_of::<SingleCycleTracingData>();
        let delegation_tracing_data_count = max_concurrent_batches + device_count * 2;
        let delegation_tracing_data_bytes_needed =
            delegation_tracing_data_count * combined_bytes_for_delegation_traces;
        let total_bytes_needed = setups_and_teardowns_bytes_needed
            + cycles_tracing_data_bytes_needed
            + delegation_tracing_data_bytes_needed;
        let total_gb_needed = total_bytes_needed.next_multiple_of(1 << 30) >> 30;
        let host_allocations_count = total_gb_needed + device_count * 2;
        info!("PROVER initializing host allocator with {host_allocations_count} x 1 GB");
        MemPoolProverContext::initialize_host_allocator(host_allocations_count, 1 << 8, 22)
            .unwrap();
        info!("PROVER host allocator initialized");
        let gpu_manager = GpuManager::new();
        let (free_setup_and_teardowns_sender, free_setup_and_teardowns_receiver) = unbounded();
        for _ in 0..setup_and_teardowns_count {
            let lazy_init_data = Vec::with_capacity_in(max_num_cycles, A::default());
            let message = ShuffleRamSetupAndTeardown { lazy_init_data };
            free_setup_and_teardowns_sender.send(message).unwrap();
        }
        let (free_cycle_tracing_data_sender, free_cycle_tracing_data_receiver) = unbounded();
        for _ in 0..cycles_tracing_data_count {
            let message = CycleTracingData::with_cycles_capacity(max_num_cycles);
            free_cycle_tracing_data_sender.send(message).unwrap();
        }
        let mut free_delegation_witness_senders = HashMap::new();
        let mut free_delegation_witness_receivers = HashMap::new();
        for (circuit_type, factory) in binaries
            .iter()
            .map(|b| Self::get_delegation_factories(b.circuit_type).into_iter())
            .flatten()
            .unique_by(|(t, _)| *t)
        {
            let (sender, receiver) = unbounded();
            for _ in 0..delegation_tracing_data_count {
                sender.send(factory()).unwrap();
            }
            free_delegation_witness_senders.insert(circuit_type, sender);
            free_delegation_witness_receivers.insert(circuit_type, receiver);
        }
        let worker = Worker::new();
        info!(
            "PROVER thread pool with {} threads created",
            worker.num_cores
        );
        let wait_group = Some(WaitGroup::new());
        let binaries = binaries
            .into_iter()
            .map(|b| {
                let ExecutableBinary {
                    key,
                    circuit_type,
                    bytecode,
                } = b;
                let bytecode = Arc::new(bytecode.into());
                info!(
                    "PROVER producing precomputations for main circuit {:?} with binary {:?}",
                    circuit_type, key
                );
                let precomputations = Self::get_precomputations(circuit_type, &bytecode, &worker);
                info!(
                    "PROVER produced precomputations for main circuit {:?} with binary {:?}",
                    circuit_type, key
                );
                (
                    key,
                    BinaryHolder {
                        circuit_type,
                        bytecode,
                        precomputations,
                    },
                )
            })
            .collect();
        info!("PROVER producing precomputations for all delegation circuits");
        let delegation_circuits_precomputations =
            setups::all_delegation_circuits_precomputations(&worker)
                .into_iter()
                .map(|(id, p)| (DelegationCircuitType::from(id as u16), p.into()))
                .collect();
        info!("PROVER produced precomputations for all delegation circuits");
        Self {
            gpu_manager,
            worker,
            wait_group,
            binaries,
            delegation_circuits_precomputations,
            free_setup_and_teardowns_sender,
            free_setup_and_teardowns_receiver,
            free_cycle_tracing_data_sender,
            free_cycle_tracing_data_receiver,
            free_delegation_witness_senders,
            free_delegation_witness_receivers,
        }
    }

    fn get_results(
        &self,
        proving: bool,
        batch_id: u64,
        binary_key: &K,
        num_instances_upper_bound: usize,
        non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
        external_challenges: Option<ExternalChallenges>,
    ) -> (
        [FinalRegisterValue; 32],
        Vec<Vec<MerkleTreeCapVarLength>>,
        Vec<(u32, Vec<Vec<MerkleTreeCapVarLength>>)>,
        Vec<Proof>,
        Vec<(u32, Vec<Proof>)>,
    ) {
        assert!(proving ^ external_challenges.is_none());
        let binary = &self.binaries[&binary_key];
        let trace_len = binary.precomputations.compiled_circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let cycles_per_circuit = trace_len - 1;
        let (work_results_sender, worker_results_receiver) = unbounded();
        trace!("BATCH[{batch_id}] PROVER spawning CPU workers");
        let non_determinism_source = Arc::new(non_determinism_source);
        let mut cpu_worker_id = 0;
        let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
            free_setup_and_teardowns: self.free_setup_and_teardowns_receiver.clone(),
        };
        self.spawn_cpu_worker(
            binary.circuit_type,
            batch_id,
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
                free_cycle_tracing_data: self.free_cycle_tracing_data_receiver.clone(),
            };
            self.spawn_cpu_worker(
                binary.circuit_type,
                batch_id,
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
            free_delegation_witnesses: self.free_delegation_witness_receivers.clone(),
        };
        self.spawn_cpu_worker(
            binary.circuit_type,
            batch_id,
            cpu_worker_id,
            num_instances_upper_bound,
            binary.bytecode.clone(),
            non_determinism_source.clone(),
            delegation_mode,
            work_results_sender.clone(),
        );
        trace!("BATCH[{batch_id}] PROVER CPU workers spawned");
        let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
        let gpu_work_batch = GpuWorkBatch {
            batch_id,
            receiver: gpu_work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        trace!("BATCH[{batch_id}] PROVER sending work batch to GPU manager");
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
                let circuit_type = CircuitType::Main(binary.circuit_type);
                let precomputations = binary.precomputations.clone();
                let request = if proving {
                    let proof_request = ProofRequest {
                        batch_id,
                        circuit_type,
                        circuit_sequence,
                        precomputations,
                        tracing_data,
                        external_challenges: external_challenges.unwrap(),
                    };
                    GpuWorkRequest::Proof(proof_request)
                } else {
                    let memory_commitment_request = MemoryCommitmentRequest {
                        batch_id,
                        circuit_type,
                        circuit_sequence,
                        precomputations,
                        tracing_data,
                    };
                    GpuWorkRequest::MemoryCommitment(memory_commitment_request)
                };
                if proving {
                    trace!("BATCH[{batch_id}] PROVER sending main circuit proof request for chunk {circuit_sequence} to GPU manager");
                } else {
                    trace!("BATCH[{batch_id}] PROVER sending main circuit memory commitment request for chunk {circuit_sequence} to GPU manager");
                }
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
                    trace!("BATCH[{batch_id}] PROVER received setup and teardown chunk {index}");
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
                    trace!("BATCH[{batch_id}] PROVER received RAM tracing result with final register values and {chunks_traced_count} chunk(s) traced");
                    let previous_count = final_main_chunks_count.replace(chunks_traced_count);
                    assert!(previous_count.is_none_or(|v| v == chunks_traced_count));
                    final_register_values = Some(values);
                }
                WorkerResult::CyclesChunk(chunk) => {
                    let CyclesChunk { index, data } = chunk;
                    trace!("BATCH[{batch_id}] PROVER received cycles chunk {index}");
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
                    trace!("BATCH[{batch_id}] PROVER received cycles tracing result with {chunks_traced_count} chunk(s) traced");
                    let previous_count = final_main_chunks_count.replace(chunks_traced_count);
                    assert!(previous_count.is_none_or(|count| count == chunks_traced_count));
                }
                WorkerResult::DelegationWitness(witness) => {
                    let id = witness.delegation_type;
                    let delegation_circuit_type = DelegationCircuitType::from(id);
                    let circuit_type = CircuitType::Delegation(delegation_circuit_type);
                    trace!("BATCH[{batch_id}] PROVER received delegation witnesses for delegation {:?}", delegation_circuit_type);
                    let precomputations =
                        self.delegation_circuits_precomputations[&delegation_circuit_type].clone();
                    let tracing_data = TracingDataHost::Delegation(witness.into());
                    let request = if proving {
                        let proof_request = ProofRequest {
                            batch_id,
                            circuit_type,
                            circuit_sequence: 0,
                            precomputations,
                            tracing_data,
                            external_challenges: external_challenges.unwrap(),
                        };
                        trace!("BATCH[{batch_id}] PROVER sending delegation proof request for delegation {:?}", delegation_circuit_type);
                        GpuWorkRequest::Proof(proof_request)
                    } else {
                        let memory_commitment_request = MemoryCommitmentRequest {
                            batch_id,
                            circuit_type,
                            circuit_sequence: 0,
                            precomputations,
                            tracing_data,
                        };
                        trace!("BATCH[{batch_id}] PROVER sending delegation memory commitment request for delegation {:?}", delegation_circuit_type);
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
                        let delegation_circuit_type = DelegationCircuitType::from(*id);
                        trace!("BATCH[{batch_id}] PROVER received delegation tracing result for delegation {:?} with {count} delegation chunk(s) produced", delegation_circuit_type);
                    }
                    assert!(final_delegation_chunks_counts
                        .replace(delegation_chunks_counts)
                        .is_none());
                    trace!(
                        "BATCH[{batch_id}] PROVER sent all delegation memory commitment requests"
                    );
                    delegation_work_sender = None;
                }
                WorkerResult::MemoryCommitment(commitment) => {
                    assert!(!proving);
                    let MemoryCommitmentResult {
                        batch_id: result_batch_id,
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        merkle_tree_caps,
                    } = commitment;
                    assert_eq!(result_batch_id, batch_id);
                    match tracing_data {
                        TracingDataHost::Main {
                            setup_and_teardown,
                            trace,
                        } => {
                            let circuit_type = circuit_type.as_main().unwrap();
                            trace!("BATCH[{batch_id}] PROVER received memory commitment for main circuit {:?} chunk {}", circuit_type, circuit_sequence);
                            if let Some(setup_and_teardown) = setup_and_teardown {
                                let lazy_init_data =
                                    Arc::into_inner(setup_and_teardown.lazy_init_data).unwrap();
                                let setup_and_teardown =
                                    ShuffleRamSetupAndTeardown { lazy_init_data };
                                self.free_setup_and_teardowns_sender
                                    .send(setup_and_teardown)
                                    .unwrap();
                            }
                            let mut per_cycle_data = Arc::into_inner(trace.cycle_data).unwrap();
                            per_cycle_data.clear();
                            let cycle_tracing_data = CycleTracingData { per_cycle_data };
                            self.free_cycle_tracing_data_sender
                                .send(cycle_tracing_data)
                                .unwrap();
                            main_memory_commitments.push((circuit_sequence, merkle_tree_caps));
                        }
                        TracingDataHost::Delegation(witness) => {
                            let circuit_type = circuit_type.as_delegation().unwrap();
                            trace!("BATCH[{batch_id}] PROVER received memory commitment for delegation circuit type: {:?}", circuit_type);
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
                            self.free_delegation_witness_senders
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
                        batch_id: result_batch_id,
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                        proof,
                    } = proof;
                    assert_eq!(result_batch_id, batch_id);
                    match tracing_data {
                        TracingDataHost::Main {
                            setup_and_teardown,
                            trace,
                        } => {
                            let circuit_type = circuit_type.as_main().unwrap();
                            trace!("BATCH[{batch_id}] PROVER received proof for main circuit {:?} chunk {}", circuit_type, circuit_sequence);
                            if let Some(setup_and_teardown) = setup_and_teardown {
                                let mut lazy_init_data =
                                    Arc::into_inner(setup_and_teardown.lazy_init_data).unwrap();
                                lazy_init_data.clear();
                                let setup_and_teardown =
                                    ShuffleRamSetupAndTeardown { lazy_init_data };
                                self.free_setup_and_teardowns_sender
                                    .send(setup_and_teardown)
                                    .unwrap();
                            }
                            let mut per_cycle_data = Arc::into_inner(trace.cycle_data).unwrap();
                            per_cycle_data.clear();
                            let cycle_tracing_data = CycleTracingData { per_cycle_data };
                            self.free_cycle_tracing_data_sender
                                .send(cycle_tracing_data)
                                .unwrap();
                            main_proofs.push((circuit_sequence, proof));
                        }
                        TracingDataHost::Delegation(witness) => {
                            let circuit_type = circuit_type.as_delegation().unwrap();
                            trace!("BATCH[{batch_id}] PROVER received proof for delegation circuit: {:?}", circuit_type);
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
                            self.free_delegation_witness_senders
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
            if send_main_work_request.is_some() {
                if let Some(count) = final_main_chunks_count {
                    if main_work_requests_count == count {
                        trace!("BATCH[{batch_id}] PROVER sent all main memory commitment requests");
                        send_main_work_request = None;
                    }
                }
            }
        }
        assert!(send_main_work_request.is_none());
        assert!(delegation_work_sender.is_none());
        assert!(setup_and_teardown_chunks.is_empty());
        assert!(cycles_chunks.is_empty());
        let final_main_chunks_count = final_main_chunks_count.unwrap();
        assert_ne!(final_main_chunks_count, 0);
        let final_register_values = final_register_values.unwrap();
        if proving {
            assert!(main_memory_commitments.is_empty());
            assert!(delegation_memory_commitments.is_empty());
            assert_eq!(main_proofs.len(), final_main_chunks_count);
            for (id, count) in final_delegation_chunks_counts.unwrap() {
                assert_eq!(count, delegation_proofs.get(&id).unwrap().len());
            }
        } else {
            assert!(main_proofs.is_empty());
            assert!(delegation_proofs.is_empty());
            assert_eq!(main_memory_commitments.len(), final_main_chunks_count);
            for (id, count) in final_delegation_chunks_counts.unwrap() {
                assert_eq!(count, delegation_memory_commitments.get(&id).unwrap().len());
            }
        }
        let main_memory_commitments = main_memory_commitments
            .into_iter()
            .sorted_by_key(|(index, _)| *index)
            .map(|(_, caps)| caps)
            .collect_vec();
        // delegation_memory_commitments is a HashMap.
        // We unpack it into a vector with helper logic to ensure elements are ordered by id.
        let mut delegation_memory_commitment_keys =
            delegation_memory_commitments.keys().copied().collect_vec();
        delegation_memory_commitment_keys.sort_unstable();
        let delegation_memory_commitments = delegation_memory_commitment_keys
            .iter()
            .map(|id| {
                let proofs = delegation_memory_commitments.remove(id).unwrap();
                (*id as u32, proofs)
            })
            .collect_vec();
        let main_proofs = main_proofs
            .into_iter()
            .sorted_by_key(|(index, _)| *index)
            .map(|(_, proof)| proof)
            .collect_vec();
        // delegation_proofs is a HashMap.
        // We unpack it into a vector with helper logic to ensure elements are ordered by id.
        let mut delegation_proof_keys = delegation_proofs.keys().copied().collect_vec();
        delegation_proof_keys.sort_unstable();
        let delegation_proofs = delegation_proof_keys
            .iter()
            .map(|id| {
                let proofs = delegation_proofs.remove(id).unwrap();
                (*id as u32, proofs)
            })
            .collect_vec();
        let delegation_proofs = delegation_proofs
            .into_iter()
            .map(|(id, proofs)| (id as u32, proofs))
            .collect_vec();
        (
            final_register_values,
            main_memory_commitments,
            delegation_memory_commitments,
            main_proofs,
            delegation_proofs,
        )
    }

    ///  Produces memory commitments.
    ///
    /// # Arguments
    ///
    /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    /// * `num_instances_upper_bound`: maximum number of main circuit instances that the prover will try to trace, if the simulation does not end within this limit, it will fail
    /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    ///
    /// returns: a tuple containing:
    ///     - final register values for the main circuit,
    ///     - a vector of memory commitments for the chunks of the main circuit,
    ///     - a vector of memory commitments for the chunks of the delegation circuits, where each element is a tuple containing the delegation circuit type and a vector of memory commitments for that type
    ///
    pub fn commit_memory(
        &self,
        batch_id: u64,
        binary_key: &K,
        num_instances_upper_bound: usize,
        non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
    ) -> (
        [FinalRegisterValue; 32],
        Vec<Vec<MerkleTreeCapVarLength>>,
        Vec<(u32, Vec<Vec<MerkleTreeCapVarLength>>)>,
    ) {
        info!(
            "BATCH[{batch_id}] PROVER producing memory commitment for binary with key {:?}",
            &binary_key
        );
        let timer = Instant::now();
        let (
            final_register_values,
            main_memory_commitments,
            delegation_memory_commitments,
            main_proofs,
            delegation_proofs,
        ) = self.get_results(
            false,
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
            None,
        );
        assert!(main_proofs.is_empty());
        assert!(delegation_proofs.is_empty());
        info!(
            "BATCH[{batch_id}] PROVER produced commitments for binary with key {:?} in {:.3}s",
            binary_key,
            timer.elapsed().as_secs_f64()
        );
        (
            final_register_values,
            main_memory_commitments,
            delegation_memory_commitments,
        )
    }

    ///  Produces proofs.
    ///
    /// # Arguments
    ///
    /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    /// * `num_instances_upper_bound`: maximum number of main circuit instances that the prover will try to trace, if the simulation does not end within this limit, it will fail
    /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    /// * `external_challenges`: an instance of `ExternalChallenges` that contains the challenges to be used in the proof generation
    ///
    /// returns: a tuple containing:
    ///     - final register values for the main circuit,
    ///     - a vector of proofs for the chunks of the main circuit,
    ///     - a vector of proofs for the chunks of the delegation circuits, where each element is a tuple containing the delegation circuit type and a vector of memory commitments for that type
    ///
    pub fn prove(
        &self,
        batch_id: u64,
        binary_key: &K,
        num_instances_upper_bound: usize,
        non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
        external_challenges: ExternalChallenges,
    ) -> ([FinalRegisterValue; 32], Vec<Proof>, Vec<(u32, Vec<Proof>)>) {
        info!(
            "BATCH[{batch_id}] PROVER producing proofs for binary with key {:?}",
            &binary_key
        );
        let timer = Instant::now();
        let (
            final_register_values,
            main_memory_commitments,
            delegation_memory_commitments,
            main_proofs,
            delegation_proofs,
        ) = self.get_results(
            true,
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
            Some(external_challenges),
        );
        assert!(main_memory_commitments.is_empty());
        assert!(delegation_memory_commitments.is_empty());
        info!(
            "BATCH[{batch_id}] PROVER produced proofs for binary with key {:?} in {:.3}s",
            binary_key,
            timer.elapsed().as_secs_f64()
        );
        (final_register_values, main_proofs, delegation_proofs)
    }

    ///  Commits to memory and produces proofs using challenge derived from the memory commitments.
    ///
    /// # Arguments
    ///
    /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    /// * `num_instances_upper_bound`: maximum number of main circuit instances that the prover will try to trace, if the simulation does not end within this limit, it will fail
    /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    ///
    /// returns: a tuple containing:
    ///     - final register values for the main circuit,
    ///     - a vector of proofs for the chunks of the main circuit,
    ///     - a vector of proofs for the chunks of the delegation circuits, where each element is a tuple containing the delegation circuit type and a vector of memory commitments for that type
    ///
    pub fn commit_memory_and_prove(
        &self,
        batch_id: u64,
        binary_key: &K,
        num_instances_upper_bound: usize,
        non_determinism_source: impl NonDeterminism + Clone + Send + Sync + 'static,
    ) -> ([FinalRegisterValue; 32], Vec<Proof>, Vec<(u32, Vec<Proof>)>) {
        let timer = Instant::now();
        let (final_register_values, main_memory_commitments, delegation_memory_commitments) = self
            .commit_memory(
                batch_id,
                binary_key,
                num_instances_upper_bound,
                non_determinism_source.clone(),
            );
        let memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
            &self.binaries[&binary_key].precomputations.tree_caps,
            &final_register_values,
            &main_memory_commitments,
            &delegation_memory_commitments,
        );
        let produce_delegation_challenge = match &self.binaries[&binary_key].circuit_type {
            MainCircuitType::FinalReducedRiscVMachine => false,
            MainCircuitType::MachineWithoutSignedMulDiv => true,
            MainCircuitType::ReducedRiscVMachine => true,
            MainCircuitType::RiscVCycles => true,
        };
        let external_challenges = ExternalChallenges::draw_from_transcript_seed(
            memory_challenges_seed,
            produce_delegation_challenge,
        );
        let result = self.prove(
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
            external_challenges,
        );
        info!(
            "BATCH[{batch_id}] PROVER committed to memory and produced proofs for binary with key {:?} in {:.3}s",
            binary_key,
            timer.elapsed().as_secs_f64()
        );
        result
    }

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

    fn get_num_cycles(circuit_type: MainCircuitType) -> usize {
        match circuit_type {
            MainCircuitType::FinalReducedRiscVMachine => {
                setups::num_cycles_for_machine::<IWithoutByteAccessIsaConfig>()
            }
            MainCircuitType::MachineWithoutSignedMulDiv => {
                setups::num_cycles_for_machine::<IMWithoutSignedMulDivIsaConfig>()
            }
            MainCircuitType::ReducedRiscVMachine => {
                setups::num_cycles_for_machine::<IWithoutByteAccessIsaConfigWithDelegation>()
            }
            MainCircuitType::RiscVCycles => setups::num_cycles_for_machine::<IMStandardIsaConfig>(),
        }
    }

    fn spawn_cpu_worker(
        &self,
        circuit_type: MainCircuitType,
        batch_id: u64,
        worker_id: usize,
        num_main_chunks_upper_bound: usize,
        binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
        non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
        mode: CpuWorkerMode<A>,
        results: Sender<WorkerResult<A>>,
    ) {
        let wait_group = self.wait_group.as_ref().unwrap().clone();
        match circuit_type {
            MainCircuitType::FinalReducedRiscVMachine => {
                let func = get_cpu_worker_func::<IWithoutByteAccessIsaConfig, _>(
                    wait_group,
                    batch_id,
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
                    wait_group,
                    batch_id,
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
                    wait_group,
                    batch_id,
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
                    wait_group,
                    batch_id,
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

impl<'a, K: Debug + Eq + Hash> Drop for ExecutionProver<'a, K> {
    fn drop(&mut self) {
        trace!("PROVER waiting for all threads to finish");
        self.wait_group.take().unwrap().wait();
        trace!("PROVER all threads finished");
    }
}
