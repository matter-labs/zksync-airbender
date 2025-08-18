use super::cpu_worker::{
    get_cpu_worker_func, CpuWorkerMode, CyclesChunk, NonDeterminism, SetupAndTeardownChunk,
};
use super::gpu_manager::{GpuManager, GpuWorkBatch};
use super::gpu_worker::{
    GpuWorkRequest, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest, ProofResult,
    SetupToCache,
};
use super::messages::WorkerResult;
use super::precomputations::{
    get_delegation_circuit_precomputations, get_main_circuit_precomputations,
    CircuitPrecomputations,
};
use super::tracer::CycleTracingData;
use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::circuit_type::{CircuitType, DelegationCircuitType, MainCircuitType};
use crate::cudart::device::get_device_count;
use crate::cudart::memory::{CudaHostAllocFlags, HostAllocation};
use crate::prover::tracing_data::TracingDataHost;
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
use prover::tracers::main_cycle_optimized::SingleCycleTracingData;
use prover::ShuffleRamSetupAndTeardown;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use std::alloc::Global;
use std::cmp::min;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;
use std::time::Instant;
use trace_and_split::{fs_transform_for_memory_and_delegation_arguments, FinalRegisterValue};
use worker::Worker;

type A = ConcurrentStaticHostAllocator;

const CPU_WORKERS_COUNT: usize = 6;
const CYCLES_TRACING_WORKERS_COUNT: usize = CPU_WORKERS_COUNT - 2;
const CACHE_DELEGATIONS: bool = false;

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
    precomputations: CircuitPrecomputations,
}

pub struct ExecutionProver<K: Debug + Eq + Hash> {
    device_count: usize,
    gpu_manager: GpuManager,
    worker: Worker,
    wait_group: Option<WaitGroup>,
    binaries: HashMap<K, BinaryHolder>,
    delegation_circuits_precomputations: HashMap<DelegationCircuitType, CircuitPrecomputations>,
    free_allocator_sender: Sender<A>,
    free_allocator_receiver: Receiver<A>,
}

struct ChunksCacheEntry<A: GoodAllocator> {
    circuit_type: CircuitType,
    circuit_sequence: usize,
    tracing_data: TracingDataHost<A>,
}

struct ChunksCache<A: GoodAllocator> {
    queue: VecDeque<ChunksCacheEntry<A>>,
}

impl<A: GoodAllocator> ChunksCache<A> {
    fn new(capacity: usize) -> Self {
        assert_ne!(capacity, 0);
        ChunksCache {
            queue: VecDeque::with_capacity(capacity),
        }
    }

    fn len(&self) -> usize {
        self.queue.len()
    }

    fn capacity(&self) -> usize {
        self.queue.capacity()
    }

    fn is_at_capacity(&self) -> bool {
        assert!(self.len() <= self.capacity());
        self.len() == self.capacity()
    }
}

impl<K: Clone + Debug + Eq + Hash> ExecutionProver<K> {
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
        assert_ne!(device_count, 0);
        let main_circuit_types = binaries
            .iter()
            .map(|b| b.circuit_type)
            .unique()
            .collect_vec();
        let delegation_circuit_types = main_circuit_types
            .iter()
            .flat_map(|t| t.get_allowed_delegation_circuit_types())
            .unique()
            .collect_vec();
        let max_num_cycles = main_circuit_types
            .iter()
            .map(|t| t.get_num_cycles())
            .max()
            .unwrap();
        fn delegation_witness_size(circuit_type: &DelegationCircuitType) -> usize {
            let factory = circuit_type.get_witness_factory_fn();
            let witness = factory(Global);
            witness.write_timestamp.capacity() * size_of::<TimestampData>()
                + witness.register_accesses.capacity()
                    * size_of::<RegisterOrIndirectReadWriteData>()
                + witness.indirect_reads.capacity() * size_of::<RegisterOrIndirectReadData>()
                + witness.indirect_writes.capacity() * size_of::<RegisterOrIndirectReadWriteData>()
        }
        let max_setups_and_teardowns_bytes = max_num_cycles * size_of::<LazyInitAndTeardown>();
        let max_cycles_tracing_data_bytes = max_num_cycles * size_of::<SingleCycleTracingData>();
        let max_delegation_bytes = delegation_circuit_types
            .iter()
            .map(delegation_witness_size)
            .max()
            .unwrap_or_default();
        let max_bytes = max_setups_and_teardowns_bytes
            .max(max_cycles_tracing_data_bytes)
            .max(max_delegation_bytes);
        let delegation_types_count = delegation_circuit_types.len();
        let total_allocators_count = max_concurrent_batches
            * (1 + CYCLES_TRACING_WORKERS_COUNT + delegation_types_count + 1)
            + device_count * 4;
        let (free_allocator_sender, free_allocator_receiver) = unbounded();
        const LOG_CHUNK_SIZE: u32 = 22; // 2^22 = 4 MB
        const CHUNK_SIZE: usize = 1 << LOG_CHUNK_SIZE;
        let length = max_bytes.next_multiple_of(CHUNK_SIZE);
        info!(
            "PROVER initializing {total_allocators_count} host buffers with {} MB per buffer",
            length >> 20
        );
        let allocations: Vec<HostAllocation<u8>> = (0..total_allocators_count)
            .into_par_iter()
            .map(|_| HostAllocation::alloc(length, CudaHostAllocFlags::DEFAULT).unwrap())
            .collect();
        info!("PROVER host buffers allocated");
        for allocation in allocations {
            let allocator = ConcurrentStaticHostAllocator::new([allocation], LOG_CHUNK_SIZE);
            free_allocator_sender.send(allocator).unwrap();
        }
        let worker = Worker::new();
        info!(
            "PROVER thread pool with {} threads created",
            worker.num_cores
        );
        let wait_group = Some(WaitGroup::new());
        let binaries: HashMap<K, BinaryHolder> = binaries
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
                let precomputations =
                    get_main_circuit_precomputations(circuit_type, &bytecode, &worker);
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
        let delegation_circuits_precomputations: HashMap<
            DelegationCircuitType,
            CircuitPrecomputations,
        > = delegation_circuit_types
            .into_iter()
            .map(|t| {
                info!("PROVER producing precomputations for delegation circuit {t:?}");
                let result = (t, get_delegation_circuit_precomputations(t, &worker));
                info!("PROVER produced precomputations for delegation circuit {t:?}");
                result
            })
            .collect();
        let mut setups_to_cache = vec![];
        for value in binaries.values() {
            let setup = SetupToCache {
                circuit_type: CircuitType::Main(value.circuit_type),
                precomputations: value.precomputations.clone(),
            };
            setups_to_cache.push(setup);
        }
        for (&circuit_type, precomputations) in delegation_circuits_precomputations.iter() {
            let setup = SetupToCache {
                circuit_type: CircuitType::Delegation(circuit_type),
                precomputations: precomputations.clone(),
            };
            setups_to_cache.push(setup);
        }
        let gpu_wait_group = WaitGroup::new();
        let gpu_manager = GpuManager::new(setups_to_cache, gpu_wait_group.clone());
        gpu_wait_group.wait();
        for value in binaries.values() {
            assert!(value.precomputations.tree_caps.get().is_some());
        }
        Self {
            device_count,
            gpu_manager,
            worker,
            wait_group,
            binaries,
            delegation_circuits_precomputations,
            free_allocator_sender,
            free_allocator_receiver,
        }
    }

    fn get_results(
        &self,
        proving: bool,
        chunks_cache: &mut Option<ChunksCache<A>>,
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
        let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
        let gpu_work_batch = GpuWorkBatch {
            batch_id,
            receiver: gpu_work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        trace!("BATCH[{batch_id}] PROVER sending work batch to GPU manager");
        self.gpu_manager.send_batch(gpu_work_batch);
        let skip_set = chunks_cache
            .as_ref()
            .map(|c| {
                c.queue
                    .iter()
                    .map(|entry| (entry.circuit_type, entry.circuit_sequence))
                    .collect::<HashSet<(CircuitType, usize)>>()
            })
            .unwrap_or_default();
        let mut main_work_requests_count = 0;
        if proving {
            if let Some(cache) = chunks_cache.take() {
                let external_challenges = external_challenges.unwrap();
                for entry in cache.queue.into_iter() {
                    let ChunksCacheEntry {
                        circuit_type,
                        circuit_sequence,
                        tracing_data,
                    } = entry;
                    match circuit_type {
                        CircuitType::Main(main_circuit_type) => {
                            assert_eq!(main_circuit_type, binary.circuit_type);
                            let precomputations = binary.precomputations.clone();
                            let request = ProofRequest {
                                batch_id,
                                circuit_type,
                                circuit_sequence,
                                precomputations,
                                tracing_data,
                                external_challenges,
                            };
                            let request = GpuWorkRequest::Proof(request);
                            trace!("BATCH[{batch_id}] PROVER sending cached main circuit {main_circuit_type:?} chunk {circuit_sequence} proof request to GPU manager");
                            gpu_work_requests_sender.send(request).unwrap();
                            main_work_requests_count += 1;
                        }
                        CircuitType::Delegation(delegation_circuit_type) => {
                            let precomputations = self.delegation_circuits_precomputations
                                [&delegation_circuit_type]
                                .clone();
                            let request = ProofRequest {
                                batch_id,
                                circuit_type,
                                circuit_sequence,
                                precomputations,
                                tracing_data,
                                external_challenges,
                            };
                            let request = GpuWorkRequest::Proof(request);
                            trace!("BATCH[{batch_id}] PROVER sending cached delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence} proof request to GPU manager");
                            gpu_work_requests_sender.send(request).unwrap();
                        }
                    }
                }
            }
        }
        trace!("BATCH[{batch_id}] PROVER spawning CPU workers");
        let non_determinism_source = Arc::new(non_determinism_source);
        let mut cpu_worker_id = 0;
        let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
            circuit_type: binary.circuit_type,
            skip_set: skip_set.clone(),
            free_allocator: self.free_allocator_receiver.clone(),
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
                circuit_type: binary.circuit_type,
                skip_set: skip_set.clone(),
                split_count: CYCLES_TRACING_WORKERS_COUNT,
                split_index,
                free_allocator: self.free_allocator_receiver.clone(),
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
            circuit_type: binary.circuit_type,
            skip_set,
            free_allocator: self.free_allocator_receiver.clone(),
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
        drop(work_results_sender);
        let mut final_main_chunks_count = None;
        let mut final_register_values = None;
        let mut final_delegation_chunks_counts = None;
        let mut main_memory_commitments = HashMap::new();
        let mut delegation_memory_commitments = HashMap::new();
        let mut main_proofs = HashMap::new();
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
                let main_circuit_type = binary.circuit_type;
                let circuit_type = CircuitType::Main(main_circuit_type);
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
                    trace!("BATCH[{batch_id}] PROVER sending main circuit {main_circuit_type:?} chunk {circuit_sequence} proof request to GPU manager");
                } else {
                    trace!("BATCH[{batch_id}] PROVER sending main circuit {main_circuit_type:?} chunk {circuit_sequence} memory commitment request to GPU manager");
                }
                gpu_work_requests_sender.send(request).unwrap();
            };
        let mut send_main_work_request = Some(send_main_work_request);
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
                WorkerResult::DelegationWitness {
                    circuit_sequence,
                    witness,
                } => {
                    let id = witness.delegation_type;
                    let delegation_circuit_type = DelegationCircuitType::from(id);
                    if witness.write_timestamp.is_empty() {
                        trace!("BATCH[{batch_id}] PROVER skipping empty delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence}");
                        let allocator = witness.write_timestamp.allocator().clone();
                        drop(witness);
                        assert_eq!(allocator.get_used_mem_current(), 0);
                        self.free_allocator_sender.send(allocator).unwrap();
                    } else {
                        let circuit_type = CircuitType::Delegation(delegation_circuit_type);
                        trace!("BATCH[{batch_id}] PROVER received delegation circuit {:?} chunk {circuit_sequence} witnesses", delegation_circuit_type);
                        let precomputations = self.delegation_circuits_precomputations
                            [&delegation_circuit_type]
                            .clone();
                        let tracing_data = TracingDataHost::Delegation(witness.into());
                        let request = if proving {
                            let proof_request = ProofRequest {
                                batch_id,
                                circuit_type,
                                circuit_sequence,
                                precomputations,
                                tracing_data,
                                external_challenges: external_challenges.unwrap(),
                            };
                            trace!("BATCH[{batch_id}] PROVER sending delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence} proof request");
                            GpuWorkRequest::Proof(proof_request)
                        } else {
                            let memory_commitment_request = MemoryCommitmentRequest {
                                batch_id,
                                circuit_type,
                                circuit_sequence,
                                precomputations,
                                tracing_data,
                            };
                            trace!("BATCH[{batch_id}] PROVER sending delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence} memory commitment request");
                            GpuWorkRequest::MemoryCommitment(memory_commitment_request)
                        };
                        delegation_work_sender
                            .as_ref()
                            .unwrap()
                            .send(request)
                            .unwrap();
                    }
                }
                WorkerResult::DelegationTracingResult {
                    delegation_chunks_counts,
                } => {
                    for (id, count) in delegation_chunks_counts.iter() {
                        let delegation_circuit_type = DelegationCircuitType::from(*id);
                        trace!("BATCH[{batch_id}] PROVER received delegation circuit {delegation_circuit_type:?} tracing result with {count} chunk(s) produced", );
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
                            trace!("BATCH[{batch_id}] PROVER received main circuit {circuit_type:?} chunk {circuit_sequence} memory commitment");
                            if chunks_cache
                                .as_ref()
                                .map_or(false, |cache| !cache.is_at_capacity())
                            {
                                trace!("BATCH[{batch_id}] PROVER caching main circuit {circuit_type:?} chunk {circuit_sequence} trace");
                                let data = TracingDataHost::Main {
                                    setup_and_teardown,
                                    trace,
                                };
                                let entry = ChunksCacheEntry {
                                    circuit_type: CircuitType::Main(circuit_type),
                                    circuit_sequence,
                                    tracing_data: data,
                                };
                                chunks_cache.as_mut().unwrap().queue.push_back(entry);
                            } else {
                                if let Some(setup_and_teardown) = setup_and_teardown {
                                    let allocator =
                                        setup_and_teardown.lazy_init_data.allocator().clone();
                                    drop(setup_and_teardown);
                                    assert_eq!(allocator.get_used_mem_current(), 0);
                                    self.free_allocator_sender.send(allocator).unwrap();
                                }
                                let allocator = trace.cycle_data.allocator().clone();
                                drop(trace);
                                assert_eq!(allocator.get_used_mem_current(), 0);
                                self.free_allocator_sender.send(allocator).unwrap();
                            }
                            assert!(main_memory_commitments
                                .insert(circuit_sequence, merkle_tree_caps)
                                .is_none());
                        }
                        TracingDataHost::Delegation(witness) => {
                            let circuit_type = circuit_type.as_delegation().unwrap();
                            trace!("BATCH[{batch_id}] PROVER received memory commitment for delegation circuit {circuit_type:?} chunk {circuit_sequence}");
                            if CACHE_DELEGATIONS
                                && chunks_cache
                                    .as_ref()
                                    .map_or(false, |cache| !cache.is_at_capacity())
                            {
                                trace!("BATCH[{batch_id}] PROVER caching trace for delegation circuit {circuit_type:?} chunk {circuit_sequence}");
                                let data = TracingDataHost::Delegation(witness);
                                let entry = ChunksCacheEntry {
                                    circuit_type: CircuitType::Delegation(circuit_type),
                                    circuit_sequence,
                                    tracing_data: data,
                                };
                                chunks_cache.as_mut().unwrap().queue.push_back(entry);
                            } else {
                                let allocator = witness.write_timestamp.allocator().clone();
                                drop(witness);
                                assert_eq!(allocator.get_used_mem_current(), 0);
                                self.free_allocator_sender.send(allocator).unwrap();
                            }
                            assert!(delegation_memory_commitments
                                .entry(circuit_type)
                                .or_insert_with(HashMap::new)
                                .insert(circuit_sequence, merkle_tree_caps)
                                .is_none());
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
                            trace!("BATCH[{batch_id}] PROVER received proof for main circuit {circuit_type:?} chunk {circuit_sequence}");
                            if let Some(setup_and_teardown) = setup_and_teardown {
                                let allocator =
                                    setup_and_teardown.lazy_init_data.allocator().clone();
                                drop(setup_and_teardown);
                                assert_eq!(allocator.get_used_mem_current(), 0);
                                self.free_allocator_sender.send(allocator).unwrap();
                            }
                            let allocator = trace.cycle_data.allocator().clone();
                            drop(trace);
                            assert_eq!(allocator.get_used_mem_current(), 0);
                            self.free_allocator_sender.send(allocator).unwrap();
                            assert!(main_proofs.insert(circuit_sequence, proof).is_none());
                        }
                        TracingDataHost::Delegation(witness) => {
                            let circuit_type = circuit_type.as_delegation().unwrap();
                            trace!("BATCH[{batch_id}] PROVER received proof for delegation circuit: {circuit_type:?} chunk {circuit_sequence}");
                            let circuit_type = DelegationCircuitType::from(witness.delegation_type);
                            let allocator = witness.write_timestamp.allocator().clone();
                            drop(witness);
                            assert_eq!(allocator.get_used_mem_current(), 0);
                            self.free_allocator_sender.send(allocator).unwrap();
                            assert!(delegation_proofs
                                .entry(circuit_type)
                                .or_insert_with(HashMap::new)
                                .insert(circuit_sequence, proof)
                                .is_none());
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
                assert_eq!(count, delegation_proofs.get(&id.into()).unwrap().len());
            }
        } else {
            assert!(main_proofs.is_empty());
            assert!(delegation_proofs.is_empty());
            assert_eq!(main_memory_commitments.len(), final_main_chunks_count);
            for (id, count) in final_delegation_chunks_counts.unwrap() {
                assert_eq!(
                    count,
                    delegation_memory_commitments.get(&id.into()).unwrap().len()
                );
            }
        }
        let main_memory_commitments = main_memory_commitments
            .into_iter()
            .sorted_by_key(|(index, _)| *index)
            .map(|(_, caps)| caps)
            .collect_vec();
        let delegation_memory_commitments = delegation_memory_commitments
            .into_iter()
            .sorted_by_key(|(t, _)| *t)
            .map(|(t, c)| {
                let caps = c
                    .into_iter()
                    .sorted_by_key(|(index, _)| *index)
                    .map(|(_, caps)| caps)
                    .collect_vec();
                (t as u32, caps)
            })
            .collect_vec();
        let main_proofs = main_proofs
            .into_iter()
            .sorted_by_key(|(index, _)| *index)
            .map(|(_, proof)| proof)
            .collect_vec();
        let delegation_proofs = delegation_proofs
            .into_iter()
            .sorted_by_key(|(t, _)| *t)
            .map(|(t, p)| {
                let proofs = p
                    .into_iter()
                    .sorted_by_key(|(id, _)| *id)
                    .map(|(_, proofs)| proofs)
                    .collect_vec();
                (t as u32, proofs)
            })
            .collect_vec();
        (
            final_register_values,
            main_memory_commitments,
            delegation_memory_commitments,
            main_proofs,
            delegation_proofs,
        )
    }

    fn commit_memory_inner(
        &self,
        chunks_cache: &mut Option<ChunksCache<A>>,
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
            "BATCH[{batch_id}] PROVER producing memory commitments for binary with key {:?}",
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
            chunks_cache,
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
            None,
        );
        assert!(main_proofs.is_empty());
        assert!(delegation_proofs.is_empty());
        info!(
            "BATCH[{batch_id}] PROVER produced memory commitments for binary with key {:?} in {:.3}s",
            binary_key,
            timer.elapsed().as_secs_f64()
        );
        (
            final_register_values,
            main_memory_commitments,
            delegation_memory_commitments,
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
        self.commit_memory_inner(
            &mut None,
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
        )
    }

    fn prove_inner(
        &self,
        chunks_cache: &mut Option<ChunksCache<A>>,
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
            chunks_cache,
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
        self.prove_inner(
            &mut None,
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
            external_challenges,
        )
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
        let cache_capacity = self.device_count * 2;
        let mut chunks_cache = Some(ChunksCache::new(cache_capacity));
        let (final_register_values, main_memory_commitments, delegation_memory_commitments) = self
            .commit_memory_inner(
                &mut chunks_cache,
                batch_id,
                binary_key,
                num_instances_upper_bound,
                non_determinism_source.clone(),
            );
        let maximum_cached_count = if CACHE_DELEGATIONS {
            main_memory_commitments.len()
                + delegation_memory_commitments
                    .iter()
                    .map(|(_, v)| v.len())
                    .sum::<usize>()
        } else {
            main_memory_commitments.len()
        };
        assert_eq!(
            chunks_cache.as_ref().unwrap().len(),
            min(cache_capacity, maximum_cached_count)
        );
        let memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
            self.binaries[&binary_key]
                .precomputations
                .tree_caps
                .get()
                .unwrap(),
            &final_register_values,
            &main_memory_commitments,
            &delegation_memory_commitments,
        );
        let produce_delegation_challenge = self.binaries[&binary_key]
            .circuit_type
            .needs_delegation_challenge();
        let external_challenges = ExternalChallenges::draw_from_transcript_seed(
            memory_challenges_seed,
            produce_delegation_challenge,
        );
        let result = self.prove_inner(
            &mut chunks_cache,
            batch_id,
            binary_key,
            num_instances_upper_bound,
            non_determinism_source,
            external_challenges,
        );
        assert!(chunks_cache.is_none());
        let (prove_final_register_values, main_proofs, delegation_proofs) = &result;
        assert_eq!(&final_register_values, prove_final_register_values);
        let prove_main_memory_commitments = main_proofs
            .iter()
            .map(|p| p.memory_tree_caps.clone())
            .collect_vec();
        assert_eq!(main_memory_commitments, prove_main_memory_commitments);
        let prove_delegation_memory_commitments = delegation_proofs
            .iter()
            .map(|(t, p)| {
                (
                    *t,
                    p.iter()
                        .map(|proof| proof.memory_tree_caps.clone())
                        .collect_vec(),
                )
            })
            .collect_vec();
        assert_eq!(
            delegation_memory_commitments,
            prove_delegation_memory_commitments
        );
        info!(
            "BATCH[{batch_id}] PROVER committed to memory and produced proofs for binary with key {:?} in {:.3}s",
            binary_key,
            timer.elapsed().as_secs_f64()
        );
        result
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
                let func = get_cpu_worker_func::<IMWithoutSignedMulDivIsaConfig, _>(
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
            MainCircuitType::ReducedRiscVLog23Machine | MainCircuitType::ReducedRiscVMachine => {
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

impl<'a, K: Debug + Eq + Hash> Drop for ExecutionProver<K> {
    fn drop(&mut self) {
        trace!("PROVER waiting for all threads to finish");
        self.wait_group.take().unwrap().wait();
        trace!("PROVER all threads finished");
    }
}
