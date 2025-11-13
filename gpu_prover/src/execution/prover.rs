use super::gpu_manager::{GpuManager, GpuWorkBatch};
use super::precomputations::{get_common_precomputations, CircuitPrecomputations};
use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::circuit_type::{
    CircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::cudart::device::get_device_count;
use crate::cudart::memory::{CudaHostAllocFlags, HostAllocation};
use crate::execution::cpu_worker::{run_split_replayer, run_split_simulator, NonDeterminism};
use crate::execution::gpu_worker::{
    GpuWorkRequest, GpuWorkResult, MemoryCommitmentRequest, MemoryCommitmentResult, ProofRequest,
    ProofResult,
};
use crate::execution::messages::{InitsAndTeardownsData, TracingData, WorkerResult};
use crate::machine_type::MachineType;
use crate::prover::context::ProverContextConfig;
use crossbeam_channel::{bounded, unbounded, Receiver, Sender};
use crossbeam_utils::sync::WaitGroup;
use itertools::Itertools;
use log::{debug, info, trace};
use prover::definitions::{ExternalChallenges, OPTIMAL_FOLDING_PROPERTIES};
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use riscv_transpiler::ir::{
    decode, FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use riscv_transpiler::vm::SimpleTape;
use std::cell::LazyCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter;
use std::sync::{Arc, RwLock};
use trace_and_split::FinalRegisterValue;
use worker::Worker;

type A = ConcurrentStaticHostAllocator;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExecutionKind {
    Unrolled,
    Unified,
}

// const CPU_WORKERS_COUNT: usize = 6;
// const CYCLES_TRACING_WORKERS_COUNT: usize = CPU_WORKERS_COUNT - 2;
// const CACHE_DELEGATIONS: bool = false;

/// Represents an executable binary that can be proven by the prover
///
///  # Fields
/// * `key`: unique identifier for the binary, can be for example a &str or usize, anything that implements Clone, Debug, Eq, and Hash
/// * `circuit_type`: the type of the circuit this binary is for, one of the values from the `MainCircuitType` enumeration
/// * `bytecode`: the bytecode of the binary, can be a Vec<u32> or any other type that can be converted into Box<[u32]>
///
// #[derive(Clone)]
// pub struct ExecutableBinary<K: Clone + Debug + Eq + Hash, B: Into<Box<[u32]>>> {
//     pub key: K,
//     pub circuit_type: MainCircuitType,
//     pub bytecode: B,
// }

struct BinaryHolder {
    execution_kind: ExecutionKind,
    machine_type: MachineType,
    binary_image: Arc<Box<[u32]>>,
    instruction_tape: Arc<SimpleTape>,
    precomputations: HashMap<UnrolledCircuitType, CircuitPrecomputations>,
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration {
    pub prover_context_config: ProverContextConfig,
    pub host_allocator_backing_allocation_size: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocators_per_worker_count: usize,
    pub host_allocators_per_device_count: usize,
}

impl Default for ExecutionProverConfiguration {
    fn default() -> Self {
        Self {
            prover_context_config: Default::default(),
            host_allocator_backing_allocation_size: 1 << 26, // 64 MB
            replay_worker_threads_count: 4,
            host_allocators_per_worker_count: 64, // 4 GB
            host_allocators_per_device_count: 64, // 4 GB
        }
    }
}

enum ExecutionProverResult {
    MemoryCommitment(HashMap<CircuitType, Vec<Vec<MerkleTreeCapVarLength>>>),
    Proof(HashMap<CircuitType, Vec<UnrolledModeProof>>),
}

pub struct ExecutionProver<K: Debug + Eq + Hash> {
    configuration: ExecutionProverConfiguration,
    device_count: usize,
    gpu_manager: GpuManager,
    worker: Worker,
    binary_holders: HashMap<K, BinaryHolder>,
    common_precomputations: HashMap<CircuitType, CircuitPrecomputations>,
    free_allocators_sender: Sender<A>,
    free_allocators_receiver: Receiver<A>,
}

impl<K: Clone + Debug + Eq + Hash> ExecutionProver<K> {
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
    }
    ///  Creates a new instance of `ExecutionProver`.
    ///
    /// # Arguments
    ///
    /// * `max_concurrent_batches`: maximum number of concurrent batches that the prover allocates host buffers for, this is a soft limit, the prover will work with more batches if needed, but it can stall certain operations for some time
    /// * `binaries`: a vector of executable binaries that the prover can work with, each binary must have a unique key
    ///
    /// returns: an instance of `ExecutionProver` that can be used to generate memory commitments and proofs for the provided binaries, it is supposed to be a Singleton instance
    ///
    pub fn with_configuration(configuration: ExecutionProverConfiguration) -> Self {
        let device_count = get_device_count().unwrap() as usize;
        assert_ne!(device_count, 0, "no CUDA capable devices found");
        let gpu_wait_group = WaitGroup::new();
        let gpu_manager =
            GpuManager::new(gpu_wait_group.clone(), configuration.prover_context_config);
        let worker = Worker::new();
        info!(
            "PROVER thread pool with {} threads created",
            worker.num_cores
        );
        let binary_holders = HashMap::new();
        info!("PROVER generating common precomputations");
        let common_precomputations = get_common_precomputations(&worker);
        let host_allocators_count = configuration.replay_worker_threads_count
            * configuration.host_allocators_per_worker_count
            + device_count * configuration.host_allocators_per_device_count;
        let host_allocation_size = configuration.host_allocator_backing_allocation_size;
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
                HostAllocation::alloc(host_allocation_size, CudaHostAllocFlags::DEFAULT).unwrap();
            let allocator =
                ConcurrentStaticHostAllocator::new([allocation], host_allocation_log_chunk_size);
            free_allocators_sender_ref.send(allocator).unwrap();
        });
        gpu_wait_group.wait();
        info!("PROVER initialized");
        Self {
            configuration,
            device_count,
            gpu_manager,
            worker,
            binary_holders,
            common_precomputations,
            free_allocators_sender,
            free_allocators_receiver,
        }
    }

    pub fn add_binary(
        &mut self,
        key: K,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        binary_image: &[u32],
        text_section: &[u32],
    ) {
        let mut binary_image = binary_image.to_vec();
        setups::pad_bytecode_for_proving(&mut binary_image);
        let binary_image = Arc::new(binary_image.into_boxed_slice());
        let decode_fn = match machine_type {
            MachineType::Full => decode::<FullMachineDecoderConfig>,
            MachineType::FullUnsigned => decode::<FullUnsignedMachineDecoderConfig>,
            MachineType::Reduced => decode::<ReducedMachineDecoderConfig>,
        };
        let preprocessed_bytecode = text_section.iter().copied().map(decode_fn).collect_vec();
        let mut text_section = text_section.to_vec();
        setups::pad_bytecode_for_proving(&mut text_section);
        let instruction_tape = Arc::new(SimpleTape::new(&preprocessed_bytecode));
        let circuit_types = match execution_kind {
            ExecutionKind::Unrolled => {
                let memory =
                    UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .into_iter()
                        .copied()
                        .map(|ct| UnrolledCircuitType::Memory(ct));
                let non_memory =
                    UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .into_iter()
                        .copied()
                        .map(|ct| UnrolledCircuitType::NonMemory(ct));
                memory.chain(non_memory).collect_vec()
            }
            ExecutionKind::Unified => {
                assert_eq!(
                    machine_type,
                    MachineType::Reduced,
                    "Unified execution kind is only supported for Reduced machine type"
                );
                vec![UnrolledCircuitType::Unified]
            }
        };
        let precomputations = circuit_types.into_iter().map(|circuit_type| {
            debug!("PROVER producing precomputations for circuit {circuit_type:?} and binary with key {key:?}");
            let precomputations = CircuitPrecomputations::new(CircuitType::Unrolled(circuit_type), &binary_image, &text_section, &self.worker);
            (circuit_type, precomputations)
        }).collect();
        let holder = BinaryHolder {
            execution_kind,
            machine_type,
            binary_image,
            instruction_tape,
            precomputations,
        };
        info!("PROVER inserting binary with key {key:?}");
        assert!(self.binary_holders.insert(key, holder).is_none());
    }

    pub fn remove_binary(&mut self, key: &K) {
        info!("PROVER removing binary with key {key:?}");
        assert!(self.binary_holders.remove(key).is_some());
    }

    fn get_results(
        &self,
        proving: bool,
        batch_id: u64,
        binary_key: &K,
        cycles_limit: usize,
        non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
        external_challenges: Option<ExternalChallenges>,
    ) -> ([FinalRegisterValue; 32], ExecutionProverResult) {
        assert!(proving ^ external_challenges.is_none());
        let replayers_count = self.configuration.replay_worker_threads_count;
        let holder = &self.binary_holders[&binary_key];
        let (work_results_sender, work_results_receiver) = unbounded();
        let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
        let mut gpu_work_requests_sender = Some(gpu_work_requests_sender);
        let (snapshot_sender, snapshot_receiver) = bounded(replayers_count);
        let gpu_work_batch = GpuWorkBatch {
            batch_id,
            receiver: gpu_work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        trace!("BATCH[{batch_id}] PROVER sending work batch to GPU manager");
        self.gpu_manager.send_batch(gpu_work_batch);
        let execution_kind = holder.execution_kind;
        let machine_type = holder.machine_type;
        trace!("BATCH[{batch_id}] PROVER spawning SIMULATOR worker");
        {
            let free_allocators_receiver = self.free_allocators_receiver.clone();
            let binary_image = holder.binary_image.clone();
            let instruction_tape = holder.instruction_tape.clone();
            let work_results_sender = work_results_sender.clone();
            self.worker.pool.spawn(move || match execution_kind {
                ExecutionKind::Unrolled => run_split_simulator(
                    batch_id,
                    machine_type,
                    binary_image,
                    instruction_tape,
                    non_determinism_source,
                    cycles_limit,
                    snapshot_sender,
                    work_results_sender,
                    free_allocators_receiver,
                ),
                ExecutionKind::Unified => todo!(),
            });
        }
        trace!("BATCH[{batch_id}] PROVER spawning REPLAY workers");
        for worker_id in 0..replayers_count {
            let instruction_tape = holder.instruction_tape.clone();
            let snapshot_receiver = snapshot_receiver.clone();
            let work_results_sender = work_results_sender.clone();
            self.worker.pool.spawn(move || match execution_kind {
                ExecutionKind::Unrolled => run_split_replayer(
                    batch_id,
                    worker_id,
                    instruction_tape,
                    snapshot_receiver,
                    work_results_sender,
                ),
                ExecutionKind::Unified => todo!(),
            });
        }
        drop(snapshot_receiver);
        drop(work_results_sender);
        let mut final_register_values = None;
        let mut expected_requests_count = 0;
        let mut pending_requests_count = 0;
        let mut tracing_data: HashMap<(CircuitType, usize), TracingData<A>> = HashMap::new();
        let mut tracing_data_key_by_snapshot_index: HashMap<usize, Vec<(CircuitType, usize)>> =
            HashMap::new();
        let mut processed_snapshots = HashSet::<usize>::new();
        let mut gpu_work_requests = VecDeque::new();
        let mut memory_commitments = HashMap::new();
        let mut proofs = HashMap::new();
        let get_gpu_work_request = |tracing_data: TracingData<A>| -> GpuWorkRequest<A> {
            let TracingData {
                circuit_type,
                sequence_id,
                tracing_data,
                ..
            } = tracing_data;
            let precomputations = match circuit_type {
                CircuitType::Delegation(_)
                | CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    self.common_precomputations[&circuit_type].clone()
                }
                CircuitType::Unrolled(circuit_type) => {
                    holder.precomputations[&circuit_type].clone()
                }
            };
            let inits_and_teardowns = match circuit_type {
                CircuitType::Unrolled(UnrolledCircuitType::Unified) => todo!(),
                _ => None,
            };
            let tracing_data = Some(tracing_data);
            if proving {
                let request = ProofRequest {
                    batch_id,
                    circuit_type,
                    sequence_id,
                    precomputations,
                    inits_and_teardowns,
                    tracing_data,
                    external_challenges: external_challenges.clone().unwrap(),
                };
                GpuWorkRequest::Proof(request)
            } else {
                let request = MemoryCommitmentRequest {
                    batch_id,
                    circuit_type,
                    sequence_id,
                    precomputations,
                    inits_and_teardowns,
                    tracing_data,
                };
                GpuWorkRequest::MemoryCommitment(request)
            }
        };
        for work_result in work_results_receiver {
            match work_result {
                WorkerResult::InitsAndTeardownsData(data) => {
                    let InitsAndTeardownsData {
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                    } = data;
                    match circuit_type {
                        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                            assert!(inits_and_teardowns.is_some());
                            let precomputations =
                                self.common_precomputations[&circuit_type].clone();
                            let request = if proving {
                                let request = ProofRequest {
                                    batch_id,
                                    circuit_type,
                                    sequence_id,
                                    precomputations,
                                    inits_and_teardowns,
                                    tracing_data: None,
                                    external_challenges: external_challenges.clone().unwrap(),
                                };
                                GpuWorkRequest::Proof(request)
                            } else {
                                let request = MemoryCommitmentRequest {
                                    batch_id,
                                    circuit_type,
                                    sequence_id,
                                    precomputations,
                                    inits_and_teardowns,
                                    tracing_data: None,
                                };
                                GpuWorkRequest::MemoryCommitment(request)
                            };
                            gpu_work_requests.push_back(request);
                            expected_requests_count += 1;
                        }
                        CircuitType::Unrolled(UnrolledCircuitType::Unified) => todo!(),
                        _ => panic!("unexpected circuit type for inits and teardowns data"),
                    }
                }
                WorkerResult::TracingData(data) => {
                    if data
                        .participating_snapshot_indexes
                        .is_subset(&processed_snapshots)
                    {
                        let request = get_gpu_work_request(data);
                        gpu_work_requests.push_back(request);
                    } else {
                        let key = (data.circuit_type, data.sequence_id);
                        for snapshot_index in data.participating_snapshot_indexes.iter().copied() {
                            let entry = tracing_data_key_by_snapshot_index
                                .entry(snapshot_index)
                                .or_insert_with(|| Vec::new());
                            assert!(!entry.contains(&key));
                            entry.push(key);
                        }
                        assert!(tracing_data.insert(key, data).is_none());
                    }
                    expected_requests_count += 1;
                }
                WorkerResult::SimulationResult {
                    cycles_count: _,
                    final_register_values: final_values,
                } => {
                    final_register_values = Some(final_values);
                }
                WorkerResult::SnapshotReplayed(sequence_id) => {
                    assert!(processed_snapshots.insert(sequence_id));
                    if let Some(keys) = tracing_data_key_by_snapshot_index.get_mut(&sequence_id) {
                        for key in keys.clone().iter() {
                            if tracing_data
                                .get(key)
                                .unwrap()
                                .participating_snapshot_indexes
                                .is_subset(&processed_snapshots)
                            {
                                let (index, _) =
                                    keys.iter().copied().find_position(|k| k.eq(key)).unwrap();
                                keys.remove(index);
                                let data = tracing_data.remove(key).unwrap();
                                let request = get_gpu_work_request(data);
                                gpu_work_requests.push_back(request);
                            }
                        }
                    }
                }
                WorkerResult::GpuWorkResult(result) => match result {
                    GpuWorkResult::MemoryCommitment(commitment) => {
                        assert!(!proving);
                        let MemoryCommitmentResult {
                            batch_id,
                            circuit_type,
                            sequence_id,
                            inits_and_teardowns,
                            tracing_data,
                            merkle_tree_caps,
                        } = commitment;
                        trace!("BATCH[{batch_id}] PROVER received memory commitment for circuit {circuit_type:?}[{sequence_id}]");
                        if let Some(inits_and_teardowns) = inits_and_teardowns {
                            for allocator in inits_and_teardowns.into_allocators() {
                                self.free_allocators_sender.send(allocator).unwrap();
                            }
                        }
                        if let Some(tracing_data) = tracing_data {
                            for allocator in tracing_data.into_allocators() {
                                self.free_allocators_sender.send(allocator).unwrap();
                            }
                        }
                        let entry = memory_commitments
                            .entry(circuit_type)
                            .or_insert_with(|| HashMap::new());
                        assert!(entry.insert(sequence_id, merkle_tree_caps).is_none());
                    }
                    GpuWorkResult::Proof(proof) => {
                        assert!(proving);
                        let ProofResult {
                            batch_id,
                            circuit_type,
                            sequence_id,
                            inits_and_teardowns,
                            tracing_data,
                            proof,
                        } = proof;
                        trace!("BATCH[{batch_id}] PROVER received proof for circuit {circuit_type:?}[{sequence_id}]");
                        if let Some(inits_and_teardowns) = inits_and_teardowns {
                            for allocator in inits_and_teardowns.into_allocators() {
                                self.free_allocators_sender.send(allocator).unwrap();
                            }
                        }
                        if let Some(tracing_data) = tracing_data {
                            for allocator in tracing_data.into_allocators() {
                                self.free_allocators_sender.send(allocator).unwrap();
                            }
                        }
                        let entry = proofs.entry(circuit_type).or_insert_with(|| HashMap::new());
                        assert!(entry.insert(sequence_id, proof).is_none());
                    }
                },
            }
            while let Some(request) = gpu_work_requests.pop_front() {
                gpu_work_requests_sender
                    .as_ref()
                    .unwrap()
                    .send(request)
                    .unwrap();
                pending_requests_count += 1;
            }
            if pending_requests_count == expected_requests_count && final_register_values.is_some()
            {
                gpu_work_requests_sender = None;
            }
        }
        let final_register_values = final_register_values.unwrap();
        let result = if proving {
            let count = proofs.values().map(|v| v.len()).sum::<usize>();
            assert_eq!(expected_requests_count, count);
            let proofs = proofs
                .into_iter()
                .map(|(ct, v)| {
                    let vec = v
                        .into_iter()
                        .sorted_by_key(|(key, _)| *key)
                        .map(|(_, v)| v)
                        .collect_vec();
                    (ct, vec)
                })
                .collect();
            ExecutionProverResult::Proof(proofs)
        } else {
            let count = memory_commitments.values().map(|v| v.len()).sum::<usize>();
            assert_eq!(expected_requests_count, count);
            let memory_commitments = memory_commitments
                .into_iter()
                .map(|(ct, v)| {
                    let vec = v
                        .into_iter()
                        .sorted_by_key(|(key, _)| *key)
                        .map(|(_, v)| v)
                        .collect_vec();
                    (ct, vec)
                })
                .collect();
            ExecutionProverResult::MemoryCommitment(memory_commitments)
        };
        (final_register_values, result)
    }

    //     fn get_results(
    //         &self,
    //         proving: bool,
    //         chunks_cache: &mut Option<ChunksCache<A>>,
    //         batch_id: u64,
    //         binary_key: &K,
    //         num_instances_upper_bound: usize,
    //         non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
    //         external_challenges: Option<ExternalChallenges>,
    //     ) -> (
    //         [FinalRegisterValue; 32],
    //         Vec<Vec<MerkleTreeCapVarLength>>,
    //         Vec<(u32, Vec<Vec<MerkleTreeCapVarLength>>)>,
    //         Vec<Proof>,
    //         Vec<(u32, Vec<Proof>)>,
    //     ) {
    //         assert!(proving ^ external_challenges.is_none());
    //         let binary = &self.binaries[&binary_key];
    //         let trace_len = binary.precomputations.compiled_circuit.trace_len;
    //         assert!(trace_len.is_power_of_two());
    //         let cycles_per_circuit = trace_len - 1;
    //         let (work_results_sender, worker_results_receiver) = unbounded();
    //         let (gpu_work_requests_sender, gpu_work_requests_receiver) = unbounded();
    //         let gpu_work_batch = GpuWorkBatch {
    //             batch_id,
    //             receiver: gpu_work_requests_receiver,
    //             sender: work_results_sender.clone(),
    //         };
    //         trace!("BATCH[{batch_id}] PROVER sending work batch to GPU manager");
    //         self.gpu_manager.send_batch(gpu_work_batch);
    //         let skip_set = chunks_cache
    //             .as_ref()
    //             .map(|c| {
    //                 c.queue
    //                     .iter()
    //                     .map(|entry| (entry.circuit_type, entry.circuit_sequence))
    //                     .collect::<HashSet<(CircuitType, usize)>>()
    //             })
    //             .unwrap_or_default();
    //         let mut main_work_requests_count = 0;
    //         if proving {
    //             if let Some(cache) = chunks_cache.take() {
    //                 let external_challenges = external_challenges.unwrap();
    //                 for entry in cache.queue.into_iter() {
    //                     let ChunksCacheEntry {
    //                         circuit_type,
    //                         circuit_sequence,
    //                         tracing_data,
    //                     } = entry;
    //                     match circuit_type {
    //                         CircuitType::Main(main_circuit_type) => {
    //                             assert_eq!(main_circuit_type, binary.circuit_type);
    //                             let precomputations = binary.precomputations.clone();
    //                             let request = ProofRequest {
    //                                 batch_id,
    //                                 circuit_type,
    //                                 circuit_sequence,
    //                                 precomputations,
    //                                 tracing_data,
    //                                 external_challenges,
    //                             };
    //                             let request = GpuWorkRequest::Proof(request);
    //                             trace!("BATCH[{batch_id}] PROVER sending cached main circuit {main_circuit_type:?} chunk {circuit_sequence} proof request to GPU manager");
    //                             gpu_work_requests_sender.send(request).unwrap();
    //                             main_work_requests_count += 1;
    //                         }
    //                         CircuitType::Delegation(delegation_circuit_type) => {
    //                             let precomputations = self.delegation_circuits_precomputations
    //                                 [&delegation_circuit_type]
    //                                 .clone();
    //                             let request = ProofRequest {
    //                                 batch_id,
    //                                 circuit_type,
    //                                 circuit_sequence,
    //                                 precomputations,
    //                                 tracing_data,
    //                                 external_challenges,
    //                             };
    //                             let request = GpuWorkRequest::Proof(request);
    //                             trace!("BATCH[{batch_id}] PROVER sending cached delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence} proof request to GPU manager");
    //                             gpu_work_requests_sender.send(request).unwrap();
    //                         }
    //                         CircuitType::Unrolled(_) => todo!(),
    //                     }
    //                 }
    //             }
    //         }
    //         trace!("BATCH[{batch_id}] PROVER spawning CPU workers");
    //         let non_determinism_source = Arc::new(non_determinism_source);
    //         let mut cpu_worker_id = 0;
    //         let ram_tracing_mode = CpuWorkerMode::TraceTouchedRam {
    //             circuit_type: binary.circuit_type,
    //             skip_set: skip_set.clone(),
    //             free_allocator: self.free_allocator_receiver.clone(),
    //         };
    //         self.spawn_cpu_worker(
    //             binary.circuit_type,
    //             batch_id,
    //             cpu_worker_id,
    //             num_instances_upper_bound,
    //             binary.bytecode.clone(),
    //             non_determinism_source.clone(),
    //             ram_tracing_mode,
    //             work_results_sender.clone(),
    //         );
    //         cpu_worker_id += 1;
    //         for split_index in 0..CYCLES_TRACING_WORKERS_COUNT {
    //             let ram_tracing_mode = CpuWorkerMode::TraceCycles {
    //                 circuit_type: binary.circuit_type,
    //                 skip_set: skip_set.clone(),
    //                 split_count: CYCLES_TRACING_WORKERS_COUNT,
    //                 split_index,
    //                 free_allocator: self.free_allocator_receiver.clone(),
    //             };
    //             self.spawn_cpu_worker(
    //                 binary.circuit_type,
    //                 batch_id,
    //                 cpu_worker_id,
    //                 num_instances_upper_bound,
    //                 binary.bytecode.clone(),
    //                 non_determinism_source.clone(),
    //                 ram_tracing_mode,
    //                 work_results_sender.clone(),
    //             );
    //             cpu_worker_id += 1;
    //         }
    //         let delegation_mode = CpuWorkerMode::TraceDelegations {
    //             circuit_type: binary.circuit_type,
    //             skip_set,
    //             free_allocator: self.free_allocator_receiver.clone(),
    //         };
    //         self.spawn_cpu_worker(
    //             binary.circuit_type,
    //             batch_id,
    //             cpu_worker_id,
    //             num_instances_upper_bound,
    //             binary.bytecode.clone(),
    //             non_determinism_source.clone(),
    //             delegation_mode,
    //             work_results_sender.clone(),
    //         );
    //         trace!("BATCH[{batch_id}] PROVER CPU workers spawned");
    //         drop(work_results_sender);
    //         let mut final_main_chunks_count = None;
    //         let mut final_register_values = None;
    //         let mut final_delegation_chunks_counts = None;
    //         let mut main_memory_commitments = HashMap::new();
    //         let mut delegation_memory_commitments = HashMap::new();
    //         let mut main_proofs = HashMap::new();
    //         let mut delegation_proofs = HashMap::new();
    //         let mut inits_and_teardowns_chunks = HashMap::new();
    //         let mut cycles_chunks = HashMap::new();
    //         let mut delegation_work_sender = Some(gpu_work_requests_sender.clone());
    //         let send_main_work_request =
    //             move |circuit_sequence: usize,
    //                   inits_and_teardowns_chunk: Option<ShuffleRamSetupAndTeardown<_>>,
    //                   cycles_chunk: CycleTracingData<_>| {
    //                 let inits_and_teardowns = inits_and_teardowns_chunk.map(|chunk| chunk.into());
    //                 let trace = MainTraceHost {
    //                     cycles_traced: cycles_chunk.per_cycle_data.len(),
    //                     cycle_data: Arc::new(cycles_chunk.per_cycle_data),
    //                     num_cycles_chunk_size: cycles_per_circuit,
    //                 };
    //                 let tracing_data = TracingDataHost::Main {
    //                     inits_and_teardowns,
    //                     trace,
    //                 };
    //                 let main_circuit_type = binary.circuit_type;
    //                 let circuit_type = CircuitType::Main(main_circuit_type);
    //                 let precomputations = binary.precomputations.clone();
    //                 let request = if proving {
    //                     let proof_request = ProofRequest {
    //                         batch_id,
    //                         circuit_type,
    //                         circuit_sequence,
    //                         precomputations,
    //                         tracing_data,
    //                         external_challenges: external_challenges.unwrap(),
    //                     };
    //                     GpuWorkRequest::Proof(proof_request)
    //                 } else {
    //                     let memory_commitment_request = MemoryCommitmentRequest {
    //                         batch_id,
    //                         circuit_type,
    //                         circuit_sequence,
    //                         precomputations,
    //                         tracing_data,
    //                     };
    //                     GpuWorkRequest::MemoryCommitment(memory_commitment_request)
    //                 };
    //                 if proving {
    //                     trace!("BATCH[{batch_id}] PROVER sending main circuit {main_circuit_type:?} chunk {circuit_sequence} proof request to GPU manager");
    //                 } else {
    //                     trace!("BATCH[{batch_id}] PROVER sending main circuit {main_circuit_type:?} chunk {circuit_sequence} memory commitment request to GPU manager");
    //                 }
    //                 gpu_work_requests_sender.send(request).unwrap();
    //             };
    //         let mut send_main_work_request = Some(send_main_work_request);
    //         for result in worker_results_receiver {
    //             match result {
    //                 WorkerResult::InitsAndTeardownsChunk(chunk) => {
    //                     let InitsAndTeardownsChunk {
    //                         index,
    //                         chunk: inits_and_teardowns_chunk,
    //                     } = chunk;
    //                     trace!("BATCH[{batch_id}] PROVER received setup and teardown chunk {index}");
    //                     if let Some(cycles_chunk) = cycles_chunks.remove(&index) {
    //                         let send = send_main_work_request.as_ref().unwrap();
    //                         send(index, inits_and_teardowns_chunk, cycles_chunk);
    //                         main_work_requests_count += 1;
    //                     } else {
    //                         inits_and_teardowns_chunks.insert(index, inits_and_teardowns_chunk);
    //                     }
    //                 }
    //                 WorkerResult::RAMTracingResult {
    //                     chunks_traced_count,
    //                     final_register_values: values,
    //                 } => {
    //                     trace!("BATCH[{batch_id}] PROVER received RAM tracing result with final register values and {chunks_traced_count} chunk(s) traced");
    //                     let previous_count = final_main_chunks_count.replace(chunks_traced_count);
    //                     assert!(previous_count.is_none_or(|v| v == chunks_traced_count));
    //                     final_register_values = Some(values);
    //                 }
    //                 WorkerResult::CyclesChunk(chunk) => {
    //                     let CyclesChunk { index, data } = chunk;
    //                     trace!("BATCH[{batch_id}] PROVER received cycles chunk {index}");
    //                     if let Some(inits_and_teardowns_chunk) =
    //                         inits_and_teardowns_chunks.remove(&index)
    //                     {
    //                         let send = send_main_work_request.as_ref().unwrap();
    //                         send(index, inits_and_teardowns_chunk, data);
    //                         main_work_requests_count += 1;
    //                     } else {
    //                         cycles_chunks.insert(index, data);
    //                     }
    //                 }
    //                 WorkerResult::CyclesTracingResult {
    //                     chunks_traced_count,
    //                 } => {
    //                     trace!("BATCH[{batch_id}] PROVER received cycles tracing result with {chunks_traced_count} chunk(s) traced");
    //                     let previous_count = final_main_chunks_count.replace(chunks_traced_count);
    //                     assert!(previous_count.is_none_or(|count| count == chunks_traced_count));
    //                 }
    //                 WorkerResult::DelegationWitness {
    //                     circuit_sequence,
    //                     witness,
    //                 } => {
    //                     let id = witness.delegation_type;
    //                     let delegation_circuit_type = DelegationCircuitType::from(id);
    //                     if witness.write_timestamp.is_empty() {
    //                         trace!("BATCH[{batch_id}] PROVER skipping empty delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence}");
    //                         let allocator = witness.write_timestamp.allocator().clone();
    //                         drop(witness);
    //                         assert_eq!(allocator.get_used_mem_current(), 0);
    //                         self.free_allocator_sender.send(allocator).unwrap();
    //                     } else {
    //                         let circuit_type = CircuitType::Delegation(delegation_circuit_type);
    //                         trace!("BATCH[{batch_id}] PROVER received delegation circuit {:?} chunk {circuit_sequence} witnesses", delegation_circuit_type);
    //                         let precomputations = self.delegation_circuits_precomputations
    //                             [&delegation_circuit_type]
    //                             .clone();
    //                         let tracing_data = TracingDataHost::Delegation(witness.into());
    //                         let request = if proving {
    //                             let proof_request = ProofRequest {
    //                                 batch_id,
    //                                 circuit_type,
    //                                 circuit_sequence,
    //                                 precomputations,
    //                                 tracing_data,
    //                                 external_challenges: external_challenges.unwrap(),
    //                             };
    //                             trace!("BATCH[{batch_id}] PROVER sending delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence} proof request");
    //                             GpuWorkRequest::Proof(proof_request)
    //                         } else {
    //                             let memory_commitment_request = MemoryCommitmentRequest {
    //                                 batch_id,
    //                                 circuit_type,
    //                                 circuit_sequence,
    //                                 precomputations,
    //                                 tracing_data,
    //                             };
    //                             trace!("BATCH[{batch_id}] PROVER sending delegation circuit {delegation_circuit_type:?} chunk {circuit_sequence} memory commitment request");
    //                             GpuWorkRequest::MemoryCommitment(memory_commitment_request)
    //                         };
    //                         delegation_work_sender
    //                             .as_ref()
    //                             .unwrap()
    //                             .send(request)
    //                             .unwrap();
    //                     }
    //                 }
    //                 WorkerResult::DelegationTracingResult {
    //                     delegation_chunks_counts,
    //                 } => {
    //                     for (id, count) in delegation_chunks_counts.iter() {
    //                         let delegation_circuit_type = DelegationCircuitType::from(*id);
    //                         trace!("BATCH[{batch_id}] PROVER received delegation circuit {delegation_circuit_type:?} tracing result with {count} chunk(s) produced", );
    //                     }
    //                     assert!(final_delegation_chunks_counts
    //                         .replace(delegation_chunks_counts)
    //                         .is_none());
    //                     trace!(
    //                         "BATCH[{batch_id}] PROVER sent all delegation memory commitment requests"
    //                     );
    //                     delegation_work_sender = None;
    //                 }
    //                 WorkerResult::MemoryCommitment(commitment) => {
    //                     assert!(!proving);
    //                     let MemoryCommitmentResult {
    //                         batch_id: result_batch_id,
    //                         circuit_type,
    //                         circuit_sequence,
    //                         tracing_data,
    //                         merkle_tree_caps,
    //                     } = commitment;
    //                     assert_eq!(result_batch_id, batch_id);
    //                     match tracing_data {
    //                         TracingDataHost::Main {
    //                             inits_and_teardowns,
    //                             trace,
    //                         } => {
    //                             let circuit_type = circuit_type.as_main().unwrap();
    //                             trace!("BATCH[{batch_id}] PROVER received main circuit {circuit_type:?} chunk {circuit_sequence} memory commitment");
    //                             if chunks_cache
    //                                 .as_ref()
    //                                 .map_or(false, |cache| !cache.is_at_capacity())
    //                             {
    //                                 trace!("BATCH[{batch_id}] PROVER caching main circuit {circuit_type:?} chunk {circuit_sequence} trace");
    //                                 let data = TracingDataHost::Main {
    //                                     inits_and_teardowns,
    //                                     trace,
    //                                 };
    //                                 let entry = ChunksCacheEntry {
    //                                     circuit_type: CircuitType::Main(circuit_type),
    //                                     circuit_sequence,
    //                                     tracing_data: data,
    //                                 };
    //                                 chunks_cache.as_mut().unwrap().queue.push_back(entry);
    //                             } else {
    //                                 if let Some(inits_and_teardowns) = inits_and_teardowns {
    //                                     let allocator =
    //                                         inits_and_teardowns.inits_and_teardowns.allocator().clone();
    //                                     drop(inits_and_teardowns);
    //                                     assert_eq!(allocator.get_used_mem_current(), 0);
    //                                     self.free_allocator_sender.send(allocator).unwrap();
    //                                 }
    //                                 let allocator = trace.cycle_data.allocator().clone();
    //                                 drop(trace);
    //                                 assert_eq!(allocator.get_used_mem_current(), 0);
    //                                 self.free_allocator_sender.send(allocator).unwrap();
    //                             }
    //                             assert!(main_memory_commitments
    //                                 .insert(circuit_sequence, merkle_tree_caps)
    //                                 .is_none());
    //                         }
    //                         TracingDataHost::Delegation(witness) => {
    //                             let circuit_type = circuit_type.as_delegation().unwrap();
    //                             trace!("BATCH[{batch_id}] PROVER received memory commitment for delegation circuit {circuit_type:?} chunk {circuit_sequence}");
    //                             if CACHE_DELEGATIONS
    //                                 && chunks_cache
    //                                     .as_ref()
    //                                     .map_or(false, |cache| !cache.is_at_capacity())
    //                             {
    //                                 trace!("BATCH[{batch_id}] PROVER caching trace for delegation circuit {circuit_type:?} chunk {circuit_sequence}");
    //                                 let data = TracingDataHost::Delegation(witness);
    //                                 let entry = ChunksCacheEntry {
    //                                     circuit_type: CircuitType::Delegation(circuit_type),
    //                                     circuit_sequence,
    //                                     tracing_data: data,
    //                                 };
    //                                 chunks_cache.as_mut().unwrap().queue.push_back(entry);
    //                             } else {
    //                                 let allocator = witness.write_timestamp.allocator().clone();
    //                                 drop(witness);
    //                                 assert_eq!(allocator.get_used_mem_current(), 0);
    //                                 self.free_allocator_sender.send(allocator).unwrap();
    //                             }
    //                             assert!(delegation_memory_commitments
    //                                 .entry(circuit_type)
    //                                 .or_insert_with(HashMap::new)
    //                                 .insert(circuit_sequence, merkle_tree_caps)
    //                                 .is_none());
    //                         }
    //                         TracingDataHost::Unrolled(_) => todo!(),
    //                     }
    //                 }
    //                 WorkerResult::Proof(proof) => {
    //                     assert!(proving);
    //                     let ProofResult {
    //                         batch_id: result_batch_id,
    //                         circuit_type,
    //                         circuit_sequence,
    //                         tracing_data,
    //                         proof,
    //                     } = proof;
    //                     assert_eq!(result_batch_id, batch_id);
    //                     match tracing_data {
    //                         TracingDataHost::Main {
    //                             inits_and_teardowns,
    //                             trace,
    //                         } => {
    //                             let circuit_type = circuit_type.as_main().unwrap();
    //                             trace!("BATCH[{batch_id}] PROVER received proof for main circuit {circuit_type:?} chunk {circuit_sequence}");
    //                             if let Some(inits_and_teardowns) = inits_and_teardowns {
    //                                 let allocator =
    //                                     inits_and_teardowns.inits_and_teardowns.allocator().clone();
    //                                 drop(inits_and_teardowns);
    //                                 assert_eq!(allocator.get_used_mem_current(), 0);
    //                                 self.free_allocator_sender.send(allocator).unwrap();
    //                             }
    //                             let allocator = trace.cycle_data.allocator().clone();
    //                             drop(trace);
    //                             assert_eq!(allocator.get_used_mem_current(), 0);
    //                             self.free_allocator_sender.send(allocator).unwrap();
    //                             assert!(main_proofs
    //                                 .insert(circuit_sequence, proof.into_regular().unwrap())
    //                                 .is_none());
    //                         }
    //                         TracingDataHost::Delegation(witness) => {
    //                             let circuit_type = circuit_type.as_delegation().unwrap();
    //                             trace!("BATCH[{batch_id}] PROVER received proof for delegation circuit: {circuit_type:?} chunk {circuit_sequence}");
    //                             let circuit_type = DelegationCircuitType::from(witness.delegation_type);
    //                             let allocator = witness.write_timestamp.allocator().clone();
    //                             drop(witness);
    //                             assert_eq!(allocator.get_used_mem_current(), 0);
    //                             self.free_allocator_sender.send(allocator).unwrap();
    //                             assert!(delegation_proofs
    //                                 .entry(circuit_type)
    //                                 .or_insert_with(HashMap::new)
    //                                 .insert(circuit_sequence, proof.into_regular().unwrap())
    //                                 .is_none());
    //                         }
    //                         TracingDataHost::Unrolled(_) => todo!(),
    //                     }
    //                 }
    //             };
    //             if send_main_work_request.is_some() {
    //                 if let Some(count) = final_main_chunks_count {
    //                     if main_work_requests_count == count {
    //                         trace!("BATCH[{batch_id}] PROVER sent all main memory commitment requests");
    //                         send_main_work_request = None;
    //                     }
    //                 }
    //             }
    //         }
    //         assert!(send_main_work_request.is_none());
    //         assert!(delegation_work_sender.is_none());
    //         assert!(inits_and_teardowns_chunks.is_empty());
    //         assert!(cycles_chunks.is_empty());
    //         let final_main_chunks_count = final_main_chunks_count.unwrap();
    //         assert_ne!(final_main_chunks_count, 0);
    //         let final_register_values = final_register_values.unwrap();
    //         if proving {
    //             assert!(main_memory_commitments.is_empty());
    //             assert!(delegation_memory_commitments.is_empty());
    //             assert_eq!(main_proofs.len(), final_main_chunks_count);
    //             for (id, count) in final_delegation_chunks_counts.unwrap() {
    //                 assert_eq!(count, delegation_proofs.get(&id.into()).unwrap().len());
    //             }
    //         } else {
    //             assert!(main_proofs.is_empty());
    //             assert!(delegation_proofs.is_empty());
    //             assert_eq!(main_memory_commitments.len(), final_main_chunks_count);
    //             for (id, count) in final_delegation_chunks_counts.unwrap() {
    //                 assert_eq!(
    //                     count,
    //                     delegation_memory_commitments.get(&id.into()).unwrap().len()
    //                 );
    //             }
    //         }
    //         let main_memory_commitments = main_memory_commitments
    //             .into_iter()
    //             .sorted_by_key(|(index, _)| *index)
    //             .map(|(_, caps)| caps)
    //             .collect_vec();
    //         let delegation_memory_commitments = delegation_memory_commitments
    //             .into_iter()
    //             .sorted_by_key(|(t, _)| *t)
    //             .map(|(t, c)| {
    //                 let caps = c
    //                     .into_iter()
    //                     .sorted_by_key(|(index, _)| *index)
    //                     .map(|(_, caps)| caps)
    //                     .collect_vec();
    //                 (t as u32, caps)
    //             })
    //             .collect_vec();
    //         let main_proofs = main_proofs
    //             .into_iter()
    //             .sorted_by_key(|(index, _)| *index)
    //             .map(|(_, proof)| proof)
    //             .collect_vec();
    //         let delegation_proofs = delegation_proofs
    //             .into_iter()
    //             .sorted_by_key(|(t, _)| *t)
    //             .map(|(t, p)| {
    //                 let proofs = p
    //                     .into_iter()
    //                     .sorted_by_key(|(id, _)| *id)
    //                     .map(|(_, proofs)| proofs)
    //                     .collect_vec();
    //                 (t as u32, proofs)
    //             })
    //             .collect_vec();
    //         (
    //             final_register_values,
    //             main_memory_commitments,
    //             delegation_memory_commitments,
    //             main_proofs,
    //             delegation_proofs,
    //         )
    //     }
    //
    //     fn commit_memory_inner(
    //         &self,
    //         chunks_cache: &mut Option<ChunksCache<A>>,
    //         batch_id: u64,
    //         binary_key: &K,
    //         num_instances_upper_bound: usize,
    //         non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
    //     ) -> (
    //         [FinalRegisterValue; 32],
    //         Vec<Vec<MerkleTreeCapVarLength>>,
    //         Vec<(u32, Vec<Vec<MerkleTreeCapVarLength>>)>,
    //     ) {
    //         info!(
    //             "BATCH[{batch_id}] PROVER producing memory commitments for binary with key {:?}",
    //             &binary_key
    //         );
    //         let timer = Instant::now();
    //         let (
    //             final_register_values,
    //             main_memory_commitments,
    //             delegation_memory_commitments,
    //             main_proofs,
    //             delegation_proofs,
    //         ) = self.get_results(
    //             false,
    //             chunks_cache,
    //             batch_id,
    //             binary_key,
    //             num_instances_upper_bound,
    //             non_determinism_source,
    //             None,
    //         );
    //         assert!(main_proofs.is_empty());
    //         assert!(delegation_proofs.is_empty());
    //         info!(
    //             "BATCH[{batch_id}] PROVER produced memory commitments for binary with key {:?} in {:.3}s",
    //             binary_key,
    //             timer.elapsed().as_secs_f64()
    //         );
    //         (
    //             final_register_values,
    //             main_memory_commitments,
    //             delegation_memory_commitments,
    //         )
    //     }
    //
    //     ///  Produces memory commitments.
    //     ///
    //     /// # Arguments
    //     ///
    //     /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    //     /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    //     /// * `num_instances_upper_bound`: maximum number of main circuit instances that the prover will try to trace, if the simulation does not end within this limit, it will fail
    //     /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    //     ///
    //     /// returns: a tuple containing:
    //     ///     - final register values for the main circuit,
    //     ///     - a vector of memory commitments for the chunks of the main circuit,
    //     ///     - a vector of memory commitments for the chunks of the delegation circuits, where each element is a tuple containing the delegation circuit type and a vector of memory commitments for that type
    //     ///
    //     pub fn commit_memory(
    //         &self,
    //         batch_id: u64,
    //         binary_key: &K,
    //         num_instances_upper_bound: usize,
    //         non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
    //     ) -> (
    //         [FinalRegisterValue; 32],
    //         Vec<Vec<MerkleTreeCapVarLength>>,
    //         Vec<(u32, Vec<Vec<MerkleTreeCapVarLength>>)>,
    //     ) {
    //         self.commit_memory_inner(
    //             &mut None,
    //             batch_id,
    //             binary_key,
    //             num_instances_upper_bound,
    //             non_determinism_source,
    //         )
    //     }
    //
    //     fn prove_inner(
    //         &self,
    //         chunks_cache: &mut Option<ChunksCache<A>>,
    //         batch_id: u64,
    //         binary_key: &K,
    //         num_instances_upper_bound: usize,
    //         non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
    //         external_challenges: ExternalChallenges,
    //     ) -> ([FinalRegisterValue; 32], Vec<Proof>, Vec<(u32, Vec<Proof>)>) {
    //         info!(
    //             "BATCH[{batch_id}] PROVER producing proofs for binary with key {:?}",
    //             &binary_key
    //         );
    //         let timer = Instant::now();
    //         let (
    //             final_register_values,
    //             main_memory_commitments,
    //             delegation_memory_commitments,
    //             main_proofs,
    //             delegation_proofs,
    //         ) = self.get_results(
    //             true,
    //             chunks_cache,
    //             batch_id,
    //             binary_key,
    //             num_instances_upper_bound,
    //             non_determinism_source,
    //             Some(external_challenges),
    //         );
    //         assert!(main_memory_commitments.is_empty());
    //         assert!(delegation_memory_commitments.is_empty());
    //         info!(
    //             "BATCH[{batch_id}] PROVER produced proofs for binary with key {:?} in {:.3}s",
    //             binary_key,
    //             timer.elapsed().as_secs_f64()
    //         );
    //         (final_register_values, main_proofs, delegation_proofs)
    //     }
    //
    //     ///  Produces proofs.
    //     ///
    //     /// # Arguments
    //     ///
    //     /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    //     /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    //     /// * `num_instances_upper_bound`: maximum number of main circuit instances that the prover will try to trace, if the simulation does not end within this limit, it will fail
    //     /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    //     /// * `external_challenges`: an instance of `ExternalChallenges` that contains the challenges to be used in the proof generation
    //     ///
    //     /// returns: a tuple containing:
    //     ///     - final register values for the main circuit,
    //     ///     - a vector of proofs for the chunks of the main circuit,
    //     ///     - a vector of proofs for the chunks of the delegation circuits, where each element is a tuple containing the delegation circuit type and a vector of memory commitments for that type
    //     ///
    //     pub fn prove(
    //         &self,
    //         batch_id: u64,
    //         binary_key: &K,
    //         num_instances_upper_bound: usize,
    //         non_determinism_source: impl NonDeterminism + Send + Sync + 'static,
    //         external_challenges: ExternalChallenges,
    //     ) -> ([FinalRegisterValue; 32], Vec<Proof>, Vec<(u32, Vec<Proof>)>) {
    //         self.prove_inner(
    //             &mut None,
    //             batch_id,
    //             binary_key,
    //             num_instances_upper_bound,
    //             non_determinism_source,
    //             external_challenges,
    //         )
    //     }
    //
    //     ///  Commits to memory and produces proofs using challenge derived from the memory commitments.
    //     ///
    //     /// # Arguments
    //     ///
    //     /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    //     /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    //     /// * `num_instances_upper_bound`: maximum number of main circuit instances that the prover will try to trace, if the simulation does not end within this limit, it will fail
    //     /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    //     ///
    //     /// returns: a tuple containing:
    //     ///     - final register values for the main circuit,
    //     ///     - a vector of proofs for the chunks of the main circuit,
    //     ///     - a vector of proofs for the chunks of the delegation circuits, where each element is a tuple containing the delegation circuit type and a vector of memory commitments for that type
    //     ///
    //     pub fn commit_memory_and_prove(
    //         &self,
    //         batch_id: u64,
    //         binary_key: &K,
    //         num_instances_upper_bound: usize,
    //         non_determinism_source: impl NonDeterminism + Clone + Send + Sync + 'static,
    //     ) -> ([FinalRegisterValue; 32], Vec<Proof>, Vec<(u32, Vec<Proof>)>) {
    //         let timer = Instant::now();
    //         let cache_capacity = self.device_count * 2;
    //         let mut chunks_cache = Some(ChunksCache::new(cache_capacity));
    //         let (final_register_values, main_memory_commitments, delegation_memory_commitments) = self
    //             .commit_memory_inner(
    //                 &mut chunks_cache,
    //                 batch_id,
    //                 binary_key,
    //                 num_instances_upper_bound,
    //                 non_determinism_source.clone(),
    //             );
    //         let maximum_cached_count = if CACHE_DELEGATIONS {
    //             main_memory_commitments.len()
    //                 + delegation_memory_commitments
    //                     .iter()
    //                     .map(|(_, v)| v.len())
    //                     .sum::<usize>()
    //         } else {
    //             main_memory_commitments.len()
    //         };
    //         assert_eq!(
    //             chunks_cache.as_ref().unwrap().len(),
    //             min(cache_capacity, maximum_cached_count)
    //         );
    //         let caps = &self.binaries[&binary_key]
    //             .precomputations
    //             .setup_trees_and_caps
    //             .get()
    //             .unwrap()
    //             .caps;
    //         let memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
    //             caps,
    //             &final_register_values,
    //             &main_memory_commitments,
    //             &delegation_memory_commitments,
    //         );
    //         let produce_delegation_challenge = self.binaries[&binary_key]
    //             .circuit_type
    //             .needs_delegation_challenge();
    //         let external_challenges = ExternalChallenges::draw_from_transcript_seed(
    //             memory_challenges_seed,
    //             produce_delegation_challenge,
    //         );
    //         let result = self.prove_inner(
    //             &mut chunks_cache,
    //             batch_id,
    //             binary_key,
    //             num_instances_upper_bound,
    //             non_determinism_source,
    //             external_challenges,
    //         );
    //         assert!(chunks_cache.is_none());
    //         let (prove_final_register_values, main_proofs, delegation_proofs) = &result;
    //         assert_eq!(&final_register_values, prove_final_register_values);
    //         let prove_main_memory_commitments = main_proofs
    //             .iter()
    //             .map(|p| p.memory_tree_caps.clone())
    //             .collect_vec();
    //         assert_eq!(main_memory_commitments, prove_main_memory_commitments);
    //         let prove_delegation_memory_commitments = delegation_proofs
    //             .iter()
    //             .map(|(t, p)| {
    //                 (
    //                     *t,
    //                     p.iter()
    //                         .map(|proof| proof.memory_tree_caps.clone())
    //                         .collect_vec(),
    //                 )
    //             })
    //             .collect_vec();
    //         assert_eq!(
    //             delegation_memory_commitments,
    //             prove_delegation_memory_commitments
    //         );
    //         info!(
    //             "BATCH[{batch_id}] PROVER committed to memory and produced proofs for binary with key {:?} in {:.3}s",
    //             binary_key,
    //             timer.elapsed().as_secs_f64()
    //         );
    //         result
    //     }
    //
    //     fn spawn_cpu_worker(
    //         &self,
    //         circuit_type: MainCircuitType,
    //         batch_id: u64,
    //         worker_id: usize,
    //         num_main_chunks_upper_bound: usize,
    //         binary: impl Deref<Target = impl Deref<Target = [u32]>> + Send + 'static,
    //         non_determinism: impl Deref<Target = impl NonDeterminism> + Send + 'static,
    //         mode: CpuWorkerMode<A>,
    //         results: Sender<WorkerResult<A>>,
    //     ) {
    //         let wait_group = self.wait_group.as_ref().unwrap().clone();
    //         match circuit_type {
    //             MainCircuitType::FinalReducedRiscVMachine => {
    //                 let func = get_cpu_worker_func::<IWithoutByteAccessIsaConfig, _>(
    //                     wait_group,
    //                     batch_id,
    //                     worker_id,
    //                     num_main_chunks_upper_bound,
    //                     binary,
    //                     non_determinism,
    //                     mode,
    //                     results,
    //                 );
    //                 self.worker.pool.spawn(func);
    //             }
    //             MainCircuitType::MachineWithoutSignedMulDiv => {
    //                 let func = get_cpu_worker_func::<IMStandardIsaConfigWithUnsignedMulDiv, _>(
    //                     wait_group,
    //                     batch_id,
    //                     worker_id,
    //                     num_main_chunks_upper_bound,
    //                     binary,
    //                     non_determinism,
    //                     mode,
    //                     results,
    //                 );
    //                 self.worker.pool.spawn(func);
    //             }
    //             MainCircuitType::ReducedRiscVLog23Machine | MainCircuitType::ReducedRiscVMachine => {
    //                 let func = get_cpu_worker_func::<IWithoutByteAccessIsaConfigWithDelegation, _>(
    //                     wait_group,
    //                     batch_id,
    //                     worker_id,
    //                     num_main_chunks_upper_bound,
    //                     binary,
    //                     non_determinism,
    //                     mode,
    //                     results,
    //                 );
    //                 self.worker.pool.spawn(func);
    //             }
    //             MainCircuitType::RiscVCycles => {
    //                 let func = get_cpu_worker_func::<IMStandardIsaConfig, _>(
    //                     wait_group,
    //                     batch_id,
    //                     worker_id,
    //                     num_main_chunks_upper_bound,
    //                     binary,
    //                     non_determinism,
    //                     mode,
    //                     results,
    //                 );
    //                 self.worker.pool.spawn(func);
    //             }
    //         }
    //     }
}

// impl<'a, K: Debug + Eq + Hash> Drop for ExecutionProver<K> {
//     fn drop(&mut self) {
//         trace!("PROVER waiting for all threads to finish");
//         self.wait_group.take().unwrap().wait();
//         trace!("PROVER all threads finished");
//     }
// }

#[cfg(test)]
mod tests {
    use crate::circuit_type::{CircuitType, UnrolledCircuitType};
    use crate::execution::prover::{ExecutionKind, ExecutionProver, ExecutionProverResult};
    use crate::machine_type::MachineType;
    use crate::tests::{init_logger, read_binary};
    use itertools::Itertools;
    use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use std::path::Path;

    #[test]
    fn test_execution_prover() {
        init_logger();
        let mut prover = ExecutionProver::<usize>::new();
        let binary_image = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
        let text_section = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
        prover.add_binary(
            0,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            &binary_image,
            &text_section,
        );
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 26, 0]);
        let (_, result) =
            prover.get_results(false, 0, &0usize, 1 << 36, non_determinism_source, None);
        // match result {
        //     ExecutionProverResult::MemoryCommitment(memory_commitment) => {
        //         for (circuit_type, commitment) in memory_commitment
        //             .iter()
        //             .filter(|(c, _)| {
        //                 matches!(c, CircuitType::Unrolled(UnrolledCircuitType::NonMemory(_)))
        //             })
        //             .sorted_by_key(|(c, _)| c.as_unrolled().unwrap().get_family_idx())
        //         {
        //             for cap in commitment {
        //                 dbg!(circuit_type, cap);
        //             }
        //         }
        //         for (circuit_type, commitment) in memory_commitment
        //             .iter()
        //             .filter(|(c, _)| {
        //                 matches!(c, CircuitType::Unrolled(UnrolledCircuitType::Memory(_)))
        //             })
        //             .sorted_by_key(|(c, _)| c.as_unrolled().unwrap().get_family_idx())
        //         {
        //             for cap in commitment {
        //                 dbg!(circuit_type, cap);
        //             }
        //         }
        //         for (circuit_type, commitment) in memory_commitment
        //             .iter()
        //             .filter(|(c, _)| {
        //                 matches!(
        //                     c,
        //                     CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
        //                 )
        //             })
        //             .sorted_by_key(|(c, _)| c.as_unrolled().unwrap().get_family_idx())
        //         {
        //             for cap in commitment {
        //                 dbg!(circuit_type, cap);
        //             }
        //         }
        //         for (circuit_type, commitment) in memory_commitment
        //             .iter()
        //             .filter(|(c, _)| matches!(c, CircuitType::Delegation(_)))
        //             .sorted_by_key(|(c, _)| c.as_delegation().unwrap())
        //         {
        //             for cap in commitment {
        //                 dbg!(circuit_type, cap);
        //             }
        //         }
        //     }
        //     ExecutionProverResult::Proof(_) => {}
        // }
        drop(prover);
    }
}
