use super::gpu_manager::GpuManager;
use super::precomputations::{get_common_precomputations, CircuitPrecomputations};
use super::A;
use crate::circuit_type::{
    CircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::cudart::device::get_device_count;
use crate::cudart::memory::{CudaHostAllocFlags, HostAllocation};
use crate::execution::cpu_worker::{run_replayer, run_simulator};
use crate::execution::messages::{
    GpuWorkBatch, GpuWorkRequest, GpuWorkResult, InitsAndTeardownsData, MemoryCommitmentRequest,
    MemoryCommitmentResult, ProofRequest, ProofResult, SimulationResult, TracingData, WorkerResult,
};
use crate::execution::simulation_runner::{LockedBoxedMemoryHolder, LockedBoxedTraceChunk};
use crate::execution::tracing::{SplitTracingType, UnifiedTracingType};
use crate::machine_type::MachineType;
use crate::prover::context::ProverContextConfig;
use crate::prover::tracing_data::TracingDataHost;
use crate::witness::trace_unrolled::ShuffleRamInitsAndTeardownsHost;
use crossbeam_channel::{unbounded, Receiver, Sender};
use crossbeam_utils::sync::WaitGroup;
use cs::definitions::TimestampScalar;
use itertools::Itertools;
use log::{debug, info, trace, warn};
use prover::definitions::{
    AuxArgumentsBoundaryValues, ExternalChallenges, ExternalValues, Transcript,
};
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use riscv_transpiler::ir::{
    preprocess_bytecode, FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig,
    ReducedMachineDecoderConfig,
};
use riscv_transpiler::vm::{NonDeterminismCSRSource, RamPeek, SimpleTape};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::time::Instant;
use trace_and_split::{
    fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits, FinalRegisterValue,
};
use type_map::concurrent::TypeMap;
use verifier_common::MEMORY_DELEGATION_POW_BITS;
use worker::Worker;

/// Specifies the execution mode for the prover.
///
/// Variants:
/// - `Unrolled`: Uses unrolled circuit types for proof and memory commitment generation.
/// - `Unified`: Uses a unified circuit type, supported only for the `Reduced` machine type.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExecutionKind {
    Unrolled,
    Unified,
}

struct BinaryHolder {
    execution_kind: ExecutionKind,
    machine_type: MachineType,
    binary_image: Arc<Box<[u32]>>,
    text_section: Arc<Box<[u32]>>,
    cycles_bound: Option<u32>,
    jit_cache: Arc<Mutex<TypeMap>>,
    instruction_tape: Arc<SimpleTape>,
    precomputations: HashMap<UnrolledCircuitType, CircuitPrecomputations>,
}

/// Configuration for the `ExecutionProver`.
///
/// Fields:
/// - `prover_context_config`: Configuration for the prover context.
/// - `max_thread_pool_threads`: Optional maximum number of threads for the prover's thread pool.
/// - `expected_concurrent_jobs`: Expected number of concurrent jobs the prover will handle.
/// - `replay_worker_threads_count`: Number of threads for replay workers.
/// - `host_allocator_backing_allocation_size`: Size (in bytes) of each host buffer allocation.
/// - `host_allocators_per_job_count`: Number of host allocators allocated per job.
/// - `host_allocators_per_device_count`: Number of host allocators allocated per device.
/// - `min_free_host_allocators_per_job`: Minimum number of free host allocators per job before cache trimming is triggered.
#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration {
    pub prover_context_config: ProverContextConfig,
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_per_job_count: usize,
    pub host_allocators_per_device_count: usize,
    pub min_free_host_allocators_per_job: usize,
}

impl Default for ExecutionProverConfiguration {
    fn default() -> Self {
        Self {
            prover_context_config: Default::default(),
            max_thread_pool_threads: None,
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 8,
            host_allocator_backing_allocation_size: 1 << 26, // 64 MB
            host_allocators_per_job_count: 256,              // 16 GB
            host_allocators_per_device_count: 128,           // 8 GB
            min_free_host_allocators_per_job: 32,            // 2 GB
        }
    }
}

pub struct CommitMemoryResult {
    pub final_register_values: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub circuit_families_memory_caps: BTreeMap<u8, Vec<Vec<MerkleTreeCapVarLength>>>,
    pub inits_and_teardowns_memory_caps: Vec<Vec<MerkleTreeCapVarLength>>,
    pub delegation_circuits_memory_caps: BTreeMap<u32, Vec<Vec<MerkleTreeCapVarLength>>>,
}

pub struct ProveResult {
    pub register_final_values: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub circuit_families_proofs: BTreeMap<u8, Vec<UnrolledModeProof>>,
    pub inits_and_teardowns_proofs: Vec<UnrolledModeProof>,
    pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
    pub pow_challenge: u64,
}

enum ExecutionProverResult {
    CommitMemory(CommitMemoryResult),
    Prove(ProveResult),
}

impl ExecutionProverResult {
    pub fn into_memory_commitment_result(self) -> CommitMemoryResult {
        match self {
            ExecutionProverResult::CommitMemory(result) => result,
            _ => panic!("expected CommitMemoryResult"),
        }
    }

    pub fn into_proof_result(self) -> ProveResult {
        match self {
            ExecutionProverResult::Prove(result) => result,
            _ => panic!("expected ProveResult"),
        }
    }
}

struct TraceCacheEntry {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
}

#[derive(Default)]
struct TraceCache {
    entries: VecDeque<TraceCacheEntry>,
    total_requests_count: usize,
    trivial_unified_inits_and_teardowns_count: usize,
    simulation_result: Option<SimulationResult>,
}

impl TraceCache {
    fn new() -> Self {
        Self::default()
    }

    fn push_back(&mut self, entry: TraceCacheEntry) {
        self.entries.push_back(entry);
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn is_not_initialized(&self) -> bool {
        self.entries.is_empty()
            && self.total_requests_count == 0
            && self.trivial_unified_inits_and_teardowns_count == 0
            && self.simulation_result.is_none()
    }
}

pub struct ExecutionProver {
    configuration: ExecutionProverConfiguration,
    gpu_manager: GpuManager,
    worker: Arc<Worker>,
    memory_holders_cache: Arc<Mutex<Vec<LockedBoxedMemoryHolder>>>,
    trace_chunks_cache: Arc<Mutex<Vec<Vec<LockedBoxedTraceChunk>>>>,
    binary_holders: BTreeMap<usize, BinaryHolder>,
    common_precomputations: BTreeMap<CircuitType, CircuitPrecomputations>,
    free_allocators_sender: Sender<A>,
    free_allocators_receiver: Receiver<A>,
}

impl ExecutionProver {
    ///  Creates a new instance of `ExecutionProver` with the default configuration.
    ///
    /// returns: an instance of `ExecutionProver` that can be used to generate memory commitments and proofs for the provided binaries, it is supposed to be a Singleton instance
    ///
    pub fn new() -> Self {
        Self::with_configuration(ExecutionProverConfiguration::default())
    }

    ///  Creates a new instance of `ExecutionProver` with the supplied configuration.
    ///
    /// # Arguments
    ///
    /// * `configuration`: the configuration for the execution prover
    ///
    /// returns: an instance of `ExecutionProver` that can be used to generate memory commitments and proofs for the provided binaries, it is supposed to be a Singleton instance
    ///
    pub fn with_configuration(configuration: ExecutionProverConfiguration) -> Self {
        let ExecutionProverConfiguration {
            prover_context_config,
            max_thread_pool_threads,
            expected_concurrent_jobs,
            replay_worker_threads_count,
            host_allocator_backing_allocation_size,
            host_allocators_per_job_count,
            host_allocators_per_device_count,
            min_free_host_allocators_per_job: _,
        } = configuration.clone();
        let device_count = get_device_count().unwrap() as usize;
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
        info!("PROVER creating trace chunks cache with {simulator_cache_entries_count} x {trace_chunks_count} entries");
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
        let common_precomputations = get_common_precomputations(&worker);
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
                HostAllocation::alloc(host_allocation_size, CudaHostAllocFlags::DEFAULT).unwrap();
            let allocator = A::new([allocation], host_allocation_log_chunk_size);
            free_allocators_sender_ref.send(allocator).unwrap();
        });
        gpu_wait_group.wait();
        info!("PROVER initialized");
        Self {
            configuration,
            gpu_manager,
            worker,
            memory_holders_cache,
            trace_chunks_cache,
            binary_holders,
            common_precomputations,
            free_allocators_sender,
            free_allocators_receiver,
        }
    }

    /// Adds a binary to the `ExecutionProver` for proof or memory commitment generation.
    ///
    /// # Arguments
    ///
    /// * `key` - A unique identifier for the binary.
    /// * `execution_kind` - Specifies the execution mode (`Unrolled` or `Unified`).
    /// * `machine_type` - The type of machine for which the binary is intended.
    /// * `binary_image` - The unpadded binary image as a vector of `u32`.
    /// * `text_section` - The unpadded text section as a vector of `u32`.
    /// * `cycles_bound` - An optional upper bound on execution cycles.
    pub fn add_binary(
        &mut self,
        key: usize,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        cycles_bound: Option<u32>,
    ) {
        info!("PROVER inserting binary with key {key:?}");
        // setups::pad_bytecode_for_proving(&mut binary_image);
        let preprocess_bytecode_fn = match machine_type {
            MachineType::Full => preprocess_bytecode::<FullMachineDecoderConfig>,
            MachineType::FullUnsigned => preprocess_bytecode::<FullUnsignedMachineDecoderConfig>,
            MachineType::Reduced => preprocess_bytecode::<ReducedMachineDecoderConfig>,
        };
        let preprocessed_bytecode = preprocess_bytecode_fn(&text_section);
        // setups::pad_bytecode_for_proving(&mut text_section);
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
            let mut binary_image = binary_image.clone();
            setups::pad_bytecode_for_proving(&mut binary_image);
            let mut text_section = text_section.clone();
            setups::pad_bytecode_for_proving(&mut text_section);
            let precomputations = CircuitPrecomputations::new(CircuitType::Unrolled(circuit_type), &binary_image, &text_section, &self.worker);
            (circuit_type, precomputations)
        }).collect();
        let binary_image = Arc::new(binary_image.into_boxed_slice());
        let text_section = Arc::new(text_section.into_boxed_slice());
        let jit_cache = Arc::new(Mutex::new(TypeMap::new()));
        let holder = BinaryHolder {
            execution_kind,
            machine_type,
            binary_image,
            text_section,
            cycles_bound,
            instruction_tape,
            jit_cache,
            precomputations,
        };
        assert!(self.binary_holders.insert(key, holder).is_none());
    }

    /// Removes a binary from the `ExecutionProver`.
    ///
    /// # Arguments
    ///
    /// * `key`: A unique identifier for the binary to be removed.
    ///
    /// returns: ()
    ///
    pub fn remove_binary(&mut self, key: usize) {
        info!("PROVER removing binary with key {key:?}");
        assert!(self.binary_holders.remove(&key).is_some());
    }

    fn get_result(
        &self,
        proving: bool,
        cache: &mut Option<TraceCache>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: Arc<Mutex<Option<impl NonDeterminismCSRSource + Send + 'static>>>,
        pow_challenge: u64,
        external_challenges: Option<ExternalChallenges>,
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
        let mut pending_requests_count = 0;
        let mut sent_requests_count = 0;
        let mut requests_served_from_cache = BTreeSet::new();
        let mut trivial_unified_inits_and_teardowns_count = 0;
        let mut trivial_unified_inits_and_teardowns = BTreeSet::new();
        if let Some(cache) = cache.as_mut() {
            trivial_unified_inits_and_teardowns_count =
                cache.trivial_unified_inits_and_teardowns_count;
            for i in 0..trivial_unified_inits_and_teardowns_count {
                trivial_unified_inits_and_teardowns.insert(i);
            }
            for entry in cache.entries.drain(..) {
                let TraceCacheEntry {
                    circuit_type,
                    sequence_id,
                    inits_and_teardowns,
                    tracing_data,
                } = entry;
                if matches!(
                    circuit_type,
                    CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
                ) && sequence_id < trivial_unified_inits_and_teardowns_count
                {
                    assert!(trivial_unified_inits_and_teardowns.remove(&sequence_id));
                }
                let precomputations = match circuit_type {
                    CircuitType::Delegation(_)
                    | CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                        self.common_precomputations[&circuit_type].clone()
                    }
                    CircuitType::Unrolled(circuit_type) => {
                        binary_holder.precomputations[&circuit_type].clone()
                    }
                };
                let request = ProofRequest {
                    batch_id,
                    circuit_type,
                    sequence_id,
                    precomputations,
                    inits_and_teardowns,
                    tracing_data,
                    external_challenges: external_challenges.clone().unwrap(),
                };
                let request = GpuWorkRequest::Proof(request);
                gpu_work_requests_sender.send(request).unwrap();
                pending_requests_count += 1;
                sent_requests_count += 1;
                requests_served_from_cache.insert((circuit_type, sequence_id));
            }
        }
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
            debug!("BATCH[{batch_id}] all proof requests have been served from cache, skipping simulation");
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
                        let mut cache = memory_holders_cache.lock().unwrap();
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
                        let mut cache = trace_chunks_cache.lock().unwrap();
                        let chunks = if cache.is_empty() {
                            drop(cache);
                            warn!("BATCH[{batch_id}] PROVER trace chunks cache is empty, creating a new set of trace chunks");
                            (0..trace_chunks_count)
                                .into_par_iter()
                                .map(|_| LockedBoxedTraceChunk::new())
                                .collect()
                        }
                        else {
                            cache.pop().unwrap()
                        };
                        for chunk in chunks {
                            free_trace_chunks_sender.send(chunk).unwrap();
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
                    memory_holders_cache.lock().unwrap().push(memory_holder);
                    let trace_chunks = free_trace_chunks_receiver_clone.iter().collect_vec();
                    assert_eq!(trace_chunks.len(), trace_chunks_count);
                    trace_chunks_cache.lock().unwrap().push(trace_chunks);
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
        let get_gpu_work_request = |inits_and_teardowns: Option<InitsAndTeardownsData<A>>,
                                    tracing_data: Option<TracingData<A>>|
         -> GpuWorkRequest<A> {
            let mut circuit_type_value = None;
            let mut sequence_id_value = None;
            let inits_and_teardowns = if let Some(inits_and_teardowns) = inits_and_teardowns {
                let InitsAndTeardownsData {
                    circuit_type,
                    sequence_id,
                    inits_and_teardowns,
                } = inits_and_teardowns;
                circuit_type_value = Some(circuit_type);
                sequence_id_value = Some(sequence_id);
                inits_and_teardowns
            } else {
                None
            };
            let tracing_data = if let Some(tracing_data) = tracing_data {
                let TracingData {
                    circuit_type,
                    sequence_id,
                    tracing_data,
                    ..
                } = tracing_data;
                assert_eq!(
                    circuit_type_value.get_or_insert(circuit_type),
                    &circuit_type
                );
                assert_eq!(sequence_id_value.get_or_insert(sequence_id), &sequence_id);
                Some(tracing_data)
            } else {
                None
            };
            let circuit_type = circuit_type_value.unwrap();
            let sequence_id = sequence_id_value.unwrap();
            let precomputations = match circuit_type {
                CircuitType::Delegation(_)
                | CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    self.common_precomputations[&circuit_type].clone()
                }
                CircuitType::Unrolled(circuit_type) => {
                    binary_holder.precomputations[&circuit_type].clone()
                }
            };
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
            let mut gpu_work_requests = VecDeque::new();
            match work_result {
                WorkerResult::SnapshotProduced => {
                    if !proving {
                        if let Some(cache) = cache.as_mut() {
                            self.trim_cache(cache)
                        }
                    }
                }
                WorkerResult::InitsAndTeardownsData(data) => match data.circuit_type {
                    CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                        let request = get_gpu_work_request(Some(data), None);
                        gpu_work_requests.push_back(request);
                    }
                    CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
                        let sequence_id = data.sequence_id;
                        if sequence_id < trivial_unified_inits_and_teardowns_count {
                            assert!(data.inits_and_teardowns.is_none());
                        }
                        if !proving
                            || cache.is_none()
                            || sequence_id >= trivial_unified_inits_and_teardowns_count
                        {
                            assert!(
                                !unpaired_unified_inits_and_teardowns.contains_key(&sequence_id)
                            );
                            if sequence_id >= trivial_unified_inits_and_teardowns_count {
                                if proving && cache.is_some() {
                                    assert!(data.inits_and_teardowns.is_some())
                                } else if data.inits_and_teardowns.is_none() {
                                    trivial_unified_inits_and_teardowns_count = sequence_id + 1;
                                }
                            }
                            if let Some(tracing_data) =
                                unpaired_unified_tracing_data.remove(&sequence_id)
                            {
                                let request = get_gpu_work_request(Some(data), Some(tracing_data));
                                gpu_work_requests.push_back(request);
                            } else {
                                assert!(unpaired_unified_inits_and_teardowns
                                    .insert(sequence_id, data)
                                    .is_none());
                            }
                        }
                    }
                    _ => panic!("unexpected circuit type for inits and teardowns data"),
                },
                WorkerResult::TracingData(data) => {
                    if data
                        .participating_snapshot_indexes
                        .is_subset(&processed_snapshots)
                    {
                        match data.circuit_type {
                            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                                panic!(
                                    "tracing data can not have the inits and teardowns circuit_type"
                                )
                            }
                            CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
                                let sequence_id = data.sequence_id;
                                assert!(!unpaired_unified_tracing_data.contains_key(&sequence_id));
                                if let Some(inits_and_teardowns) =
                                    unpaired_unified_inits_and_teardowns.remove(&sequence_id)
                                {
                                    let request =
                                        get_gpu_work_request(Some(inits_and_teardowns), Some(data));
                                    gpu_work_requests.push_back(request);
                                } else {
                                    assert!(unpaired_unified_tracing_data
                                        .insert(sequence_id, data)
                                        .is_none());
                                }
                            }
                            _ => {
                                let request = get_gpu_work_request(None, Some(data));
                                gpu_work_requests.push_back(request);
                            }
                        }
                    } else {
                        let key = (data.circuit_type, data.sequence_id);
                        for snapshot_index in data.participating_snapshot_indexes.iter().copied() {
                            let entry = uninitialized_tracing_data_key_by_snapshot_index
                                .entry(snapshot_index)
                                .or_insert_with(|| BTreeSet::new());
                            assert!(!entry.contains(&key));
                            entry.insert(key);
                        }
                        assert!(uninitialized_tracing_data.insert(key, data).is_none());
                    }
                }
                WorkerResult::SimulationResult(result) => {
                    simulation_result = Some(result);
                }
                WorkerResult::SnapshotReplayed(sequence_id) => {
                    assert!(processed_snapshots.insert(sequence_id));
                    if let Some(keys) =
                        uninitialized_tracing_data_key_by_snapshot_index.get_mut(&sequence_id)
                    {
                        for key in keys.clone().into_iter() {
                            if uninitialized_tracing_data
                                .get(&key)
                                .unwrap()
                                .participating_snapshot_indexes
                                .is_subset(&processed_snapshots)
                            {
                                keys.remove(&key);
                                let data = uninitialized_tracing_data.remove(&key).unwrap();
                                match data.circuit_type {
                                    CircuitType::Unrolled(
                                        UnrolledCircuitType::InitsAndTeardowns,
                                    ) => {
                                        panic!(
                                            "tracing data can not have the inits and teardowns circuit_type"
                                        )
                                    }
                                    CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
                                        let sequence_id = data.sequence_id;
                                        assert!(!unpaired_unified_tracing_data
                                            .contains_key(&sequence_id));
                                        if let Some(inits_and_teardowns) =
                                            unpaired_unified_inits_and_teardowns
                                                .remove(&sequence_id)
                                        {
                                            let request = get_gpu_work_request(
                                                Some(inits_and_teardowns),
                                                Some(data),
                                            );
                                            gpu_work_requests.push_back(request);
                                        } else {
                                            assert!(unpaired_unified_tracing_data
                                                .insert(sequence_id, data)
                                                .is_none());
                                        }
                                    }
                                    _ => {
                                        let request = get_gpu_work_request(None, Some(data));
                                        gpu_work_requests.push_back(request);
                                    }
                                }
                            }
                        }
                    }
                }
                WorkerResult::GpuWorkResult(result) => {
                    assert_ne!(pending_requests_count, 0);
                    pending_requests_count -= 1;
                    match result {
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
                            if let Some(cache) = cache.as_mut() {
                                let cache_entry = TraceCacheEntry {
                                    circuit_type,
                                    sequence_id,
                                    inits_and_teardowns,
                                    tracing_data,
                                };
                                cache.push_back(cache_entry);
                                if simulation_result.is_none() {
                                    self.trim_cache(cache);
                                }
                            } else {
                                self.free_traces(inits_and_teardowns, tracing_data)
                            }
                            let caps = match circuit_type {
                                CircuitType::Delegation(circuit_type) => {
                                    &mut delegation_circuits_memory_caps
                                        .entry(circuit_type as u32)
                                        .or_insert_with(|| BTreeMap::new())
                                }
                                CircuitType::Unrolled(circuit_type) => match circuit_type {
                                    UnrolledCircuitType::InitsAndTeardowns => {
                                        &mut inits_and_teardowns_memory_caps
                                    }
                                    _ => &mut circuit_families_memory_caps
                                        .get_mut(&circuit_type.get_family_idx())
                                        .unwrap(),
                                },
                            };
                            assert!(caps.insert(sequence_id, merkle_tree_caps).is_none());
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
                            self.free_traces(inits_and_teardowns, tracing_data);
                            match circuit_type {
                                CircuitType::Delegation(circuit_type) => {
                                    assert!(delegation_circuits_proofs
                                        .entry(circuit_type as u32)
                                        .or_insert_with(|| BTreeMap::new())
                                        .insert(sequence_id, unrolled_proof_into_proof(proof))
                                        .is_none())
                                }
                                CircuitType::Unrolled(circuit_type) => match circuit_type {
                                    UnrolledCircuitType::InitsAndTeardowns => {
                                        assert!(inits_and_teardowns_proofs
                                            .insert(sequence_id, proof)
                                            .is_none())
                                    }
                                    _ => assert!(circuit_families_proofs
                                        .get_mut(&circuit_type.get_family_idx())
                                        .unwrap()
                                        .insert(sequence_id, proof)
                                        .is_none()),
                                },
                            };
                        }
                    }
                }
            }
            for request in gpu_work_requests {
                let key = (request.circuit_type(), request.sequence_id());
                if requests_served_from_cache.contains(&key) {
                    match request {
                        GpuWorkRequest::Proof(request) => {
                            let ProofRequest {
                                batch_id,
                                circuit_type,
                                sequence_id,
                                inits_and_teardowns,
                                tracing_data,
                                ..
                            } = request;
                            trace!("BATCH[{batch_id}] PROVER skipping cached proof request for circuit {circuit_type:?}[{sequence_id}]");
                            self.free_traces(inits_and_teardowns, tracing_data);
                        }
                        _ => panic!("only proof requests are cached"),
                    }
                    continue;
                }
                gpu_work_requests_sender
                    .as_ref()
                    .unwrap()
                    .send(request)
                    .unwrap();
                pending_requests_count += 1;
                sent_requests_count += 1;
            }
            if simulation_result.is_some()
                && uninitialized_tracing_data.is_empty()
                && unpaired_unified_inits_and_teardowns.is_empty()
                && unpaired_unified_tracing_data.is_empty()
            {
                gpu_work_requests_sender = None;
            }
            if let Some(cache) = cache.as_mut() {
                if proving
                    && !abort_signaled
                    && gpu_work_requests_sender.is_some()
                    && cache.total_requests_count == sent_requests_count
                {
                    debug!("BATCH[{batch_id}] PROVER all remaining proof requests have been served from cache, signaling abort of simulation");
                    gpu_work_requests_sender = None;
                    abort.store(true, std::sync::atomic::Ordering::Relaxed);
                    simulation_result = cache.simulation_result.clone();
                    abort_signaled = true;
                }
            }
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
        } = simulation_result.unwrap();
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
            let result = ProveResult {
                register_final_values: final_register_values,
                final_pc,
                final_timestamp,
                circuit_families_proofs,
                inits_and_teardowns_proofs,
                delegation_proofs: delegation_circuits_proofs,
                pow_challenge,
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
            };
            ExecutionProverResult::CommitMemory(result)
        }
    }

    fn free_inits_and_teardowns(&self, inits_and_teardowns: ShuffleRamInitsAndTeardownsHost<A>) {
        for allocator in inits_and_teardowns.into_allocators() {
            self.free_allocators_sender.send(allocator).unwrap();
        }
    }

    fn free_tracing_data(&self, tracing_data: TracingDataHost<A>) {
        for allocator in tracing_data.into_allocators() {
            self.free_allocators_sender.send(allocator).unwrap();
        }
    }

    fn free_traces(
        &self,
        inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
        tracing_data: Option<TracingDataHost<A>>,
    ) {
        if let Some(inits_and_teardowns) = inits_and_teardowns {
            self.free_inits_and_teardowns(inits_and_teardowns);
        }
        if let Some(tracing_data) = tracing_data {
            self.free_tracing_data(tracing_data);
        }
    }

    fn trim_cache(&self, cache: &mut TraceCache) {
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

    fn commit_memory_inner(
        &self,
        cache: &mut Option<TraceCache>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: Arc<Mutex<Option<impl NonDeterminismCSRSource + Send + 'static>>>,
    ) -> CommitMemoryResult {
        info!("BATCH[{batch_id}] PROVER producing memory commitments for binary with key {binary_key:?}");
        let timer = Instant::now();
        let result = self
            .get_result(
                false,
                cache,
                batch_id,
                binary_key,
                non_determinism_source,
                0,
                None,
            )
            .into_memory_commitment_result();
        let elapsed = timer.elapsed().as_secs_f64();
        info!("BATCH[{batch_id}] PROVER produced memory commitments for binary with key {binary_key:?} in {elapsed:.3}s");
        result
    }

    ///  Produces memory commitments.
    ///
    /// # Arguments
    ///
    /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys of the binaries that were previously added to the `ExecutionProver` using the `add_binary` method
    /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    ///
    /// returns: a CommitMemoryResult structure
    ///
    pub fn commit_memory(
        &self,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: impl NonDeterminismCSRSource + Send + 'static,
    ) -> CommitMemoryResult {
        let non_determinism_source = Arc::new(Mutex::new(Some(non_determinism_source)));
        self.commit_memory_inner(&mut None, batch_id, binary_key, non_determinism_source)
    }

    fn prove_inner(
        &self,
        cache: &mut Option<TraceCache>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: Arc<Mutex<Option<impl NonDeterminismCSRSource + Send + 'static>>>,
        pow_challenge: u64,
        external_challenges: ExternalChallenges,
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
            )
            .into_proof_result();
        let elapsed = timer.elapsed().as_secs_f64();
        info!("BATCH[{batch_id}] PROVER produced proofs for binary with key {binary_key:?} in {elapsed:.3}s");
        result
    }

    ///  Produces proofs.
    ///
    /// # Arguments
    ///
    /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    /// * `external_challenges`: an instance of `ExternalChallenges` that contains the challenges to be used in the proof generation
    ///
    /// returns: a ProveResult structure
    ///
    pub fn prove(
        &self,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: impl NonDeterminismCSRSource + Send + 'static,
        pow_challenge: u64,
        external_challenges: ExternalChallenges,
    ) -> ProveResult {
        let non_determinism_source = Arc::new(Mutex::new(Some(non_determinism_source)));
        self.prove_inner(
            &mut None,
            batch_id,
            binary_key,
            non_determinism_source,
            pow_challenge,
            external_challenges,
        )
    }

    ///  Commits to memory and produces proofs using challenge derived from the memory commitments.
    ///
    /// # Arguments
    ///
    /// * `batch_id`: a unique identifier for the batch of work, used to distinguish batches in a multithreaded scenario
    /// * `binary_key`: a key that identifies the binary to work with, this key must match one of the keys in the `binaries` map provided during the creation of the `ExecutionProver`
    /// * `non_determinism_source`: a value implementing the `NonDeterminism` trait that provides non-deterministic values for the simulation
    ///
    /// returns: a ProveResult structure
    ///
    pub fn commit_memory_and_prove(
        &self,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: impl NonDeterminismCSRSource + Send + 'static,
    ) -> ProveResult {
        let nd_rapper = NonDeterminismWrapper::new(non_determinism_source);
        let non_determinism_source = Arc::new(Mutex::new(Some(nd_rapper)));
        let mut cache = Some(TraceCache::new());
        let timer = Instant::now();
        let memory_commitment_result = self.commit_memory_inner(
            &mut cache,
            batch_id,
            binary_key,
            non_determinism_source.clone(),
        );
        let non_determinism_values = Arc::into_inner(non_determinism_source)
            .unwrap()
            .into_inner()
            .unwrap()
            .unwrap()
            .into_values();
        let non_determinism_source = QuasiUARTSource::new_with_reads(non_determinism_values);
        let non_determinism_source = Arc::new(Mutex::new(Some(non_determinism_source)));
        let CommitMemoryResult {
            final_register_values,
            final_pc,
            final_timestamp,
            circuit_families_memory_caps,
            inits_and_teardowns_memory_caps,
            delegation_circuits_memory_caps,
        } = memory_commitment_result;
        let all_challenges_seed =
            fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
                &final_register_values,
                final_pc,
                final_timestamp,
                &circuit_families_memory_caps
                    .iter()
                    .map(|(i, v)| (*i as u32, v.clone()))
                    .collect_vec(),
                &inits_and_teardowns_memory_caps,
                &delegation_circuits_memory_caps
                    .iter()
                    .map(|(i, v)| (*i, v.clone()))
                    .collect_vec(),
            );
        let pow_challenge = if MEMORY_DELEGATION_POW_BITS == 0 {
            0
        } else {
            Transcript::search_pow(
                &all_challenges_seed,
                MEMORY_DELEGATION_POW_BITS as u32,
                &self.worker,
            )
            .1
        };
        let external_challenges =
            ExternalChallenges::draw_from_transcript_seed_with_state_permutation(
                all_challenges_seed,
                MEMORY_DELEGATION_POW_BITS,
                pow_challenge,
            );
        let prove_result = self.prove_inner(
            &mut cache,
            batch_id,
            binary_key,
            non_determinism_source,
            pow_challenge,
            external_challenges,
        );
        assert_eq!(prove_result.register_final_values, final_register_values);
        assert_eq!(prove_result.final_pc, final_pc);
        assert_eq!(prove_result.final_timestamp, final_timestamp);
        fn assert_caps_mach(
            a: &Vec<Vec<MerkleTreeCapVarLength>>,
            b: &Vec<Vec<MerkleTreeCapVarLength>>,
        ) {
            for (a, b) in a.iter().zip(b.iter()) {
                assert_eq!(a, b);
            }
        }
        prove_result
            .circuit_families_proofs
            .iter()
            .zip(circuit_families_memory_caps.iter())
            .for_each(|(a, b)| {
                assert_eq!(a.0, b.0);
                assert_caps_mach(
                    &a.1.iter().map(|p| p.memory_tree_caps.clone()).collect_vec(),
                    &b.1,
                );
            });
        assert_caps_mach(
            &prove_result
                .inits_and_teardowns_proofs
                .iter()
                .map(|p| p.memory_tree_caps.clone())
                .collect_vec(),
            &inits_and_teardowns_memory_caps,
        );
        prove_result
            .delegation_proofs
            .iter()
            .zip(delegation_circuits_memory_caps.iter())
            .for_each(|(a, b)| {
                assert_eq!(a.0, b.0);
                assert_caps_mach(
                    &a.1.iter().map(|p| p.memory_tree_caps.clone()).collect_vec(),
                    &b.1,
                );
            });
        let elapsed = timer.elapsed().as_secs_f64();
        info!("BATCH[{batch_id}] PROVER committed to memory and produced proofs for binary with key {binary_key:?} in {elapsed:.3}s");
        prove_result
    }
}

fn unrolled_proof_into_proof(proof: UnrolledModeProof) -> Proof {
    assert!(proof.aux_boundary_values.is_empty());
    Proof {
        external_values: ExternalValues {
            challenges: proof.external_challenges,
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        },
        public_inputs: proof.public_inputs,
        witness_tree_caps: proof.witness_tree_caps,
        memory_tree_caps: proof.memory_tree_caps,
        setup_tree_caps: proof.setup_tree_caps,
        stage_2_tree_caps: proof.stage_2_tree_caps,
        memory_grand_product_accumulator: proof.permutation_grand_product_accumulator,
        delegation_argument_accumulator: proof.delegation_argument_accumulator,
        quotient_tree_caps: proof.quotient_tree_caps,
        evaluations_at_random_points: proof.evaluations_at_random_points,
        deep_poly_caps: proof.deep_poly_caps,
        intermediate_fri_oracle_caps: proof.intermediate_fri_oracle_caps,
        last_fri_step_plain_leaf_values: proof.last_fri_step_plain_leaf_values,
        final_monomial_form: proof.final_monomial_form,
        queries: proof.queries,
        pow_challenges: proof.pow_challenges,
        circuit_sequence: 0,
        delegation_type: proof.delegation_type,
    }
}

struct NonDeterminismWrapper<N> {
    inner: N,
    values: Vec<u32>,
}

impl<N> NonDeterminismWrapper<N> {
    fn new(inner: N) -> Self {
        Self {
            inner,
            values: Vec::new(),
        }
    }

    fn into_values(self) -> Vec<u32> {
        self.values
    }
}

impl<N: NonDeterminismCSRSource> NonDeterminismCSRSource for NonDeterminismWrapper<N> {
    fn read(&mut self) -> u32 {
        let value = self.inner.read();
        self.values.push(value);
        value
    }

    fn write_with_memory_access<R: RamPeek>(&mut self, ram: &R, value: u32) {
        self.inner.write_with_memory_access(ram, value)
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.inner.write_with_memory_access_dyn(ram, value)
    }
}

#[cfg(test)]
mod tests {
    use crate::execution::prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration};
    use crate::machine_type::MachineType;
    use crate::tests::init_logger;
    use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use setups::read_binary;
    use std::path::Path;

    #[test]
    fn test_execution_prover() {
        init_logger();
        let mut configuration = ExecutionProverConfiguration::default();
        configuration.replay_worker_threads_count = 8;
        let mut prover = ExecutionProver::with_configuration(configuration);
        let (_, binary_image) = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
        let (_, text_section) = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
        prover.add_binary(
            0,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            binary_image,
            text_section,
            None,
        );
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![3 << 25, 0]);
        let _base_layer_result = prover.commit_memory_and_prove(0, 0, non_determinism_source);
        let (_, binary_image) =
            read_binary(&Path::new("../tools/verifier/unrolled_base_layer.bin"));
        let (_, text_section) =
            read_binary(&Path::new("../tools/verifier/unrolled_base_layer.text"));
        prover.add_binary(
            1,
            ExecutionKind::Unrolled,
            MachineType::Reduced,
            binary_image,
            text_section,
            None,
        );
        drop(prover);
    }
}
