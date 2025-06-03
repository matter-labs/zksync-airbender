//! Module with multiGPU support for the prover.
//
// multigpu_prove_image_execution_for_machine_with_gpu_tracers is the main entry point
// which has similar arguments gpu_prove_image_execution_for_machine_with_gpu_tracers from the
// gpu module.

// It starts a thread per GPU machine, and creates crossbeam channels to each one to communicate jobs
// that should be executed.

use std::{
    alloc::Global,
    collections::{HashMap, HashSet},
    ffi::CStr,
    hash::RandomState,
    sync::Arc,
    thread,
};

use crossbeam::channel::{bounded, unbounded, Receiver, Sender, TryRecvError};
use cs::utils::split_timestamp;
use era_cudart::{
    device::{get_device_count, get_device_properties, set_device},
    result::CudaResult,
};
use gpu_prover::{
    allocator::host::ConcurrentStaticHostAllocator,
    prover::{
        context::MemPoolProverContext,
        memory::commit_memory,
        setup::SetupPrecomputations,
        tracing_data::{TracingDataHost, TracingDataTransfer},
    },
    witness::{
        trace_delegation::{DelegationCircuitType, DelegationTraceHost},
        trace_main::{
            get_aux_arguments_boundary_values, MainCircuitType, MainTraceHost,
            ShuffleRamSetupAndTeardownHost,
        },
        CircuitType,
    },
};
use prover::{
    definitions::{
        produce_register_contribution_into_memory_accumulator_raw, AuxArgumentsBoundaryValues,
        ExternalChallenges, ExternalValues, OPTIMAL_FOLDING_PROPERTIES,
    },
    field::{Field, Mersenne31Field, Mersenne31Quartic},
    merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength, MerkleTreeConstructor},
    prover_stages::Proof,
    risc_v_simulator::{
        abstractions::non_determinism::NonDeterminismCSRSource,
        cycle::{IMStandardIsaConfig, IWithoutByteAccessIsaConfigWithDelegation, MachineConfig},
    },
    worker::Worker,
    VectorMemoryImplWithRom,
};
use setups::{DelegationCircuitPrecomputations, MainCircuitPrecomputations};
use trace_and_split::{fs_transform_for_memory_and_delegation_arguments, FinalRegisterValue};

use crate::{
    gpu::{
        create_default_prover_context, initialize_host_allocator_if_needed, trace_execution_for_gpu,
    },
    NUM_QUERIES, POW_BITS,
};

/// GpuJob is an enum that represents different types of jobs that can be sent to the GPU thread.
// Most the enums are using the 'reply_to' channel to send the result back to the main thread.
pub enum GpuJob {
    MainCircuitMemoryCommit(MainCircuitMemoryCommitRequest),
    DelegationCircuitMemoryCommit(DelegationCircuitMemoryCommitRequest),
    SetSetup(SetSetupRequest),
    ProveMainCircuit(ProveMainCircuitRequest<IMStandardIsaConfig>),
    ProveReducedCircuit(ProveMainCircuitRequest<IWithoutByteAccessIsaConfigWithDelegation>),
    ProveDelegationCircuit(ProveDelegationCircuitRequest),
    Shutdown,
}

/// Special trait for stuff related to basic vs reduced circuits.
pub trait CreateGpuJob: MachineConfig {
    fn create_job(request: ProveMainCircuitRequest<Self>) -> GpuJob;
}

impl CreateGpuJob for IMStandardIsaConfig {
    fn create_job(request: ProveMainCircuitRequest<Self>) -> GpuJob {
        GpuJob::ProveMainCircuit(request)
    }
}
impl CreateGpuJob for IWithoutByteAccessIsaConfigWithDelegation {
    fn create_job(request: ProveMainCircuitRequest<Self>) -> GpuJob {
        GpuJob::ProveReducedCircuit(request)
    }
}

pub struct MainCircuitMemoryCommitRequest {
    lde_factor: usize,
    trace_len: usize,
    setup_and_teardown: Option<ShuffleRamSetupAndTeardownHost<ConcurrentStaticHostAllocator>>,
    witness_chunk: MainTraceHost<ConcurrentStaticHostAllocator>,
    circuit_type: CircuitType,
    compiled_circuit: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    pub reply_to: Sender<CudaResult<Vec<MerkleTreeCapVarLength>>>,
}

pub struct DelegationCircuitMemoryCommitRequest {
    lde_factor: usize,
    witness_chunk: DelegationTraceHost<ConcurrentStaticHostAllocator>,
    circuit_type: CircuitType,
    compiled_circuit: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    pub reply_to: Sender<CudaResult<Vec<MerkleTreeCapVarLength>>>,
}

pub struct ProveMainCircuitRequest<C: MachineConfig + CreateGpuJob> {
    lde_factor: usize,
    circuit_sequence: usize,
    aux_boundary_values: AuxArgumentsBoundaryValues,
    setup_and_teardown: Option<ShuffleRamSetupAndTeardownHost<ConcurrentStaticHostAllocator>>,
    witness_chunk: MainTraceHost<ConcurrentStaticHostAllocator>,
    circuit_type: CircuitType,
    external_challenges: ExternalChallenges,
    precomputations: Arc<MainCircuitPrecomputations<C, Global, ConcurrentStaticHostAllocator>>,
    pub reply_to: Sender<CudaResult<Proof>>,
}

pub struct ProveDelegationCircuitRequest {
    witness_chunk: DelegationTraceHost<ConcurrentStaticHostAllocator>,
    circuit_type: CircuitType,
    external_challenges: ExternalChallenges,
    precomputations: Arc<
        Vec<(
            u32,
            DelegationCircuitPrecomputations<Global, ConcurrentStaticHostAllocator>,
        )>,
    >,
    pub reply_to: Sender<CudaResult<Proof>>,
}

#[derive(Clone)]
pub struct SetSetupRequest {
    circuit_type: CircuitType,
    lde_factor: usize,
    trace_len: usize,
    setup_evaluations: Arc<Vec<Mersenne31Field, ConcurrentStaticHostAllocator>>,
    compiled_circuit: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
}

/// Thread that is responsible for running all computation on a single gpu.
pub struct GpuThread {
    pub device_id: i32,
    gpu_thread: Option<Sender<GpuJob>>,
}

impl GpuThread {
    /// Creates a new GPU threads - one for each GPU device.
    pub fn init_multigpu() -> CudaResult<Vec<GpuThread>> {
        let device_count = get_device_count()?;
        let mut gpu_threads = Vec::with_capacity(device_count as usize);
        for device_id in 0..device_count {
            let gpu_thread = GpuThread::new(device_id)?;
            gpu_threads.push(gpu_thread);
        }

        Ok(gpu_threads)
    }

    /// Starts gpu threads. Each one will fully occupy a single core.
    pub fn start_multigpu(gpu_threads: &mut Vec<GpuThread>) {
        initialize_host_allocator_if_needed();

        for gpu_thread in gpu_threads.iter_mut() {
            gpu_thread.start();
        }
    }

    /// Sends a single job to the GPU thread.
    // Most jobs will have a reply_to channel inside to get back the results.
    pub fn send_job(&self, job: GpuJob) -> Result<(), TryRecvError> {
        if let Some(gpu_thread) = &self.gpu_thread {
            gpu_thread.send(job).map_err(|_| TryRecvError::Disconnected)
        } else {
            Err(TryRecvError::Disconnected)
        }
    }

    /// Creates a new GPU thread for a given device id.
    pub fn new(device_id: i32) -> CudaResult<Self> {
        let props = get_device_properties(device_id)?;
        let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
        println!(
            "Device {}: {} ({} SMs, {} GB memory)",
            device_id,
            name,
            props.multiProcessorCount,
            props.totalGlobalMem as f32 / 1024.0 / 1024.0 / 1024.0
        );

        Ok(Self {
            device_id,
            gpu_thread: None,
        })
    }

    /// Starts the gpu thread for a given device.
    pub fn start(&mut self) {
        if self.gpu_thread.is_none() {
            let gpu_thread = Self::spawn_gpu_thread(self.device_id);
            self.gpu_thread = Some(gpu_thread);
        } else {
            println!(
                "GPU thread for device {} is already running.",
                self.device_id
            );
        }
    }

    /// Main loop with the gpu thread - it will block the CPU core until it receives a shutdown command.
    fn spawn_gpu_thread(device_id: i32) -> Sender<GpuJob> {
        // Create a channel.  We only need Sender in the parent; Receiver moves into the GPU thread.
        let (tx, rx): (Sender<GpuJob>, Receiver<GpuJob>) = unbounded();

        // Spawn the dedicated GPU thread:
        thread::spawn(move || {
            println!("[GPU {}] Initializing GPU context...", device_id);
            set_device(device_id).unwrap();
            let context = create_default_prover_context();

            let mut gpu_setup_main = None;
            let mut gpu_setup_reduced = None;

            let mut delegation_setup: HashMap<
                gpu_prover::witness::trace_delegation::DelegationCircuitType,
                SetupPrecomputations<'_, MemPoolProverContext<'_>>,
                RandomState,
            > = HashMap::default();

            println!("[GPU {}] GPU context ready.", device_id);
            loop {
                match rx.try_recv() {
                    Ok(job) => match job {
                        GpuJob::Shutdown => {
                            println!("[GPU thread] Received Shutdown. Cleaning up and exiting ...");
                            break;
                        }
                        GpuJob::MainCircuitMemoryCommit(request) => {
                            println!(
                                "[GPU {}] Received MainCircuitMemoryCommit request",
                                device_id
                            );
                            let result = GpuThread::compute_main_circuit_memory_commit(
                                request.lde_factor,
                                request.trace_len,
                                request.setup_and_teardown,
                                request.witness_chunk,
                                request.circuit_type,
                                &request.compiled_circuit,
                                &context,
                            );

                            request.reply_to.send(result).unwrap();

                            println!("[GPU {}] Finished MainCircuitMemoryCommit.", device_id);
                        }
                        GpuJob::DelegationCircuitMemoryCommit(request) => {
                            println!(
                                "[GPU {}] Received DelegationCircuitMemoryCommit request",
                                device_id
                            );
                            let result = GpuThread::compute_delegation_circuit_memory_commit(
                                request.lde_factor,
                                request.witness_chunk,
                                request.circuit_type,
                                &request.compiled_circuit,
                                &context,
                            );

                            request.reply_to.send(result).unwrap();

                            println!(
                                "[GPU {}] Finished DelegationCircuitMemoryCommit.",
                                device_id
                            );
                        }

                        GpuJob::SetSetup(request) => {
                            println!(
                                "[GPU {}] Received SetSetup request: {:?}",
                                device_id, request.circuit_type
                            );

                            let new_setup = GpuThread::set_circuit_setup(
                                request.lde_factor,
                                request.trace_len,
                                request.setup_evaluations,
                                &request.compiled_circuit,
                                &context,
                            )
                            .unwrap();
                            match request.circuit_type {
                                CircuitType::Main(MainCircuitType::RiscVCycles) => {
                                    gpu_setup_main = Some(new_setup)
                                }
                                CircuitType::Main(MainCircuitType::ReducedRiscVMachine) => {
                                    gpu_setup_reduced = Some(new_setup)
                                }
                                CircuitType::Main(MainCircuitType::FinalReducedRiscVMachine) => {
                                    panic!("Not supported")
                                }
                                CircuitType::Delegation(delegation_circuit_type) => {
                                    delegation_setup.insert(delegation_circuit_type, new_setup);
                                }
                            }
                            println!("[GPU {}] Finished SetSetup.", device_id);
                        }
                        GpuJob::ProveMainCircuit(request) => {
                            let mut gpu_setup_main_ref = gpu_setup_main.as_mut().unwrap();
                            println!("[GPU {}] Received ProveMainCircuit request", device_id);
                            let result = GpuThread::prove_main_circuit(
                                request.lde_factor,
                                request.circuit_sequence,
                                request.setup_and_teardown,
                                request.aux_boundary_values,
                                request.witness_chunk,
                                request.circuit_type,
                                request.external_challenges,
                                &request.precomputations,
                                &context,
                                &mut gpu_setup_main_ref,
                            );

                            request.reply_to.send(result).unwrap();

                            println!("[GPU {}] Finished ProveMainCircuit.", device_id);
                        }
                        GpuJob::ProveReducedCircuit(request) => {
                            let mut gpu_setup_reduced_ref = gpu_setup_reduced.as_mut().unwrap();
                            println!("[GPU {}] Received ProveReducedCircuit request", device_id);
                            let result = GpuThread::prove_main_circuit(
                                request.lde_factor,
                                request.circuit_sequence,
                                request.setup_and_teardown,
                                request.aux_boundary_values,
                                request.witness_chunk,
                                request.circuit_type,
                                request.external_challenges,
                                &request.precomputations,
                                &context,
                                &mut gpu_setup_reduced_ref,
                            );

                            request.reply_to.send(result).unwrap();

                            println!("[GPU {}] Finished ProveReducedCircuit.", device_id);
                        }
                        GpuJob::ProveDelegationCircuit(request) => {
                            let delegation_id = request
                                .circuit_type
                                .as_delegation()
                                .expect("Expected delegation circuit type");

                            let mut gpu_setup_ref =
                                delegation_setup.get_mut(&delegation_id).unwrap();
                            println!(
                                "[GPU {}] Received ProveDelegationCircuit request",
                                device_id
                            );
                            let result = GpuThread::prove_delegation_circuit(
                                request.witness_chunk,
                                request.circuit_type.as_delegation().unwrap(),
                                request.external_challenges,
                                &request.precomputations,
                                &context,
                                &mut gpu_setup_ref,
                            );

                            request.reply_to.send(result).unwrap();

                            println!("[GPU {}] Finished ProveDelegationCircuit.", device_id);
                        }
                    },
                    Err(TryRecvError::Empty) => {
                        // No message right now → just loop again immediately.
                        // We do NOT call `thread::sleep` or `recv()`, because we intentionally want
                        // the thread to stay “busy” (never yield CPU in a blocking wait).
                        continue;
                    }
                    Err(TryRecvError::Disconnected) => {
                        // All senders have been dropped. We will exit.
                        println!("[GPU thread] Channel closed, exiting ...");
                        break;
                    }
                }
            }

            println!("[GPU {}] Exiting now.", device_id);
        });

        tx
    }

    fn compute_main_circuit_memory_commit(
        lde_factor: usize,
        trace_len: usize,
        setup_and_teardown: Option<ShuffleRamSetupAndTeardownHost<ConcurrentStaticHostAllocator>>,
        witness_chunk: MainTraceHost<ConcurrentStaticHostAllocator>,
        circuit_type: CircuitType,
        compiled_circuit: &cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
        prover_context: &MemPoolProverContext<'_>,
    ) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
        let gpu_caps = {
            let log_lde_factor = lde_factor.trailing_zeros();
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;

            let data = TracingDataHost::Main {
                setup_and_teardown,
                trace: witness_chunk,
            };

            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let job = commit_memory(
                transfer,
                compiled_circuit,
                log_lde_factor,
                log_tree_cap_size,
                prover_context,
            )?;
            job.finish()?
        };
        Ok(gpu_caps)
    }

    fn compute_delegation_circuit_memory_commit(
        lde_factor: usize,
        witness_chunk: DelegationTraceHost<ConcurrentStaticHostAllocator>,
        circuit_type: CircuitType,
        compiled_circuit: &cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
        prover_context: &MemPoolProverContext<'_>,
    ) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
        let gpu_caps = {
            let trace_len = compiled_circuit.trace_len;

            let log_lde_factor = lde_factor.trailing_zeros();
            let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize]
                .total_caps_size_log2 as u32;

            let data = TracingDataHost::Delegation(witness_chunk);

            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let job = commit_memory(
                transfer,
                compiled_circuit,
                log_lde_factor,
                log_tree_cap_size,
                prover_context,
            )?;
            job.finish()?
        };
        Ok(gpu_caps)
    }

    fn set_circuit_setup<'a>(
        lde_factor: usize,
        trace_len: usize,
        setup_evaluations: Arc<Vec<Mersenne31Field, ConcurrentStaticHostAllocator>>,
        compiled_circuit: &cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
        prover_context: &MemPoolProverContext<'a>,
    ) -> CudaResult<SetupPrecomputations<'a, MemPoolProverContext<'a>>> {
        let gpu_setup_main = {
            let log_lde_factor = lde_factor.trailing_zeros();
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;

            let mut setup = SetupPrecomputations::new(
                compiled_circuit,
                log_lde_factor,
                log_tree_cap_size,
                prover_context,
            )?;
            setup.schedule_transfer(setup_evaluations, prover_context)?;
            setup
        };

        Ok(gpu_setup_main)
    }

    fn prove_main_circuit<'a, C: MachineConfig + CreateGpuJob>(
        lde_factor: usize,
        circuit_sequence: usize,
        setup_and_teardown: Option<ShuffleRamSetupAndTeardownHost<ConcurrentStaticHostAllocator>>,
        aux_boundary_values: AuxArgumentsBoundaryValues,
        witness_chunk: MainTraceHost<ConcurrentStaticHostAllocator>,
        circuit_type: CircuitType,
        external_challenges: ExternalChallenges,
        precomputations: &MainCircuitPrecomputations<C, Global, ConcurrentStaticHostAllocator>,
        prover_context: &MemPoolProverContext<'a>,
        gpu_setup_main: &mut SetupPrecomputations<'a, MemPoolProverContext<'a>>,
    ) -> CudaResult<Proof> {
        let gpu_proof = {
            let data = TracingDataHost::Main {
                setup_and_teardown,
                trace: witness_chunk.into(),
            };
            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values,
            };
            let job = gpu_prover::prover::proof::prove(
                &precomputations.compiled_circuit,
                external_values,
                gpu_setup_main,
                transfer,
                &precomputations.twiddles,
                &precomputations.lde_precomputations,
                circuit_sequence,
                None,
                lde_factor,
                NUM_QUERIES,
                POW_BITS,
                None,
                prover_context,
            )?;
            job.finish()?
        };
        Ok(gpu_proof)
    }

    fn prove_delegation_circuit<'a>(
        witness_chunk: DelegationTraceHost<ConcurrentStaticHostAllocator>,
        delegation_type: DelegationCircuitType,
        external_challenges: ExternalChallenges,
        delegation_circuits_precomputations: &Vec<(
            u32,
            DelegationCircuitPrecomputations<Global, ConcurrentStaticHostAllocator>,
        )>,
        prover_context: &MemPoolProverContext<'a>,
        gpu_setup_delegation: &mut SetupPrecomputations<'a, MemPoolProverContext<'a>>,
    ) -> CudaResult<Proof> {
        let external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        };
        let delegation_type_id = delegation_type as u32;

        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == delegation_type_id)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;

        let gpu_proof = {
            let data = TracingDataHost::Delegation(witness_chunk);
            let circuit_type = CircuitType::Delegation(delegation_type);
            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let job = gpu_prover::prover::proof::prove(
                &prec.compiled_circuit.compiled_circuit,
                external_values,
                gpu_setup_delegation,
                transfer,
                &prec.twiddles,
                &prec.lde_precomputations,
                0,
                Some(delegation_type as u16),
                prec.lde_factor,
                NUM_QUERIES,
                POW_BITS,
                None,
                prover_context,
            )?;
            job.finish()?
        };
        Ok(gpu_proof)
    }
}

pub struct GpuThreadManager<'a> {
    pub gpu_threads: &'a Vec<GpuThread>,
    pub current: usize,
    pub threads_with_setup: HashMap<CircuitType, HashSet<usize>>,
    pub main_setup_request: Option<SetSetupRequest>,
    pub setup_requests: HashMap<CircuitType, SetSetupRequest>,
}

impl<'a> GpuThreadManager<'a> {
    pub fn new(gpu_threads: &'a Vec<GpuThread>) -> Self {
        Self {
            gpu_threads,
            current: 0,
            threads_with_setup: Default::default(),
            main_setup_request: None,
            setup_requests: Default::default(),
        }
    }

    fn send_setup_to_gpu_if_needed(
        &mut self,
        circuit_type: CircuitType,
    ) -> Result<(), TryRecvError> {
        if !self
            .threads_with_setup
            .get(&circuit_type)
            .map_or(false, |x| x.contains(&self.current))
        {
            if let Some(main_setup_request) = self.setup_requests.get(&circuit_type) {
                // We have to pass the new setup to the device.
                println!("Sending main setup to GPU thread {}", self.current);
                let tmp_request = main_setup_request.clone();
                let gpu_thread = &self.gpu_threads[self.current];

                gpu_thread.send_job(GpuJob::SetSetup(tmp_request))?;

                self.threads_with_setup
                    .get_mut(&circuit_type)
                    .unwrap()
                    .insert(self.current);
            }
        }
        Ok(())
    }

    pub fn send_job(&mut self, job: GpuJob) -> Result<(), TryRecvError> {
        if self.gpu_threads.is_empty() {
            return Err(TryRecvError::Disconnected);
        }

        let gpu_thread = &self.gpu_threads[self.current];

        match &job {
            GpuJob::ProveMainCircuit(_) => {
                let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
                self.send_setup_to_gpu_if_needed(circuit_type)?;
            }
            GpuJob::ProveReducedCircuit(_) => {
                let circuit_type = CircuitType::Main(MainCircuitType::ReducedRiscVMachine);
                self.send_setup_to_gpu_if_needed(circuit_type)?;
            }
            GpuJob::ProveDelegationCircuit(request) => {
                let circuit_type = request.circuit_type;
                self.send_setup_to_gpu_if_needed(circuit_type)?;
            }

            _ => {}
        }

        gpu_thread.send_job(job)?;

        // Round-robin to the next GPU thread.
        self.current = (self.current + 1) % self.gpu_threads.len();

        Ok(())
    }

    pub fn set_setup(&mut self, setup_request: SetSetupRequest) {
        self.threads_with_setup
            .insert(setup_request.circuit_type, HashSet::new());

        self.setup_requests
            .insert(setup_request.circuit_type, setup_request);
    }
}

pub fn multigpu_prove_image_execution_for_machine_with_gpu_tracers<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig + CreateGpuJob,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: Arc<
        MainCircuitPrecomputations<C, Global, ConcurrentStaticHostAllocator>,
    >,
    risc_v_setup: Arc<Vec<Mersenne31Field, ConcurrentStaticHostAllocator>>,
    delegation_circuits_precomputations: Arc<
        Vec<(
            u32,
            DelegationCircuitPrecomputations<Global, ConcurrentStaticHostAllocator>,
        )>,
    >,
    delegation_setups: Arc<
        Vec<(
            u32,
            Arc<Vec<Mersenne31Field, ConcurrentStaticHostAllocator>>,
        )>,
    >,
    gpu_threads: &Vec<GpuThread>,
    worker: &Worker,
) -> CudaResult<(Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>)>
where
    [(); { C::SUPPORT_LOAD_LESS_THAN_WORD } as usize]:,
{
    let mut gpu_manager = GpuThreadManager::new(gpu_threads);
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let trace_len = setups::trace_len_for_machine::<C>();
    assert_eq!(cycles_per_circuit + 1, trace_len);
    let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;

    // Guess circuit type based on the machine type.
    let circuit_type = match std::any::TypeId::of::<C>() {
        id if id == std::any::TypeId::of::<IMStandardIsaConfig>() => {
            CircuitType::Main(MainCircuitType::RiscVCycles)
        }
        id if id == std::any::TypeId::of::<IWithoutByteAccessIsaConfigWithDelegation>() => {
            CircuitType::Main(MainCircuitType::ReducedRiscVMachine)
        }
        _ => {
            panic!("Unsupported machine type");
        }
    };

    let (
        main_circuits_witness,
        inits_and_teardowns,
        delegation_circuits_witness,
        final_register_values,
    ) = trace_execution_for_gpu::<ND, C, ConcurrentStaticHostAllocator>(
        max_cycles_to_run,
        bytecode,
        non_determinism,
        worker,
    );

    let (num_paddings, inits_and_teardowns) = inits_and_teardowns;

    let mut memory_tree_requests = vec![];
    // commit memory trees
    for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
        let (resp_tx, resp_rx) = bounded::<CudaResult<Vec<MerkleTreeCapVarLength>>>(1);

        let request = MainCircuitMemoryCommitRequest {
            lde_factor: setups::lde_factor_for_machine::<C>(),
            trace_len,
            setup_and_teardown: if circuit_sequence < num_paddings {
                None
            } else {
                Some(inits_and_teardowns[circuit_sequence - num_paddings].clone())
            },
            witness_chunk: witness_chunk.clone(),
            circuit_type,
            // TODO: maybe Arc?
            compiled_circuit: risc_v_circuit_precomputations.compiled_circuit.clone(),
            reply_to: resp_tx,
        };

        gpu_manager
            .send_job(GpuJob::MainCircuitMemoryCommit(request))
            .unwrap();

        memory_tree_requests.push(resp_rx);
    }

    // same for delegation circuits

    let mut delegation_types: Vec<_> = delegation_circuits_witness.keys().copied().collect();
    delegation_types.sort();

    let mut delegation_memory_trees_requests = HashMap::new();

    for delegation_type in delegation_types.iter().cloned() {
        let els = &delegation_circuits_witness[&delegation_type];
        let delegation_type_id = delegation_type as u32;
        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == delegation_type_id)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        for el in els.iter() {
            let (resp_tx, resp_rx) = bounded::<CudaResult<Vec<MerkleTreeCapVarLength>>>(1);

            let request = DelegationCircuitMemoryCommitRequest {
                lde_factor: prec.lde_factor,
                witness_chunk: el.clone(),
                circuit_type: CircuitType::Delegation(delegation_type),
                // TODO:  maybe Arc?
                compiled_circuit: prec.compiled_circuit.compiled_circuit.clone(),
                reply_to: resp_tx,
            };

            gpu_manager
                .send_job(GpuJob::DelegationCircuitMemoryCommit(request))
                .unwrap();

            delegation_memory_trees_requests
                .entry(delegation_type_id)
                .or_insert_with(Vec::new)
                .push(resp_rx);
        }
    }

    // Now pick up the results.

    let mut memory_trees = vec![];
    for resp_rx in memory_tree_requests.into_iter() {
        let gpu_caps = resp_rx.recv().unwrap()?;
        memory_trees.push(gpu_caps);
    }

    let mut delegation_memory_trees = vec![];
    for delegation_type in delegation_types.iter().cloned() {
        let delegation_type_id = delegation_type as u32;
        let mut per_tree_set = vec![];

        for resp_rx in delegation_memory_trees_requests
            .remove(&delegation_type_id)
            .unwrap()
        {
            let gpu_caps = resp_rx.recv().unwrap()?;
            per_tree_set.push(gpu_caps);
        }
        delegation_memory_trees.push((delegation_type_id, per_tree_set));
    }

    let setup_caps = DefaultTreeConstructor::dump_caps(&risc_v_circuit_precomputations.setup.trees);

    // commit memory challenges
    let memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
        &setup_caps,
        &final_register_values,
        &memory_trees,
        &delegation_memory_trees,
    );

    let external_challenges =
        ExternalChallenges::draw_from_transcript_seed(memory_challenges_seed, true);

    let input = final_register_values
        .iter()
        .map(|el| (el.value, split_timestamp(el.last_access_timestamp)))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut memory_grand_product = produce_register_contribution_into_memory_accumulator_raw(
        &input,
        external_challenges
            .memory_argument
            .memory_argument_linearization_challenges,
        external_challenges.memory_argument.memory_argument_gamma,
    );
    let mut delegation_argument_sum = Mersenne31Quartic::ZERO;

    let mut aux_memory_trees = vec![];

    println!(
        "Producing proofs for main RISC-V circuit, {} proofs in total",
        main_circuits_witness.len()
    );

    let total_proving_start = std::time::Instant::now();

    let main_circuits_witness_len = main_circuits_witness.len();

    gpu_manager.set_setup(SetSetupRequest {
        circuit_type,
        lde_factor: setups::lde_factor_for_machine::<C>(),
        trace_len,

        setup_evaluations: risc_v_setup.clone(),
        // make this into some Arc.
        compiled_circuit: risc_v_circuit_precomputations.compiled_circuit.clone(),
    });

    println!("Setup took {:?}", total_proving_start.elapsed());

    // now prove one by one
    let mut main_proofs = vec![];

    let mut main_proofs_responses = vec![];

    for (circuit_sequence, witness_chunk) in main_circuits_witness.into_iter().enumerate() {
        let (resp_tx, resp_rx) = bounded::<CudaResult<Proof>>(1);

        let (setup_and_teardown, aux_boundary_values) = if circuit_sequence < num_paddings {
            (None, AuxArgumentsBoundaryValues::default())
        } else {
            let shuffle_rams = &inits_and_teardowns[circuit_sequence - num_paddings];
            (
                Some(shuffle_rams.clone()),
                get_aux_arguments_boundary_values(&shuffle_rams.lazy_init_data, cycles_per_circuit),
            )
        };

        let request = ProveMainCircuitRequest {
            lde_factor: setups::lde_factor_for_machine::<C>(),
            circuit_sequence,
            aux_boundary_values,
            setup_and_teardown,
            witness_chunk,
            circuit_type,
            external_challenges,
            // Replace with some Arc
            precomputations: risc_v_circuit_precomputations.clone(),
            reply_to: resp_tx,
        };

        gpu_manager.send_job(C::create_job(request)).unwrap();

        main_proofs_responses.push(resp_rx);
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0u32;

    let mut proving_jobs: HashMap<_, _, RandomState> = HashMap::default();

    // Do the delegation proving.
    for delegation_type in delegation_types.iter().cloned() {
        let els = &delegation_circuits_witness[&delegation_type];
        let delegation_type_id = delegation_type as u32;
        println!(
            "Producing proofs for delegation circuit type {}, {} proofs in total",
            delegation_type_id,
            els.len()
        );

        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == delegation_type_id)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let circuit = &prec.compiled_circuit.compiled_circuit;
        let setup_start = std::time::Instant::now();

        let circuit_type = CircuitType::Delegation(delegation_type);

        gpu_manager.set_setup(SetSetupRequest {
            circuit_type,
            lde_factor: prec.lde_factor,
            trace_len: circuit.trace_len,
            setup_evaluations: delegation_setups
                .iter()
                .find(|(el, _)| *el == delegation_type_id)
                .map_or_else(
                    || panic!("Delegation setup for type {} not found", delegation_type_id),
                    |(_, setup)| setup.clone(),
                ),
            compiled_circuit: prec.compiled_circuit.compiled_circuit.clone(),
        });

        println!(
            "Setup for delegation type {} took {:?}",
            delegation_type_id,
            setup_start.elapsed()
        );

        for (_circuit_idx, el) in els.iter().enumerate() {
            delegation_proofs_count += 1;

            let (resp_tx, resp_rx) = bounded::<CudaResult<Proof>>(1);

            let request = ProveDelegationCircuitRequest {
                // TODO: remove this clone
                witness_chunk: el.clone(),
                circuit_type,
                external_challenges,
                precomputations: delegation_circuits_precomputations.clone(),
                reply_to: resp_tx,
            };

            gpu_manager
                .send_job(GpuJob::ProveDelegationCircuit(request))
                .unwrap();

            proving_jobs
                .entry(delegation_type)
                .or_insert_with(Vec::new)
                .push(resp_rx);
        }
    }

    for resp_rx in main_proofs_responses {
        let gpu_proof = resp_rx.recv().unwrap()?;
        memory_grand_product.mul_assign(&gpu_proof.memory_grand_product_accumulator);
        delegation_argument_sum.add_assign(&gpu_proof.delegation_argument_accumulator.unwrap());

        aux_memory_trees.push(gpu_proof.memory_tree_caps.clone());

        main_proofs.push(gpu_proof);
    }

    if main_circuits_witness_len > 0 {
        println!(
            "=== Total (async) proving time: {:?} for {} circuits - avg: {:?}",
            total_proving_start.elapsed(),
            main_circuits_witness_len,
            total_proving_start.elapsed() / main_circuits_witness_len.try_into().unwrap()
        )
    }

    for delegation_type in delegation_types.iter().cloned() {
        let delegation_type_id = delegation_type as u32;

        let mut per_tree_set = vec![];
        let mut per_delegation_type_proofs = vec![];

        for resp_rx in proving_jobs.remove(&delegation_type).unwrap() {
            let gpu_proof = resp_rx.recv().unwrap()?;

            memory_grand_product.mul_assign(&gpu_proof.memory_grand_product_accumulator);
            delegation_argument_sum.sub_assign(&gpu_proof.delegation_argument_accumulator.unwrap());

            per_tree_set.push(gpu_proof.memory_tree_caps.clone());

            per_delegation_type_proofs.push(gpu_proof);
        }

        aux_delegation_memory_trees.push((delegation_type_id, per_tree_set));
        delegation_proofs.push((delegation_type_id, per_delegation_type_proofs));
    }

    if delegation_proofs_count > 0 {
        println!(
            "=== Total (async) delegation proving time: {:?} for {} circuits - avg: {:?}",
            delegation_proving_start.elapsed(),
            delegation_proofs_count,
            delegation_proving_start.elapsed() / delegation_proofs_count
        )
    }

    assert_eq!(memory_grand_product, Mersenne31Quartic::ONE);
    assert_eq!(delegation_argument_sum, Mersenne31Quartic::ZERO);

    let setup_caps = DefaultTreeConstructor::dump_caps(&risc_v_circuit_precomputations.setup.trees);

    // compare challenge
    let aux_memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
        &setup_caps,
        &final_register_values,
        &aux_memory_trees,
        &aux_delegation_memory_trees,
    );

    assert_eq!(aux_memory_challenges_seed, memory_challenges_seed);

    Ok((main_proofs, delegation_proofs, final_register_values))
}
