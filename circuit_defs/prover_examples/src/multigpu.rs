use std::{alloc::Global, ffi::CStr, sync::Arc, thread, time::Duration};

use crossbeam::channel::{bounded, unbounded, Receiver, Sender, TryRecvError};
use cs::utils::split_timestamp;
use era_cudart::{
    device::{get_device_count, get_device_properties, set_device},
    result::CudaResult,
};
use gpu_prover::{
    allocator::host::ConcurrentStaticHostAllocator,
    prover::{
        context::{MemPoolProverContext, ProverContext},
        memory::commit_memory,
        setup::SetupPrecomputations,
        tracing_data::{TracingDataHost, TracingDataTransfer},
    },
    witness::{
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
    gpu::{create_default_prover_context, trace_execution_for_gpu},
    NUM_QUERIES, POW_BITS,
};

//#[derive(Debug)]
pub enum GpuJob {
    ComputeSomething(u32),
    MainCircuitMemoryCommit(MainCircuitMemoryCommitRequest),
    Shutdown,
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

/// Thread that is responsible for running all computation on a single gpu.
pub struct GpuThread {
    pub device_id: i32,
    gpu_thread: Option<Sender<GpuJob>>,
}

impl GpuThread {
    pub fn init_multigpu() -> CudaResult<Vec<GpuThread>> {
        // REMOVE REMOVE - temporary hack.
        let device_count = 1;
        //let device_count = get_device_count()?;
        let mut gpu_threads = Vec::with_capacity(device_count as usize);
        for device_id in 0..device_count {
            let gpu_thread = GpuThread::new(device_id)?;
            gpu_threads.push(gpu_thread);
        }

        Ok(gpu_threads)
    }

    pub fn start_multigpu(gpu_threads: &mut Vec<GpuThread>) {
        if !MemPoolProverContext::is_host_allocator_initialized() {
            // allocate 4 x 1 GB ((1 << 8) << 22) of pinned host memory with 4 MB (1 << 22) chunking
            MemPoolProverContext::initialize_host_allocator(4, 1 << 8, 22).unwrap();
        }
        for gpu_thread in gpu_threads.iter_mut() {
            gpu_thread.start();
        }
    }

    pub fn send_job(&self, job: GpuJob) -> Result<(), TryRecvError> {
        if let Some(gpu_thread) = &self.gpu_thread {
            gpu_thread.send(job).map_err(|_| TryRecvError::Disconnected)
        } else {
            Err(TryRecvError::Disconnected)
        }
    }

    /// Creates a new GPU thread.
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

    fn spawn_gpu_thread(device_id: i32) -> Sender<GpuJob> {
        // Create a channel.  We only need Sender in the parent; Receiver moves into the GPU thread.
        let (tx, rx): (Sender<GpuJob>, Receiver<GpuJob>) = unbounded();

        // Spawn the dedicated GPU thread:
        thread::spawn(move || {
            println!("[GPU {}] Initializing GPU context...", device_id);
            set_device(device_id).unwrap();
            let context = create_default_prover_context();

            println!("[GPU {}] GPU context ready.", device_id);
            loop {
                match rx.try_recv() {
                    Ok(job) => match job {
                        GpuJob::ComputeSomething(value) => {
                            println!(
                                "[GPU thread] Got ComputeSomething({}), sending it to GPU ...",
                                value
                            );
                            thread::sleep(Duration::from_millis(50));
                            println!("[GPU thread] Finished ComputeSomething({}).", value);
                        }
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
                                request.lde_factor,         // lde_factor
                                request.trace_len,          // trace_len
                                request.setup_and_teardown, // setup_and_teardown
                                request.witness_chunk,      // witness_chunk
                                request.circuit_type,       // circuit_type
                                &request.compiled_circuit,  // compiled_circuit
                                &context,                   // prover_context
                            );

                            request.reply_to.send(result).unwrap();

                            println!("[GPU {}] Finished MainCircuitMemoryCommit.", device_id);
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

            // (Optional) Any final cleanup here before thread exits.
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
}

pub fn multigpu_prove_image_execution_for_machine_with_gpu_tracers<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: &MainCircuitPrecomputations<
        C,
        Global,
        ConcurrentStaticHostAllocator,
    >,
    delegation_circuits_precomputations: &[(
        u32,
        DelegationCircuitPrecomputations<Global, ConcurrentStaticHostAllocator>,
    )],
    gpu_threads: &Vec<GpuThread>,
    worker: &Worker,
) -> CudaResult<(Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>)>
where
    [(); { C::SUPPORT_LOAD_LESS_THAN_WORD } as usize]:,
{
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

    let mut memory_trees = vec![];
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
            // TODO: this is the only one that is being copied around.. in the future - maybe Arc?
            compiled_circuit: risc_v_circuit_precomputations.compiled_circuit.clone(),
            reply_to: resp_tx,
        };

        gpu_threads[0]
            .send_job(GpuJob::MainCircuitMemoryCommit(request))
            .unwrap();

        // TODO: this wait could be also done later.
        let gpu_caps = resp_rx.recv().unwrap()?;
        memory_trees.push(gpu_caps);
    }

    // REMOVE REMOVE
    set_device(1).unwrap();
    let prover_context_val = create_default_prover_context();
    let prover_context = &prover_context_val;
    // REMOVE REMOVE

    // same for delegation circuits
    let mut delegation_memory_trees = vec![];

    let mut delegation_types: Vec<_> = delegation_circuits_witness.keys().copied().collect();
    delegation_types.sort();

    for delegation_type in delegation_types.iter().cloned() {
        let els = &delegation_circuits_witness[&delegation_type];
        let delegation_type_id = delegation_type as u32;
        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == delegation_type_id)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let mut per_tree_set = vec![];
        for el in els.iter() {
            let gpu_caps = {
                let circuit = &prec.compiled_circuit.compiled_circuit;
                let trace_len = circuit.trace_len;
                let lde_factor = prec.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES
                    [trace_len.trailing_zeros() as usize]
                    .total_caps_size_log2 as u32;
                let trace = el.clone();
                let data = TracingDataHost::Delegation(trace);
                let circuit_type = CircuitType::Delegation(delegation_type);
                let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
                transfer.schedule_transfer(prover_context)?;
                let job = commit_memory(
                    transfer,
                    &circuit,
                    log_lde_factor,
                    log_tree_cap_size,
                    prover_context,
                )?;
                job.finish()?
            };
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

    let mut gpu_setup_main = {
        let setup_row_major = &risc_v_circuit_precomputations.setup.ldes[0].trace;
        let mut setup_evaluations = Vec::with_capacity_in(
            setup_row_major.as_slice().len(),
            ConcurrentStaticHostAllocator::default(),
        );
        unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
        transpose::transpose(
            setup_row_major.as_slice(),
            &mut setup_evaluations,
            setup_row_major.padded_width,
            setup_row_major.len(),
        );
        setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
        let circuit = &risc_v_circuit_precomputations.compiled_circuit;
        let lde_factor = setups::lde_factor_for_machine::<C>();
        let log_lde_factor = lde_factor.trailing_zeros();
        let log_domain_size = trace_len.trailing_zeros();
        let log_tree_cap_size =
            OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
        let mut setup =
            SetupPrecomputations::new(circuit, log_lde_factor, log_tree_cap_size, prover_context)?;
        setup.schedule_transfer(Arc::new(setup_evaluations), prover_context)?;
        setup
    };

    // now prove one by one
    let mut main_proofs = vec![];
    for (circuit_sequence, witness_chunk) in main_circuits_witness.into_iter().enumerate() {
        let gpu_proof = {
            let lde_factor = setups::lde_factor_for_machine::<C>();
            let circuit = &risc_v_circuit_precomputations.compiled_circuit;
            let (setup_and_teardown, aux_boundary_values) = if circuit_sequence < num_paddings {
                (None, AuxArgumentsBoundaryValues::default())
            } else {
                let shuffle_rams = &inits_and_teardowns[circuit_sequence - num_paddings];
                (
                    Some(shuffle_rams.clone()),
                    get_aux_arguments_boundary_values(
                        &shuffle_rams.lazy_init_data,
                        cycles_per_circuit,
                    ),
                )
            };
            let trace = witness_chunk.into();
            let data = TracingDataHost::Main {
                setup_and_teardown,
                trace,
            };
            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values,
            };
            let job = gpu_prover::prover::proof::prove(
                circuit,
                external_values,
                &mut gpu_setup_main,
                transfer,
                &risc_v_circuit_precomputations.twiddles,
                &risc_v_circuit_precomputations.lde_precomputations,
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

        memory_grand_product.mul_assign(&gpu_proof.memory_grand_product_accumulator);
        delegation_argument_sum.add_assign(&gpu_proof.delegation_argument_accumulator.unwrap());

        aux_memory_trees.push(gpu_proof.memory_tree_caps.clone());

        main_proofs.push(gpu_proof);
    }

    drop(gpu_setup_main);

    if main_circuits_witness_len > 0 {
        println!(
            "=== Total proving time: {:?} for {} circuits - avg: {:?}",
            total_proving_start.elapsed(),
            main_circuits_witness_len,
            total_proving_start.elapsed() / main_circuits_witness_len.try_into().unwrap()
        )
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0u32;
    // commit memory trees
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
        let mut gpu_setup_delegation = {
            let lde_factor = prec.lde_factor;
            let log_lde_factor = lde_factor.trailing_zeros();
            let trace_len = circuit.trace_len;
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
            let setup_row_major = &prec.setup.ldes[0].trace;
            let mut setup_evaluations = Vec::with_capacity_in(
                setup_row_major.as_slice().len(),
                ConcurrentStaticHostAllocator::default(),
            );
            unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
            transpose::transpose(
                setup_row_major.as_slice(),
                &mut setup_evaluations,
                setup_row_major.padded_width,
                setup_row_major.len(),
            );
            setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
            let mut setup = SetupPrecomputations::new(
                circuit,
                log_lde_factor,
                log_tree_cap_size,
                prover_context,
            )?;
            setup.schedule_transfer(Arc::new(setup_evaluations), prover_context)?;
            setup
        };

        let mut per_tree_set = vec![];

        let mut per_delegation_type_proofs = vec![];
        for (_circuit_idx, el) in els.iter().enumerate() {
            delegation_proofs_count += 1;

            // and prove
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values: AuxArgumentsBoundaryValues::default(),
            };
            let gpu_proof = {
                let trace = el.clone();
                let data = TracingDataHost::Delegation(trace);
                let circuit_type = CircuitType::Delegation(delegation_type);
                let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
                transfer.schedule_transfer(prover_context)?;
                let job = gpu_prover::prover::proof::prove(
                    circuit,
                    external_values,
                    &mut gpu_setup_delegation,
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

            memory_grand_product.mul_assign(&gpu_proof.memory_grand_product_accumulator);
            delegation_argument_sum.sub_assign(&gpu_proof.delegation_argument_accumulator.unwrap());

            per_tree_set.push(gpu_proof.memory_tree_caps.clone());

            per_delegation_type_proofs.push(gpu_proof);
        }

        aux_delegation_memory_trees.push((delegation_type_id, per_tree_set));
        delegation_proofs.push((delegation_type_id, per_delegation_type_proofs));

        drop(gpu_setup_delegation);
    }

    if delegation_proofs_count > 0 {
        println!(
            "=== Total delegation proving time: {:?} for {} circuits - avg: {:?}",
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
