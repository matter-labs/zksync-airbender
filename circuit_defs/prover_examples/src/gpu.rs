use std::{alloc::Global, collections::HashMap, sync::Arc};

use cs::utils::split_timestamp;
pub use gpu_prover::allocator::host::ConcurrentStaticHostAllocator;
use gpu_prover::circuit_type::{CircuitType, DelegationCircuitType, MainCircuitType};
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::witness::trace_delegation::DelegationTraceHost;
use gpu_prover::witness::trace_main::{MainTraceHost, ShuffleRamSetupAndTeardownHost};
use gpu_prover::{
    prover::{
        context::{MemPoolProverContext, ProverContext, ProverContextConfig},
        memory::commit_memory,
        setup::SetupPrecomputations,
        tracing_data::{TracingDataHost, TracingDataTransfer},
    },
    witness::trace_main::get_aux_arguments_boundary_values,
};
use itertools::Itertools;
use prover::{
    definitions::{
        produce_register_contribution_into_memory_accumulator_raw, AuxArgumentsBoundaryValues,
        ExternalChallenges,
    },
    fft::GoodAllocator,
    field::{Field, Mersenne31Quartic},
    merkle_trees::{DefaultTreeConstructor, MerkleTreeConstructor},
    risc_v_simulator::cycle::{IMStandardIsaConfig, IWithoutByteAccessIsaConfigWithDelegation},
};

use prover::{
    definitions::{ExternalValues, OPTIMAL_FOLDING_PROPERTIES},
    prover_stages::Proof,
    risc_v_simulator::{
        abstractions::non_determinism::NonDeterminismCSRSource, cycle::MachineConfig,
    },
    tracers::oracles::chunk_lazy_init_and_teardown,
    worker::Worker,
    VectorMemoryImplWithRom,
};

use setups::{DelegationCircuitPrecomputations, MainCircuitPrecomputations};
use trace_and_split::{
    fs_transform_for_memory_and_delegation_arguments, run_and_split_for_gpu, FinalRegisterValue,
};

use crate::{NUM_QUERIES, POW_BITS};

pub fn initialize_host_allocator_if_needed() {
    if !MemPoolProverContext::is_host_allocator_initialized() {
        // allocate 8 x 1 GB ((1 << 8) << 22) of pinned host memory with 4 MB (1 << 22) chunking
        MemPoolProverContext::initialize_host_allocator(8, 1 << 8, 22).unwrap();
    }
}

pub fn create_default_prover_context<'a>() -> MemPoolProverContext<'a> {
    initialize_host_allocator_if_needed();
    let mut prover_context_config = ProverContextConfig::default();
    prover_context_config.allocation_block_log_size = 22;

    let prover_context = MemPoolProverContext::new(&prover_context_config).unwrap();
    prover_context
}

pub fn gpu_prove_image_execution_for_machine_with_gpu_tracers<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    P: ProverContext,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: &MainCircuitPrecomputations<C, Global, P::HostAllocator>,
    delegation_circuits_precomputations: &[(
        u32,
        DelegationCircuitPrecomputations<Global, P::HostAllocator>,
    )],
    prover_context: &P,
    worker: &Worker,
) -> CudaResult<(Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>)> {
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
    ) = trace_execution_for_gpu::<ND, C, P::HostAllocator>(
        max_cycles_to_run,
        bytecode,
        non_determinism,
        worker,
    );

    let (num_paddings, inits_and_teardowns) = inits_and_teardowns;

    let mut memory_trees = vec![];
    // commit memory trees
    for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
        let (gpu_caps, _) = {
            let lde_factor = setups::lde_factor_for_machine::<C>();
            let log_lde_factor = lde_factor.trailing_zeros();
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
            let setup_and_teardown = if circuit_sequence < num_paddings {
                None
            } else {
                Some(inits_and_teardowns[circuit_sequence - num_paddings].clone())
            };
            let trace = witness_chunk.clone();
            let data = TracingDataHost::Main {
                setup_and_teardown,
                trace,
            };

            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let job = commit_memory(
                transfer,
                &risc_v_circuit_precomputations.compiled_circuit,
                log_lde_factor,
                log_tree_cap_size,
                prover_context,
            )?;
            job.finish()?
        };

        memory_trees.push(gpu_caps);
    }

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
            let (gpu_caps, _) = {
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
            P::HostAllocator::default(),
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
    let main_compiled_circuit = Arc::new(risc_v_circuit_precomputations.compiled_circuit.clone());
    let mut main_proofs = vec![];
    for (circuit_sequence, witness_chunk) in main_circuits_witness.into_iter().enumerate() {
        let (gpu_proof, _) = {
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
                main_compiled_circuit.clone(),
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
        let delegation_compiled_circuit = Arc::new(circuit.clone());
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
                P::HostAllocator::default(),
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
            let (gpu_proof, _) = {
                let trace = el.clone();
                let data = TracingDataHost::Delegation(trace);
                let circuit_type = CircuitType::Delegation(delegation_type);
                let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
                transfer.schedule_transfer(prover_context)?;
                let job = gpu_prover::prover::proof::prove(
                    delegation_compiled_circuit.clone(),
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

pub fn trace_execution_for_gpu<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    mut non_determinism: ND,
    worker: &Worker,
) -> (
    Vec<MainTraceHost<A>>,
    (
        usize, // number of empty ones to assume
        Vec<ShuffleRamSetupAndTeardownHost<A>>,
    ),
    HashMap<DelegationCircuitType, Vec<DelegationTraceHost<A>>>,
    Vec<FinalRegisterValue>,
) {
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;

    let delegation_factories = setups::delegation_factories_for_machine::<C, A>();

    let (
        final_pc,
        main_circuits_witness,
        delegation_circuits_witness,
        final_register_values,
        init_and_teardown_chunks,
    ) = run_and_split_for_gpu::<ND, C, A>(
        max_cycles_to_run,
        bytecode,
        &mut non_determinism,
        delegation_factories,
        worker,
    );

    println!(
        "Program finished execution with final pc = 0x{:08x} and final register state\n{}",
        final_pc,
        final_register_values
            .iter()
            .enumerate()
            .map(|(idx, r)| format!("x{} = {}", idx, r.value))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // we just need to chunk inits/teardowns

    let init_and_teardown_chunks = chunk_lazy_init_and_teardown(
        main_circuits_witness.len(),
        cycles_per_circuit,
        &init_and_teardown_chunks,
        worker,
    );

    let main_circuits_witness = main_circuits_witness
        .into_iter()
        .map(|c| c.into())
        .collect_vec();

    let init_and_teardown_chunks = (
        init_and_teardown_chunks.0,
        init_and_teardown_chunks
            .1
            .into_iter()
            .map(|c| c.into())
            .collect_vec(),
    );

    let delegation_circuits_witness = delegation_circuits_witness
        .into_iter()
        .map(|(k, v)| (k.into(), v.into_iter().map(|c| c.into()).collect_vec()))
        .collect();

    (
        main_circuits_witness,
        init_and_teardown_chunks,
        delegation_circuits_witness,
        final_register_values,
    )
}
