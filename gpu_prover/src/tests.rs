use crate::circuit_type::CircuitType;
use crate::circuit_type::MainCircuitType;
use crate::prover::context::{MemPoolProverContext, ProverContext, ProverContextConfig};
use crate::prover::memory::commit_memory;
use crate::prover::setup::SetupPrecomputations;
use crate::prover::tracing_data::{TracingDataHost, TracingDataTransfer};
use crate::witness::trace_main::get_aux_arguments_boundary_values;
use cs::definitions::split_timestamp;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::device::{get_device_count, get_device_properties, set_device};
use era_cudart::event::elapsed_time;
use era_cudart::event::CudaEvent;
use era_cudart::memory::memory_copy;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use execution_utils::{find_binary_exit_point, get_padded_binary};
use fft::{adjust_to_zero_c0_var_length, GoodAllocator, LdePrecomputations, Twiddles};
use field::{Field, Mersenne31Complex, Mersenne31Field, Mersenne31Quartic};
use itertools::Itertools;
use prover::definitions::{
    produce_register_contribution_into_memory_accumulator_raw, AuxArgumentsBoundaryValues,
    ExternalChallenges, ExternalValues, OPTIMAL_FOLDING_PROPERTIES,
};
use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength, MerkleTreeConstructor};
use prover::prover_stages::stage5::Query;
use prover::prover_stages::{prove, Proof};
use prover::risc_v_simulator::abstractions::non_determinism::{
    NonDeterminismCSRSource, QuasiUARTSource,
};
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
use prover::transcript::Seed;
use prover::{
    evaluate_delegation_memory_witness, evaluate_memory_witness, evaluate_witness,
    DelegationMemoryOnlyWitnessEvaluationData, MemoryOnlyWitnessEvaluationData,
    ShuffleRamSetupAndTeardown, VectorMemoryImplWithRom, WitnessEvaluationAuxData,
};
use std::alloc::Global;
use std::collections::HashMap;
use std::ffi::CStr;
use std::io::Read;
use std::mem;
use std::mem::MaybeUninit;
use std::sync::Arc;
use trace_and_split::setups::{
    risc_v_cycles, DelegationCircuitPrecomputations, MainCircuitPrecomputations,
};
use trace_and_split::{
    fs_transform_for_memory_and_delegation_arguments, run_and_split_for_gpu, setups,
    FinalRegisterValue,
};
use trace_holder::RowMajorTrace;
use worker::Worker;

pub const NUM_QUERIES: usize = 53;
pub const POW_BITS: u32 = 28;

#[test]
fn test_prove_hashed_fibonacci() -> CudaResult<()> {
    let instant = std::time::Instant::now();
    MemPoolProverContext::initialize_host_allocator(4, 1 << 8, 22)?;
    let mut prover_context_config = ProverContextConfig::default();
    prover_context_config.allocation_block_log_size = 22;
    let prover_context = MemPoolProverContext::new(&prover_context_config)?;
    println!("prover_context created in {:?}", instant.elapsed());

    let instant = std::time::Instant::now();

    let worker = Worker::new();

    let mut binary = vec![];
    std::fs::File::open("../examples/hashed_fibonacci/app.bin")
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();

    let expected_final_pc = find_binary_exit_point(&binary);
    println!(
        "Expected final PC for base program is 0x{:08x}",
        expected_final_pc
    );

    let binary = get_padded_binary(&binary);
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 16, 1 << 14]);
    let main_circuit_precomputations = setups::get_main_riscv_circuit_setup(&binary, &worker);
    // let _end_params = compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
    let delegation_precomputations = setups::all_delegation_circuits_precomputations(&worker);

    println!("precomputations created in {:?}", instant.elapsed());

    let (main_proofs, delegation_proofs, _register_values) =
        prove_image_execution_for_machine_with_gpu_tracers(
            10,
            &binary,
            non_determinism_source,
            &main_circuit_precomputations,
            &delegation_precomputations,
            &prover_context,
            &worker,
        )?;

    let total_delegation_proofs: usize = delegation_proofs.iter().map(|(_, x)| x.len()).sum();

    println!(
        "Created {} basic proofs and {} delegation proofs.",
        main_proofs.len(),
        total_delegation_proofs
    );
    Ok(())
}

#[test]
fn bench_prove_hashed_fibonacci() -> CudaResult<()> {
    let instant = std::time::Instant::now();
    MemPoolProverContext::initialize_host_allocator(4, 1 << 8, 22)?;
    println!("host allocator initialized in {:?}", instant.elapsed());
    let instant = std::time::Instant::now();
    let device_count = get_device_count()?;
    println!("Found {} CUDA capable devices", device_count);
    let mut contexts = vec![];
    for device_id in 0..device_count {
        set_device(device_id)?;
        let props = get_device_properties(device_id)?;
        let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
        println!(
            "Device {}: {} ({} SMs, {} GB memory)",
            device_id,
            name,
            props.multiProcessorCount,
            props.totalGlobalMem as f32 / 1024.0 / 1024.0 / 1024.0
        );
        let mut prover_context_config = ProverContextConfig::default();
        prover_context_config.allocation_block_log_size = 22;
        let prover_context = MemPoolProverContext::new(&prover_context_config)?;
        contexts.push(prover_context);
    }
    println!("prover contexts created in {:?}", instant.elapsed());

    let instant = std::time::Instant::now();

    let worker = Worker::new();

    let mut binary = vec![];
    std::fs::File::open("../examples/hashed_fibonacci/app.bin")
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();

    let expected_final_pc = find_binary_exit_point(&binary);
    println!(
        "Expected final PC for base program is 0x{:08x}",
        expected_final_pc
    );

    let binary = get_padded_binary(&binary);
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 16, 0]);
    let main_circuit_precomputations = setups::get_main_riscv_circuit_setup(&binary, &worker);

    println!("precomputations created in {:?}", instant.elapsed());

    bench_proof_main(
        &binary,
        non_determinism_source,
        &main_circuit_precomputations,
        &contexts,
        &worker,
    )
}

fn prove_image_execution_for_machine_with_gpu_tracers<
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
    let padding_shuffle_ram_inits_and_teardowns = ShuffleRamSetupAndTeardown {
        lazy_init_data: {
            let len = risc_v_circuit_precomputations.compiled_circuit.trace_len - 1;
            let mut data = Vec::with_capacity_in(len, P::HostAllocator::default());
            data.spare_capacity_mut()
                .fill(MaybeUninit::new(Default::default()));
            unsafe { data.set_len(len) };
            data
        },
    };

    // commit memory trees
    for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
        let shuffle_rams = if circuit_sequence < num_paddings {
            &padding_shuffle_ram_inits_and_teardowns
        } else {
            &inits_and_teardowns[circuit_sequence - num_paddings]
        };

        let (gpu_caps, _) = {
            let lde_factor = setups::lde_factor_for_machine::<C>();
            let log_lde_factor = lde_factor.trailing_zeros();
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
            let setup_and_teardown = if circuit_sequence < num_paddings {
                None
            } else {
                Some(shuffle_rams.clone().into())
            };
            let trace = witness_chunk.clone().into();
            let data = TracingDataHost::Main {
                setup_and_teardown,
                trace,
            };
            let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
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

        let (caps, _aux_data) = commit_memory_tree_for_riscv_circuit_using_gpu_tracer(
            &risc_v_circuit_precomputations.compiled_circuit,
            witness_chunk,
            shuffle_rams,
            circuit_sequence,
            &risc_v_circuit_precomputations.twiddles,
            &risc_v_circuit_precomputations.lde_precomputations,
            worker,
        );

        gpu_caps
            .iter()
            .zip(caps.iter())
            .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

        memory_trees.push(caps);
    }

    // same for delegation circuits
    let mut delegation_memory_trees = vec![];

    let mut delegation_types: Vec<_> = delegation_circuits_witness.keys().copied().collect();
    delegation_types.sort();

    for delegation_type in delegation_types.iter() {
        let els = &delegation_circuits_witness[&delegation_type];
        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == *delegation_type as u32)
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
                let trace = el.clone().into();
                let data = TracingDataHost::Delegation(trace);
                let circuit_type = CircuitType::from_delegation_type(*delegation_type);
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

            let (cpu_caps, delegation_t) =
                commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );

            gpu_caps
                .iter()
                .zip(cpu_caps.iter())
                .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

            assert_eq!(*delegation_type as u32, delegation_t);
            per_tree_set.push(cpu_caps);
        }

        delegation_memory_trees.push((*delegation_type as u32, per_tree_set));
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

    let gpu_circuit = Arc::new(risc_v_circuit_precomputations.compiled_circuit.clone());

    // now prove one by one
    let mut main_proofs = vec![];
    for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
        let shuffle_rams = if circuit_sequence < num_paddings {
            &padding_shuffle_ram_inits_and_teardowns
        } else {
            &inits_and_teardowns[circuit_sequence - num_paddings]
        };

        let oracle = MainRiscVOracle {
            cycle_data: witness_chunk,
        };

        let witness_trace = evaluate_witness(
            &risc_v_circuit_precomputations.compiled_circuit,
            risc_v_circuit_precomputations.witness_eval_fn_for_gpu_tracer,
            cycles_per_circuit,
            &oracle,
            &shuffle_rams.lazy_init_data,
            &risc_v_circuit_precomputations.table_driver,
            circuit_sequence,
            worker,
            Global,
        );

        // and prove
        let mut public_inputs = witness_trace.aux_data.first_row_public_inputs.clone();
        public_inputs.extend_from_slice(&witness_trace.aux_data.one_before_last_row_public_inputs);

        let external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: AuxArgumentsBoundaryValues {
                lazy_init_first_row: witness_trace.aux_data.lazy_init_first_row,
                teardown_value_first_row: witness_trace.aux_data.teardown_value_first_row,
                teardown_timestamp_first_row: witness_trace.aux_data.teardown_timestamp_first_row,
                lazy_init_one_before_last_row: witness_trace.aux_data.lazy_init_one_before_last_row,
                teardown_value_one_before_last_row: witness_trace
                    .aux_data
                    .teardown_value_one_before_last_row,
                teardown_timestamp_one_before_last_row: witness_trace
                    .aux_data
                    .teardown_timestamp_one_before_last_row,
            },
        };

        let lde_factor = setups::lde_factor_for_machine::<C>();

        let (_, cpu_proof) = prove(
            &risc_v_circuit_precomputations.compiled_circuit,
            &public_inputs,
            &external_values,
            witness_trace.clone(),
            &risc_v_circuit_precomputations.setup,
            &risc_v_circuit_precomputations.twiddles,
            &risc_v_circuit_precomputations.lde_precomputations,
            circuit_sequence,
            None,
            lde_factor,
            risc_v_cycles::TREE_CAP_SIZE,
            NUM_QUERIES,
            POW_BITS,
            worker,
        );

        let (gpu_proof, _) = {
            let circuit = &risc_v_circuit_precomputations.compiled_circuit;
            let log_lde_factor = lde_factor.trailing_zeros();
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
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
            let mut setup = SetupPrecomputations::new(
                circuit,
                log_lde_factor,
                log_tree_cap_size,
                prover_context,
            )?;
            setup.schedule_transfer(Arc::new(setup_evaluations), prover_context)?;
            let (setup_and_teardown, aux_boundary_values) = if circuit_sequence < num_paddings {
                (None, AuxArgumentsBoundaryValues::default())
            } else {
                (
                    Some(shuffle_rams.clone().into()),
                    get_aux_arguments_boundary_values(
                        &shuffle_rams.lazy_init_data,
                        cycles_per_circuit,
                    ),
                )
            };
            let trace = witness_chunk.clone().into();
            let data = TracingDataHost::Main {
                setup_and_teardown,
                trace,
            };
            let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
            let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
            transfer.schedule_transfer(prover_context)?;
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values,
            };
            let job = crate::prover::proof::prove(
                gpu_circuit.clone(),
                external_values,
                &mut setup,
                transfer,
                &risc_v_circuit_precomputations.twiddles,
                &risc_v_circuit_precomputations.lde_precomputations,
                circuit_sequence,
                None,
                lde_factor,
                NUM_QUERIES,
                POW_BITS,
                Some(cpu_proof.pow_nonce),
                prover_context,
            )?;
            job.finish()?
        };

        compare_proofs(&cpu_proof, &gpu_proof);

        memory_grand_product.mul_assign(&cpu_proof.memory_grand_product_accumulator);
        delegation_argument_sum.add_assign(&cpu_proof.delegation_argument_accumulator.unwrap());

        // assert_eq!(&proof.memory_tree_caps, &memory_trees[circuit_sequence]);

        aux_memory_trees.push(cpu_proof.memory_tree_caps.clone());

        main_proofs.push(cpu_proof);
    }

    if main_circuits_witness.len() > 0 {
        println!(
            "=== Total proving time: {:?} for {} circuits - avg: {:?}",
            total_proving_start.elapsed(),
            main_circuits_witness.len(),
            total_proving_start.elapsed() / main_circuits_witness.len().try_into().unwrap()
        )
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0u32;
    // commit memory trees
    for delegation_type in delegation_types.iter() {
        let els = &delegation_circuits_witness[&delegation_type];
        println!(
            "Producing proofs for delegation circuit type {}, {} proofs in total",
            delegation_type,
            els.len()
        );

        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == *delegation_type as u32)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let mut per_tree_set = vec![];

        let mut per_delegation_type_proofs = vec![];
        let gpu_circuit = Arc::new(prec.compiled_circuit.compiled_circuit.clone());

        for (_circuit_idx, el) in els.iter().enumerate() {
            delegation_proofs_count += 1;
            let oracle = DelegationCircuitOracle { cycle_data: el };

            let witness_trace = evaluate_witness(
                &prec.compiled_circuit.compiled_circuit,
                prec.witness_eval_fn_for_gpu_tracer,
                prec.compiled_circuit.num_requests_per_circuit,
                &oracle,
                &[],
                &prec.compiled_circuit.table_driver,
                0,
                worker,
                Global,
            );

            // and prove
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values: AuxArgumentsBoundaryValues::default(),
            };

            assert!(*delegation_type < 1 << 12);
            let (_, cpu_proof) = prove(
                &prec.compiled_circuit.compiled_circuit,
                &[],
                &external_values,
                witness_trace,
                &prec.setup,
                &prec.twiddles,
                &prec.lde_precomputations,
                0,
                Some(*delegation_type),
                prec.lde_factor,
                prec.tree_cap_size,
                NUM_QUERIES,
                POW_BITS,
                worker,
            );

            let (gpu_proof, _) = {
                let lde_factor = prec.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let trace_len = gpu_circuit.trace_len;
                let log_domain_size = trace_len.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                    .total_caps_size_log2 as u32;
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
                    &gpu_circuit,
                    log_lde_factor,
                    log_tree_cap_size,
                    prover_context,
                )?;
                setup.schedule_transfer(Arc::new(setup_evaluations), prover_context)?;
                let trace = el.clone().into();
                let data = TracingDataHost::Delegation(trace);
                let circuit_type = CircuitType::from_delegation_type(*delegation_type);
                let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
                transfer.schedule_transfer(prover_context)?;
                let job = crate::prover::proof::prove(
                    gpu_circuit.clone(),
                    external_values,
                    &mut setup,
                    transfer,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    0,
                    Some(*delegation_type),
                    prec.lde_factor,
                    NUM_QUERIES,
                    POW_BITS,
                    Some(cpu_proof.pow_nonce),
                    prover_context,
                )?;
                job.finish()?
            };

            compare_proofs(&cpu_proof, &gpu_proof);

            memory_grand_product.mul_assign(&cpu_proof.memory_grand_product_accumulator);
            delegation_argument_sum.sub_assign(&cpu_proof.delegation_argument_accumulator.unwrap());

            per_tree_set.push(cpu_proof.memory_tree_caps.clone());

            per_delegation_type_proofs.push(cpu_proof);
        }

        aux_delegation_memory_trees.push((*delegation_type as u32, per_tree_set));
        delegation_proofs.push((*delegation_type as u32, per_delegation_type_proofs));
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

    // assert_eq!(&aux_memory_trees, &memory_trees);
    // assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees);

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

fn bench_proof_main<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    P: ProverContext,
>(
    bytecode: &[u32],
    non_determinism: ND,
    precomputations: &MainCircuitPrecomputations<C, Global, P::HostAllocator>,
    contexts: &[P],
    worker: &Worker,
) -> CudaResult<()> {
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let trace_len = setups::trace_len_for_machine::<C>();
    assert_eq!(cycles_per_circuit + 1, trace_len);
    let max_cycles_to_run = cycles_per_circuit;

    let (
        main_circuits_witness,
        _inits_and_teardowns,
        _delegation_circuits_witness,
        _final_register_values,
    ) = trace_execution_for_gpu::<ND, C, P::HostAllocator>(
        max_cycles_to_run,
        bytecode,
        non_determinism,
        worker,
    );

    let trace = main_circuits_witness.into_iter().nth(0).unwrap().into();
    let data = TracingDataHost::Main {
        setup_and_teardown: None,
        trace,
    };
    let lde_factor = setups::lde_factor_for_machine::<C>();
    let circuit = &precomputations.compiled_circuit;
    let gpu_circuit = Arc::new(circuit.clone());
    let log_lde_factor = lde_factor.trailing_zeros();
    let log_domain_size = trace_len.trailing_zeros();
    let log_tree_cap_size =
        OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
    let setup_row_major = &precomputations.setup.ldes[0].trace;
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
    let setup_evaluations = Arc::new(setup_evaluations);
    let mut setups = Vec::with_capacity(contexts.len());
    for context in contexts.iter() {
        context.switch_to_device()?;
        let mut setup =
            SetupPrecomputations::new(circuit, log_lde_factor, log_tree_cap_size, context)?;
        setup.schedule_transfer(setup_evaluations.clone(), context)?;
        setups.push(setup);
    }
    let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
    nvtx::range_push!("warmup");
    {
        let external_values = ExternalValues {
            challenges: ExternalChallenges::draw_from_transcript_seed(Seed([0; 8]), true),
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        };
        for (context, setup) in contexts.iter().zip(setups.iter_mut()) {
            context.switch_to_device()?;
            let mut transfer = TracingDataTransfer::new(circuit_type, data.clone(), context)?;
            transfer.schedule_transfer(context)?;
            let job = crate::prover::proof::prove(
                gpu_circuit.clone(),
                external_values,
                setup,
                transfer,
                &precomputations.twiddles,
                &precomputations.lde_precomputations,
                0,
                None,
                lde_factor,
                NUM_QUERIES,
                POW_BITS,
                None,
                context,
            )?;
            job.finish()?;
        }
    }
    println!("warmup done");
    nvtx::range_pop!();

    let mut current_transfers = vec![];
    let mut current_jobs = vec![];
    let mut start_events = vec![];
    let mut end_events = vec![];

    for context in contexts.iter() {
        context.switch_to_device()?;
        let mut transfer = TracingDataTransfer::new(circuit_type, data.clone(), context)?;
        transfer.schedule_transfer(context)?;
        current_transfers.push(transfer);
        current_jobs.push(None);
        context.get_h2d_stream().synchronize()?;
        context.get_exec_stream().synchronize()?;
        start_events.push(CudaEvent::create()?);
        end_events.push(CudaEvent::create()?);
    }

    const PROOF_COUNT: usize = 64;

    nvtx::range_push!("bench");

    for (context, event) in contexts.iter().zip(start_events.iter()) {
        event.record(context.get_exec_stream())?;
    }
    for i in 0..PROOF_COUNT {
        let external_values = ExternalValues {
            challenges: ExternalChallenges::draw_from_transcript_seed(Seed([i as u32; 8]), true),
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        };
        for (((context, setup), current_transfer), current_job) in contexts
            .iter()
            .zip(setups.iter_mut())
            .zip(current_transfers.iter_mut())
            .zip(current_jobs.iter_mut())
        {
            context.switch_to_device()?;
            let mut transfer = TracingDataTransfer::new(circuit_type, data.clone(), context)?;
            transfer.schedule_transfer(context)?;
            mem::swap(current_transfer, &mut transfer);
            let job = crate::prover::proof::prove(
                gpu_circuit.clone(),
                external_values,
                setup,
                transfer,
                &precomputations.twiddles,
                &precomputations.lde_precomputations,
                0,
                None,
                lde_factor,
                NUM_QUERIES,
                POW_BITS,
                None,
                context,
            )?;
            let mut job = Some(job);
            mem::swap(current_job, &mut job);
            if let Some(job) = job {
                job.finish()?;
            }
        }
    }
    for (context, end_event) in contexts.iter().zip(end_events.iter_mut()) {
        end_event.record(context.get_exec_stream())?;
    }

    for (end_event, current_job) in end_events.iter_mut().zip(current_jobs.iter_mut()) {
        current_job.take().unwrap().finish()?;
        end_event.synchronize()?;
    }
    nvtx::range_pop!();

    let mut elapsed_times = vec![];
    for (start_event, end_event) in start_events.iter().zip(end_events.iter()) {
        elapsed_times.push(elapsed_time(start_event, end_event)?);
    }

    for (context, elapsed_time) in contexts.iter().zip(elapsed_times.iter()) {
        let device_id = context.get_device_id();
        println!("Device ID {device_id} elapsed time: {:.3} ms", elapsed_time);
        let average = elapsed_time / PROOF_COUNT as f32;
        println!(
            "Device ID {device_id} average proof time: {:.3} ms",
            average
        );
        let speed = (PROOF_COUNT * trace_len) as f32 / elapsed_time / 1_000.0;
        println!(
            "Device ID {device_id} average proof speed: {:.3} MHz",
            speed
        );
    }

    let elapsed_time = elapsed_times.iter().sum::<f32>() / contexts.len() as f32;
    println!("Combined average elapsed time: {:.3} ms", elapsed_time);
    let average = elapsed_time / PROOF_COUNT as f32;
    println!("Combined average proof time: {:.3} ms", average);
    let speed = (PROOF_COUNT * trace_len) as f32 / elapsed_time / 1_000.0;
    println!("Combined average proof speed: {:.3} MHz", speed);
    println!(
        "Aggregate proof speed: {:.3} MHz",
        speed * contexts.len() as f32
    );
    Ok(())
}

fn trace_execution_for_gpu<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    mut non_determinism: ND,
    worker: &Worker,
) -> (
    Vec<CycleData<C, A>>,
    (
        usize, // number of empty ones to assume
        Vec<ShuffleRamSetupAndTeardown<A>>,
    ),
    HashMap<u16, Vec<DelegationWitness<A>>>,
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

    (
        main_circuits_witness,
        init_and_teardown_chunks,
        delegation_circuits_witness,
        final_register_values,
    )
}

fn commit_memory_tree_for_riscv_circuit_using_gpu_tracer<C: MachineConfig>(
    compiled_machine: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_chunk: &CycleData<C, impl GoodAllocator>,
    inits_and_teardowns: &ShuffleRamSetupAndTeardown<impl GoodAllocator>,
    _circuit_sequence: usize,
    twiddles: &Twiddles<Mersenne31Complex, Global>,
    lde_precomputations: &LdePrecomputations<Global>,
    worker: &Worker,
) -> (Vec<MerkleTreeCapVarLength>, WitnessEvaluationAuxData) {
    let lde_factor = setups::lde_factor_for_machine::<C>();

    use setups::prover::prover_stages::stage1::compute_wide_ldes;
    let trace_len = witness_chunk.num_cycles_chunk_size + 1;
    assert!(trace_len.is_power_of_two());

    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let num_cycles_in_chunk = trace_len - 1;
    let now = std::time::Instant::now();

    let oracle = MainRiscVOracle {
        cycle_data: witness_chunk,
    };

    let memory_chunk = evaluate_memory_witness(
        compiled_machine,
        num_cycles_in_chunk,
        &oracle,
        &inits_and_teardowns.lazy_init_data,
        &worker,
        Global,
    );
    println!(
        "Materializing memory trace for {} cycles took {:?}",
        num_cycles_in_chunk,
        now.elapsed()
    );

    let MemoryOnlyWitnessEvaluationData {
        aux_data,
        memory_trace,
    } = memory_chunk;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    (caps, aux_data)
}

fn commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
    compiled_machine: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_chunk: &DelegationWitness<impl GoodAllocator>,
    twiddles: &Twiddles<Mersenne31Complex, Global>,
    lde_precomputations: &LdePrecomputations<Global>,
    lde_factor: usize,
    _tree_cap_size: usize,
    worker: &Worker,
) -> (Vec<MerkleTreeCapVarLength>, u32) {
    use setups::prover::prover_stages::stage1::compute_wide_ldes;

    let trace_len = witness_chunk.num_requests + 1;

    assert!(trace_len.is_power_of_two());
    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let num_cycles_in_chunk = trace_len - 1;
    let now = std::time::Instant::now();
    let oracle = DelegationCircuitOracle {
        cycle_data: witness_chunk,
    };
    let memory_chunk = evaluate_delegation_memory_witness(
        compiled_machine,
        num_cycles_in_chunk,
        &oracle,
        &worker,
        Global,
    );
    println!(
        "Materializing delegation type {} memory trace for {} cycles took {:?}",
        witness_chunk.delegation_type,
        num_cycles_in_chunk,
        now.elapsed()
    );

    let DelegationMemoryOnlyWitnessEvaluationData { memory_trace } = memory_chunk;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    (caps, witness_chunk.delegation_type as u32)
}

#[allow(dead_code)]
pub(crate) fn compare_row_major_trace<
    T: Copy + std::fmt::Debug + Default + PartialEq,
    const N: usize,
>(
    cpu_data: &RowMajorTrace<T, N, impl GoodAllocator>,
    cpu_col_offset: usize,
    gpu_data: &DeviceSlice<T>,
    gpu_col_offset: usize,
    col_count: usize,
    row_count: usize,
) {
    let mut error_count = 0;
    let stride = cpu_data.len();
    assert_eq!(gpu_data.len() % stride, 0);
    let mut h_trace = vec![T::default(); col_count * stride];
    let gpu_range = gpu_col_offset * stride..(gpu_col_offset + col_count) * stride;
    memory_copy(&mut h_trace, &gpu_data[gpu_range]).unwrap();
    let mut gpu_data = vec![T::default(); h_trace.len()];
    transpose::transpose(&h_trace, &mut gpu_data, stride, col_count);
    let mut view = cpu_data.row_view(0..row_count);
    for (row, gpu_row) in gpu_data.chunks(col_count).take(row_count).enumerate() {
        let cpu_row = &view.current_row_ref()[cpu_col_offset..cpu_col_offset + col_count];
        if cpu_row != gpu_row {
            dbg!(row, cpu_row, gpu_row);
            error_count += 1;
            if error_count > 4 {
                panic!("too many errors");
            }
        }
        view.advance_row();
    }
    assert_eq!(error_count, 0);
}

fn compare_proofs(left: &Proof, right: &Proof) {
    assert_eq!(
        &left.setup_tree_caps, &right.setup_tree_caps,
        "setup_tree_caps mismatch"
    );
    assert_eq!(
        &left.memory_tree_caps, &right.memory_tree_caps,
        "memory_tree_caps mismatch"
    );
    assert_eq!(
        &left.witness_tree_caps, &right.witness_tree_caps,
        "witness_tree_caps mismatch"
    );
    assert_eq!(
        &left.stage_2_tree_caps, &right.stage_2_tree_caps,
        "stage_2_tree_caps mismatch"
    );
    assert_eq!(
        &left.memory_grand_product_accumulator, &right.memory_grand_product_accumulator,
        "memory_grand_product_accumulator mismatch"
    );
    assert_eq!(
        &left.delegation_argument_accumulator, &right.delegation_argument_accumulator,
        "delegation_argument_accumulator mismatch"
    );
    assert_eq!(
        &left.quotient_tree_caps, &right.quotient_tree_caps,
        "quotient_tree_caps mismatch"
    );
    assert_eq!(
        &left.evaluations_at_random_points, &right.evaluations_at_random_points,
        "evaluations_at_random_points mismatch"
    );
    assert_eq!(
        &left.deep_poly_caps, &right.deep_poly_caps,
        "deep_poly_caps mismatch"
    );
    assert_eq!(
        &left.intermediate_fri_oracle_caps, &right.intermediate_fri_oracle_caps,
        "intermediate_fri_oracle_caps mismatch"
    );
    assert_eq!(
        &left.last_fri_step_plain_leaf_values, &right.last_fri_step_plain_leaf_values,
        "last_fri_step_plain_leaf_values mismatch"
    );
    assert_eq!(&left.final_monomial_form, &right.final_monomial_form);
    for (cpu_query_set, gpu_query_set) in left.queries.iter().zip_eq(right.queries.iter()) {
        let assert_query = |cpu: &Query, gpu: &Query, set: &str| {
            assert_eq!(
                cpu.query_index, gpu.query_index,
                "query_index mismatch {}",
                set
            );
            assert_eq!(
                cpu.tree_index, gpu.tree_index,
                "tree_index mismatch {}",
                set
            );
            assert_eq!(
                cpu.leaf_content, gpu.leaf_content,
                "leaf_content mismatch {} query_index: {} tree_index: {} ",
                set, cpu.query_index, cpu.tree_index
            );
            assert_eq!(
                cpu.merkle_proof, gpu.merkle_proof,
                "merkle_proof mismatch {} query_index: {} tree_index: {}",
                set, cpu.query_index, cpu.tree_index
            );
        };
        assert_query(
            &cpu_query_set.witness_query,
            &gpu_query_set.witness_query,
            "witness_query",
        );
        assert_query(
            &cpu_query_set.memory_query,
            &gpu_query_set.memory_query,
            "memory_query",
        );
        assert_query(
            &cpu_query_set.setup_query,
            &gpu_query_set.setup_query,
            "setup_query",
        );
        assert_query(
            &cpu_query_set.stage_2_query,
            &gpu_query_set.stage_2_query,
            "stage_2_query",
        );
        assert_query(
            &cpu_query_set.quotient_query,
            &gpu_query_set.quotient_query,
            "quotient_query",
        );
        assert_query(
            &cpu_query_set.initial_fri_query,
            &gpu_query_set.initial_fri_query,
            "initial_fri_query",
        );
        for (i, (cpu, gpu)) in cpu_query_set
            .intermediate_fri_queries
            .iter()
            .zip_eq(gpu_query_set.intermediate_fri_queries.iter())
            .enumerate()
        {
            assert_query(cpu, gpu, &format!("fri_query {i}"));
        }
    }
    assert_eq!(left.pow_nonce, right.pow_nonce);
}
