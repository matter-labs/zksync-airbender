#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(allocator_api)]
#![feature(array_chunks)]

use std::alloc::Global;
use std::collections::HashMap;

pub use prover;
use prover::cs::utils::split_timestamp;
use prover::trace_holder::RowMajorTrace;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
pub use setups;

use merkle_trees::DefaultTreeConstructor;
use prover::cs::definitions::ColumnSet;
use prover::definitions::produce_register_contribution_into_memory_accumulator_raw;
use prover::definitions::*;
use prover::fft::*;
use prover::field::*;
use prover::merkle_trees::MerkleTreeConstructor;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::*;
use prover_stages::prove;
use prover_stages::Proof;
use risc_v_simulator::abstractions::non_determinism::*;
use risc_v_simulator::cycle::IMStandardIsaConfig;
use risc_v_simulator::cycle::IWithoutByteAccessIsaConfig;
use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
use risc_v_simulator::cycle::MachineConfig;
use setups::*;
use trace_and_split::*;

#[cfg(feature = "gpu")]
pub mod gpu;

pub const NUM_QUERIES: usize = 53;
pub const POW_BITS: u32 = 28;

#[cfg(not(feature = "precheck_satisfied"))]
const PRECHECK_SATISFIED: bool = false;

#[cfg(feature = "precheck_satisfied")]
const PRECHECK_SATISFIED: bool = true;

const DUMP_WITNESS_VAR: &str = "DUMP_WITNESS";

#[allow(dead_code)]
fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

fn bincode_serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    bincode::serialize_into(&mut dst, el).unwrap();
}

fn u32_from_field_elems(src: &[Mersenne31Field; 2]) -> u32 {
    use prover::field::PrimeField;

    let low = u16::try_from(src[0].as_u64_reduced()).expect("read value is not 16 bit long") as u32;
    let high =
        u16::try_from(src[1].as_u64_reduced()).expect("read value is not 16 bit long") as u32;
    low + (high << 16)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
struct MemAccess {
    is_register: bool,
    address: u32,
    timestamp: u32,
    value: u32,
}

#[allow(dead_code)]
fn read_u32_for_column_set(mem_row: &[Mersenne31Field], column_set: ColumnSet<2>) -> u32 {
    let low = mem_row[column_set.start()];
    let high = mem_row[column_set.start() + 1];
    low.to_reduced_u32() + (high.to_reduced_u32() << 16)
}

pub fn prove_image_execution<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: &MainCircuitPrecomputations<IMStandardIsaConfig, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A>)],
    worker: &worker::Worker,
) -> (Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>) {
    prove_image_execution_for_machine_with_gpu_tracers::<ND, IMStandardIsaConfig, A>(
        num_instances_upper_bound,
        bytecode,
        non_determinism,
        risc_v_circuit_precomputations,
        delegation_circuits_precomputations,
        worker,
    )
}

pub fn prove_image_execution_on_reduced_machine<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: &MainCircuitPrecomputations<
        IWithoutByteAccessIsaConfigWithDelegation,
        A,
    >,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A>)],
    worker: &worker::Worker,
) -> (Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>) {
    prove_image_execution_for_machine_with_gpu_tracers::<
        ND,
        IWithoutByteAccessIsaConfigWithDelegation,
        A,
    >(
        num_instances_upper_bound,
        bytecode,
        non_determinism,
        risc_v_circuit_precomputations,
        delegation_circuits_precomputations,
        worker,
    )
}

pub fn prove_image_execution_on_final_reduced_machine<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: &MainCircuitPrecomputations<IWithoutByteAccessIsaConfig, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A>)],
    worker: &worker::Worker,
) -> (Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>) {
    prove_image_execution_for_machine_with_gpu_tracers::<ND, IWithoutByteAccessIsaConfig, A>(
        num_instances_upper_bound,
        bytecode,
        non_determinism,
        risc_v_circuit_precomputations,
        delegation_circuits_precomputations,
        worker,
    )
}

pub fn trace_execution_for_gpu<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    mut non_determinism: ND,
    worker: &worker::Worker,
) -> (
    Vec<CycleData<C>>,
    (
        usize, // number of empty ones to assume
        Vec<ShuffleRamSetupAndTeardown>,
    ),
    HashMap<u16, Vec<DelegationWitness>>,
    Vec<FinalRegisterValue>,
) {
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;

    let delegation_factories = setups::delegation_factories_for_machine::<C, Global>();

    let (
        final_pc,
        main_circuits_witness,
        delegation_circuits_witness,
        final_register_values,
        init_and_teardown_chunks,
    ) = run_and_split_for_gpu::<ND, C, Global>(
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

pub fn prove_image_execution_for_machine_with_gpu_tracers<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    non_determinism: ND,
    risc_v_circuit_precomputations: &MainCircuitPrecomputations<C, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A>)],
    worker: &worker::Worker,
) -> (Vec<Proof>, Vec<(u32, Vec<Proof>)>, Vec<FinalRegisterValue>) {
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;

    let (
        main_circuits_witness,
        inits_and_teardowns,
        delegation_circuits_witness,
        final_register_values,
    ) = trace_execution_for_gpu::<ND, C, A>(max_cycles_to_run, bytecode, non_determinism, worker);

    let (num_paddings, inits_and_teardowns) = inits_and_teardowns;

    let should_dump_witness = std::env::var(DUMP_WITNESS_VAR)
        .map(|el| el.parse::<u32>().unwrap_or(0) == 1)
        .unwrap_or(false);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let mut memory_trees = vec![];
    let mut previous_aux: Option<WitnessEvaluationAuxData> = None;
    let padding_shuffle_ram_inits_and_teardowns = ShuffleRamSetupAndTeardown {
        lazy_init_data: vec![
            Default::default();
            risc_v_circuit_precomputations.compiled_circuit.trace_len - 1
        ],
    };

    // commit memory trees
    for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
        let shuffle_rams = if circuit_sequence < num_paddings {
            &padding_shuffle_ram_inits_and_teardowns
        } else {
            &inits_and_teardowns[circuit_sequence - num_paddings]
        };
        let (caps, aux_data) = commit_memory_tree_for_riscv_circuit_using_gpu_tracer(
            &risc_v_circuit_precomputations.compiled_circuit,
            witness_chunk,
            shuffle_rams,
            circuit_sequence,
            &risc_v_circuit_precomputations.twiddles,
            &risc_v_circuit_precomputations.lde_precomputations,
            worker,
        );

        memory_trees.push(caps);
        if let Some(previous_aux) = previous_aux.take() {
            let this = u32_from_field_elems(&aux_data.lazy_init_first_row);
            let previous = u32_from_field_elems(&previous_aux.lazy_init_one_before_last_row);
            if this > previous {
                // normal ascending comparison
            } else {
                // we expect zero prepadding, and zero teardown data
                assert_eq!(this, previous);
                assert_eq!(previous, 0);
                assert_eq!(
                    u32_from_field_elems(&previous_aux.teardown_value_one_before_last_row),
                    0
                );
                assert_eq!(
                    u32_from_field_elems(&previous_aux.teardown_timestamp_one_before_last_row),
                    0
                );
            }
        }

        previous_aux = Some(aux_data);
    }
    #[cfg(feature = "timing_logs")]
    println!(
        "=== Commitment for {} RISC-V circuits memory trees took {:?}",
        main_circuits_witness.len(),
        now.elapsed()
    );

    // same for delegation circuits
    let now = std::time::Instant::now();
    let mut delegation_memory_trees = vec![];

    let mut delegation_types: Vec<_> = delegation_circuits_witness.keys().copied().collect();
    delegation_types.sort();

    for delegation_type in delegation_types.iter() {
        let els = &delegation_circuits_witness[&delegation_type];
        if els.is_empty() {
            continue;
        }
        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == *delegation_type as u32)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let mut per_tree_set = vec![];
        for el in els.iter() {
            let (caps, delegation_t) = commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
                &prec.compiled_circuit.compiled_circuit,
                el,
                &prec.twiddles,
                &prec.lde_precomputations,
                prec.lde_factor,
                prec.tree_cap_size,
                worker,
            );
            assert_eq!(*delegation_type as u32, delegation_t);
            per_tree_set.push(caps);
        }

        delegation_memory_trees.push((*delegation_type as u32, per_tree_set));
    }
    #[cfg(feature = "timing_logs")]
    println!(
        "=== Commitment for {} delegation circuits memory trees took {:?}",
        delegation_circuits_witness.len(),
        now.elapsed()
    );

    #[cfg(feature = "debug_logs")]
    println!("Will create FS transformation challenge for memory and delegation arguments");

    let setup_caps = DefaultTreeConstructor::dump_caps(&risc_v_circuit_precomputations.setup.trees);

    // commit memory challenges
    let memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
        &setup_caps,
        &final_register_values,
        &memory_trees,
        &delegation_memory_trees,
    );

    #[cfg(feature = "debug_logs")]
    println!(
        "FS transformation memory seed is {:?}",
        memory_challenges_seed
    );

    let external_challenges =
        ExternalChallenges::draw_from_transcript_seed(memory_challenges_seed, true);

    #[cfg(feature = "debug_logs")]
    println!("External challenges = {:?}", external_challenges);

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

    // now prove one by one
    let mut main_proofs = vec![];
    for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
        let shuffle_rams = if circuit_sequence < num_paddings {
            &padding_shuffle_ram_inits_and_teardowns
        } else {
            &inits_and_teardowns[circuit_sequence - num_paddings]
        };

        if should_dump_witness {
            bincode_serialize_to_file(
                shuffle_rams,
                &format!("riscv_shuffle_ram_inits_chunk_{}.bin", circuit_sequence),
            );
            bincode_serialize_to_file(
                witness_chunk,
                &format!("riscv_witness_chunk_{}.bin", circuit_sequence),
            );
        }

        let oracle = MainRiscVOracle {
            cycle_data: witness_chunk,
        };

        let now = std::time::Instant::now();
        let witness_trace = evaluate_witness(
            &risc_v_circuit_precomputations.compiled_circuit,
            risc_v_circuit_precomputations.witness_eval_fn_for_gpu_tracer,
            cycles_per_circuit,
            &oracle,
            &shuffle_rams.lazy_init_data,
            &risc_v_circuit_precomputations.table_driver,
            circuit_sequence,
            worker,
            A::default(),
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for main RISC-V circuit ({}) took {:?}",
            circuit_sequence,
            now.elapsed()
        );

        if PRECHECK_SATISFIED {
            println!("Will evaluate basic satisfiability checks for main circuit");

            assert!(check_satisfied(
                &risc_v_circuit_precomputations.compiled_circuit,
                &witness_trace.exec_trace,
                witness_trace.num_witness_columns
            ));
        }

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

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let (_, proof) = prove(
            &risc_v_circuit_precomputations.compiled_circuit,
            &public_inputs,
            &external_values,
            witness_trace,
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
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving for main RISC-V circuit ({}) took {:?}",
            circuit_sequence,
            now.elapsed()
        );

        // {
        //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
        // }

        memory_grand_product.mul_assign(&proof.memory_grand_product_accumulator);
        delegation_argument_sum.add_assign(&proof.delegation_argument_accumulator.unwrap());

        // assert_eq!(&proof.memory_tree_caps, &memory_trees[circuit_sequence]);

        aux_memory_trees.push(proof.memory_tree_caps.clone());

        main_proofs.push(proof);
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

        if els.is_empty() {
            continue;
        }

        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == *delegation_type as u32)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let mut per_tree_set = vec![];

        let mut per_delegation_type_proofs = vec![];
        for (_circuit_idx, el) in els.iter().enumerate() {
            delegation_proofs_count += 1;
            let oracle = DelegationCircuitOracle { cycle_data: el };

            if should_dump_witness {
                println!(
                    "Will serialize witness for delegaiton circuit {}",
                    delegation_type
                );
                bincode_serialize_to_file(
                    &oracle.cycle_data,
                    &format!(
                        "delegation_circuit_{}_{}_oracle_witness.bin",
                        delegation_type, _circuit_idx
                    ),
                );
                println!("Serialization is done");
            }

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let witness_trace = evaluate_witness(
                &prec.compiled_circuit.compiled_circuit,
                prec.witness_eval_fn_for_gpu_tracer,
                prec.compiled_circuit.num_requests_per_circuit,
                &oracle,
                &[],
                &prec.compiled_circuit.table_driver,
                0,
                worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for delegation circuit type {} took {:?}",
                delegation_type,
                now.elapsed()
            );

            if PRECHECK_SATISFIED {
                println!(
                    "Will evaluate basic satisfiability checks for delegation circuit {}",
                    delegation_type
                );

                assert!(check_satisfied(
                    &prec.compiled_circuit.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            // and prove
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values: AuxArgumentsBoundaryValues::default(),
            };

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            assert!(*delegation_type < 1 << 12);
            let (_, proof) = prove(
                &prec.compiled_circuit.compiled_circuit,
                &[],
                &external_values,
                witness_trace,
                &prec.setup,
                &prec.twiddles,
                &prec.lde_precomputations,
                0,
                Some(*delegation_type as u16),
                prec.lde_factor,
                prec.tree_cap_size,
                NUM_QUERIES,
                POW_BITS,
                worker,
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Proving for delegation circuit type {} took {:?}",
                delegation_type,
                now.elapsed()
            );

            memory_grand_product.mul_assign(&proof.memory_grand_product_accumulator);
            delegation_argument_sum.sub_assign(&proof.delegation_argument_accumulator.unwrap());

            per_tree_set.push(proof.memory_tree_caps.clone());

            per_delegation_type_proofs.push(proof);
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

    (main_proofs, delegation_proofs, final_register_values)
}

pub fn create_circuit_setup<A: GoodAllocator, B: GoodAllocator, const N: usize>(
    setup_row_major: &RowMajorTrace<Mersenne31Field, N, A>,
) -> Vec<Mersenne31Field, B> {
    #[cfg(feature = "gpu")]
    gpu::initialize_host_allocator_if_needed();

    let mut setup_evaluations =
        Vec::with_capacity_in(setup_row_major.as_slice().len(), B::default());
    unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
    transpose::transpose(
        setup_row_major.as_slice(),
        &mut setup_evaluations,
        setup_row_major.padded_width,
        setup_row_major.len(),
    );
    setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
    setup_evaluations
}

#[cfg(test)]
mod test {
    use super::*;
    use std::alloc::Global;
    use std::io::Read;

    #[test]
    fn test_prove_full_machine() {
        let num_instances = 1;

        let path = "./app.bin";
        let mut file = std::fs::File::open(path).expect("must open provided file");
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).expect("must read the file");
        let mut binary = vec![];
        for el in buffer.array_chunks::<4>() {
            binary.push(u32::from_le_bytes(*el));
        }
        setups::pad_bytecode_for_proving(&mut binary);

        // let num_instances = (cycles / risc_v_cycles::NUM_CYCLES) + 1;

        println!(
            "Will try proving now, with up to {} circuits.",
            num_instances
        );

        let worker = worker::Worker::new_with_num_threads(8);

        let delegation_precomputations =
            setups::all_delegation_circuits_precomputations::<Global, Global>(&worker);

        let non_determinism_source = QuasiUARTSource::default();
        let main_circuit_precomputations =
            setups::get_main_riscv_circuit_setup::<Global, Global>(&binary, &worker);
        let (_main_proofs, _delegation_proofs, _register_values) = crate::prove_image_execution(
            num_instances,
            &binary,
            non_determinism_source,
            &main_circuit_precomputations,
            &delegation_precomputations,
            &worker,
        );
    }
}
