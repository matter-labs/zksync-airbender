use crate::circuit_type::{CircuitType, DelegationCircuitType, UnrolledMemoryCircuitType};
use crate::circuit_type::{UnrolledCircuitType, UnrolledNonMemoryCircuitType};
use crate::prover::context::{ProverContext, ProverContextConfig};
use crate::prover::setup::SetupPrecomputations;
use crate::prover::trace_holder::TreesCacheMode;
use crate::prover::tracing_data::{
    DelegationTracingDataHost, DelegationTracingDataHostSource, InitsAndTeardownsTransfer,
    TracingDataHost, TracingDataTransfer, UnrolledTracingDataHost,
};
use cs::definitions::{
    split_timestamp, TimestampScalar, BLAKE2S_DELEGATION_CSR_REGISTER, INITIAL_TIMESTAMP,
    NUM_DELEGATION_ARGUMENT_KEY_PARTS, NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
    NUM_MEM_ARGUMENT_KEY_PARTS, REDUCED_MACHINE_CIRCUIT_FAMILY_IDX, TIMESTAMP_STEP,
};
use era_cudart::memory::{memory_copy, memory_copy_async};
use era_cudart::result::CudaResult;
use fft::{
    materialize_powers_serial_starting_with_elem, GoodAllocator, LdePrecomputations, Twiddles,
};
use itertools::Itertools;
use prover::definitions::{
    produce_pc_into_permutation_accumulator_raw, AuxArgumentsBoundaryValues, ExternalChallenges,
    ExternalDelegationArgumentChallenges, ExternalMachineStateArgumentChallenges,
    ExternalMemoryArgumentChallenges, ExternalValues, OPTIMAL_FOLDING_PROPERTIES,
};
use prover::merkle_trees::DefaultTreeConstructor;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use prover::risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::unrolled::{
    evaluate_init_and_teardown_witness, evaluate_memory_witness_for_unified_executor,
    evaluate_witness_for_unified_executor, MemoryCircuitOracle, NonMemoryCircuitOracle,
    UnifiedRiscvCircuitOracle,
};
use prover::{
    check_satisfied, get_aux_boundary_data, RamShuffleMemStateRecord,
    DEFAULT_TRACE_PADDING_MULTIPLE,
};
use prover::{
    common_constants, ExecutorFamilyWitnessEvaluationAuxData, WitnessEvaluationData,
    WitnessEvaluationDataForExecutionFamily,
};

use crate::allocator::tracker::AllocationPlacement;
use crate::circuit_type::CircuitType::Unrolled;
use crate::field::BaseField;
use crate::machine_type::MachineType;
use crate::prover::memory::commit_memory;
use crate::witness::trace_delegation::DelegationTraceHost;
use crate::witness::trace_unrolled::{
    get_aux_arguments_boundary_values, ShuffleRamInitsAndTeardownsHost, UnrolledMemoryTraceHost,
    UnrolledNonMemoryTraceHost, UnrolledUnifiedTraceHost,
};
use cs::cs::circuit::Circuit;
use cs::machine::ops::unrolled::{
    compile_unified_circuit_state_transition, materialize_flattened_decoder_table,
    process_binary_into_separate_tables_ext, ReducedMachineDecoder,
};
use cs::machine::NON_DETERMINISM_CSR;
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::tables::TableDriver;
use era_cudart::slice::DeviceSlice;
use field::{Field, Mersenne31Field, Mersenne31Quartic};
use prover::mem_utils::produce_register_contribution_into_memory_accumulator;
use prover::prover_stages::stage5::Query;
use prover::prover_stages::unrolled_prover::{
    prove_configured_for_unrolled_circuits, UnrolledModeProof,
};
use prover::prover_stages::Proof;
use prover::risc_v_simulator::machine_mode_only_unrolled::UnifiedOpcodeTracingDataWithTimestamp;
use prover::tracers::oracles::transpiler_oracles::delegation::DelegationOracle;
use riscv_transpiler::ir::{preprocess_bytecode, Instruction, ReducedMachineDecoderConfig};
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    DelegationsCounters, RamWithRomRegion, ReplayBuffer, SimpleSnapshotter, SimpleTape, State, VM,
};
use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::{DelegationAbiDescription, UnifiedDestinationHolder};
use setups::{
    read_binary, unified_reduced_machine_circuit_setup, DelegationCircuitPrecomputations,
};
use setups::{UnrolledCircuitPrecomputations, UnrolledCircuitWitnessEvalFn};
use std::alloc::Global;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::Arc;
use trace_and_split::{
    commit_memory_tree_for_delegation_circuit_with_replayer_format,
    commit_memory_tree_for_inits_and_teardowns_unrolled_circuit,
    commit_memory_tree_for_unrolled_mem_circuits, commit_memory_tree_for_unrolled_nonmem_circuits,
    fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits, FinalRegisterValue,
};
use trace_holder::RowMajorTrace;
use worker::Worker;

pub const NUM_QUERIES: usize = 53;
pub const POW_BITS: u32 = 28;
const RECOMPUTE_COSETS_FOR_CORRECTNESS: bool = true;
// const TREES_CACHE_MODE_FOR_CORRECTNESS: TreesCacheMode = TreesCacheMode::CacheNone;
// const RECOMPUTE_COSETS_FOR_BENCHMARKS: bool = false;
// const TREES_CACHE_MODE_FOR_BENCHMARKS: TreesCacheMode = TreesCacheMode::CacheFull;

pub fn init_logger() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("trace"))
        .target(env_logger::Target::Stdout)
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .init();
}

// #[test]
// fn test_prove_hashed_fibonacci() -> CudaResult<()> {
//     init_logger();
//     let instant = std::time::Instant::now();
//     ProverContext::initialize_global_host_allocator(4, 1 << 8, 22)?;
//     let mut prover_context_config = ProverContextConfig::default();
//     prover_context_config.device_allocation_block_log_size = 22;
//     let prover_context = ProverContext::new(&prover_context_config)?;
//     println!("prover_context created in {:?}", instant.elapsed());
//
//     let instant = std::time::Instant::now();
//
//     let worker = Worker::new();
//
//     let mut binary = vec![];
//     std::fs::File::open("../examples/hashed_fibonacci/app.bin")
//         .unwrap()
//         .read_to_end(&mut binary)
//         .unwrap();
//
//     let expected_final_pc = find_binary_exit_point(&binary);
//     println!(
//         "Expected final PC for base program is 0x{:08x}",
//         expected_final_pc
//     );
//
//     let binary = get_padded_binary(&binary);
//     let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 16, 1 << 14]);
//     let main_circuit_precomputations = setups::get_main_riscv_circuit_setup(&binary, &worker);
//     // let _end_params = compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
//     let delegation_precomputations = setups::all_delegation_circuits_precomputations(&worker);
//
//     println!("precomputations created in {:?}", instant.elapsed());
//
//     prove_image_execution_for_machine_with_gpu_tracers(
//         10,
//         &binary,
//         non_determinism_source,
//         &main_circuit_precomputations,
//         &delegation_precomputations,
//         &prover_context,
//         &worker,
//     )
// }
//
// #[test]
// fn test_prove_keccak_simple() -> CudaResult<()> {
//     init_logger();
//     let instant = std::time::Instant::now();
//     ProverContext::initialize_global_host_allocator(4, 1 << 8, 22)?;
//     let mut prover_context_config = ProverContextConfig::default();
//     prover_context_config.device_allocation_block_log_size = 22;
//     let prover_context = ProverContext::new(&prover_context_config)?;
//     println!("prover_context created in {:?}", instant.elapsed());
//
//     let instant = std::time::Instant::now();
//
//     let worker = Worker::new();
//
//     let mut binary = vec![];
//     std::fs::File::open("../prover/app_keccak_simple.bin")
//         .unwrap()
//         .read_to_end(&mut binary)
//         .unwrap();
//
//     let expected_final_pc = find_binary_exit_point(&binary);
//     println!(
//         "Expected final PC for base program is 0x{:08x}",
//         expected_final_pc
//     );
//
//     let binary = get_padded_binary(&binary);
//     let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 16, 1 << 14]);
//     let main_circuit_precomputations = setups::get_main_riscv_circuit_setup(&binary, &worker);
//     // let _end_params = compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
//     let delegation_precomputations = setups::all_delegation_circuits_precomputations(&worker);
//
//     println!("precomputations created in {:?}", instant.elapsed());
//
//     prove_image_execution_for_machine_with_gpu_tracers(
//         10,
//         &binary,
//         non_determinism_source,
//         &main_circuit_precomputations,
//         &delegation_precomputations,
//         &prover_context,
//         &worker,
//     )
// }
//
// #[test]
// fn bench_prove_hashed_fibonacci() -> CudaResult<()> {
//     init_logger();
//     let instant = std::time::Instant::now();
//     ProverContext::initialize_global_host_allocator(4, 1 << 8, 22)?;
//     println!("host allocator initialized in {:?}", instant.elapsed());
//     let instant = std::time::Instant::now();
//     let device_count = get_device_count()?;
//     println!("Found {} CUDA capable devices", device_count);
//     let mut contexts = vec![];
//     for device_id in 0..device_count {
//         set_device(device_id)?;
//         let props = get_device_properties(device_id)?;
//         let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
//         println!(
//             "Device {}: {} ({} SMs, {} GB memory)",
//             device_id,
//             name,
//             props.multiProcessorCount,
//             props.totalGlobalMem as f32 / 1024.0 / 1024.0 / 1024.0
//         );
//         let mut prover_context_config = ProverContextConfig::default();
//         prover_context_config.device_allocation_block_log_size = 22;
//         let prover_context = ProverContext::new(&prover_context_config)?;
//         contexts.push(prover_context);
//     }
//     println!("prover contexts created in {:?}", instant.elapsed());
//
//     let instant = std::time::Instant::now();
//
//     let worker = Worker::new();
//
//     let mut binary = vec![];
//     std::fs::File::open("../examples/hashed_fibonacci/app.bin")
//         .unwrap()
//         .read_to_end(&mut binary)
//         .unwrap();
//
//     let expected_final_pc = find_binary_exit_point(&binary);
//     println!(
//         "Expected final PC for base program is 0x{:08x}",
//         expected_final_pc
//     );
//
//     let binary = get_padded_binary(&binary);
//     let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 16, 0]);
//     let main_circuit_precomputations = setups::get_main_riscv_circuit_setup(&binary, &worker);
//
//     println!("precomputations created in {:?}", instant.elapsed());
//
//     bench_proof_main(
//         &binary,
//         non_determinism_source,
//         &main_circuit_precomputations,
//         &contexts,
//         &worker,
//     )
// }

// #[test]
// fn test_prove_unrolled_fibonacci() -> CudaResult<()> {
//     init_logger();
//     let instant = std::time::Instant::now();
//     ProverContext::initialize_global_host_allocator(4, 1 << 8, 22)?;
//     let mut prover_context_config = ProverContextConfig::default();
//     prover_context_config.allocator_block_log_size = 22;
//     let prover_context = ProverContext::new(&prover_context_config)?;
//     println!("prover_context created in {:?}", instant.elapsed());
//
//     let binary_image = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
//     let text_section = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
//
//     // setups::pad_bytecode_for_proving(&mut binary);
//
//     let worker = Worker::new();
//     println!("Performing precomputations for circuit families");
//     let families_precomps =
//         setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<
//             IMStandardIsaConfigWithUnsignedMulDiv,
//             _,
//             _,
//         >(&binary_image, &text_section, &worker);
//
//     println!("Performing precomputations for inits and teardowns");
//     let inits_and_teardowns_precomps = setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
//         &binary_image,
//         &text_section,
//         &worker,
//     );
//
//     println!("Performing precomputations for delegation circuits");
//     let delegation_precomputations = setups::all_delegation_circuits_precomputations(&worker);
//
//     let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 20, 1 << 16]);
//
//     prove_unrolled_execution::<
//         _,
//         IMStandardIsaConfigWithUnsignedMulDiv,
//         Global,
//         { common_constants::ROM_SECOND_WORD_BITS },
//     >(
//         1 << 30,
//         &binary_image,
//         &text_section,
//         non_determinism_source,
//         &families_precomps,
//         &inits_and_teardowns_precomps,
//         &delegation_precomputations,
//         1 << 32,
//         &prover_context,
//         &worker,
//     )
// }
//
// fn prove_image_execution_for_machine_with_gpu_tracers<
//     ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
// >(
//     num_instances_upper_bound: usize,
//     bytecode: &[u32],
//     non_determinism: ND,
//     risc_v_circuit_precomputations: &MainCircuitPrecomputations<
//         IMStandardIsaConfig,
//         Global,
//         ConcurrentStaticHostAllocator,
//     >,
//     delegation_circuits_precomputations: &[(
//         u32,
//         DelegationCircuitPrecomputations<Global, ConcurrentStaticHostAllocator>,
//     )],
//     prover_context: &ProverContext,
//     worker: &Worker,
// ) -> CudaResult<()> {
//     let cycles_per_circuit = MainCircuitType::RiscVCycles.get_num_cycles();
//     let trace_len = MainCircuitType::RiscVCycles.get_domain_size();
//     assert_eq!(cycles_per_circuit + 1, trace_len);
//     let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;
//
//     let (
//         main_circuits_witness,
//         inits_and_teardowns,
//         delegation_circuits_witness,
//         final_register_values,
//     ) = trace_execution_for_gpu::<ND, ConcurrentStaticHostAllocator>(
//         max_cycles_to_run,
//         bytecode,
//         non_determinism,
//         worker,
//     );
//
//     let (num_paddings, inits_and_teardowns) = inits_and_teardowns;
//
//     let mut memory_trees = vec![];
//     let padding_shuffle_ram_inits_and_teardowns = ShuffleRamSetupAndTeardown {
//         lazy_init_data: {
//             let len = risc_v_circuit_precomputations.compiled_circuit.trace_len - 1;
//             let mut data = Vec::with_capacity_in(len, ConcurrentStaticHostAllocator::default());
//             data.spare_capacity_mut()
//                 .fill(MaybeUninit::new(Default::default()));
//             unsafe { data.set_len(len) };
//             data
//         },
//     };
//
//     // commit memory trees
//     for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
//         let shuffle_rams = if circuit_sequence < num_paddings {
//             &padding_shuffle_ram_inits_and_teardowns
//         } else {
//             &inits_and_teardowns[circuit_sequence - num_paddings]
//         };
//
//         let (gpu_caps, _) = {
//             let lde_factor = MainCircuitType::RiscVCycles.get_lde_factor();
//             let log_lde_factor = lde_factor.trailing_zeros();
//             let log_domain_size = trace_len.trailing_zeros();
//             let log_tree_cap_size =
//                 OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
//             let inits_and_teardowns = if circuit_sequence < num_paddings {
//                 None
//             } else {
//                 Some(shuffle_rams.clone().into())
//             };
//             let trace = witness_chunk.clone().into();
//             let data = TracingDataHost::Main {
//                 inits_and_teardowns,
//                 trace,
//             };
//             let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
//             let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
//             transfer.schedule_transfer(prover_context)?;
//             let job = commit_memory(
//                 transfer,
//                 &risc_v_circuit_precomputations.compiled_circuit,
//                 None,
//                 0,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 prover_context,
//             )?;
//             job.finish()?
//         };
//
//         let (caps, _aux_data) = commit_memory_tree_for_riscv_circuit_using_gpu_tracer(
//             &risc_v_circuit_precomputations.compiled_circuit,
//             witness_chunk,
//             shuffle_rams,
//             circuit_sequence,
//             &risc_v_circuit_precomputations.twiddles,
//             &risc_v_circuit_precomputations.lde_precomputations,
//             worker,
//         );
//
//         gpu_caps
//             .iter()
//             .zip(caps.iter())
//             .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));
//
//         memory_trees.push(caps);
//     }
//
//     // same for delegation circuits
//     let mut delegation_memory_trees = vec![];
//
//     let mut delegation_types: Vec<_> = delegation_circuits_witness.keys().copied().collect();
//     delegation_types.sort();
//
//     for delegation_type in delegation_types.iter() {
//         let els = &delegation_circuits_witness[&delegation_type];
//         let idx = delegation_circuits_precomputations
//             .iter()
//             .position(|el| el.0 == *delegation_type as u32)
//             .unwrap();
//         let prec = &delegation_circuits_precomputations[idx].1;
//         let mut per_tree_set = vec![];
//         for el in els.iter() {
//             let (gpu_caps, _) = {
//                 let circuit = &prec.compiled_circuit.compiled_circuit;
//                 let trace_len = circuit.trace_len;
//                 let lde_factor = prec.lde_factor;
//                 let log_lde_factor = lde_factor.trailing_zeros();
//                 let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES
//                     [trace_len.trailing_zeros() as usize]
//                     .total_caps_size_log2 as u32;
//                 let trace = el.clone().into();
//                 let data = TracingDataHost::Delegation(trace);
//                 let circuit_type = CircuitType::from_delegation_type(*delegation_type);
//                 let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
//                 transfer.schedule_transfer(prover_context)?;
//                 let job = commit_memory(
//                     transfer,
//                     &circuit,
//                     None,
//                     0,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     prover_context,
//                 )?;
//                 job.finish()?
//             };
//
//             let (cpu_caps, delegation_t) =
//                 commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
//                     &prec.compiled_circuit.compiled_circuit,
//                     el,
//                     &prec.twiddles,
//                     &prec.lde_precomputations,
//                     prec.lde_factor,
//                     prec.tree_cap_size,
//                     worker,
//                 );
//
//             gpu_caps
//                 .iter()
//                 .zip(cpu_caps.iter())
//                 .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));
//
//             assert_eq!(*delegation_type as u32, delegation_t);
//             per_tree_set.push(cpu_caps);
//         }
//
//         delegation_memory_trees.push((*delegation_type as u32, per_tree_set));
//     }
//
//     let setup_caps = DefaultTreeConstructor::dump_caps(&risc_v_circuit_precomputations.setup.trees);
//
//     // commit memory challenges
//     let memory_challenges_seed = fs_transform_for_memory_and_delegation_arguments(
//         &setup_caps,
//         &final_register_values,
//         &memory_trees,
//         &delegation_memory_trees,
//     );
//
//     let external_challenges =
//         ExternalChallenges::draw_from_transcript_seed(memory_challenges_seed, true);
//
//     println!(
//         "Producing proofs for main RISC-V circuit, {} proofs in total",
//         main_circuits_witness.len()
//     );
//
//     let total_proving_start = std::time::Instant::now();
//
//     let gpu_circuit = Arc::new(risc_v_circuit_precomputations.compiled_circuit.clone());
//
//     // now prove one by one
//     for (circuit_sequence, witness_chunk) in main_circuits_witness.iter().enumerate() {
//         let shuffle_rams = if circuit_sequence < num_paddings {
//             &padding_shuffle_ram_inits_and_teardowns
//         } else {
//             &inits_and_teardowns[circuit_sequence - num_paddings]
//         };
//
//         let oracle = MainRiscVOracle {
//             cycle_data: witness_chunk,
//         };
//
//         let witness_trace = evaluate_witness(
//             &risc_v_circuit_precomputations.compiled_circuit,
//             risc_v_circuit_precomputations.witness_eval_fn_for_gpu_tracer,
//             cycles_per_circuit,
//             &oracle,
//             &shuffle_rams.lazy_init_data,
//             &risc_v_circuit_precomputations.table_driver,
//             circuit_sequence,
//             worker,
//             Global,
//         );
//
//         // and prove
//         let mut public_inputs = witness_trace.aux_data.first_row_public_inputs.clone();
//         public_inputs.extend_from_slice(&witness_trace.aux_data.one_before_last_row_public_inputs);
//         let aux_boundary_data = witness_trace.aux_data.aux_boundary_data[0];
//         let external_values = ExternalValues {
//             challenges: external_challenges,
//             aux_boundary_values: AuxArgumentsBoundaryValues {
//                 lazy_init_first_row: aux_boundary_data.lazy_init_first_row,
//                 teardown_value_first_row: aux_boundary_data.teardown_value_first_row,
//                 teardown_timestamp_first_row: aux_boundary_data.teardown_timestamp_first_row,
//                 lazy_init_one_before_last_row: aux_boundary_data.lazy_init_one_before_last_row,
//                 teardown_value_one_before_last_row: aux_boundary_data
//                     .teardown_value_one_before_last_row,
//                 teardown_timestamp_one_before_last_row: aux_boundary_data
//                     .teardown_timestamp_one_before_last_row,
//             },
//         };
//
//         let lde_factor = MainCircuitType::RiscVCycles.get_lde_factor();
//
//         let (_, cpu_proof) = prover::prover_stages::prove(
//             &risc_v_circuit_precomputations.compiled_circuit,
//             &public_inputs,
//             &external_values,
//             witness_trace.clone(),
//             &risc_v_circuit_precomputations.setup,
//             &risc_v_circuit_precomputations.twiddles,
//             &risc_v_circuit_precomputations.lde_precomputations,
//             circuit_sequence,
//             None,
//             lde_factor,
//             setups::risc_v_cycles::TREE_CAP_SIZE,
//             NUM_QUERIES,
//             POW_BITS,
//             worker,
//         );
//
//         let (gpu_proof, _) = {
//             let circuit = &risc_v_circuit_precomputations.compiled_circuit;
//             let log_lde_factor = lde_factor.trailing_zeros();
//             let log_domain_size = trace_len.trailing_zeros();
//             let log_tree_cap_size =
//                 OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
//             let setup_row_major = &risc_v_circuit_precomputations.setup.ldes[0].trace;
//             let mut setup_evaluations = Vec::with_capacity_in(
//                 setup_row_major.as_slice().len(),
//                 ConcurrentStaticHostAllocator::default(),
//             );
//             unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
//             transpose::transpose(
//                 setup_row_major.as_slice(),
//                 &mut setup_evaluations,
//                 setup_row_major.padded_width,
//                 setup_row_major.len(),
//             );
//             setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
//             let setup_evaluations = Arc::new(setup_evaluations);
//             let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
//                 circuit,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 setup_evaluations.clone(),
//                 prover_context,
//             )?;
//             let mut setup = SetupPrecomputations::new(
//                 circuit,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                 setup_trees_and_caps,
//                 prover_context,
//             )?;
//             setup.schedule_transfer(setup_evaluations, prover_context)?;
//             let (inits_and_teardowns, aux_boundary_values) = if circuit_sequence < num_paddings {
//                 (None, vec![AuxArgumentsBoundaryValues::default()])
//             } else {
//                 (
//                     Some(shuffle_rams.clone().into()),
//                     get_aux_arguments_boundary_values(
//                         circuit,
//                         cycles_per_circuit,
//                         &shuffle_rams.lazy_init_data,
//                     ),
//                 )
//             };
//             let trace = witness_chunk.clone().into();
//             let data = TracingDataHost::Main {
//                 inits_and_teardowns,
//                 trace,
//             };
//             let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
//             let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
//             transfer.schedule_transfer(prover_context)?;
//             let job = prove(
//                 circuit_type,
//                 gpu_circuit.clone(),
//                 external_challenges,
//                 aux_boundary_values,
//                 None,
//                 0,
//                 &mut setup,
//                 transfer,
//                 &risc_v_circuit_precomputations.lde_precomputations,
//                 circuit_sequence,
//                 None,
//                 lde_factor,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 Some(cpu_proof.pow_nonce),
//                 RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                 TREES_CACHE_MODE_FOR_CORRECTNESS,
//                 prover_context,
//             )?;
//             job.finish()?
//         };
//         let gpu_proof = gpu_proof.into_regular().unwrap();
//         compare_proofs(&cpu_proof, &gpu_proof);
//     }
//
//     if main_circuits_witness.len() > 0 {
//         println!(
//             "=== Total proving time: {:?} for {} circuits - avg: {:?}",
//             total_proving_start.elapsed(),
//             main_circuits_witness.len(),
//             total_proving_start.elapsed() / main_circuits_witness.len().try_into().unwrap()
//         )
//     }
//
//     // all the same for delegation circuit
//     let delegation_proving_start = std::time::Instant::now();
//     let mut delegation_proofs_count = 0u32;
//     // commit memory trees
//     for delegation_type in delegation_types.iter() {
//         let els = &delegation_circuits_witness[&delegation_type];
//         println!(
//             "Producing proofs for delegation circuit type {}, {} proofs in total",
//             delegation_type,
//             els.len()
//         );
//
//         let idx = delegation_circuits_precomputations
//             .iter()
//             .position(|el| el.0 == *delegation_type as u32)
//             .unwrap();
//         let prec = &delegation_circuits_precomputations[idx].1;
//
//         let gpu_circuit = Arc::new(prec.compiled_circuit.compiled_circuit.clone());
//
//         for (_circuit_idx, el) in els.iter().enumerate() {
//             delegation_proofs_count += 1;
//             let oracle = DelegationCircuitOracle { cycle_data: el };
//
//             let witness_trace = evaluate_witness(
//                 &prec.compiled_circuit.compiled_circuit,
//                 prec.witness_eval_fn_for_gpu_tracer,
//                 prec.compiled_circuit.num_requests_per_circuit,
//                 &oracle,
//                 &[],
//                 &prec.compiled_circuit.table_driver,
//                 0,
//                 worker,
//                 Global,
//             );
//
//             // and prove
//             let external_values = ExternalValues {
//                 challenges: external_challenges,
//                 aux_boundary_values: AuxArgumentsBoundaryValues::default(),
//             };
//
//             assert!(*delegation_type < 1 << 12);
//             let (_, cpu_proof) = prover::prover_stages::prove(
//                 &prec.compiled_circuit.compiled_circuit,
//                 &[],
//                 &external_values,
//                 witness_trace,
//                 &prec.setup,
//                 &prec.twiddles,
//                 &prec.lde_precomputations,
//                 0,
//                 Some(*delegation_type),
//                 prec.lde_factor,
//                 prec.tree_cap_size,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 worker,
//             );
//
//             let (gpu_proof, _) = {
//                 let lde_factor = prec.lde_factor;
//                 let log_lde_factor = lde_factor.trailing_zeros();
//                 let trace_len = gpu_circuit.trace_len;
//                 let log_domain_size = trace_len.trailing_zeros();
//                 let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
//                     .total_caps_size_log2 as u32;
//                 let setup_row_major = &prec.setup.ldes[0].trace;
//                 let mut setup_evaluations = Vec::with_capacity_in(
//                     setup_row_major.as_slice().len(),
//                     ConcurrentStaticHostAllocator::default(),
//                 );
//                 unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
//                 transpose::transpose(
//                     setup_row_major.as_slice(),
//                     &mut setup_evaluations,
//                     setup_row_major.padded_width,
//                     setup_row_major.len(),
//                 );
//                 setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
//                 let setup_evaluations = Arc::new(setup_evaluations);
//                 let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
//                     &gpu_circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     setup_evaluations.clone(),
//                     prover_context,
//                 )?;
//                 let mut setup = SetupPrecomputations::new(
//                     &gpu_circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                     setup_trees_and_caps,
//                     prover_context,
//                 )?;
//                 setup.schedule_transfer(setup_evaluations, prover_context)?;
//                 let trace = el.clone().into();
//                 let data = TracingDataHost::Delegation(trace);
//                 let circuit_type = CircuitType::from_delegation_type(*delegation_type);
//                 let mut transfer = TracingDataTransfer::new(circuit_type, data, prover_context)?;
//                 transfer.schedule_transfer(prover_context)?;
//                 let aux_boundary_values = vec![AuxArgumentsBoundaryValues::default()];
//                 let job = prove(
//                     circuit_type,
//                     gpu_circuit.clone(),
//                     external_challenges,
//                     aux_boundary_values,
//                     None,
//                     0,
//                     &mut setup,
//                     transfer,
//                     &prec.lde_precomputations,
//                     0,
//                     Some(*delegation_type),
//                     prec.lde_factor,
//                     NUM_QUERIES,
//                     POW_BITS,
//                     Some(cpu_proof.pow_nonce),
//                     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                     TREES_CACHE_MODE_FOR_CORRECTNESS,
//                     prover_context,
//                 )?;
//                 job.finish()?
//             };
//             let gpu_proof = gpu_proof.into_regular().unwrap();
//             compare_proofs(&cpu_proof, &gpu_proof);
//         }
//     }
//
//     if delegation_proofs_count > 0 {
//         println!(
//             "=== Total delegation proving time: {:?} for {} circuits - avg: {:?}",
//             delegation_proving_start.elapsed(),
//             delegation_proofs_count,
//             delegation_proving_start.elapsed() / delegation_proofs_count
//         )
//     }
//
//     Ok(())
// }
//
// fn bench_proof_main<ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>>(
//     bytecode: &[u32],
//     non_determinism: ND,
//     precomputations: &MainCircuitPrecomputations<
//         IMStandardIsaConfig,
//         Global,
//         ConcurrentStaticHostAllocator,
//     >,
//     contexts: &[ProverContext],
//     worker: &Worker,
// ) -> CudaResult<()> {
//     let cycles_per_circuit = MainCircuitType::RiscVCycles.get_num_cycles();
//     let trace_len = MainCircuitType::RiscVCycles.get_domain_size();
//     assert_eq!(cycles_per_circuit + 1, trace_len);
//     let max_cycles_to_run = cycles_per_circuit;
//
//     let (
//         main_circuits_witness,
//         _inits_and_teardowns,
//         _delegation_circuits_witness,
//         _final_register_values,
//     ) = trace_execution_for_gpu::<ND, ConcurrentStaticHostAllocator>(
//         max_cycles_to_run,
//         bytecode,
//         non_determinism,
//         worker,
//     );
//
//     let trace = main_circuits_witness.into_iter().nth(0).unwrap().into();
//     let data = TracingDataHost::Main {
//         inits_and_teardowns: None,
//         trace,
//     };
//     let lde_factor = MainCircuitType::RiscVCycles.get_lde_factor();
//     let circuit = &precomputations.compiled_circuit;
//     let gpu_circuit = Arc::new(circuit.clone());
//     let log_lde_factor = lde_factor.trailing_zeros();
//     let log_domain_size = trace_len.trailing_zeros();
//     let log_tree_cap_size =
//         OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
//     let setup_row_major = &precomputations.setup.ldes[0].trace;
//     let mut setup_evaluations = Vec::with_capacity_in(
//         setup_row_major.as_slice().len(),
//         ConcurrentStaticHostAllocator::default(),
//     );
//     unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
//     transpose::transpose(
//         setup_row_major.as_slice(),
//         &mut setup_evaluations,
//         setup_row_major.padded_width,
//         setup_row_major.len(),
//     );
//     setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
//     let setup_evaluations = Arc::new(setup_evaluations);
//     let mut setups = Vec::with_capacity(contexts.len());
//     for context in contexts.iter() {
//         context.switch_to_device()?;
//         let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
//             circuit,
//             log_lde_factor,
//             log_tree_cap_size,
//             setup_evaluations.clone(),
//             context,
//         )?;
//         let mut setup = SetupPrecomputations::new(
//             circuit,
//             log_lde_factor,
//             log_tree_cap_size,
//             RECOMPUTE_COSETS_FOR_BENCHMARKS,
//             setup_trees_and_caps,
//             context,
//         )?;
//         setup.schedule_transfer(setup_evaluations.clone(), context)?;
//         setups.push(setup);
//     }
//     let circuit_type = CircuitType::Main(MainCircuitType::RiscVCycles);
//     nvtx::range_push!("warmup");
//     {
//         let external_challenges = ExternalChallenges::draw_from_transcript_seed(Seed([0; 8]), true);
//         for (context, setup) in contexts.iter().zip(setups.iter_mut()) {
//             context.switch_to_device()?;
//             let mut transfer = TracingDataTransfer::new(circuit_type, data.clone(), context)?;
//             transfer.schedule_transfer(context)?;
//             let job = prove(
//                 circuit_type,
//                 gpu_circuit.clone(),
//                 external_challenges,
//                 vec![AuxArgumentsBoundaryValues::default()],
//                 None,
//                 0,
//                 setup,
//                 transfer,
//                 &precomputations.lde_precomputations,
//                 0,
//                 None,
//                 lde_factor,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 None,
//                 RECOMPUTE_COSETS_FOR_BENCHMARKS,
//                 TREES_CACHE_MODE_FOR_BENCHMARKS,
//                 context,
//             )?;
//             job.finish()?;
//         }
//     }
//     println!("warmup done");
//     nvtx::range_pop!();
//
//     let mut current_transfers = vec![];
//     let mut current_jobs = vec![];
//     let mut start_events = vec![];
//     let mut end_events = vec![];
//
//     for context in contexts.iter() {
//         context.switch_to_device()?;
//         let mut transfer = TracingDataTransfer::new(circuit_type, data.clone(), context)?;
//         transfer.schedule_transfer(context)?;
//         current_transfers.push(transfer);
//         current_jobs.push(None);
//         context.get_h2d_stream().synchronize()?;
//         context.get_exec_stream().synchronize()?;
//         start_events.push(CudaEvent::create()?);
//         end_events.push(CudaEvent::create()?);
//     }
//
//     const PROOF_COUNT: usize = 64;
//
//     nvtx::range_push!("bench");
//
//     for (context, event) in contexts.iter().zip(start_events.iter()) {
//         event.record(context.get_exec_stream())?;
//     }
//     for i in 0..PROOF_COUNT {
//         let external_challenges =
//             ExternalChallenges::draw_from_transcript_seed(Seed([i as u32; 8]), true);
//         for (((context, setup), current_transfer), current_job) in contexts
//             .iter()
//             .zip(setups.iter_mut())
//             .zip(current_transfers.iter_mut())
//             .zip(current_jobs.iter_mut())
//         {
//             context.switch_to_device()?;
//             let mut transfer = TracingDataTransfer::new(circuit_type, data.clone(), context)?;
//             transfer.schedule_transfer(context)?;
//             mem::swap(current_transfer, &mut transfer);
//             let job = prove(
//                 circuit_type,
//                 gpu_circuit.clone(),
//                 external_challenges,
//                 vec![AuxArgumentsBoundaryValues::default()],
//                 None,
//                 0,
//                 setup,
//                 transfer,
//                 &precomputations.lde_precomputations,
//                 0,
//                 None,
//                 lde_factor,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 None,
//                 RECOMPUTE_COSETS_FOR_BENCHMARKS,
//                 TREES_CACHE_MODE_FOR_BENCHMARKS,
//                 context,
//             )?;
//             let mut job = Some(job);
//             mem::swap(current_job, &mut job);
//             if let Some(job) = job {
//                 job.finish()?;
//             }
//         }
//     }
//     for (context, end_event) in contexts.iter().zip(end_events.iter_mut()) {
//         end_event.record(context.get_exec_stream())?;
//     }
//
//     for (end_event, current_job) in end_events.iter_mut().zip(current_jobs.iter_mut()) {
//         current_job.take().unwrap().finish()?;
//         end_event.synchronize()?;
//     }
//     nvtx::range_pop!();
//
//     let mut elapsed_times = vec![];
//     for (start_event, end_event) in start_events.iter().zip(end_events.iter()) {
//         elapsed_times.push(elapsed_time(start_event, end_event)?);
//     }
//
//     for (context, elapsed_time) in contexts.iter().zip(elapsed_times.iter()) {
//         let device_id = context.get_device_id();
//         println!("Device ID {device_id} elapsed time: {:.3} ms", elapsed_time);
//         let average = elapsed_time / PROOF_COUNT as f32;
//         println!(
//             "Device ID {device_id} average proof time: {:.3} ms",
//             average
//         );
//         let speed = (PROOF_COUNT * trace_len) as f32 / elapsed_time / 1_000.0;
//         println!(
//             "Device ID {device_id} average proof speed: {:.3} MHz",
//             speed
//         );
//     }
//
//     let elapsed_time = elapsed_times.iter().sum::<f32>() / contexts.len() as f32;
//     println!("Combined average elapsed time: {:.3} ms", elapsed_time);
//     let average = elapsed_time / PROOF_COUNT as f32;
//     println!("Combined average proof time: {:.3} ms", average);
//     let speed = (PROOF_COUNT * trace_len) as f32 / elapsed_time / 1_000.0;
//     println!("Combined average proof speed: {:.3} MHz", speed);
//     println!(
//         "Aggregate proof speed: {:.3} MHz",
//         speed * contexts.len() as f32
//     );
//     Ok(())
// }
//
// fn trace_execution_for_gpu<
//     ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
//     A: GoodAllocator,
// >(
//     num_instances_upper_bound: usize,
//     bytecode: &[u32],
//     mut non_determinism: ND,
//     worker: &Worker,
// ) -> (
//     Vec<CycleData<IMStandardIsaConfig, A>>,
//     (
//         usize, // number of empty ones to assume
//         Vec<ShuffleRamSetupAndTeardown<A>>,
//     ),
//     HashMap<u16, Vec<DelegationWitness<A>>>,
//     Vec<FinalRegisterValue>,
// ) {
//     let cycles_per_circuit = MainCircuitType::RiscVCycles.get_num_cycles();
//     let domain_size = MainCircuitType::RiscVCycles.get_domain_size();
//     assert_eq!(cycles_per_circuit + 1, domain_size);
//     assert!(domain_size.is_power_of_two());
//     let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;
//
//     let delegation_factories = setups::delegation_factories_for_machine::<IMStandardIsaConfig, A>();
//
//     let (
//         final_pc,
//         main_circuits_witness,
//         delegation_circuits_witness,
//         final_register_values,
//         init_and_teardown_chunks,
//     ) = run_and_split_for_gpu::<ND, IMStandardIsaConfig, A>(
//         max_cycles_to_run,
//         domain_size,
//         bytecode,
//         &mut non_determinism,
//         delegation_factories,
//         worker,
//     );
//
//     println!(
//         "Program finished execution with final pc = 0x{:08x} and final register state\n{}",
//         final_pc,
//         final_register_values
//             .iter()
//             .enumerate()
//             .map(|(idx, r)| format!("x{} = {}", idx, r.value))
//             .collect::<Vec<_>>()
//             .join(", ")
//     );
//
//     // we just need to chunk inits/teardowns
//
//     let init_and_teardown_chunks = chunk_lazy_init_and_teardown(
//         main_circuits_witness.len(),
//         cycles_per_circuit,
//         &init_and_teardown_chunks,
//         worker,
//     );
//
//     (
//         main_circuits_witness,
//         init_and_teardown_chunks,
//         delegation_circuits_witness,
//         final_register_values,
//     )
// }
//
// fn commit_memory_tree_for_riscv_circuit_using_gpu_tracer<C: MachineConfig>(
//     compiled_machine: &CompiledCircuitArtifact<Mersenne31Field>,
//     witness_chunk: &CycleData<C, impl GoodAllocator>,
//     inits_and_teardowns: &ShuffleRamSetupAndTeardown<impl GoodAllocator>,
//     _circuit_sequence: usize,
//     twiddles: &Twiddles<Mersenne31Complex, Global>,
//     lde_precomputations: &LdePrecomputations<Global>,
//     worker: &Worker,
// ) -> (Vec<MerkleTreeCapVarLength>, WitnessEvaluationAuxData) {
//     let lde_factor = MainCircuitType::RiscVCycles.get_lde_factor();
//
//     use setups::prover::prover_stages::stage1::compute_wide_ldes;
//     let trace_len = witness_chunk.num_cycles_chunk_size + 1;
//     assert!(trace_len.is_power_of_two());
//
//     let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];
//
//     let num_cycles_in_chunk = trace_len - 1;
//     let now = std::time::Instant::now();
//
//     let oracle = MainRiscVOracle {
//         cycle_data: witness_chunk,
//     };
//
//     let memory_chunk = evaluate_memory_witness(
//         compiled_machine,
//         num_cycles_in_chunk,
//         &oracle,
//         &inits_and_teardowns.lazy_init_data,
//         &worker,
//         Global,
//     );
//     println!(
//         "Materializing memory trace for {} cycles took {:?}",
//         num_cycles_in_chunk,
//         now.elapsed()
//     );
//
//     let MemoryOnlyWitnessEvaluationData {
//         aux_data,
//         memory_trace,
//     } = memory_chunk;
//     // now we should commit to it
//     let width = memory_trace.width();
//     let mut memory_trace = memory_trace;
//     adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);
//
//     let memory_ldes = compute_wide_ldes(
//         memory_trace,
//         twiddles,
//         lde_precomputations,
//         0,
//         lde_factor,
//         worker,
//     );
//     assert_eq!(memory_ldes.len(), lde_factor);
//
//     // now form a tree
//     let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
//     assert!(subtree_cap_size > 0);
//
//     let mut memory_subtrees = Vec::with_capacity(lde_factor);
//     let now = std::time::Instant::now();
//     for domain in memory_ldes.iter() {
//         let memory_tree = DefaultTreeConstructor::construct_for_coset(
//             &domain.trace,
//             subtree_cap_size,
//             true,
//             worker,
//         );
//         memory_subtrees.push(memory_tree);
//     }
//
//     let dump_fn = |caps: &[DefaultTreeConstructor]| {
//         let mut result = Vec::with_capacity(caps.len());
//         for el in caps.iter() {
//             result.push(el.get_cap());
//         }
//
//         result
//     };
//
//     let caps = dump_fn(&memory_subtrees);
//     println!("Memory witness commitment took {:?}", now.elapsed());
//
//     (caps, aux_data)
// }
//
// fn commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
//     compiled_machine: &CompiledCircuitArtifact<Mersenne31Field>,
//     witness_chunk: &DelegationWitness<impl GoodAllocator>,
//     twiddles: &Twiddles<Mersenne31Complex, Global>,
//     lde_precomputations: &LdePrecomputations<Global>,
//     lde_factor: usize,
//     _tree_cap_size: usize,
//     worker: &Worker,
// ) -> (Vec<MerkleTreeCapVarLength>, u32) {
//     use setups::prover::prover_stages::stage1::compute_wide_ldes;
//
//     let trace_len = witness_chunk.num_requests + 1;
//
//     assert!(trace_len.is_power_of_two());
//     let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];
//
//     let num_cycles_in_chunk = trace_len - 1;
//     let now = std::time::Instant::now();
//     let oracle = DelegationCircuitOracle {
//         cycle_data: witness_chunk,
//     };
//     let memory_chunk = evaluate_delegation_memory_witness(
//         compiled_machine,
//         num_cycles_in_chunk,
//         &oracle,
//         &worker,
//         Global,
//     );
//     println!(
//         "Materializing delegation type {} memory trace for {} cycles took {:?}",
//         witness_chunk.delegation_type,
//         num_cycles_in_chunk,
//         now.elapsed()
//     );
//
//     let DelegationMemoryOnlyWitnessEvaluationData { memory_trace } = memory_chunk;
//     // now we should commit to it
//     let width = memory_trace.width();
//     let mut memory_trace = memory_trace;
//     adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);
//
//     let memory_ldes = compute_wide_ldes(
//         memory_trace,
//         twiddles,
//         lde_precomputations,
//         0,
//         lde_factor,
//         worker,
//     );
//     assert_eq!(memory_ldes.len(), lde_factor);
//
//     // now form a tree
//     let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
//     assert!(subtree_cap_size > 0);
//
//     let mut memory_subtrees = Vec::with_capacity(lde_factor);
//     let now = std::time::Instant::now();
//     for domain in memory_ldes.iter() {
//         let memory_tree = DefaultTreeConstructor::construct_for_coset(
//             &domain.trace,
//             subtree_cap_size,
//             true,
//             worker,
//         );
//         memory_subtrees.push(memory_tree);
//     }
//
//     let dump_fn = |caps: &[DefaultTreeConstructor]| {
//         let mut result = Vec::with_capacity(caps.len());
//         for el in caps.iter() {
//             result.push(el.get_cap());
//         }
//
//         result
//     };
//
//     let caps = dump_fn(&memory_subtrees);
//     println!("Memory witness commitment took {:?}", now.elapsed());
//
//     (caps, witness_chunk.delegation_type as u32)
// }
//
// fn run_and_split_unrolled<
//     ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
//     C: MachineConfig,
//     A: GoodAllocator,
//     const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
// >(
//     cycles_bound: usize,
//     binary_image: &[u32],
//     _text_section: &[u32],
//     non_determinism: &mut ND,
//     non_mem_factories: HashMap<
//         u8,
//         Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>,
//     >,
//     mut mem_factories: HashMap<
//         u8,
//         Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>,
//     >,
//     delegation_factories: HashMap<
//         u16,
//         Box<dyn Fn() -> DelegationWitness<A> + Send + Sync + 'static>,
//     >,
//     ram_bound: usize,
//     worker: &Worker,
// ) -> (
//     u32,
//     TimestampScalar,
//     usize,
//     BTreeMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
//     (Vec<MemTracingFamilyChunk<A>>, Vec<MemTracingFamilyChunk<A>>),
//     BTreeMap<u16, Vec<DelegationWitness<A>>>,
//     [FinalRegisterValue; 32],
//     Vec<ShuffleRamSetupAndTeardown<A>>,
// ) {
//     let rom_address_space_bound: usize = 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS);
//     assert!(ram_bound > rom_address_space_bound);
//     let mut memory = VectorMemoryImplWithRom::new_for_byte_size(ram_bound, rom_address_space_bound);
//     for (idx, insn) in binary_image.iter().enumerate() {
//         memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
//     }
//
//     let csr_processor = DelegationsCSRProcessor;
//
//     let (
//         final_pc,
//         final_timestamp,
//         cycles_used,
//         family_circuits,
//         (word_mem_circuits, subword_mem_circuits),
//         delegation_circuits,
//         register_final_state,
//         shuffle_ram_touched_addresses,
//     ) = if setups::is_default_machine_configuration::<C>() {
//         let word_mem_factory = mem_factories
//             .remove(&common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
//             .expect("must exist");
//         let subword_mem_factory = mem_factories
//             .remove(&common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX)
//             .expect("must exist");
//         run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization::<
//             _,
//             IMStandardIsaConfigWithUnsignedMulDiv,
//             A,
//         >(
//             cycles_bound,
//             ENTRY_POINT,
//             csr_processor,
//             &mut memory,
//             rom_address_space_bound,
//             non_determinism,
//             non_mem_factories,
//             word_mem_factory,
//             subword_mem_factory,
//             delegation_factories,
//             ram_bound,
//             &worker,
//         )
//     } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
//         let word_mem_factory = mem_factories
//             .remove(&common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
//             .expect("must exist");
//         let subword_mem_factory = mem_factories
//             .remove(&common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX)
//             .expect("must exist");
//         run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization::<
//             _,
//             IMStandardIsaConfigWithUnsignedMulDiv,
//             A,
//         >(
//             cycles_bound,
//             ENTRY_POINT,
//             csr_processor,
//             &mut memory,
//             rom_address_space_bound,
//             non_determinism,
//             non_mem_factories,
//             word_mem_factory,
//             subword_mem_factory,
//             delegation_factories,
//             ram_bound,
//             &worker,
//         )
//     } else if setups::is_reduced_machine_configuration::<C>() {
//         let word_mem_factory = mem_factories
//             .remove(&common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
//             .expect("must exist");
//         let (_, subword_mem_factory) = setups::load_store_subword_only::get_tracer_factory(); // NOT used internally
//         run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization::<
//             _,
//             IWithoutByteAccessIsaConfigWithDelegation,
//             A,
//         >(
//             cycles_bound,
//             ENTRY_POINT,
//             csr_processor,
//             &mut memory,
//             rom_address_space_bound,
//             non_determinism,
//             non_mem_factories,
//             word_mem_factory,
//             subword_mem_factory,
//             delegation_factories,
//             ram_bound,
//             &worker,
//         )
//     } else {
//         panic!("Unknown configuration {:?}", std::any::type_name::<C>());
//     };
//
//     assert_eq!(
//         (cycles_used as u64) * TIMESTAMP_STEP + INITIAL_TIMESTAMP,
//         final_timestamp
//     );
//
//     let num_inits_per_circuit = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
//         * (setups::inits_and_teardowns::DOMAIN_SIZE - 1);
//
//     let total_input_len: usize = shuffle_ram_touched_addresses
//         .iter()
//         .map(|el| el.len())
//         .sum();
//     let num_needed_chunks =
//         total_input_len.next_multiple_of(num_inits_per_circuit) / num_inits_per_circuit;
//
//     let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<A, _>(
//         num_needed_chunks,
//         num_inits_per_circuit,
//         &shuffle_ram_touched_addresses,
//         &worker,
//     );
//     assert_eq!(num_trivial, 0);
//
//     (
//         final_pc,
//         final_timestamp,
//         cycles_used,
//         BTreeMap::from_iter(family_circuits.into_iter()),
//         (word_mem_circuits, subword_mem_circuits),
//         BTreeMap::from_iter(delegation_circuits.into_iter()),
//         register_final_state.map(|el| FinalRegisterValue {
//             value: el.current_value,
//             last_access_timestamp: el.last_access_timestamp,
//         }),
//         inits_and_teardowns,
//     )
// }
//
// fn trace_unrolled_execution<
//     ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
//     C: MachineConfig,
//     A: GoodAllocator,
//     const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
// >(
//     cycles_bound: usize,
//     binary_image: &[u32],
//     text_section: &[u32],
//     mut non_determinism: ND,
//     ram_bound: usize,
//     worker: &Worker,
// ) -> (
//     u32,
//     TimestampScalar,
//     usize,
//     BTreeMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
//     (Vec<MemTracingFamilyChunk<A>>, Vec<MemTracingFamilyChunk<A>>),
//     BTreeMap<u16, Vec<DelegationWitness<A>>>,
//     [FinalRegisterValue; 32],
//     Vec<ShuffleRamSetupAndTeardown<A>>,
// ) {
//     let (non_mem_factories, mem_factories) = if setups::is_default_machine_configuration::<C>() {
//         setups::factories_for_unrolled_circuits_base_layer::<A>()
//     } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
//         setups::factories_for_unrolled_circuits_base_layer_unsigned_only::<A>()
//     } else if setups::is_reduced_machine_configuration::<C>() {
//         setups::factories_for_unrolled_circuits_recursion_layer::<A>()
//     } else {
//         panic!("Unknown configuration {:?}", std::any::type_name::<C>());
//     };
//
//     let delegation_factories = setups::delegation_factories_for_machine::<C, A>();
//
//     let (
//         final_pc,
//         final_timestamp,
//         cycles_used,
//         family_circuits,
//         (word_mem_circuits, subword_mem_circuits),
//         delegation_circuits,
//         register_final_state,
//         inits_and_teardowns,
//     ) = run_and_split_unrolled::<ND, C, A, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
//         cycles_bound,
//         binary_image,
//         text_section,
//         &mut non_determinism,
//         non_mem_factories,
//         mem_factories,
//         delegation_factories,
//         ram_bound,
//         worker,
//     );
//
//     println!(
//         "Program finished execution with final pc = 0x{:08x} and final register state\n{}",
//         final_pc,
//         register_final_state
//             .iter()
//             .enumerate()
//             .map(|(idx, r)| format!("x{} = {}", idx, r.value))
//             .collect::<Vec<_>>()
//             .join(", ")
//     );
//
//     (
//         final_pc,
//         final_timestamp,
//         cycles_used,
//         family_circuits,
//         (word_mem_circuits, subword_mem_circuits),
//         delegation_circuits,
//         register_final_state,
//         inits_and_teardowns,
//     )
// }
//
// fn prove_unrolled_execution<
//     ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
//     C: MachineConfig,
//     A: GoodAllocator,
//     const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
// >(
//     cycles_bound: usize,
//     binary_image: &[u32],
//     text_section: &[u32],
//     non_determinism: ND,
//     unrolled_circuits_precomputations: &BTreeMap<u8, UnrolledCircuitPrecomputations<A, A>>,
//     inits_and_teardowns_precomputation: &UnrolledCircuitPrecomputations<A, A>,
//     delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A, A>)],
//     ram_bound: usize,
//     prover_context: &ProverContext,
//     worker: &Worker,
// ) -> CudaResult<()> {
//     let (
//         final_pc,
//         final_timestamp,
//         _cycles_used,
//         family_circuits,
//         (word_mem_circuits, subword_mem_circuits),
//         delegation_circuits,
//         register_final_state,
//         inits_and_teardowns,
//     ) = trace_unrolled_execution::<ND, C, A, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
//         cycles_bound,
//         binary_image,
//         text_section,
//         non_determinism,
//         ram_bound,
//         worker,
//     );
//
//     let mut memory_trees = vec![];
//
//     // commit memory trees
//     for (family_idx, witness_chunks) in family_circuits.iter() {
//         if witness_chunks.is_empty() {
//             continue;
//         }
//
//         let mut family_caps = vec![];
//         let precomputation = &unrolled_circuits_precomputations[family_idx];
//         let UnrolledCircuitWitnessEvalFn::NonMemory {
//             decoder_table,
//             default_pc_value_in_padding,
//             ..
//         } = precomputation
//             .witness_eval_fn_for_gpu_tracer
//             .as_ref()
//             .unwrap()
//         else {
//             unreachable!()
//         };
//
//         let h_decoder_table = decoder_table
//             .iter()
//             .copied()
//             .map(|d| d.into())
//             .collect_vec();
//         let mut d_decoder_table =
//             prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
//         memory_copy_async(
//             &mut d_decoder_table,
//             &h_decoder_table,
//             prover_context.get_exec_stream(),
//         )?;
//
//         let machine_type = MachineType::from_machine_config::<C>();
//         let circuit_type = UnrolledNonMemoryCircuitType::from_family_idx(*family_idx, machine_type);
//         let circuit_type = Unrolled(UnrolledCircuitType::NonMemory(circuit_type));
//
//         for chunk in witness_chunks.iter() {
//             let (gpu_caps, _) = {
//                 let lde_factor = precomputation.lde_factor;
//                 let log_lde_factor = lde_factor.trailing_zeros();
//                 let circuit = &precomputation.compiled_circuit;
//                 let trace_len = circuit.trace_len;
//                 let log_domain_size = trace_len.trailing_zeros();
//                 let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
//                     .total_caps_size_log2 as u32;
//                 let trace = UnrolledNonMemoryTraceHost {
//                     chunks: vec![Arc::new(chunk.data.clone())],
//                 };
//                 let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace));
//                 let mut transfer = TracingDataTransfer::new(data, prover_context)?;
//                 transfer.schedule_transfer(prover_context)?;
//                 let job = commit_memory(
//                     circuit_type,
//                     circuit,
//                     Some(&d_decoder_table),
//                     None,
//                     Some(transfer),
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     prover_context,
//                 )?;
//                 job.finish()?
//             };
//
//             let caps = commit_memory_tree_for_unrolled_nonmem_circuits(
//                 &precomputation.compiled_circuit,
//                 &chunk.data,
//                 &precomputation.twiddles,
//                 &precomputation.lde_precomputations,
//                 *default_pc_value_in_padding,
//                 decoder_table,
//                 worker,
//             );
//
//             gpu_caps
//                 .iter()
//                 .zip(caps.iter())
//                 .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));
//
//             dbg!(circuit_type, gpu_caps);
//
//             family_caps.push(caps);
//         }
//         memory_trees.push((*family_idx as u32, family_caps));
//     }
//
//     let mem_circuits = [
//         (
//             common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
//             word_mem_circuits,
//         ),
//         (
//             common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
//             subword_mem_circuits,
//         ),
//     ];
//     for (family_idx, witness_chunks) in mem_circuits.iter() {
//         if witness_chunks.is_empty() {
//             continue;
//         }
//
//         let mut family_caps = vec![];
//         let precomputation = &unrolled_circuits_precomputations[family_idx];
//         let UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. } = precomputation
//             .witness_eval_fn_for_gpu_tracer
//             .as_ref()
//             .unwrap()
//         else {
//             unreachable!()
//         };
//
//         let h_decoder_table = decoder_table
//             .iter()
//             .copied()
//             .map(|d| d.into())
//             .collect_vec();
//         let mut d_decoder_table =
//             prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
//         memory_copy_async(
//             &mut d_decoder_table,
//             &h_decoder_table,
//             prover_context.get_exec_stream(),
//         )?;
//
//         let machine_type = MachineType::from_machine_config::<C>();
//         let circuit_type = UnrolledMemoryCircuitType::from_family_idx(*family_idx, machine_type);
//         let circuit_type = Unrolled(UnrolledCircuitType::Memory(circuit_type));
//
//         for chunk in witness_chunks.iter() {
//             let (gpu_caps, _) = {
//                 let lde_factor = precomputation.lde_factor;
//                 let log_lde_factor = lde_factor.trailing_zeros();
//                 let circuit = &precomputation.compiled_circuit;
//                 let trace_len = circuit.trace_len;
//                 let log_domain_size = trace_len.trailing_zeros();
//                 let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
//                     .total_caps_size_log2 as u32;
//                 let trace = UnrolledMemoryTraceHost {
//                     chunks: vec![Arc::new(chunk.data.clone())],
//                 };
//                 let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace));
//                 let machine_type = MachineType::from_machine_config::<C>();
//                 let circuit_type =
//                     UnrolledMemoryCircuitType::from_family_idx(*family_idx, machine_type);
//                 let circuit_type = Unrolled(UnrolledCircuitType::Memory(circuit_type));
//                 let mut transfer = TracingDataTransfer::new(data, prover_context)?;
//                 transfer.schedule_transfer(prover_context)?;
//                 let job = commit_memory(
//                     circuit_type,
//                     circuit,
//                     Some(&d_decoder_table),
//                     None,
//                     Some(transfer),
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     prover_context,
//                 )?;
//                 job.finish()?
//             };
//
//             let caps = commit_memory_tree_for_unrolled_mem_circuits(
//                 &precomputation.compiled_circuit,
//                 &chunk.data,
//                 &precomputation.twiddles,
//                 &precomputation.lde_precomputations,
//                 decoder_table,
//                 worker,
//             );
//
//             gpu_caps
//                 .iter()
//                 .zip(caps.iter())
//                 .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));
//
//             dbg!(circuit_type, gpu_caps);
//
//             family_caps.push(caps);
//         }
//         memory_trees.push((*family_idx as u32, family_caps));
//     }
//
//     // and inits and teardowns
//     let mut inits_and_teardown_trees = vec![];
//     for witness_chunk in inits_and_teardowns.iter() {
//         let circuit_type = Unrolled(UnrolledCircuitType::InitsAndTeardowns);
//
//         let (gpu_caps, _) = {
//             let lde_factor = inits_and_teardowns_precomputation.lde_factor;
//             let log_lde_factor = lde_factor.trailing_zeros();
//             let circuit = &inits_and_teardowns_precomputation.compiled_circuit;
//             let trace_len = circuit.trace_len;
//             let log_domain_size = trace_len.trailing_zeros();
//             let log_tree_cap_size =
//                 OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
//             let inits_and_teardowns = ShuffleRamInitsAndTeardownsHost {
//                 chunks: vec![Arc::new(witness_chunk.lazy_init_data.clone())],
//             };
//             let mut transfer = InitsAndTeardownsTransfer::new(inits_and_teardowns, prover_context)?;
//             transfer.schedule_transfer(prover_context)?;
//             let job = commit_memory(
//                 circuit_type,
//                 circuit,
//                 None,
//                 Some(transfer),
//                 None,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 prover_context,
//             )?;
//             job.finish()?
//         };
//
//         let (caps, _) = commit_memory_tree_for_inits_and_teardowns_unrolled_circuit(
//             &inits_and_teardowns_precomputation.compiled_circuit,
//             &witness_chunk.lazy_init_data,
//             &inits_and_teardowns_precomputation.twiddles,
//             &inits_and_teardowns_precomputation.lde_precomputations,
//             worker,
//         );
//
//         gpu_caps
//             .iter()
//             .zip(caps.iter())
//             .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));
//
//         dbg!(circuit_type, gpu_caps);
//
//         inits_and_teardown_trees.push(caps);
//     }
//
//     // same for delegation circuits
//     let mut delegation_memory_trees = vec![];
//
//     for (delegation_type, els) in delegation_circuits.iter() {
//         if els.is_empty() {
//             continue;
//         }
//         let idx = delegation_circuits_precomputations
//             .iter()
//             .position(|el| el.0 == *delegation_type as u32)
//             .unwrap();
//         let prec = &delegation_circuits_precomputations[idx].1;
//         let mut per_tree_set = vec![];
//         for el in els.iter() {
//             let (caps, delegation_t) =
//                 trace_and_split::commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
//                     &prec.compiled_circuit.compiled_circuit,
//                     el,
//                     &prec.twiddles,
//                     &prec.lde_precomputations,
//                     prec.lde_factor,
//                     prec.tree_cap_size,
//                     worker,
//                 );
//             assert_eq!(*delegation_type as u32, delegation_t);
//             dbg!(DelegationCircuitType::from(*delegation_type), &caps);
//             per_tree_set.push(caps);
//         }
//
//         delegation_memory_trees.push((*delegation_type as u32, per_tree_set));
//     }
//
//     // commit memory challenges
//     let all_challenges_seed =
//         fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
//             &register_final_state,
//             final_pc,
//             final_timestamp,
//             &memory_trees,
//             &inits_and_teardown_trees,
//             &delegation_memory_trees,
//         );
//
//     let external_challenges =
//         ExternalChallenges::draw_from_transcript_seed_with_state_permutation(all_challenges_seed);
//
//     // now prove one by one
//     for (family_idx, witness_chunks) in family_circuits.into_iter() {
//         if witness_chunks.is_empty() {
//             continue;
//         }
//
//         let precomputation = &unrolled_circuits_precomputations[&family_idx];
//         let UnrolledCircuitWitnessEvalFn::NonMemory {
//             decoder_table,
//             default_pc_value_in_padding,
//             witness_fn,
//         } = precomputation
//             .witness_eval_fn_for_gpu_tracer
//             .as_ref()
//             .unwrap()
//         else {
//             unreachable!()
//         };
//
//         let h_decoder_table = decoder_table
//             .iter()
//             .copied()
//             .map(|d| d.into())
//             .collect_vec();
//         let mut d_decoder_table =
//             prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
//         memory_copy_async(
//             &mut d_decoder_table,
//             &h_decoder_table,
//             prover_context.get_exec_stream(),
//         )?;
//
//         for chunk in witness_chunks.into_iter() {
//             let oracle = NonMemoryCircuitOracle {
//                 inner: &chunk.data,
//                 decoder_table,
//                 default_pc_value_in_padding: *default_pc_value_in_padding,
//             };
//
//             let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
//                 &precomputation.compiled_circuit,
//                 *witness_fn,
//                 precomputation.trace_len - 1,
//                 &oracle,
//                 &precomputation.table_driver,
//                 &worker,
//                 A::default(),
//             );
//             let now = std::time::Instant::now();
//             let (_, cpu_proof) = prove_configured_for_unrolled_circuits::<
//                 DEFAULT_TRACE_PADDING_MULTIPLE,
//                 A,
//                 DefaultTreeConstructor,
//             >(
//                 &precomputation.compiled_circuit,
//                 &[],
//                 &external_challenges,
//                 witness_trace.clone(),
//                 &[],
//                 &precomputation.setup,
//                 &precomputation.twiddles,
//                 &precomputation.lde_precomputations,
//                 None,
//                 precomputation.lde_factor,
//                 precomputation.tree_cap_size,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 &worker,
//             );
//             println!(
//                 "Proving time for unrolled circuit type {} is {:?}",
//                 family_idx,
//                 now.elapsed()
//             );
//             {
//                 let circuit = Arc::new(precomputation.compiled_circuit.clone());
//                 let lde_factor = precomputation.lde_factor;
//                 let trace_len = circuit.trace_len;
//                 let log_lde_factor = lde_factor.trailing_zeros();
//                 let log_domain_size = trace_len.trailing_zeros();
//                 let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
//                     .total_caps_size_log2 as u32;
//                 let setup_row_major = &precomputation.setup.ldes[0].trace;
//                 let mut setup_evaluations = Vec::with_capacity_in(
//                     setup_row_major.as_slice().len(),
//                     ConcurrentStaticHostAllocator::default(),
//                 );
//                 unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
//                 transpose::transpose(
//                     setup_row_major.as_slice(),
//                     &mut setup_evaluations,
//                     setup_row_major.padded_width,
//                     setup_row_major.len(),
//                 );
//                 setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
//                 let setup_evaluations = Arc::new(setup_evaluations);
//                 let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
//                     &circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     setup_evaluations.clone(),
//                     prover_context,
//                 )?;
//                 let mut setup = SetupPrecomputations::new(
//                     &circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                     setup_trees_and_caps,
//                     prover_context,
//                 )?;
//                 setup.schedule_transfer(setup_evaluations, prover_context)?;
//                 let trace = UnrolledNonMemoryTraceHost {
//                     chunks: vec![Arc::new(chunk.data.clone())],
//                 };
//                 let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace));
//                 let machine_type = MachineType::from_machine_config::<C>();
//                 let circuit_type =
//                     UnrolledNonMemoryCircuitType::from_family_idx(family_idx, machine_type);
//                 let circuit_type = Unrolled(UnrolledCircuitType::NonMemory(circuit_type));
//                 let mut transfer = TracingDataTransfer::new(data, prover_context)?;
//                 transfer.schedule_transfer(prover_context)?;
//                 // let external_values = ExternalValues {
//                 //     challenges: external_challenges,
//                 //     aux_boundary_values: AuxArgumentsBoundaryValues::default(),
//                 // };
//                 // let job = crate::prover::proof::prove(
//                 //     Arc::new(circuit.clone()),
//                 //     external_values,
//                 //     Some(&d_decoder_table),
//                 //     *default_pc_value_in_padding,
//                 //     &mut setup,
//                 //     transfer,
//                 //     &precomputation.lde_precomputations,
//                 //     0,
//                 //     None,
//                 //     lde_factor,
//                 //     NUM_QUERIES,
//                 //     POW_BITS,
//                 //     Some(cpu_proof.pow_nonce),
//                 //     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                 //     TREES_CACHE_MODE_FOR_CORRECTNESS,
//                 //     prover_context,
//                 // )?;
//                 // job.finish()?
//                 let mut stage_1_output = StageOneOutput::allocate_trace_holders(
//                     &circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     false,
//                     TreesCacheMode::CacheFull,
//                     prover_context,
//                 )?;
//                 let mut callbacks = Callbacks::new();
//                 stage_1_output.generate_witness(
//                     circuit_type,
//                     &circuit,
//                     &mut setup,
//                     Some(&d_decoder_table),
//                     None,
//                     Some(transfer),
//                     &mut callbacks,
//                     prover_context,
//                 )?;
//                 stage_1_output.commit_witness(&circuit, &mut callbacks, prover_context)?;
//                 let stream = prover_context.get_exec_stream();
//                 stream.synchronize()?;
//                 drop(callbacks);
//                 // let num_witness_columns = witness_trace.num_witness_columns;
//                 // let mut d_witness = prover_context
//                 //     .alloc(trace_len * num_witness_columns, AllocationPlacement::Bottom)?;
//                 // let src = DeviceMatrix::new(
//                 //     stage_1_output
//                 //         .witness_holder
//                 //         .get_evaluations(prover_context)?,
//                 //     trace_len,
//                 // );
//                 // let mut dst = DeviceMatrixMut::new(&mut d_witness, num_witness_columns);
//                 // transpose(&src, &mut dst, stream)?;
//                 // let mut h_witness = vec![BaseField::ZERO; d_witness.len()];
//                 // memory_copy_async(&mut h_witness, &d_witness, stream)?;
//                 // stream.synchronize()?;
//                 // dbg!(&circuit.executor_family_circuit_next_timestamp_aux_var);
//                 // dbg!(&circuit.memory_queries_timestamp_comparison_aux_vars);
//                 // dbg!(&circuit.memory_layout);
//                 // dbg!(&circuit.witness_layout);
//                 // dbg!(circuit_type);
//                 // unsafe {
//                 //     for row in 0..trace_len - 1 {
//                 //         let index = row * num_witness_columns;
//                 //         let gpu_row = &h_witness[index..][..num_witness_columns];
//                 //         let cpu_row = &witness_trace.exec_trace.get_row(row)[..num_witness_columns];
//                 //         assert_eq!(gpu_row, cpu_row, "failed at row {}", row);
//                 //         // for col in 0..num_witness_columns {
//                 //         //     let index = index + col;
//                 //         //     assert_eq!(
//                 //         //         h_witness[index], trace[index],
//                 //         //         "failed at row {}, col {}",
//                 //         //         row, col
//                 //         //     );
//                 //         // }
//                 //     }
//                 // }
//                 let memory_tree_caps =
//                     get_tree_caps(&stage_1_output.memory_holder.get_tree_caps_accessors());
//                 let witness_tree_caps =
//                     get_tree_caps(&stage_1_output.witness_holder.get_tree_caps_accessors());
//                 assert_eq!(&cpu_proof.memory_tree_caps, &memory_tree_caps);
//                 assert_eq!(&cpu_proof.witness_tree_caps, &witness_tree_caps);
//             };
//         }
//     }
//
//     for (family_idx, witness_chunks) in mem_circuits.into_iter() {
//         if witness_chunks.is_empty() {
//             continue;
//         }
//
//         let precomputation = &unrolled_circuits_precomputations[&family_idx];
//         let UnrolledCircuitWitnessEvalFn::Memory {
//             decoder_table,
//             witness_fn,
//         } = precomputation
//             .witness_eval_fn_for_gpu_tracer
//             .as_ref()
//             .unwrap()
//         else {
//             unreachable!()
//         };
//
//         let h_decoder_table = decoder_table
//             .iter()
//             .copied()
//             .map(|d| d.into())
//             .collect_vec();
//         let mut d_decoder_table =
//             prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
//         memory_copy_async(
//             &mut d_decoder_table,
//             &h_decoder_table,
//             prover_context.get_exec_stream(),
//         )?;
//
//         for chunk in witness_chunks.into_iter() {
//             let oracle = MemoryCircuitOracle {
//                 inner: &chunk.data[..],
//                 decoder_table,
//             };
//
//             let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
//                 &precomputation.compiled_circuit,
//                 *witness_fn,
//                 precomputation.trace_len - 1,
//                 &oracle,
//                 &precomputation.table_driver,
//                 &worker,
//                 A::default(),
//             );
//             let now = std::time::Instant::now();
//             let (_, cpu_proof) = prove_configured_for_unrolled_circuits::<
//                 DEFAULT_TRACE_PADDING_MULTIPLE,
//                 A,
//                 DefaultTreeConstructor,
//             >(
//                 &precomputation.compiled_circuit,
//                 &[],
//                 &external_challenges,
//                 witness_trace.clone(),
//                 &[],
//                 &precomputation.setup,
//                 &precomputation.twiddles,
//                 &precomputation.lde_precomputations,
//                 None,
//                 precomputation.lde_factor,
//                 precomputation.tree_cap_size,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 &worker,
//             );
//             println!(
//                 "Proving time for unrolled circuit type {} is {:?}",
//                 family_idx,
//                 now.elapsed()
//             );
//             {
//                 let circuit = Arc::new(precomputation.compiled_circuit.clone());
//                 let lde_factor = precomputation.lde_factor;
//                 let trace_len = circuit.trace_len;
//                 let log_lde_factor = lde_factor.trailing_zeros();
//                 let log_domain_size = trace_len.trailing_zeros();
//                 let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
//                     .total_caps_size_log2 as u32;
//                 let setup_row_major = &precomputation.setup.ldes[0].trace;
//                 let mut setup_evaluations = Vec::with_capacity_in(
//                     setup_row_major.as_slice().len(),
//                     ConcurrentStaticHostAllocator::default(),
//                 );
//                 unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
//                 transpose::transpose(
//                     setup_row_major.as_slice(),
//                     &mut setup_evaluations,
//                     setup_row_major.padded_width,
//                     setup_row_major.len(),
//                 );
//                 setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
//                 let setup_evaluations = Arc::new(setup_evaluations);
//                 let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
//                     &circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     setup_evaluations.clone(),
//                     prover_context,
//                 )?;
//                 let mut setup = SetupPrecomputations::new(
//                     &circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                     setup_trees_and_caps,
//                     prover_context,
//                 )?;
//                 setup.schedule_transfer(setup_evaluations, prover_context)?;
//                 let trace = UnrolledMemoryTraceHost {
//                     chunks: vec![Arc::new(chunk.data.clone())],
//                 };
//                 let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace));
//                 let machine_type = MachineType::from_machine_config::<C>();
//                 let circuit_type =
//                     UnrolledMemoryCircuitType::from_family_idx(family_idx, machine_type);
//                 let circuit_type = Unrolled(UnrolledCircuitType::Memory(circuit_type));
//                 let mut transfer = TracingDataTransfer::new(data, prover_context)?;
//                 transfer.schedule_transfer(prover_context)?;
//                 // let external_values = ExternalValues {
//                 //     challenges: external_challenges,
//                 //     aux_boundary_values: AuxArgumentsBoundaryValues::default(),
//                 // };
//                 // let job = crate::prover::proof::prove(
//                 //     Arc::new(circuit.clone()),
//                 //     external_values,
//                 //     Some(&d_decoder_table),
//                 //     *default_pc_value_in_padding,
//                 //     &mut setup,
//                 //     transfer,
//                 //     &precomputation.lde_precomputations,
//                 //     0,
//                 //     None,
//                 //     lde_factor,
//                 //     NUM_QUERIES,
//                 //     POW_BITS,
//                 //     Some(cpu_proof.pow_nonce),
//                 //     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                 //     TREES_CACHE_MODE_FOR_CORRECTNESS,
//                 //     prover_context,
//                 // )?;
//                 // job.finish()?
//                 let mut stage_1_output = StageOneOutput::allocate_trace_holders(
//                     &circuit,
//                     log_lde_factor,
//                     log_tree_cap_size,
//                     false,
//                     TreesCacheMode::CacheFull,
//                     prover_context,
//                 )?;
//                 let mut callbacks = Callbacks::new();
//                 stage_1_output.generate_witness(
//                     circuit_type,
//                     &circuit,
//                     &mut setup,
//                     Some(&d_decoder_table),
//                     None,
//                     Some(transfer),
//                     &mut callbacks,
//                     prover_context,
//                 )?;
//                 stage_1_output.commit_witness(&circuit, &mut callbacks, prover_context)?;
//                 let stream = prover_context.get_exec_stream();
//                 stream.synchronize()?;
//                 drop(callbacks);
//                 // let num_witness_columns = witness_trace.num_witness_columns;
//                 // let mut d_witness = prover_context
//                 //     .alloc(trace_len * num_witness_columns, AllocationPlacement::Bottom)?;
//                 // let src = DeviceMatrix::new(
//                 //     stage_1_output
//                 //         .witness_holder
//                 //         .get_evaluations(prover_context)?,
//                 //     trace_len,
//                 // );
//                 // let mut dst = DeviceMatrixMut::new(&mut d_witness, num_witness_columns);
//                 // transpose(&src, &mut dst, stream)?;
//                 // let mut h_witness = vec![BaseField::ZERO; d_witness.len()];
//                 // memory_copy_async(&mut h_witness, &d_witness, stream)?;
//                 // stream.synchronize()?;
//                 // dbg!(&circuit.executor_family_circuit_next_timestamp_aux_var);
//                 // dbg!(&circuit.memory_queries_timestamp_comparison_aux_vars);
//                 // dbg!(&circuit.memory_layout);
//                 // dbg!(&circuit.witness_layout);
//                 // unsafe {
//                 //     for row in 0..trace_len - 1 {
//                 //         let index = row * num_witness_columns;
//                 //         let gpu_row = &h_witness[index..][..num_witness_columns];
//                 //         let cpu_row = &witness_trace.exec_trace.get_row(row)[..num_witness_columns];
//                 //         assert_eq!(gpu_row, cpu_row, "failed at row {}", row);
//                 //         // for col in 0..num_witness_columns {
//                 //         //     let index = index + col;
//                 //         //     assert_eq!(
//                 //         //         h_witness[index], trace[index],
//                 //         //         "failed at row {}, col {}",
//                 //         //         row, col
//                 //         //     );
//                 //         // }
//                 //     }
//                 // }
//                 let memory_tree_caps =
//                     get_tree_caps(&stage_1_output.memory_holder.get_tree_caps_accessors());
//                 let witness_tree_caps =
//                     get_tree_caps(&stage_1_output.witness_holder.get_tree_caps_accessors());
//                 assert_eq!(&cpu_proof.memory_tree_caps, &memory_tree_caps);
//                 assert_eq!(&cpu_proof.witness_tree_caps, &witness_tree_caps);
//             };
//         }
//     }
//
//     // inits and teardowns
//     for witness_chunk in inits_and_teardowns.into_iter() {
//         let witness_trace = evaluate_init_and_teardown_witness::<A>(
//             &inits_and_teardowns_precomputation.compiled_circuit,
//             inits_and_teardowns_precomputation.trace_len - 1,
//             &witness_chunk.lazy_init_data,
//             &worker,
//             A::default(),
//         );
//         let WitnessEvaluationData {
//             aux_data,
//             exec_trace,
//             num_witness_columns,
//             lookup_mapping,
//         } = witness_trace;
//         let witness_trace = WitnessEvaluationDataForExecutionFamily {
//             aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
//             exec_trace,
//             num_witness_columns,
//             lookup_mapping,
//         };
//
//         let (_, cpu_proof) = prove_configured_for_unrolled_circuits::<
//             DEFAULT_TRACE_PADDING_MULTIPLE,
//             A,
//             DefaultTreeConstructor,
//         >(
//             &inits_and_teardowns_precomputation.compiled_circuit,
//             &[],
//             &external_challenges,
//             witness_trace.clone(),
//             &aux_data.aux_boundary_data,
//             &inits_and_teardowns_precomputation.setup,
//             &inits_and_teardowns_precomputation.twiddles,
//             &inits_and_teardowns_precomputation.lde_precomputations,
//             None,
//             inits_and_teardowns_precomputation.lde_factor,
//             inits_and_teardowns_precomputation.tree_cap_size,
//             NUM_QUERIES,
//             POW_BITS,
//             &worker,
//         );
//
//         {
//             let circuit = Arc::new(inits_and_teardowns_precomputation.compiled_circuit.clone());
//             let lde_factor = inits_and_teardowns_precomputation.lde_factor;
//             let trace_len = circuit.trace_len;
//             let log_lde_factor = lde_factor.trailing_zeros();
//             let log_domain_size = trace_len.trailing_zeros();
//             let log_tree_cap_size =
//                 OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
//             let setup_row_major = &inits_and_teardowns_precomputation.setup.ldes[0].trace;
//             let mut setup_evaluations = Vec::with_capacity_in(
//                 setup_row_major.as_slice().len(),
//                 ConcurrentStaticHostAllocator::default(),
//             );
//             unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
//             transpose::transpose(
//                 setup_row_major.as_slice(),
//                 &mut setup_evaluations,
//                 setup_row_major.padded_width,
//                 setup_row_major.len(),
//             );
//             setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
//             let setup_evaluations = Arc::new(setup_evaluations);
//             let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
//                 &circuit,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 setup_evaluations.clone(),
//                 prover_context,
//             )?;
//             let mut setup = SetupPrecomputations::new(
//                 &circuit,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 RECOMPUTE_COSETS_FOR_CORRECTNESS,
//                 setup_trees_and_caps,
//                 prover_context,
//             )?;
//             setup.schedule_transfer(setup_evaluations, prover_context)?;
//             let inits_and_teardowns = ShuffleRamInitsAndTeardownsHost {
//                 chunks: vec![Arc::new(witness_chunk.lazy_init_data.clone())],
//             };
//             let circuit_type = Unrolled(UnrolledCircuitType::InitsAndTeardowns);
//             let mut transfer = InitsAndTeardownsTransfer::new(inits_and_teardowns, prover_context)?;
//             transfer.schedule_transfer(prover_context)?;
//             // let external_values = ExternalValues {
//             //     challenges: external_challenges,
//             //     aux_boundary_values: AuxArgumentsBoundaryValues::default(),
//             // };
//             // let job = crate::prover::proof::prove(
//             //     Arc::new(circuit.clone()),
//             //     external_values,
//             //     Some(&d_decoder_table),
//             //     *default_pc_value_in_padding,
//             //     &mut setup,
//             //     transfer,
//             //     &precomputation.lde_precomputations,
//             //     0,
//             //     None,
//             //     lde_factor,
//             //     NUM_QUERIES,
//             //     POW_BITS,
//             //     Some(cpu_proof.pow_nonce),
//             //     RECOMPUTE_COSETS_FOR_CORRECTNESS,
//             //     TREES_CACHE_MODE_FOR_CORRECTNESS,
//             //     prover_context,
//             // )?;
//             // job.finish()?
//             let mut stage_1_output = StageOneOutput::allocate_trace_holders(
//                 &circuit,
//                 log_lde_factor,
//                 log_tree_cap_size,
//                 false,
//                 TreesCacheMode::CacheFull,
//                 prover_context,
//             )?;
//             let mut callbacks = Callbacks::new();
//             stage_1_output.generate_witness(
//                 circuit_type,
//                 &circuit,
//                 &mut setup,
//                 None,
//                 Some(transfer),
//                 None,
//                 &mut callbacks,
//                 prover_context,
//             )?;
//             stage_1_output.commit_witness(&circuit, &mut callbacks, prover_context)?;
//             let stream = prover_context.get_exec_stream();
//             stream.synchronize()?;
//             drop(callbacks);
//             // let num_witness_columns = witness_trace.num_witness_columns;
//             // let mut d_witness = prover_context
//             //     .alloc(trace_len * num_witness_columns, AllocationPlacement::Bottom)?;
//             // let src = DeviceMatrix::new(
//             //     stage_1_output
//             //         .witness_holder
//             //         .get_evaluations(prover_context)?,
//             //     trace_len,
//             // );
//             // let mut dst = DeviceMatrixMut::new(&mut d_witness, num_witness_columns);
//             // transpose(&src, &mut dst, stream)?;
//             // let mut h_witness = vec![BaseField::ZERO; d_witness.len()];
//             // memory_copy_async(&mut h_witness, &d_witness, stream)?;
//             // stream.synchronize()?;
//             // unsafe {
//             //     for row in 0..trace_len - 1 {
//             //         let index = row * num_witness_columns;
//             //         let gpu_row = &h_witness[index..][..num_witness_columns];
//             //         let cpu_row = &witness_trace.exec_trace.get_row(row)[0..num_witness_columns];
//             //         assert_eq!(gpu_row, cpu_row, "failed at row {}", row);
//             //         // for col in 0..num_witness_columns {
//             //         //     let index = index + col;
//             //         //     assert_eq!(
//             //         //         h_witness[index], trace[index],
//             //         //         "failed at row {}, col {}",
//             //         //         row, col
//             //         //     );
//             //         // }
//             //     }
//             // }
//             let memory_tree_caps =
//                 get_tree_caps(&stage_1_output.memory_holder.get_tree_caps_accessors());
//             let witness_tree_caps =
//                 get_tree_caps(&stage_1_output.witness_holder.get_tree_caps_accessors());
//             assert_eq!(&cpu_proof.memory_tree_caps, &memory_tree_caps);
//             assert_eq!(&cpu_proof.witness_tree_caps, &witness_tree_caps);
//         };
//     }
//
//     // all the same for delegation circuit
//     let delegation_proving_start = std::time::Instant::now();
//     let mut delegation_proofs_count = 0u32;
//     // commit memory trees
//     for (delegation_type, els) in delegation_circuits.into_iter() {
//         if els.is_empty() {
//             continue;
//         }
//
//         println!(
//             "Producing proofs for delegation circuit type {}, {} proofs in total",
//             delegation_type,
//             els.len()
//         );
//
//         let idx = delegation_circuits_precomputations
//             .iter()
//             .position(|el| el.0 == delegation_type as u32)
//             .unwrap();
//         let prec = &delegation_circuits_precomputations[idx].1;
//
//         for (_circuit_idx, el) in els.iter().enumerate() {
//             delegation_proofs_count += 1;
//             let oracle: DelegationCircuitOracle<'_, A> =
//                 DelegationCircuitOracle::<A> { cycle_data: el };
//
//             let witness_trace = evaluate_witness::<DelegationCircuitOracle<'_, A>, A>(
//                 &prec.compiled_circuit.compiled_circuit,
//                 prec.witness_eval_fn_for_gpu_tracer,
//                 prec.compiled_circuit.num_requests_per_circuit,
//                 &oracle,
//                 &[],
//                 &prec.compiled_circuit.table_driver,
//                 0,
//                 worker,
//                 A::default(),
//             );
//
//             // and prove
//             let external_values = ExternalValues {
//                 challenges: external_challenges,
//                 aux_boundary_values: AuxArgumentsBoundaryValues::default(),
//             };
//
//             assert!(delegation_type < 1 << 12);
//             let (_, _proof) = prover::prover_stages::prove(
//                 &prec.compiled_circuit.compiled_circuit,
//                 &[],
//                 &external_values,
//                 witness_trace,
//                 &prec.setup,
//                 &prec.twiddles,
//                 &prec.lde_precomputations,
//                 0,
//                 Some(delegation_type),
//                 prec.lde_factor,
//                 prec.tree_cap_size,
//                 NUM_QUERIES,
//                 POW_BITS,
//                 worker,
//             );
//         }
//     }
//
//     if delegation_proofs_count > 0 {
//         println!(
//             "=== Total delegation proving time: {:?} for {} circuits - avg: {:?}",
//             delegation_proving_start.elapsed(),
//             delegation_proofs_count,
//             delegation_proving_start.elapsed() / delegation_proofs_count
//         )
//     }
//
//     Ok(())
// }

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

fn compare_proofs(left: &UnrolledModeProof, right: &UnrolledModeProof) {
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
        &left.permutation_grand_product_accumulator, &right.permutation_grand_product_accumulator,
        "permutation_grand_product_accumulator mismatch"
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
//
// fn find_binary_exit_point(binary: &[u8]) -> u32 {
//     assert_eq!(binary.len() % 4, 0);
//
//     let binary: Vec<u32> = binary
//         .as_chunks::<4>()
//         .0
//         .into_iter()
//         .map(|el| u32::from_le_bytes(*el))
//         .collect();
//
//     let mut candidates = vec![];
//
//     for (start_offset, window) in binary.windows(EXIT_SEQUENCE.len()).enumerate() {
//         if window == EXIT_SEQUENCE {
//             candidates.push(start_offset);
//         }
//     }
//
//     assert_eq!(candidates.len(), 1, "too many candidates for exit sequence");
//     let start = candidates[0];
//     let final_pc = (start + EXIT_SEQUENCE.len() - 1) * size_of::<u32>();
//
//     final_pc as u32
// }
//
// pub fn get_padded_binary(binary: &[u8]) -> Vec<u32> {
//     let mut bytecode = binary
//         .as_chunks::<4>()
//         .0
//         .into_iter()
//         .map(|el| u32::from_le_bytes(*el))
//         .collect();
//     pad_bytecode_for_proving(&mut bytecode);
//
//     bytecode
// }

#[test]
fn run_unrolled_reduced_test() -> CudaResult<()> {
    type CountersT = DelegationsCounters;

    const SECOND_WORD_BITS: usize = common_constants::ROM_SECOND_WORD_BITS;
    const CIRCUIT_TYPE: UnrolledCircuitType = UnrolledCircuitType::Unified;
    const NUM_CYCLES_PER_CHUNK: usize = CIRCUIT_TYPE.get_num_cycles();
    const TRACE_LEN_LOG2: usize = CIRCUIT_TYPE.get_domain_size().trailing_zeros() as usize;
    let trace_len: usize = CIRCUIT_TYPE.get_domain_size();
    let lde_factor = CIRCUIT_TYPE.get_lde_factor();
    let tree_cap_size = CIRCUIT_TYPE.get_tree_cap_size();

    let worker = Worker::new();
    let (_, mut binary_image) = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
    setups::pad_bytecode_for_proving(&mut binary_image);
    let (_, mut text_section) = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
    setups::pad_bytecode_for_proving(&mut text_section);

    let precomputations = unified_reduced_machine_circuit_setup::<Global, Global>(
        &binary_image,
        &text_section,
        &worker,
    );
    let circuit = &precomputations.compiled_circuit;

    // first run to capture minimal information
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<SECOND_WORD_BITS>::from_rom_content(&binary_image, 1 << 30);
    let period = 1 << 20;
    let num_snapshots = 1;
    let cycles_bound = period * num_snapshots;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::default();

    VM::<CountersT>::run_basic_unrolled::<
        SimpleSnapshotter<CountersT, SECOND_WORD_BITS>,
        RamWithRomRegion<SECOND_WORD_BITS>,
        _,
    >(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        period,
        &mut non_determinism,
    );

    let total_snapshots = snapshotter.snapshots.len();
    let cycles_upper_bound = total_snapshots * period;

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<Global, _>(
        1,
        NUM_CYCLES_PER_CHUNK,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    println!("Finished at PC = 0x{:08x}", state.pc);
    for (reg_idx, reg) in state.registers.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.value);
    }

    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
        last_access_timestamp: el.timestamp,
        current_value: el.value,
    });

    let (decoder_table_data, witness_gen_data) =
        process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
            &text_section,
            // &binary, // text_section,
            &[Box::new(ReducedMachineDecoder::new())],
            1 << 20,
            &[NON_DETERMINISM_CSR, BLAKE2S_DELEGATION_CSR_REGISTER as u16],
        )
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .unwrap();

    println!("Finished at PC = 0x{:08x}", final_pc);
    for (reg_idx, reg) in register_final_state.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.current_value);
    }

    let memory_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(2),
        Mersenne31Field(5),
        Mersenne31Field(42),
        Mersenne31Field(123),
    ]);
    let memory_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(11),
        Mersenne31Field(7),
        Mersenne31Field(1024),
        Mersenne31Field(8000),
    ]);

    let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let delegation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(5),
        Mersenne31Field(8),
        Mersenne31Field(32),
        Mersenne31Field(16),
    ]);
    let delegation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(200),
        Mersenne31Field(100),
        Mersenne31Field(300),
        Mersenne31Field(400),
    ]);

    let state_permutation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(41),
        Mersenne31Field(42),
        Mersenne31Field(43),
        Mersenne31Field(44),
    ]);
    let state_permutation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(80),
        Mersenne31Field(90),
        Mersenne31Field(100),
        Mersenne31Field(110),
    ]);

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let linearization_challenges: [Mersenne31Quartic; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            state_permutation_argument_alpha,
            NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
        )
        .try_into()
        .unwrap();

    let external_challenges = ExternalChallenges {
        memory_argument: ExternalMemoryArgumentChallenges {
            memory_argument_linearization_challenges:
                memory_argument_linearization_challenges_powers,
            memory_argument_gamma,
        },
        delegation_argument: Some(ExternalDelegationArgumentChallenges {
            delegation_argument_linearization_challenges,
            delegation_argument_gamma,
        }),
        machine_state_permutation_argument: Some(ExternalMachineStateArgumentChallenges {
            linearization_challenges,
            additive_term: state_permutation_argument_gamma,
        }),
    };

    let mut permutation_argument_accumulator = produce_pc_into_permutation_accumulator_raw(
        common_constants::INITIAL_PC,
        split_timestamp(INITIAL_TIMESTAMP),
        final_pc,
        split_timestamp(final_timestamp),
        &external_challenges
            .machine_state_permutation_argument
            .as_ref()
            .unwrap()
            .linearization_challenges,
        &external_challenges
            .machine_state_permutation_argument
            .as_ref()
            .unwrap()
            .additive_term,
    );
    let t = produce_register_contribution_into_memory_accumulator(
        &register_final_state,
        external_challenges
            .memory_argument
            .memory_argument_linearization_challenges,
        external_challenges.memory_argument.memory_argument_gamma,
    );
    permutation_argument_accumulator.mul_assign(&t);

    println!("Will try to prove ReducedMachine circuit");

    use cs::machine::ops::unrolled::reduced_machine_ops::*;

    let extra_tables = create_reduced_machine_special_tables::<_, SECOND_WORD_BITS>(
        &binary_image,
        &[
            common_constants::NON_DETERMINISM_CSR,
            BLAKE2S_DELEGATION_CSR_REGISTER,
        ],
    );
    let circuit = {
        compile_unified_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                reduced_machine_table_addition_fn(cs);
                for (table_type, table) in extra_tables.clone() {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| reduced_machine_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs),
            1 << 20,
            TRACE_LEN_LOG2,
        )
    };

    let mut table_driver = TableDriver::<Mersenne31Field>::new();
    reduced_machine_table_driver_fn(&mut table_driver);
    for (table_type, table) in extra_tables.clone() {
        table_driver.add_table_with_content(table_type, table);
    }

    let num_calls = exact_cycles_passed as usize;
    dbg!(num_calls);

    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
        ram_log: &mut ram_log_buffers,
    };
    let mut nd = QuasiUARTSource::new_with_reads(vec![]);
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
        &mut state,
        &mut ram,
        &tape,
        &mut nd,
        period,
        &mut tracer,
    );

    assert!(num_calls >= total_unique_teardowns);

    let (witness_eval_fn, decoder_table) = match precomputations
        .witness_eval_fn_for_gpu_tracer
        .as_ref()
        .unwrap()
    {
        UnrolledCircuitWitnessEvalFn::Unified {
            witness_fn,
            decoder_table,
        } => (witness_fn, decoder_table),
        _ => panic!("unexpected decoder table type"),
    };
    let decoder_table_data = materialize_flattened_decoder_table(&decoder_table_data);

    let oracle = UnifiedRiscvCircuitOracle {
        // prepadding: NUM_CYCLES_PER_CHUNK - num_calls,
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
    };

    let aux_boundary_data = get_aux_boundary_data(
        &circuit,
        NUM_CYCLES_PER_CHUNK,
        &inits_and_teardowns[0].lazy_init_data,
    );

    // println!(
    //     "Opcode = 0x{:08x}",
    //     family_data[0].data[29].opcode_data.opcode
    // );

    assert_eq!(
        inits_and_teardowns[0].lazy_init_data.len(),
        NUM_CYCLES_PER_CHUNK
    );

    println!("Evaluating memory witness");

    let memory_trace = evaluate_memory_witness_for_unified_executor::<_, Global>(
        &circuit,
        NUM_CYCLES_PER_CHUNK,
        &inits_and_teardowns[0].lazy_init_data,
        &oracle,
        &worker,
        Global,
    );

    init_logger();
    let instant = std::time::Instant::now();
    let prover_context_config = ProverContextConfig::default();
    let prover_context = ProverContext::new(&prover_context_config).unwrap();
    println!("prover_context created in {:?}", instant.elapsed());

    let h_decoder_table = decoder_table
        .iter()
        .copied()
        .map(|d| d.into())
        .collect_vec();
    let mut d_decoder_table =
        prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
    memory_copy_async(
        &mut d_decoder_table,
        &h_decoder_table,
        prover_context.get_exec_stream(),
    )?;

    // let (gpu_caps, _) = {
    //     let log_lde_factor = lde_factor.trailing_zeros();
    //     let trace_len = circuit.trace_len;
    //     let log_domain_size = trace_len.trailing_zeros();
    //     let log_tree_cap_size =
    //         OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
    //     let inits_and_teardowns = ShuffleRamInitsAndTeardownsHost {
    //         chunks: vec![Arc::new(inits_and_teardowns[0].lazy_init_data.clone())],
    //     };
    //     let mut inits_and_teardowns_transfer =
    //         InitsAndTeardownsTransfer::new(inits_and_teardowns, &prover_context)?;
    //     inits_and_teardowns_transfer.schedule_transfer(&prover_context)?;
    //     let trace = UnrolledUnifiedTraceHost {
    //         chunks: vec![Arc::new(buffer.clone())],
    //     };
    //     let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(trace));
    //     let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
    //     transfer.schedule_transfer(&prover_context)?;
    //     let job = commit_memory(
    //         Unrolled(CIRCUIT_TYPE),
    //         &circuit,
    //         Some(&d_decoder_table),
    //         Some(inits_and_teardowns_transfer),
    //         Some(transfer),
    //         log_lde_factor,
    //         log_tree_cap_size,
    //         &prover_context,
    //     )?;
    //     job.finish()?
    // };
    //
    // gpu_caps
    //     .iter()
    //     .zip(caps.iter())
    //     .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

    println!("Evaluating full witness");

    let full_trace = evaluate_witness_for_unified_executor::<_, Global>(
        &circuit,
        *witness_eval_fn,
        &inits_and_teardowns[0].lazy_init_data,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &table_driver,
        &worker,
        Global,
    );

    println!("Checking is satisfied");

    let is_satisfied = check_satisfied(
        &circuit,
        &full_trace.exec_trace,
        full_trace.num_witness_columns,
    );
    assert!(is_satisfied);

    println!("Precomputing");

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
    let setup =
        prover::prover_stages::SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

    // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
    //     Some(witness.lookup_mapping.clone())
    // } else {
    //     None
    // };

    println!("Trying to prove");

    let now = std::time::Instant::now();
    let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
        DEFAULT_TRACE_PADDING_MULTIPLE,
        _,
        DefaultTreeConstructor,
    >(
        &circuit,
        &vec![],
        &external_challenges,
        full_trace,
        &aux_boundary_data,
        &setup,
        &twiddles,
        &lde_precomputations,
        None,
        lde_factor,
        tree_cap_size,
        53,
        28,
        &worker,
    );
    println!("Proving time is {:?}", now.elapsed());

    let (gpu_proof, _) = {
        let log_lde_factor = lde_factor.trailing_zeros();
        let trace_len = circuit.trace_len;
        let log_domain_size = trace_len.trailing_zeros();
        let log_tree_cap_size =
            OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
        let setup_row_major = &setup.ldes[0].trace;
        let mut setup_evaluations = Vec::with_capacity(setup_row_major.as_slice().len());
        unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
        transpose::transpose(
            setup_row_major.as_slice(),
            &mut setup_evaluations,
            setup_row_major.padded_width,
            setup_row_major.len(),
        );
        setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
        let setup_evaluations = Arc::new(setup_evaluations);
        let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
            &circuit,
            log_lde_factor,
            log_tree_cap_size,
            setup_evaluations.clone(),
            &prover_context,
        )?;
        let mut setup = SetupPrecomputations::new(
            &circuit,
            log_lde_factor,
            log_tree_cap_size,
            false,
            setup_trees_and_caps,
            &prover_context,
        )?;
        setup.schedule_transfer(setup_evaluations, &prover_context)?;
        let inits_and_teardowns = ShuffleRamInitsAndTeardownsHost {
            chunks: vec![Arc::new(inits_and_teardowns[0].lazy_init_data.clone())],
        };
        let mut inits_and_teardowns_transfer =
            InitsAndTeardownsTransfer::new(inits_and_teardowns, &prover_context)?;
        inits_and_teardowns_transfer.schedule_transfer(&prover_context)?;
        let trace = UnrolledUnifiedTraceHost {
            chunks: vec![Arc::new(buffer.clone())],
        };
        let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(trace));
        let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
        transfer.schedule_transfer(&prover_context)?;
        let job = crate::prover::proof::prove(
            Unrolled(CIRCUIT_TYPE),
            Arc::new(circuit.clone()),
            external_challenges.clone(),
            aux_boundary_data,
            &mut setup,
            Some(&d_decoder_table),
            Some(inits_and_teardowns_transfer),
            Some(transfer),
            &lde_precomputations,
            None,
            lde_factor,
            53,
            28,
            Some(proof.pow_nonce),
            true,
            TreesCacheMode::CacheNone,
            &prover_context,
        )?;
        job.finish()?
    };
    compare_proofs(&proof, &gpu_proof);

    assert_eq!(
        proof.delegation_argument_accumulator.unwrap(),
        Mersenne31Quartic::ZERO
    );
    permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);

    assert_eq!(permutation_argument_accumulator, Mersenne31Quartic::ONE);
    Ok(())
}

#[test]
fn test_prove_unrolled_hashed_fibonacci() {
    let (_, mut binary_image) = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
    setups::pad_bytecode_for_proving(&mut binary_image);
    let (_, mut text_section) = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
    setups::pad_bytecode_for_proving(&mut text_section);

    let worker = Worker::new();

    let cycles_bound = 1 << 24;
    let rom_bound = 1 << 32;
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![1, 1]);

    let _ = prove_unrolled_with_replayer_for_machine_configuration::<
        IMStandardIsaConfigWithUnsignedMulDiv,
    >(
        &binary_image,
        &text_section,
        cycles_bound,
        non_determinism_source,
        rom_bound,
        &worker,
    );
}

pub fn prove_unrolled_with_replayer_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &Worker,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<UnrolledModeProof>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
) {
    println!("Performing precomputations for circuit families");
    let families_precomps =
        setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<C, Global, Global>(
            binary_image,
            &text_section,
            &worker,
        );

    println!("Performing precomputations for inits and teardowns");
    let inits_and_teardowns_precomps = setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
        &binary_image,
        &text_section,
        worker,
    );

    println!("Performing precomputations for delegation circuits");
    let delegation_precomputations = setups::all_delegation_circuits_precomputations(worker);

    let (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    ) = prove_unrolled_execution_with_replayer::<
        C,
        Global,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(
        cycles_bound,
        &binary_image,
        &text_section,
        non_determinism,
        &families_precomps,
        &inits_and_teardowns_precomps,
        &delegation_precomputations,
        ram_bound,
        worker,
    )
    .unwrap();

    (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    )
}

pub fn prove_unrolled_execution_with_replayer<
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    mut non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    unrolled_circuits_precomputations: &BTreeMap<u8, UnrolledCircuitPrecomputations<A, A>>,
    inits_and_teardowns_precomputation: &UnrolledCircuitPrecomputations<A, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A, A>)],
    ram_bound: usize,
    worker: &Worker,
) -> CudaResult<(
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<UnrolledModeProof>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
)> {
    use prover::unrolled::run_unrolled_machine;

    init_logger();
    let instant = std::time::Instant::now();
    let mut prover_context_config = ProverContextConfig::default();
    prover_context_config.allocator_block_log_size = 22;
    let prover_context = ProverContext::new(&prover_context_config)?;
    println!("prover_context created in {:?}", instant.elapsed());

    const DEFAULT_SNAPSHOT_PERIOD: usize = 1 << 20;
    let max_snapshots = cycles_bound.div_ceil(DEFAULT_SNAPSHOT_PERIOD);

    let family_chunk_sizes = HashMap::from_iter(
        [
            (
                setups::add_sub_lui_auipc_mop::FAMILY_IDX,
                setups::add_sub_lui_auipc_mop::NUM_CYCLES,
            ),
            (
                setups::jump_branch_slt::FAMILY_IDX,
                setups::jump_branch_slt::NUM_CYCLES,
            ),
            (
                setups::shift_binary_csr::FAMILY_IDX,
                setups::shift_binary_csr::NUM_CYCLES,
            ),
            (
                setups::mul_div_unsigned::FAMILY_IDX,
                setups::mul_div_unsigned::NUM_CYCLES,
            ),
            (
                setups::load_store_word_only::FAMILY_IDX,
                setups::load_store_word_only::NUM_CYCLES,
            ),
            (
                setups::load_store_subword_only::FAMILY_IDX,
                setups::load_store_subword_only::NUM_CYCLES,
            ),
        ]
        .into_iter(),
    );

    let delegation_chunk_sizes = HashMap::from_iter(
        [
            (
                setups::blake2_with_compression::DELEGATION_TYPE_ID as u16,
                setups::blake2_with_compression::NUM_DELEGATION_CYCLES,
            ),
            (
                setups::bigint_with_control::DELEGATION_TYPE_ID as u16,
                setups::bigint_with_control::NUM_DELEGATION_CYCLES,
            ),
            (
                setups::keccak_special5::DELEGATION_TYPE_ID as u16,
                setups::keccak_special5::NUM_DELEGATION_CYCLES,
            ),
        ]
        .into_iter(),
    );

    let (
        final_pc,
        final_timestamp,
        cycles_used,
        non_mem_circuits,
        mem_circuits,
        (blake_circuits, bigint_circuits, keccak_circuits),
        register_final_state,
        shuffle_ram_touched_addresses,
    ) = run_unrolled_machine::<C, A, ROM_BOUND_SECOND_WORD_BITS>(
        common_constants::INITIAL_PC,
        text_section,
        binary_image,
        cycles_bound,
        ram_bound,
        &mut non_determinism,
        family_chunk_sizes,
        delegation_chunk_sizes,
        worker,
    );

    let mut memory_trees = vec![];

    // order by family index
    let non_mem_circuits = BTreeMap::from_iter(non_mem_circuits.into_iter());
    let mem_circuits = BTreeMap::from_iter(mem_circuits.into_iter());

    for (k, v) in non_mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }
    for (k, v) in mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }

    // restructure inits/teardowns
    let num_inits_per_circuit = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
        * (setups::inits_and_teardowns::DOMAIN_SIZE - 1);

    let total_input_len: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();
    let num_needed_chunks =
        total_input_len.next_multiple_of(num_inits_per_circuit) / num_inits_per_circuit;

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<A, _>(
        num_needed_chunks,
        num_inits_per_circuit,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0);

    let register_final_state = register_final_state.map(|el| FinalRegisterValue {
        value: el.current_value,
        last_access_timestamp: el.last_access_timestamp,
    });

    let machine_type = MachineType::from_machine_config::<C>();

    // commit memory trees
    for (family_idx, witness_chunks) in non_mem_circuits.iter().sorted_by_key(|(&id, _)| id) {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let precomputation = &unrolled_circuits_precomputations[family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            ..
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        let circuit_type = Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::from_family_idx(*family_idx, machine_type),
        ));
        let h_decoder_table = decoder_table
            .iter()
            .copied()
            .map(|d| d.into())
            .collect_vec();
        let mut d_decoder_table =
            prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
        memory_copy_async(
            &mut d_decoder_table,
            &h_decoder_table,
            prover_context.get_exec_stream(),
        )?;

        for chunk in witness_chunks.iter() {
            let (gpu_caps, _) = {
                let lde_factor = precomputation.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let circuit = &precomputation.compiled_circuit;
                let trace_len = circuit.trace_len;
                let log_domain_size = trace_len.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                    .total_caps_size_log2 as u32;
                let trace = UnrolledNonMemoryTraceHost {
                    chunks: vec![Arc::new(chunk.data.clone())],
                };
                let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace));
                let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                transfer.schedule_transfer(&prover_context)?;
                let job = commit_memory(
                    circuit_type,
                    circuit,
                    Some(&d_decoder_table),
                    None,
                    Some(transfer),
                    log_lde_factor,
                    log_tree_cap_size,
                    &prover_context,
                )?;
                job.finish()?
            };

            let caps = commit_memory_tree_for_unrolled_nonmem_circuits(
                &precomputation.compiled_circuit,
                &chunk.data,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                *default_pc_value_in_padding,
                decoder_table,
                worker,
            );

            gpu_caps
                .iter()
                .zip(caps.iter())
                .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

            family_caps.push(caps);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    for (family_idx, witness_chunks) in mem_circuits.iter().sorted_by_key(|(&id, _)| id) {
        if witness_chunks.is_empty() {
            continue;
        }

        let machine_type = MachineType::from_machine_config::<C>();
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::from_family_idx(*family_idx, machine_type),
        ));
        let mut family_caps = vec![];
        let precomputation = &unrolled_circuits_precomputations[family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        let circuit_type = Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::from_family_idx(*family_idx, machine_type),
        ));
        let h_decoder_table = decoder_table
            .iter()
            .copied()
            .map(|d| d.into())
            .collect_vec();
        let mut d_decoder_table =
            prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
        memory_copy_async(
            &mut d_decoder_table,
            &h_decoder_table,
            prover_context.get_exec_stream(),
        )?;

        for chunk in witness_chunks.iter() {
            let (gpu_caps, _) = {
                let lde_factor = precomputation.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let circuit = &precomputation.compiled_circuit;
                let trace_len = circuit.trace_len;
                let log_domain_size = trace_len.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                    .total_caps_size_log2 as u32;
                let trace = UnrolledMemoryTraceHost {
                    chunks: vec![Arc::new(chunk.data.clone())],
                };
                let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace));
                let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                transfer.schedule_transfer(&prover_context)?;
                let job = commit_memory(
                    circuit_type,
                    circuit,
                    Some(&d_decoder_table),
                    None,
                    Some(transfer),
                    log_lde_factor,
                    log_tree_cap_size,
                    &prover_context,
                )?;
                job.finish()?
            };

            let caps = commit_memory_tree_for_unrolled_mem_circuits(
                &precomputation.compiled_circuit,
                &chunk.data,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                decoder_table,
                worker,
            );

            gpu_caps
                .iter()
                .zip(caps.iter())
                .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

            family_caps.push(caps);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    // and inits and teardowns
    let mut inits_and_teardown_trees = vec![];

    {
        let circuit_type = Unrolled(UnrolledCircuitType::InitsAndTeardowns);

        for witness_chunk in inits_and_teardowns.iter() {
            let (caps, aux_data) = commit_memory_tree_for_inits_and_teardowns_unrolled_circuit(
                &inits_and_teardowns_precomputation.compiled_circuit,
                &witness_chunk.lazy_init_data,
                &inits_and_teardowns_precomputation.twiddles,
                &inits_and_teardowns_precomputation.lde_precomputations,
                worker,
            );

            let (gpu_caps, _) = {
                let lde_factor = inits_and_teardowns_precomputation.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let circuit = &inits_and_teardowns_precomputation.compiled_circuit;
                let trace_len = circuit.trace_len;
                let log_domain_size = trace_len.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                    .total_caps_size_log2 as u32;
                let trace = ShuffleRamInitsAndTeardownsHost {
                    chunks: vec![Arc::new(witness_chunk.lazy_init_data.clone())],
                };
                let mut transfer = InitsAndTeardownsTransfer::new(trace, &prover_context)?;
                transfer.schedule_transfer(&prover_context)?;
                let job = commit_memory(
                    circuit_type,
                    circuit,
                    None,
                    Some(transfer),
                    None,
                    log_lde_factor,
                    log_tree_cap_size,
                    &prover_context,
                )?;
                job.finish()?
            };

            gpu_caps
                .iter()
                .zip(caps.iter())
                .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

            inits_and_teardown_trees.push(caps);
        }
    }

    // same for delegation circuits
    let mut delegation_memory_trees = vec![];
    {
        let circuit_type = CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression);
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = setups::blake2_with_compression::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_circuits;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit_with_replayer_format::<
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    prec.trace_len - 1,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );

                let (gpu_caps, _) = {
                    let lde_factor = inits_and_teardowns_precomputation.lde_factor;
                    let log_lde_factor = lde_factor.trailing_zeros();
                    let circuit = &prec.compiled_circuit.compiled_circuit;
                    let trace_len = circuit.trace_len;
                    let log_domain_size = trace_len.trailing_zeros();
                    let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                        .total_caps_size_log2 as u32;
                    let trace = DelegationTraceHost {
                        chunks: vec![Arc::new(el.clone())],
                    };
                    let data = TracingDataHost::Delegation(
                        DelegationTracingDataHost::Blake2WithCompression(trace),
                    );
                    let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                    transfer.schedule_transfer(&prover_context)?;
                    let job = commit_memory(
                        circuit_type,
                        circuit,
                        None,
                        None,
                        Some(transfer),
                        log_lde_factor,
                        log_tree_cap_size,
                        &prover_context,
                    )?;
                    job.finish()?
                };

                gpu_caps
                    .iter()
                    .zip(caps.iter())
                    .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

                per_tree_set.push(caps);
            }

            delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        }
    }
    {
        let circuit_type = CircuitType::Delegation(DelegationCircuitType::BigIntWithControl);
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = setups::bigint_with_control::DELEGATION_TYPE_ID;
        let delegation_circuits = &bigint_circuits;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit_with_replayer_format::<
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    prec.trace_len - 1,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );

                let (gpu_caps, _) = {
                    let lde_factor = inits_and_teardowns_precomputation.lde_factor;
                    let log_lde_factor = lde_factor.trailing_zeros();
                    let circuit = &prec.compiled_circuit.compiled_circuit;
                    let trace_len = circuit.trace_len;
                    let log_domain_size = trace_len.trailing_zeros();
                    let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                        .total_caps_size_log2 as u32;
                    let trace = DelegationTraceHost {
                        chunks: vec![Arc::new(el.clone())],
                    };
                    let data = TracingDataHost::Delegation(
                        DelegationTracingDataHost::BigIntWithControl(trace),
                    );
                    let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                    transfer.schedule_transfer(&prover_context)?;
                    let job = commit_memory(
                        circuit_type,
                        circuit,
                        None,
                        None,
                        Some(transfer),
                        log_lde_factor,
                        log_tree_cap_size,
                        &prover_context,
                    )?;
                    job.finish()?
                };

                gpu_caps
                    .iter()
                    .zip(caps.iter())
                    .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

                per_tree_set.push(caps);
            }

            delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        }
    }
    {
        let circuit_type = CircuitType::Delegation(DelegationCircuitType::BigIntWithControl);
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = setups::keccak_special5::DELEGATION_TYPE_ID;
        let delegation_circuits = &keccak_circuits;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit_with_replayer_format::<
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    prec.trace_len - 1,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );

                let (gpu_caps, _) = {
                    let lde_factor = inits_and_teardowns_precomputation.lde_factor;
                    let log_lde_factor = lde_factor.trailing_zeros();
                    let circuit = &prec.compiled_circuit.compiled_circuit;
                    let trace_len = circuit.trace_len;
                    let log_domain_size = trace_len.trailing_zeros();
                    let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                        .total_caps_size_log2 as u32;
                    let trace = DelegationTraceHost {
                        chunks: vec![Arc::new(el.clone())],
                    };
                    let data = TracingDataHost::Delegation(
                        DelegationTracingDataHost::KeccakSpecial5(trace),
                    );
                    let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                    transfer.schedule_transfer(&prover_context)?;
                    let job = commit_memory(
                        circuit_type,
                        circuit,
                        None,
                        None,
                        Some(transfer),
                        log_lde_factor,
                        log_tree_cap_size,
                        &prover_context,
                    )?;
                    job.finish()?
                };

                gpu_caps
                    .iter()
                    .zip(caps.iter())
                    .for_each(|(gpu_cap, cpu_cap)| assert_eq!(gpu_cap, cpu_cap));

                per_tree_set.push(caps);
            }

            delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        }
    }

    // commit memory challenges
    let all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &memory_trees,
            &inits_and_teardown_trees,
            &delegation_memory_trees,
        );

    let external_challenges =
        ExternalChallenges::draw_from_transcript_seed_with_state_permutation(all_challenges_seed);

    let mut aux_memory_trees = vec![];

    // now prove one by one
    let mut main_proofs = BTreeMap::new();
    for (family_idx, witness_chunks) in non_mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);
            continue;
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        let circuit_type = Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::from_family_idx(family_idx, machine_type),
        ));
        let h_decoder_table = decoder_table
            .iter()
            .copied()
            .map(|d| d.into())
            .collect_vec();
        let mut d_decoder_table =
            prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
        memory_copy_async(
            &mut d_decoder_table,
            &h_decoder_table,
            prover_context.get_exec_stream(),
        )?;

        for chunk in witness_chunks.into_iter() {
            let oracle = NonMemoryCircuitOracle {
                inner: &chunk.data,
                decoder_table,
                default_pc_value_in_padding: *default_pc_value_in_padding,
            };

            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );

            let now = std::time::Instant::now();
            let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
                DEFAULT_TRACE_PADDING_MULTIPLE,
                A,
                DefaultTreeConstructor,
            >(
                &precomputation.compiled_circuit,
                &[],
                &external_challenges,
                witness_trace,
                &[],
                &precomputation.setup,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                None,
                precomputation.lde_factor,
                precomputation.tree_cap_size,
                NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                &worker,
            );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            let (gpu_proof, _) = {
                let lde_factor = precomputation.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let circuit = Arc::new(precomputation.compiled_circuit.clone());
                let trace_len = circuit.trace_len;
                let log_domain_size = trace_len.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                    .total_caps_size_log2 as u32;
                let setup_row_major = &precomputation.setup.ldes[0].trace;
                let mut setup_evaluations = Vec::with_capacity(setup_row_major.as_slice().len());
                unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
                transpose::transpose(
                    setup_row_major.as_slice(),
                    &mut setup_evaluations,
                    setup_row_major.padded_width,
                    setup_row_major.len(),
                );
                setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
                let setup_evaluations = Arc::new(setup_evaluations);
                let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
                    &circuit,
                    log_lde_factor,
                    log_tree_cap_size,
                    setup_evaluations.clone(),
                    &prover_context,
                )?;
                let mut setup = SetupPrecomputations::new(
                    &circuit,
                    log_lde_factor,
                    log_tree_cap_size,
                    false,
                    setup_trees_and_caps,
                    &prover_context,
                )?;
                setup.schedule_transfer(setup_evaluations, &prover_context)?;
                let trace = UnrolledNonMemoryTraceHost {
                    chunks: vec![Arc::new(chunk.data.clone())],
                };
                let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace));
                let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                transfer.schedule_transfer(&prover_context)?;
                let job = crate::prover::proof::prove(
                    circuit_type,
                    circuit,
                    external_challenges.clone(),
                    vec![],
                    &mut setup,
                    Some(&d_decoder_table),
                    None,
                    Some(transfer),
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    NUM_QUERIES,
                    verifier_common::POW_BITS as u32,
                    Some(proof.pow_nonce),
                    true,
                    TreesCacheMode::CacheNone,
                    &prover_context,
                )?;
                job.finish()?
            };
            compare_proofs(&proof, &gpu_proof);

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    for (family_idx, witness_chunks) in mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);
            continue;
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory {
            decoder_table,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        let circuit_type = Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::from_family_idx(family_idx, machine_type),
        ));
        let h_decoder_table = decoder_table
            .iter()
            .copied()
            .map(|d| d.into())
            .collect_vec();
        let mut d_decoder_table =
            prover_context.alloc(decoder_table.len(), AllocationPlacement::Bottom)?;
        memory_copy_async(
            &mut d_decoder_table,
            &h_decoder_table,
            prover_context.get_exec_stream(),
        )?;

        for chunk in witness_chunks.into_iter() {
            let oracle = MemoryCircuitOracle {
                inner: &chunk.data[..],
                decoder_table,
            };

            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            let now = std::time::Instant::now();
            let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
                DEFAULT_TRACE_PADDING_MULTIPLE,
                A,
                DefaultTreeConstructor,
            >(
                &precomputation.compiled_circuit,
                &[],
                &external_challenges,
                witness_trace,
                &[],
                &precomputation.setup,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                None,
                precomputation.lde_factor,
                precomputation.tree_cap_size,
                NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                &worker,
            );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            let (gpu_proof, _) = {
                let lde_factor = precomputation.lde_factor;
                let log_lde_factor = lde_factor.trailing_zeros();
                let circuit = Arc::new(precomputation.compiled_circuit.clone());
                let trace_len = circuit.trace_len;
                let log_domain_size = trace_len.trailing_zeros();
                let log_tree_cap_size = OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize]
                    .total_caps_size_log2 as u32;
                let setup_row_major = &precomputation.setup.ldes[0].trace;
                let mut setup_evaluations = Vec::with_capacity(setup_row_major.as_slice().len());
                unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
                transpose::transpose(
                    setup_row_major.as_slice(),
                    &mut setup_evaluations,
                    setup_row_major.padded_width,
                    setup_row_major.len(),
                );
                setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
                let setup_evaluations = Arc::new(setup_evaluations);
                let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
                    &circuit,
                    log_lde_factor,
                    log_tree_cap_size,
                    setup_evaluations.clone(),
                    &prover_context,
                )?;
                let mut setup = SetupPrecomputations::new(
                    &circuit,
                    log_lde_factor,
                    log_tree_cap_size,
                    false,
                    setup_trees_and_caps,
                    &prover_context,
                )?;
                setup.schedule_transfer(setup_evaluations, &prover_context)?;
                let trace = UnrolledMemoryTraceHost {
                    chunks: vec![Arc::new(chunk.data.clone())],
                };
                let data = TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace));
                let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
                transfer.schedule_transfer(&prover_context)?;
                let job = crate::prover::proof::prove(
                    circuit_type,
                    circuit,
                    external_challenges.clone(),
                    vec![],
                    &mut setup,
                    Some(&d_decoder_table),
                    None,
                    Some(transfer),
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    NUM_QUERIES,
                    verifier_common::POW_BITS as u32,
                    Some(proof.pow_nonce),
                    true,
                    TreesCacheMode::CacheNone,
                    &prover_context,
                )?;
                job.finish()?
            };
            compare_proofs(&proof, &gpu_proof);

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    // inits and teardowns
    let mut aux_inits_and_teardown_trees = vec![];
    let mut inits_and_teardowns_proofs = vec![];
    for witness_chunk in inits_and_teardowns.into_iter() {
        let witness_trace = evaluate_init_and_teardown_witness::<A>(
            &inits_and_teardowns_precomputation.compiled_circuit,
            inits_and_teardowns_precomputation.trace_len - 1,
            &witness_chunk.lazy_init_data,
            &worker,
            A::default(),
        );

        let WitnessEvaluationData {
            aux_data,
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        } = witness_trace;
        let witness_trace = WitnessEvaluationDataForExecutionFamily {
            aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        };

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            A,
            DefaultTreeConstructor,
        >(
            &inits_and_teardowns_precomputation.compiled_circuit,
            &[],
            &external_challenges,
            witness_trace,
            &aux_data.aux_boundary_data,
            &inits_and_teardowns_precomputation.setup,
            &inits_and_teardowns_precomputation.twiddles,
            &inits_and_teardowns_precomputation.lde_precomputations,
            None,
            inits_and_teardowns_precomputation.lde_factor,
            inits_and_teardowns_precomputation.tree_cap_size,
            NUM_QUERIES,
            verifier_common::POW_BITS as u32,
            &worker,
        );
        println!(
            "Proving time for inits and teardown circuit is {:?}",
            now.elapsed()
        );

        let (gpu_proof, _) = {
            let lde_factor = inits_and_teardowns_precomputation.lde_factor;
            let log_lde_factor = lde_factor.trailing_zeros();
            let circuit = Arc::new(inits_and_teardowns_precomputation.compiled_circuit.clone());
            let trace_len = circuit.trace_len;
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
            let setup_row_major = &inits_and_teardowns_precomputation.setup.ldes[0].trace;
            let mut setup_evaluations = Vec::with_capacity(setup_row_major.as_slice().len());
            unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
            transpose::transpose(
                setup_row_major.as_slice(),
                &mut setup_evaluations,
                setup_row_major.padded_width,
                setup_row_major.len(),
            );
            setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
            let setup_evaluations = Arc::new(setup_evaluations);
            let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
                &circuit,
                log_lde_factor,
                log_tree_cap_size,
                setup_evaluations.clone(),
                &prover_context,
            )?;
            let mut setup = SetupPrecomputations::new(
                &circuit,
                log_lde_factor,
                log_tree_cap_size,
                false,
                setup_trees_and_caps,
                &prover_context,
            )?;
            setup.schedule_transfer(setup_evaluations, &prover_context)?;
            let trace = ShuffleRamInitsAndTeardownsHost {
                chunks: vec![Arc::new(witness_chunk.lazy_init_data.clone())],
            };
            let aux_boundary_data = get_aux_arguments_boundary_values(&circuit, &trace);
            assert_eq!(&aux_data.aux_boundary_data, &aux_boundary_data);
            let mut transfer = InitsAndTeardownsTransfer::new(trace, &prover_context)?;
            transfer.schedule_transfer(&prover_context)?;
            let job = crate::prover::proof::prove(
                Unrolled(UnrolledCircuitType::InitsAndTeardowns),
                circuit,
                external_challenges.clone(),
                aux_boundary_data,
                &mut setup,
                None,
                Some(transfer),
                None,
                &inits_and_teardowns_precomputation.lde_precomputations,
                None,
                inits_and_teardowns_precomputation.lde_factor,
                NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                Some(proof.pow_nonce),
                true,
                TreesCacheMode::CacheNone,
                &prover_context,
            )?;
            job.finish()?
        };
        compare_proofs(&proof, &gpu_proof);

        aux_inits_and_teardown_trees.push(proof.memory_tree_caps.clone());
        inits_and_teardowns_proofs.push(proof);
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = setups::blake2_with_compression::DELEGATION_TYPE_ID;
        let delegation_circuits = blake_circuits;
        let witness_eval_fn = setups::blake2_with_compression::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                worker,
                &prover_context,
            )?;

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = setups::bigint_with_control::DELEGATION_TYPE_ID;
        let delegation_circuits = bigint_circuits;
        let witness_eval_fn = setups::bigint_with_control::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                worker,
                &prover_context,
            )?;

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = setups::keccak_special5::DELEGATION_TYPE_ID;
        let delegation_circuits = keccak_circuits;
        let witness_eval_fn = setups::keccak_special5::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                worker,
                &prover_context,
            )?;

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }

    Ok((
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    ))
}

fn prove_delegation_circuit_with_replayer_format<
    A: GoodAllocator,
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
>(
    witnesses: &[Vec<
        riscv_transpiler::witness::DelegationWitness<
            REG_ACCESSES,
            INDIRECT_READS,
            INDIRECT_WRITES,
            VARIABLE_OFFSETS,
        >,
        A,
    >],
    external_challenges: ExternalChallenges,
    prec: &DelegationCircuitPrecomputations<A, A>,
    witness_eval_fn: fn(
        &mut prover::SimpleWitnessProxy<
            '_,
            DelegationOracle<
                '_,
                D,
                REG_ACCESSES,
                INDIRECT_READS,
                INDIRECT_WRITES,
                VARIABLE_OFFSETS,
            >,
        >,
    ),
    delegation_type: u16,
    worker: &Worker,
    prover_context: &ProverContext,
) -> CudaResult<(
    Vec<Proof>,
    Vec<Vec<prover::merkle_trees::MerkleTreeCapVarLength>>,
)>
where
    riscv_transpiler::witness::DelegationWitness<
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >: DelegationTracingDataHostSource,
{
    let circuit_type = <riscv_transpiler::witness::DelegationWitness<
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    > as DelegationTracingDataHostSource>::CIRCUIT_TYPE;
    let stream = prover_context.get_exec_stream();

    let mut per_tree_set = vec![];

    let mut per_delegation_type_proofs = vec![];
    for (_circuit_idx, el) in witnesses.iter().enumerate() {
        let oracle = DelegationOracle::<D, _, _, _, _> {
            cycle_data: el,
            marker: core::marker::PhantomData,
        };

        let witness_trace = prover::evaluate_witness::<DelegationOracle<'_, D, _, _, _, _>, A>(
            &prec.compiled_circuit.compiled_circuit,
            witness_eval_fn,
            prec.compiled_circuit.num_requests_per_circuit,
            &oracle,
            &[],
            &prec.compiled_circuit.table_driver,
            0,
            worker,
            A::default(),
        );

        // and prove
        let external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        };

        assert!(delegation_type < 1 << 12);
        let (_, proof) = prover::prover_stages::prove(
            &prec.compiled_circuit.compiled_circuit,
            &[],
            &external_values,
            witness_trace,
            &prec.setup,
            &prec.twiddles,
            &prec.lde_precomputations,
            0,
            Some(delegation_type as u16),
            prec.lde_factor,
            prec.tree_cap_size,
            NUM_QUERIES,
            verifier_common::POW_BITS as u32,
            worker,
        );

        let (gpu_proof, _) = {
            let lde_factor = prec.lde_factor;
            let log_lde_factor = lde_factor.trailing_zeros();
            let circuit = Arc::new(prec.compiled_circuit.compiled_circuit.clone());
            let trace_len = circuit.trace_len;
            let log_domain_size = trace_len.trailing_zeros();
            let log_tree_cap_size =
                OPTIMAL_FOLDING_PROPERTIES[log_domain_size as usize].total_caps_size_log2 as u32;
            let setup_row_major = &prec.setup.ldes[0].trace;
            let mut setup_evaluations = Vec::with_capacity(setup_row_major.as_slice().len());
            unsafe { setup_evaluations.set_len(setup_row_major.as_slice().len()) };
            transpose::transpose(
                setup_row_major.as_slice(),
                &mut setup_evaluations,
                setup_row_major.padded_width,
                setup_row_major.len(),
            );
            setup_evaluations.truncate(setup_row_major.len() * setup_row_major.width());
            let setup_evaluations = Arc::new(setup_evaluations);
            let setup_trees_and_caps = SetupPrecomputations::get_trees_and_caps(
                &circuit,
                log_lde_factor,
                log_tree_cap_size,
                setup_evaluations.clone(),
                &prover_context,
            )?;
            let mut setup = SetupPrecomputations::new(
                &circuit,
                log_lde_factor,
                log_tree_cap_size,
                false,
                setup_trees_and_caps,
                &prover_context,
            )?;
            setup.schedule_transfer(setup_evaluations, &prover_context)?;
            let h_trace =
                <riscv_transpiler::witness::DelegationWitness<
                    REG_ACCESSES,
                    INDIRECT_READS,
                    INDIRECT_WRITES,
                    VARIABLE_OFFSETS,
                > as DelegationTracingDataHostSource>::get(DelegationTraceHost {
                    chunks: vec![Arc::new(el.clone())],
                });
            let data = TracingDataHost::Delegation(h_trace);
            let mut transfer = TracingDataTransfer::new(data, &prover_context)?;
            transfer.schedule_transfer(&prover_context)?;
            let job = crate::prover::proof::prove(
                CircuitType::Delegation(circuit_type),
                circuit,
                external_challenges.clone(),
                vec![],
                &mut setup,
                None,
                None,
                Some(transfer),
                &prec.lde_precomputations,
                Some(delegation_type),
                prec.lde_factor,
                NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                Some(proof.pow_nonce),
                true,
                TreesCacheMode::CacheNone,
                &prover_context,
            )?;
            job.finish()?
        };
        compare_proofs(&proof_as_unrolled_mode_proof(&proof), &gpu_proof);

        per_tree_set.push(proof.memory_tree_caps.clone());

        per_delegation_type_proofs.push(proof);
    }

    Ok((per_delegation_type_proofs, per_tree_set))
}

fn proof_as_unrolled_mode_proof(proof: &Proof) -> UnrolledModeProof {
    UnrolledModeProof {
        external_challenges: proof.external_values.challenges.clone(),
        public_inputs: proof.public_inputs.clone(),
        witness_tree_caps: proof.witness_tree_caps.clone(),
        memory_tree_caps: proof.memory_tree_caps.clone(),
        setup_tree_caps: proof.setup_tree_caps.clone(),
        stage_2_tree_caps: proof.stage_2_tree_caps.clone(),
        permutation_grand_product_accumulator: proof.memory_grand_product_accumulator,
        delegation_argument_accumulator: proof.delegation_argument_accumulator,
        quotient_tree_caps: proof.quotient_tree_caps.clone(),
        evaluations_at_random_points: proof.evaluations_at_random_points.clone(),
        deep_poly_caps: proof.deep_poly_caps.clone(),
        intermediate_fri_oracle_caps: proof.intermediate_fri_oracle_caps.clone(),
        last_fri_step_plain_leaf_values: proof.last_fri_step_plain_leaf_values.clone(),
        final_monomial_form: proof.final_monomial_form.clone(),
        queries: proof.queries.clone(),
        pow_nonce: proof.pow_nonce,
        delegation_type: proof.delegation_type,
        aux_boundary_values: vec![proof.external_values.aux_boundary_values.clone()],
    }
}

#[test]
fn print_circuit_sizes() {
    let worker = Worker::new();
    let print = |name: &str, circuit: CompiledCircuitArtifact<BaseField>| {
        println!("{}", name);
        println!("log_domain_size={}", circuit.trace_len.trailing_zeros());
        println!("setup={}", circuit.setup_layout.total_width);
        println!("memory={}", circuit.memory_layout.total_width);
        println!("witness={}", circuit.witness_layout.total_width);
        println!("stage_2={}", circuit.stage_2_layout.total_width);
        println!();
    };
    print(
        "bigint",
        setups::get_bigint_with_control_circuit_setup::<Global, Global>(&worker)
            .compiled_circuit
            .compiled_circuit,
    );
    print(
        "blake",
        setups::get_blake2_with_compression_circuit_setup::<Global, Global>(&worker)
            .compiled_circuit
            .compiled_circuit,
    );
    print(
        "keccak",
        setups::get_keccak_special5_circuit_setup::<Global, Global>(&worker)
            .compiled_circuit
            .compiled_circuit,
    );
    print(
        "add_sub_lui_auipc_mop",
        setups::unrolled_circuits::add_sub_lui_auipc_mop_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "inits_and_teardowns",
        setups::unrolled_circuits::inits_and_teardowns_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "jump_branch_slt",
        setups::unrolled_circuits::jump_branch_slt_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "load_store_subword_only",
        setups::unrolled_circuits::load_store_subword_only_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "load_store_word_only",
        setups::unrolled_circuits::load_store_word_only_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "mul_div",
        setups::unrolled_circuits::mul_div_circuit_setup::<Global, Global>(&[], &[], &worker)
            .compiled_circuit,
    );
    print(
        "mul_div_unsigned",
        setups::unrolled_circuits::mul_div_unsigned_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "shift_binary_csr",
        setups::unrolled_circuits::shift_binary_csr_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
    print(
        "unified_reduced_machine",
        setups::unrolled_circuits::unified_reduced_machine_circuit_setup::<Global, Global>(
            &[],
            &[],
            &worker,
        )
        .compiled_circuit,
    );
}

#[test]
fn kernel_preload() -> era_cudart::result::CudaResult<()> {
    crate::witness::witness_delegation::touch_kernels()?;
    crate::witness::witness_unrolled::touch_kernels()?;
    Ok(())
}
