use crate::definitions::*;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::prover_stages::SetupPrecomputations;
use ::field::*;
use cs::default_compile_machine;
use cs::definitions::*;
use cs::machine::machine_configurations::*;
use cs::one_row_compiler::*;
use cs::tables::LookupWrapper;
use cs::tables::{TableDriver, TableType};
use fft::*;
use mem_utils::produce_register_contribution_into_memory_accumulator;
use prover_stages::{prove, ProverData};
use std::alloc::Global;
use trace_holder::RowMajorTrace;
use worker::Worker;

pub mod full_machine_with_gpu_tracer {
    use crate::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use risc_v_simulator::cycle::IMStandardIsaConfig;

    include!("../../full_machine_with_delegation_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
        >;
        (fn_ptr)(proxy);
    }
}

// pub(crate) mod reduced_machine {
//     use crate::witness_evaluator::SimpleWitnessProxy;
//     use crate::witness_proxy::WitnessProxy;
//     use crate::JointProcCycleOracle;
//     use ::cs::cs::placeholder::Placeholder;
//     use ::cs::cs::witness_placer::WitnessTypeSet;
//     use ::cs::cs::witness_placer::{
//         WitnessComputationCore, WitnessComputationalField, WitnessComputationalInteger,
//         WitnessComputationalU16, WitnessComputationalU32, WitnessMask,
//     };
//     use ::field::Mersenne31Field;
//     use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
//     use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;

//     // include!("../../../circuit_defs/reduced_risc_v_machine/generated/witness_generation_fn.rs");
//     // include!("../../../witness_eval_generator/src/generated.rs");
//     include!("../../minimal_machine_with_delegation_generated.rs");

//     pub(crate) fn witness_eval_fn<'a, 'b>(
//         proxy: &'_ mut SimpleWitnessProxy<
//             'a,
//             JointProcCycleOracle<'b, IWithoutByteAccessIsaConfigWithDelegation, 3>,
//         >,
//     ) {
//         let fn_ptr = evaluate_witness_fn::<
//             ScalarWitnessTypeSet<Mersenne31Field, true>,
//             SimpleWitnessProxy<
//                 'a,
//                 JointProcCycleOracle<'b, IWithoutByteAccessIsaConfigWithDelegation, 3>,
//             >,
//         >;
//         (fn_ptr)(proxy);
//     }
// }

pub mod blake2s_delegation_with_gpu_tracer {
    use crate::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;

    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalInteger,
        WitnessComputationalU16, WitnessComputationalU32,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../blake_delegation_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, DelegationCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, DelegationCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

use super::*;
use std::collections::HashMap;

mod delegation_test;
mod unrolled;

#[cfg(test)]
mod lde_tests;

pub use delegation_test::run_basic_delegation_test_impl;

// NOTE: For some reason tryint to add generic tree constructor to GPU arguments just makes resolver crazy,
// it starts to complaint about `ROM_ADDRESS_SPACE_SECOND_WORD_BITS` being not a constant but unconstraint const generic,
// so we live with default config for now

#[allow(unused)]
pub struct GpuComparisonArgs<'a> {
    pub circuit: &'a CompiledCircuitArtifact<Mersenne31Field>,
    pub setup:
        &'a SetupPrecomputations<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
    pub external_values: &'a ExternalValues,
    pub public_inputs: &'a Vec<Mersenne31Field>,
    pub twiddles: &'a Twiddles<Mersenne31Complex, Global>,
    pub lde_precomputations: &'a LdePrecomputations<Global>,
    pub table_driver: &'a TableDriver<Mersenne31Field>,
    pub lookup_mapping: RowMajorTrace<u32, DEFAULT_TRACE_PADDING_MULTIPLE, Global>,
    pub log_n: usize,
    pub circuit_sequence: usize,
    pub delegation_processing_type: Option<u16>,
    pub prover_data: &'a ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
}

// pub fn run_basic_test_impl(maybe_gpu_comparison_hook: Option<Box<dyn Fn(&GpuComparisonArgs)>>) {
//     use cs::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
//     use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;

//     // const NUM_PROC_CYCLES: usize = (1 << 18) - 1;
//     const NUM_PROC_CYCLES: usize = (1 << 20) - 1;

//     let domain_size = NUM_PROC_CYCLES + 1;
//     let lde_factor = 2;
//     let tree_cap_size = 32;

//     // let insn = "addi x1, x1, 42";
//     // let insn = "jalr x0, x0, 0";
//     let insn = "jal x0, 0";

//     // let worker = Worker::new_with_num_threads(4);
//     let worker = Worker::new_with_num_threads(8);
//     println!("num threads: {}", worker.get_num_cores());

//     let mut empty_hash: HashMap<String, u32> = HashMap::new();
//     let encoding = lib_rv32_asm::assemble_ir(&insn, &mut empty_hash, 0)
//         .unwrap()
//         .unwrap();
//     // dbg!(encoding);
//     // let binary = vec![encoding; NUM_PROC_CYCLES];
//     let mut binary = vec![encoding];
//     pad_bytecode::<{ 1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS) }>(&mut binary);

//     let rom_table = create_table_for_rom_image::<
//         _,
//         { 1u32 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS) },
//     >(&binary, TableType::RomRead.to_table_id());
//     let csr_table = create_csr_table_for_delegation(
//         true,
//         &[0x7c3],
//         TableType::SpecialCSRProperties.to_table_id(),
//     );

//     let machine = MinimalMachineNoExceptionHandlingWithDelegation;
//     let compiled_machine =
//         default_compile_machine(machine, rom_table.clone(), Some(csr_table.clone()), 20);

//     // recreate table driver for witness evaluation
//     let mut table_driver = create_table_driver::<_, _, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(machine);
//     // add preimage into table driver
//     table_driver.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));
//     table_driver.add_table_with_content(
//         TableType::SpecialCSRProperties,
//         LookupWrapper::Dimensional3(csr_table.clone()),
//     );

//     let trace_len = NUM_PROC_CYCLES + 1;
//     use risc_v_simulator::delegations::DelegationsCSRProcessor;
//     let csr_processor = DelegationsCSRProcessor;

//     let delegation_circuits_eval_fns = HashMap::new();

//     let (witness_chunks, register_final_values, _delegation_circuits) =
//         dev_run_all_and_make_witness_ext::<
//             _,
//             IWithoutByteAccessIsaConfigWithDelegation,
//             _,
//             ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
//         >(
//             machine,
//             &compiled_machine,
//             reduced_machine::witness_eval_fn,
//             delegation_circuits_eval_fns,
//             &[],
//             &binary,
//             NUM_PROC_CYCLES,
//             trace_len,
//             csr_processor,
//             Some(LookupWrapper::Dimensional3(csr_table)),
//             &worker,
//         );

//     assert_eq!(witness_chunks.len(), 1);

//     let twiddles: Twiddles<_, Global> = Twiddles::new(NUM_PROC_CYCLES + 1, &worker);
//     let lde_precomputations = LdePrecomputations::new(domain_size, lde_factor, &[0, 1], &worker);

//     let setup = SetupPrecomputations::from_tables_and_trace_len(
//         &table_driver,
//         trace_len,
//         &compiled_machine.setup_layout,
//         &twiddles,
//         &lde_precomputations,
//         lde_factor,
//         tree_cap_size,
//         &worker,
//     );

//     let witness = witness_chunks.into_iter().next().unwrap();

//     println!("Checking if satisfied");
//     let is_satisfied = check_satisfied(
//         &compiled_machine,
//         &witness.exec_trace,
//         witness.num_witness_columns,
//     );
//     assert!(is_satisfied);

//     let challenge = Mersenne31Quartic {
//         c0: Mersenne31Complex {
//             c0: Mersenne31Field::from_u64_unchecked(42),
//             c1: Mersenne31Field::from_u64_unchecked(42),
//         },
//         c1: Mersenne31Complex {
//             c0: Mersenne31Field::from_u64_unchecked(42),
//             c1: Mersenne31Field::from_u64_unchecked(42),
//         },
//     };

//     let mut current_challenge = Mersenne31Quartic::ONE;

//     // tau == 1 here
//     let tau = Mersenne31Quartic::ONE;

//     // TODO: properly adjust challenges by tau^H/2, so we can move similar powers to compiled constraint without
//     // touching quadratic coefficients
//     current_challenge.mul_assign_by_base(&tau);
//     current_challenge.mul_assign_by_base(&tau);

//     let mut quad_terms_challenges = vec![];
//     for _ in 0..compiled_machine.degree_2_constraints.len() {
//         quad_terms_challenges.push(current_challenge);
//         current_challenge.mul_assign(&challenge);
//     }

//     current_challenge.mul_assign_by_base(&tau.inverse().unwrap());

//     let mut linear_terms_challenges = vec![];
//     for _ in 0..compiled_machine.degree_1_constraints.len() {
//         linear_terms_challenges.push(current_challenge);
//         current_challenge.mul_assign(&challenge);
//     }

//     let compiled_constraints = CompiledConstraintsForDomain::from_compiled_circuit(
//         &compiled_machine,
//         Mersenne31Complex::ONE,
//         trace_len as u32,
//     );

//     let now = std::time::Instant::now();
//     let quotient_view = evaluate_constraints_on_domain(
//         &witness.exec_trace,
//         witness.num_witness_columns,
//         &quad_terms_challenges,
//         &linear_terms_challenges,
//         &compiled_constraints,
//         &worker,
//     );
//     dbg!(&now.elapsed());

//     let mut quotient_row = quotient_view.row_view(0..NUM_PROC_CYCLES);
//     for _ in 0..NUM_PROC_CYCLES {
//         let as_field = unsafe {
//             quotient_row
//                 .current_row_ref()
//                 .as_ptr()
//                 .cast::<Mersenne31Quartic>()
//                 .read()
//         };
//         assert_eq!(as_field, Mersenne31Quartic::ZERO);
//         quotient_row.advance_row();
//     }

//     let memory_argument_alpha = Mersenne31Quartic::from_base(Mersenne31Field(42));
//     let memory_argument_gamma =
//         Mersenne31Quartic::from_coeffs_in_base(&[Mersenne31Complex::ZERO, Mersenne31Complex::ONE]);

//     let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
//         NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
//         materialize_powers_serial_starting_with_elem::<_, Global>(
//             memory_argument_alpha,
//             NUM_MEM_ARGUMENT_KEY_PARTS - 1,
//         )
//         .try_into()
//         .unwrap();

//     dbg!(&witness.aux_data);

//     let delegation_argument_alpha = Mersenne31Quartic::from_base(Mersenne31Field(11));
//     let delegation_argument_gamma =
//         Mersenne31Quartic::from_coeffs_in_base(&[Mersenne31Complex::ONE, Mersenne31Complex::ONE]);

//     let delegation_argument_linearization_challenges: [Mersenne31Quartic;
//         NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
//         materialize_powers_serial_starting_with_elem::<_, Global>(
//             delegation_argument_alpha,
//             NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
//         )
//         .try_into()
//         .unwrap();

//     let external_values = ExternalValues {
//         challenges: ExternalChallenges {
//             memory_argument: ExternalMemoryArgumentChallenges {
//                 memory_argument_linearization_challenges:
//                     memory_argument_linearization_challenges_powers,
//                 memory_argument_gamma,
//             },
//             delegation_argument: Some(ExternalDelegationArgumentChallenges {
//                 delegation_argument_linearization_challenges,
//                 delegation_argument_gamma,
//             }),
//         },
//         aux_boundary_values: AuxArgumentsBoundaryValues {
//             lazy_init_first_row: witness.aux_data.lazy_init_first_row,
//             teardown_value_first_row: witness.aux_data.teardown_value_first_row,
//             teardown_timestamp_first_row: witness.aux_data.teardown_timestamp_first_row,
//             lazy_init_one_before_last_row: witness.aux_data.lazy_init_one_before_last_row,
//             teardown_value_one_before_last_row: witness.aux_data.teardown_value_one_before_last_row,
//             teardown_timestamp_one_before_last_row: witness
//                 .aux_data
//                 .teardown_timestamp_one_before_last_row,
//         },
//     };

//     let mut public_inputs = witness.aux_data.first_row_public_inputs.clone();
//     public_inputs.extend(witness.aux_data.one_before_last_row_public_inputs.clone());

//     if maybe_gpu_comparison_hook.is_none() {
//         serialize_to_file(&compiled_machine, "reduced_machine_layout");
//     }

//     let lookup_mapping_for_gpu = if maybe_gpu_comparison_hook.is_some() {
//         Some(witness.lookup_mapping.clone())
//     } else {
//         None
//     };

//     let now = std::time::Instant::now();
//     let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
//         &compiled_machine,
//         &public_inputs,
//         &external_values,
//         witness,
//         &setup,
//         &twiddles,
//         &lde_precomputations,
//         0,
//         None,
//         lde_factor,
//         tree_cap_size,
//         53,
//         28,
//         &worker,
//     );
//     println!("Partial machine proving time is {:?}", now.elapsed());

//     if let Some(ref gpu_comparison_hook) = maybe_gpu_comparison_hook {
//         let log_n = (NUM_PROC_CYCLES + 1).trailing_zeros();
//         assert_eq!(log_n, 20);
//         let gpu_comparison_args = GpuComparisonArgs {
//             circuit: &compiled_machine,
//             setup: &setup,
//             external_values: &external_values,
//             public_inputs: &public_inputs,
//             twiddles: &twiddles,
//             lde_precomputations: &lde_precomputations,
//             table_driver: &table_driver,
//             lookup_mapping: lookup_mapping_for_gpu.unwrap(),
//             log_n: log_n as usize,
//             circuit_sequence: 0,
//             delegation_processing_type: None,
//             prover_data: &prover_data,
//         };
//         gpu_comparison_hook(&gpu_comparison_args);
//     }

//     let register_contribution_in_memory_argument =
//         produce_register_contribution_into_memory_accumulator(
//             &register_final_values,
//             memory_argument_linearization_challenges_powers,
//             memory_argument_gamma,
//         );

//     dbg!(&prover_data.stage_2_result.grand_product_accumulator);
//     dbg!(register_contribution_in_memory_argument);

//     let mut t = prover_data.stage_2_result.grand_product_accumulator;
//     t.mul_assign(&register_contribution_in_memory_argument);

//     assert_eq!(t, Mersenne31Quartic::ONE);

//     if maybe_gpu_comparison_hook.is_none() {
//         serialize_to_file(&proof, "reduced_machine_proof");
//     }
// }

// #[test]
// fn run_basic_test() {
//     run_basic_test_impl(None);
// }

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

#[ignore = "broken"]
#[test]
fn calculate_fft() {
    for i in 2..30 {
        let tau: Mersenne31Complex = domain_generator_for_size(1 << i);
        dbg!(tau);
    }
    let domain_size = 1 << 2;
    let worker = Worker::new_with_num_threads(1);
    let twiddles = Twiddles::<Mersenne31Complex, Global>::new(domain_size, &worker);

    let mut values_main_domain = vec![];
    let mut sum = Mersenne31Field::ZERO;
    for i in 0..(domain_size - 1) {
        let value = if i == 0 {
            Mersenne31Field(1u32 << i)
        } else {
            Mersenne31Field::ZERO
        };

        sum.add_assign(&value);
        values_main_domain.push(Mersenne31Complex::from_base(value));
    }
    sum.negate();
    values_main_domain.push(Mersenne31Complex::from_base(sum));

    dbg!(&values_main_domain);
    let mut monomials = values_main_domain.clone();
    partial_ifft_natural_to_natural(
        &mut monomials,
        Mersenne31Complex::ONE,
        &twiddles.inverse_twiddles,
    );
    // scale
    let scale =
        Mersenne31Complex::from_base(Mersenne31Field(domain_size as u32).inverse().unwrap());
    for el in monomials.iter_mut() {
        el.mul_assign(&scale);
    }

    let tau = domain_generator_for_size(domain_size as u64 * 2);
    dbg!(tau);
    let mut values_on_coset = monomials.clone();
    fft_natural_to_natural(
        &mut values_on_coset,
        Mersenne31Complex::ONE,
        tau,
        &twiddles.forward_twiddles,
    );
    dbg!(&values_on_coset);

    let mut tmp = Mersenne31Complex::ONE;
    for (a, b) in values_main_domain.iter().zip(values_on_coset.iter()) {
        let b_ext = *b;
        let a = a.c0;
        let b = b.c1;

        let mut t = b;
        t.mul_assign(&a.inverse().unwrap());
        dbg!(t);

        let mut t = b_ext;
        t.mul_assign(&tmp);
        dbg!(t);

        tmp.mul_assign(&tau.inverse().unwrap());
    }
}

#[test]
fn test_batch_inverse_amortization() {
    use rand::SeedableRng;
    let num_inputs = 32;
    let mut inputs = Vec::with_capacity(num_inputs);
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    for _ in 0..num_inputs {
        let el = rand_fp4_from_rng(&mut rng);
        inputs.push(el);
    }

    let mut buffer = inputs.clone();

    let inp = inputs[0];
    let now = std::time::Instant::now();
    for _ in 0..1 << 20 {
        let _ = std::hint::black_box(inp.inverse());
    }
    let t = now.elapsed().as_micros();
    println!(
        "Batch inverse of single element took {:?} ns",
        now.elapsed().div_f64(f64::from(1 << 20))
    );

    let now = std::time::Instant::now();
    for _ in 0..1 << 20 {
        let _ = std::hint::black_box(batch_inverse_checked(&mut inputs, &mut buffer));
    }
    let tt = now.elapsed().as_micros();
    println!(
        "Batch inverse of {} elements took {:?} ns",
        num_inputs,
        now.elapsed().div_f64(f64::from(1 << 20))
    );

    let amortization = f64::from(tt as u32) / f64::from(t as u32) / f64::from(num_inputs as u32);
    println!(
        "Amortization factor for {} elements = {}",
        num_inputs, amortization
    );
}

// #[test]
// fn test_poseidon2_compression_circuit() {
//     use cs::cs::config::Config;
//     use cs::cs::cs_reference::BasicAssembly;
//     use cs::delegation::poseidon2::define_poseidon2_compression_delegation_circuit;

//     let input: [u32; 16] = [
//         894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
//         19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
//     ];

//     let expected: [u32; 16] = [
//         1124552602, 2127602268, 1834113265, 1207687593, 1891161485, 245915620, 981277919,
//         627265710, 1534924153, 1580826924, 887997842, 1526280482, 547791593, 1028672510,
//         1803086471, 323071277,
//     ];

//     let compression_expected: [Mersenne31Field; 8] = std::array::from_fn(|i| {
//         let mut el = Mersenne31Field::from_nonreduced_u32(expected[i]);
//         el.add_assign(&Mersenne31Field::from_nonreduced_u32(input[i]));

//         el
//     });

//     let mut inputs = (0..8)
//         .map(|el| BatchedRamAccessTraceRecord {
//             read_timestamp: 4096,
//             read_value: input[el],
//             write_value: compression_expected[el].to_reduced_u32(),
//         })
//         .collect::<Vec<_>>();
//     inputs.push(BatchedRamAccessTraceRecord {
//         read_timestamp: 4096,
//         read_value: 0,
//         write_value: 0,
//     });

//     let non_det = (8..16).map(|el| input[el]).collect::<Vec<_>>();

//     let cs_config = Config::new_default();
//     let cycles_data = vec![DelegationTraceRecord {
//         delegation_type: 1990,
//         phys_address_high: 1,
//         write_timestamp: 4099,
//         accesses: inputs.into_boxed_slice(),
//         non_determinism_accesses: non_det.into_boxed_slice(),
//     }];
//     let oracle = DelegationCycleOracle {
//         cycles_data: &cycles_data,
//     };
//     let oracle: DelegationCycleOracle<'static> = unsafe { std::mem::transmute(oracle) };
//     let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle(&cs_config, oracle);
//     define_poseidon2_compression_delegation_circuit(&mut cs);
// }

// #[test]
// fn prove_poseidon2_compression_circuit() {
//     use cs::cs::circuit::Circuit;
//     use cs::cs::config::Config;
//     use cs::cs::cs_reference::BasicAssembly;
//     // use cs::delegation::poseidon2::define_poseidon2_compression_delegation_circuit;

//     let input: [u32; 16] = [
//         894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
//         19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
//     ];

//     let expected: [u32; 16] = [
//         1124552602, 2127602268, 1834113265, 1207687593, 1891161485, 245915620, 981277919,
//         627265710, 1534924153, 1580826924, 887997842, 1526280482, 547791593, 1028672510,
//         1803086471, 323071277,
//     ];

//     let compression_expected: [Mersenne31Field; 8] = std::array::from_fn(|i| {
//         let mut el = Mersenne31Field::from_nonreduced_u32(expected[i]);
//         el.add_assign(&Mersenne31Field::from_nonreduced_u32(input[i]));

//         el
//     });

//     let mut inputs = (0..8)
//         .map(|el| BatchedRamAccessTraceRecord {
//             read_timestamp: 4096,
//             read_value: input[el],
//             write_value: compression_expected[el].to_reduced_u32(),
//         })
//         .collect::<Vec<_>>();
//     inputs.push(BatchedRamAccessTraceRecord {
//         read_timestamp: 4096,
//         read_value: 0,
//         write_value: 0,
//     });

//     let non_det = (8..16).map(|el| input[el]).collect::<Vec<_>>();

//     let _cs_config = Config::new_default();
//     let cycles_data = vec![DelegationTraceRecord {
//         delegation_type: 1990,
//         phys_address_high: 1,
//         write_timestamp: 4099,
//         accesses: inputs.into_boxed_slice(),
//         non_determinism_accesses: non_det.into_boxed_slice(),
//     }];
//     let oracle = DelegationCycleOracle {
//         cycles_data: &cycles_data,
//     };

//     // let delegation_domain_size = 1usize << 17;
//     let delegation_domain_size = 1usize << 20;

//     // let oracle: DelegationCycleOracle<'static> = unsafe { std::mem::transmute(oracle) };
//     // let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle(&cs_config, oracle);
//     // define_poseidon2_compression_delegation_circuit(&mut cs);

//     let circuit_description = {
//         use cs::cs::config::Config;
//         use cs::delegation::poseidon2::define_poseidon2_compression_delegation_circuit;
//         let cs_config = Config::new_default();
//         let mut cs = BasicAssembly::<Mersenne31Field>::new(&cs_config);
//         define_poseidon2_compression_delegation_circuit(&mut cs);
//         let circuit_output = cs.finalize();
//         let table_driver = circuit_output.table_driver.clone();
//         let compiler = OneRowCompiler::default();
//         let circuit = compiler.compile_to_evaluate_delegations(
//             circuit_output,
//             delegation_domain_size.trailing_zeros() as usize,
//         );

//         serialize_to_file(&circuit, "poseidon2_layout");
//         use risc_v_simulator::delegations::poseidon2_provide_witness_and_compress::POSEIDON2_WITNESS_AND_COMPRESS_ACCESS_ID;

//         let delegation_type = POSEIDON2_WITNESS_AND_COMPRESS_ACCESS_ID;
//         let description = DelegationProcessorDescription {
//             delegation_type,
//             num_requests_per_circuit: delegation_domain_size - 1,
//             trace_len: delegation_domain_size,
//             table_driver,
//             compiled_circuit: circuit,
//         };

//         description
//     };

//     let worker = Worker::new_with_num_threads(8);
//     let lde_factor = 2;
//     let table_driver =
//         cs::delegation::poseidon2::poseidon2_compression_delegation_circuit_create_table_driver();

//     let twiddles: Twiddles<_, Global> = Twiddles::new(delegation_domain_size, &worker);
//     let lde_precomputations =
//         LdePrecomputations::new(delegation_domain_size, lde_factor, &[0, 1], &worker);

//     let setup = SetupPrecomputations::from_tables_and_trace_len(
//         &table_driver,
//         delegation_domain_size,
//         &circuit_description.compiled_circuit.setup_layout,
//         &twiddles,
//         &lde_precomputations,
//         lde_factor,
//         32,
//         &worker,
//     );

//     let memory_argument_alpha = Mersenne31Quartic::from_array_of_base([
//         Mersenne31Field(2),
//         Mersenne31Field(5),
//         Mersenne31Field(42),
//         Mersenne31Field(123),
//     ]);
//     let memory_argument_gamma = Mersenne31Quartic::from_array_of_base([
//         Mersenne31Field(11),
//         Mersenne31Field(7),
//         Mersenne31Field(1024),
//         Mersenne31Field(8000),
//     ]);

//     let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
//         NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
//         materialize_powers_serial_starting_with_elem::<_, Global>(
//             memory_argument_alpha,
//             NUM_MEM_ARGUMENT_KEY_PARTS - 1,
//         )
//         .try_into()
//         .unwrap();

//     let delegation_argument_alpha = Mersenne31Quartic::from_array_of_base([
//         Mersenne31Field(5),
//         Mersenne31Field(8),
//         Mersenne31Field(32),
//         Mersenne31Field(16),
//     ]);
//     let delegation_argument_gamma = Mersenne31Quartic::from_array_of_base([
//         Mersenne31Field(200),
//         Mersenne31Field(100),
//         Mersenne31Field(300),
//         Mersenne31Field(400),
//     ]);

//     let delegation_argument_linearization_challenges: [Mersenne31Quartic;
//         NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
//         materialize_powers_serial_starting_with_elem::<_, Global>(
//             delegation_argument_alpha,
//             NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
//         )
//         .try_into()
//         .unwrap();

//     let external_values = ExternalValues {
//         challenges: ExternalChallenges {
//             memory_argument: ExternalMemoryArgumentChallenges {
//                 memory_argument_linearization_challenges:
//                     memory_argument_linearization_challenges_powers,
//                 memory_argument_gamma,
//             },
//             delegation_argument: Some(ExternalDelegationArgumentChallenges {
//                 delegation_argument_linearization_challenges,
//                 delegation_argument_gamma,
//             }),
//         },
//         aux_boundary_values: AuxArgumentsBoundaryValues {
//             lazy_init_first_row: [Mersenne31Field::ZERO; 2],
//             lazy_init_one_before_last_row: [Mersenne31Field::ZERO; 2],
//         },
//     };

//     let witness = evaluate_witness(
//         &circuit_description.compiled_circuit,
//         delegation_domain_size - 1,
//         &oracle,
//         &[],
//         &[],
//         &table_driver,
//         0,
//         &worker,
//         Global,
//     );

//     let (_prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
//         &circuit_description.compiled_circuit,
//         &[],
//         &external_values,
//         witness,
//         &setup,
//         &twiddles,
//         &lde_precomputations,
//         0,
//         None,
//         lde_factor,
//         32,
//         53,
//         28,
//         &worker,
//     );

//     serialize_to_file(&proof, "poseidon2_proof");
// }
