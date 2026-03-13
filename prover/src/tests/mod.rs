use crate::definitions::*;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::prover_stages::SetupPrecomputations;
use ::field::*;
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

pub mod blake2s_delegation_with_transpiler {
    use crate::tracers::oracles::transpiler_oracles::delegation::Blake2sDelegationOracle;
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
        proxy: &'_ mut SimpleWitnessProxy<'a, Blake2sDelegationOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, Blake2sDelegationOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod keccak_special5_delegation_with_transpiler {
    use crate::tracers::oracles::transpiler_oracles::delegation::KeccakDelegationOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;

    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalInteger,
        WitnessComputationalU16, WitnessComputationalU32, WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../keccak_delegation_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(proxy: &mut SimpleWitnessProxy<'a, KeccakDelegationOracle<'b>>) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, KeccakDelegationOracle<'b>>,
        >;
        fn_ptr(proxy);
    }
}

use super::*;

mod unrolled;

#[cfg(test)]
mod lde_tests;

pub use unrolled::with_transpiler::{
    run_basic_unrolled_test_in_transpiler_with_word_specialization_impl,
    run_unrolled_test_program_in_transpiler_with_word_specialization_impl,
    KECCAK_F1600_TRANSPILER_TEST_PROGRAM,
};

// NOTE: For some reason tryint to add generic tree constructor to GPU arguments just makes resolver crazy,
// it starts to complaint about `ROM_ADDRESS_SPACE_SECOND_WORD_BITS` being not a constant but unconstraint const generic,
// so we live with default config for now

#[allow(unused)]
pub struct GpuComparisonArgs<'a> {
    pub circuit: &'a CompiledCircuitArtifact<Mersenne31Field>,
    pub setup:
        &'a SetupPrecomputations<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
    pub external_challenges: &'a ExternalChallenges,
    pub aux_boundary_values: &'a [AuxArgumentsBoundaryValues],
    pub public_inputs: &'a Vec<Mersenne31Field>,
    pub twiddles: &'a Twiddles<Mersenne31Complex, Global>,
    pub lde_precomputations: &'a LdePrecomputations<Global>,
    pub lookup_mapping: RowMajorTrace<u32, DEFAULT_TRACE_PADDING_MULTIPLE, Global>,
    pub log_n: usize,
    pub circuit_sequence: Option<usize>,
    pub delegation_processing_type: Option<u16>,
    pub is_unrolled: bool,
    pub prover_data: &'a ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
}

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

#[cfg(test)]
#[allow(dead_code)]
fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

#[cfg(test)]
#[allow(dead_code)]
fn fast_serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    bincode::serialize_into(&mut dst, el).unwrap();
}

#[cfg(test)]
#[allow(dead_code)]
fn fast_deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    bincode::deserialize_from(src).unwrap()
}

#[cfg(test)]
#[track_caller]
fn read_binary(path: &std::path::Path) -> (Vec<u8>, Vec<u32>) {
    use std::io::Read;
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
    let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
    for el in buffer.as_chunks::<4>().0 {
        binary.push(u32::from_le_bytes(*el));
    }

    (buffer, binary)
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
