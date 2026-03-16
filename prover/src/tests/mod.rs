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
