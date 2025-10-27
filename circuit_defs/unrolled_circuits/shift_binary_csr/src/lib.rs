#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::machine::machine_configurations::create_csr_table_for_delegation;
use crate::tables::LookupWrapper;
use crate::tables::TableType;
use common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;
use prover::cs::cs::circuit::Circuit;
use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::cs::machine::ops::unrolled::DecoderTableEntry;
use prover::cs::machine::ops::unrolled::{
    compile_unrolled_circuit_state_transition, ShiftBinaryCsrrwDecoder,
};
use prover::cs::*;
use prover::fft::GoodAllocator;
use prover::field::Mersenne31Field;
use prover::tracers::unrolled::tracer::NonMemTracingFamilyChunk;
use prover::*;

pub const FAMILY_IDX: u8 = SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;
pub const TRACE_LEN_LOG2: u32 = 24;
pub const DOMAIN_SIZE: usize = 1 << TRACE_LEN_LOG2;
pub const NUM_CYCLES: usize = DOMAIN_SIZE - 1;
pub const LDE_FACTOR: usize = 2;
pub const LDE_SOURCE_COSETS: &[usize] = &[0, 1];
pub const TREE_CAP_SIZE: usize = 32;
pub const MAX_ROM_SIZE: usize = 1 << 21; // bytes
pub const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize = (MAX_ROM_SIZE.trailing_zeros() - 16) as usize;

pub const ALLOWED_DELEGATION_CSRS: &[u32] = &[
    common_constants::NON_DETERMINISM_CSR,
    common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
];

pub const ALLOWED_DELEGATION_CSRS_U16: &[u16] = &[
    common_constants::NON_DETERMINISM_CSR as u16,
    common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER
        as u16,
    common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
        as u16,
    common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16,
];

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn get_circuit(
    bytecode: &[u32],
) -> one_row_compiler::CompiledCircuitArtifact<field::Mersenne31Field> {
    get_circuit_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode)
}

pub fn get_circuit_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    bytecode: &[u32],
) -> one_row_compiler::CompiledCircuitArtifact<field::Mersenne31Field> {
    let num_bytecode_words = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    assert!(bytecode.len() <= num_bytecode_words);
    use prover::cs::machine::ops::unrolled::shift_binary_csr::*;

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        ALLOWED_DELEGATION_CSRS,
        TableType::SpecialCSRProperties.to_table_id(),
    );

    compile_unrolled_circuit_state_transition::<Mersenne31Field>(
        &|cs| {
            shift_binop_csrrw_table_addition_fn(cs);
            cs.add_table_with_content(
                TableType::SpecialCSRProperties,
                LookupWrapper::Dimensional3(csr_table.clone()),
            );
        },
        &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode(cs),
        num_bytecode_words,
        TRACE_LEN_LOG2 as usize,
    )
}

pub fn dump_ssa_form(
    bytecode: &[u32],
) -> Vec<Vec<prover::cs::cs::witness_placer::graph_description::RawExpression<Mersenne31Field>>> {
    dump_ssa_form_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode)
}

pub fn dump_ssa_form_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    bytecode: &[u32],
) -> Vec<Vec<prover::cs::cs::witness_placer::graph_description::RawExpression<Mersenne31Field>>> {
    let num_bytecode_words = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    assert!(bytecode.len() <= num_bytecode_words);
    use crate::machine::ops::unrolled::dump_ssa_witness_eval_form_for_unrolled_circuit;
    use prover::cs::machine::ops::unrolled::shift_binary_csr::*;

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        ALLOWED_DELEGATION_CSRS,
        TableType::SpecialCSRProperties.to_table_id(),
    );

    dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
        &|cs| {
            shift_binop_csrrw_table_addition_fn(cs);
            cs.add_table_with_content(
                TableType::SpecialCSRProperties,
                LookupWrapper::Dimensional3(csr_table.clone()),
            );
        },
        &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode(cs),
    )
}

pub fn get_table_driver(bytecode: &[u32]) -> prover::cs::tables::TableDriver<Mersenne31Field> {
    get_table_driver_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode)
}

pub fn get_table_driver_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    bytecode: &[u32],
) -> prover::cs::tables::TableDriver<Mersenne31Field> {
    use crate::tables::TableDriver;
    use prover::cs::machine::ops::unrolled::shift_binary_csr::*;

    let num_bytecode_words = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    assert!(bytecode.len() <= num_bytecode_words);

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        ALLOWED_DELEGATION_CSRS,
        TableType::SpecialCSRProperties.to_table_id(),
    );

    let mut table_driver = TableDriver::<Mersenne31Field>::new();
    shift_binop_csrrw_table_driver_fn(&mut table_driver);
    table_driver.add_table_with_content(
        TableType::SpecialCSRProperties,
        LookupWrapper::Dimensional3(csr_table.clone()),
    );

    table_driver
}

pub fn get_tracer_factory<A: GoodAllocator>() -> (
    u8,
    Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>,
) {
    use prover::tracers::unrolled::tracer::NonMemTracingFamilyChunk;
    let factory = Box::new(|| NonMemTracingFamilyChunk::new_for_num_cycles(DOMAIN_SIZE - 1));

    (FAMILY_IDX, factory as _)
}

pub fn get_decoder_table<A: GoodAllocator>(
    bytecode: &[u32],
) -> (
    Vec<Option<DecoderTableEntry<Mersenne31Field>>, A>,
    Vec<ExecutorFamilyDecoderData, A>,
) {
    get_decoder_table_for_rom_bound::<A, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode)
}

pub fn get_decoder_table_for_rom_bound<
    A: GoodAllocator,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    bytecode: &[u32],
) -> (
    Vec<Option<DecoderTableEntry<Mersenne31Field>>, A>,
    Vec<ExecutorFamilyDecoderData, A>,
) {
    let num_bytecode_words = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    assert!(bytecode.len() <= num_bytecode_words);

    use crate::machine::ops::unrolled::process_binary_into_separate_tables_ext;
    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, A>(
        bytecode,
        &[Box::new(ShiftBinaryCsrrwDecoder)],
        num_bytecode_words,
        ALLOWED_DELEGATION_CSRS_U16,
    );

    t.remove(&FAMILY_IDX).expect("decoder data")
}

#[cfg(feature = "witness_eval_fn")]
mod sealed {
    use crate::field::Mersenne31Field;
    use prover::cs::cs::placeholder::Placeholder;
    use prover::cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use prover::cs::cs::witness_placer::WitnessTypeSet;
    use prover::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use prover::unrolled::NonMemoryCircuitOracle;
    use prover::witness_proxy::WitnessProxy;
    use prover::SimpleWitnessProxy;

    include!("../generated/witness_generation_fn.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

#[cfg(feature = "witness_eval_fn")]
pub fn witness_eval_fn_for_gpu_tracer<'a, 'b>(
    proxy: &'_ mut SimpleWitnessProxy<'a, prover::unrolled::NonMemoryCircuitOracle<'b>>,
) {
    self::sealed::witness_eval_fn(proxy)
}

/// This function will generate layout and quotient files for verifier
pub fn generate_artifacts() {
    use std::io::Write;

    // particular bytecode doesn't matter here - it only goes to special lookup tables in setup
    let compiled_machine = get_circuit_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(&[]);
    serialize_to_file(&compiled_machine, "generated/layout.json");

    let (layout, quotient) = verifier_generator::generate_for_description(compiled_machine);

    let mut dst = std::fs::File::create("generated/circuit_layout.rs").unwrap();
    dst.write_all(&layout.as_bytes()).unwrap();

    let mut dst = std::fs::File::create("generated/quotient.rs").unwrap();
    dst.write_all(&quotient.as_bytes()).unwrap();
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn generate() {
        generate_artifacts();
    }
}
