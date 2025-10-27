#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
use prover::cs::*;
use prover::field::Mersenne31Field;
use prover::*;

pub const FAMILY_IDX: u8 = INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
pub const TRACE_LEN_LOG2: u32 = 24;
pub const NUM_INIT_AND_TEARDOWN_SETS: usize = 6;
pub const DOMAIN_SIZE: usize = 1 << TRACE_LEN_LOG2;
pub const NUM_CYCLES: usize = DOMAIN_SIZE - 1;
pub const LDE_FACTOR: usize = 2;
pub const LDE_SOURCE_COSETS: &[usize] = &[0, 1];
pub const TREE_CAP_SIZE: usize = 32;
pub const MAX_ROM_SIZE: usize = 1 << 21; // bytes
pub const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize = (MAX_ROM_SIZE.trailing_zeros() - 16) as usize;

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
    use crate::one_row_compiler::OneRowCompiler;

    let compiler = OneRowCompiler::<Mersenne31Field>::default();
    compiler.compile_init_and_teardown_circuit(NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2 as usize)
}

pub fn dump_ssa_form(
    bytecode: &[u32],
) -> Vec<Vec<prover::cs::cs::witness_placer::graph_description::RawExpression<Mersenne31Field>>> {
    dump_ssa_form_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode)
}

pub fn dump_ssa_form_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    _bytecode: &[u32],
) -> Vec<Vec<prover::cs::cs::witness_placer::graph_description::RawExpression<Mersenne31Field>>> {
    vec![vec![]]
}

pub fn get_table_driver(bytecode: &[u32]) -> prover::cs::tables::TableDriver<Mersenne31Field> {
    get_table_driver_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode)
}

pub fn get_table_driver_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    bytecode: &[u32],
) -> prover::cs::tables::TableDriver<Mersenne31Field> {
    use crate::tables::TableDriver;

    let num_bytecode_words = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    assert!(bytecode.len() <= num_bytecode_words);

    TableDriver::new()
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
