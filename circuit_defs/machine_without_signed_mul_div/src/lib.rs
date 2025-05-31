#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::machine::machine_configurations::full_isa_with_delegation_no_exceptions_no_signed_mul_div::FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv;
use prover::cs::*;
use prover::fft::GoodAllocator;
use prover::field::Mersenne31Field;
use prover::risc_v_simulator::cycle::{IMWithoutSignedMulDivIsaConfig, MachineConfig};
use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
use prover::*;

pub const DOMAIN_SIZE: usize = 1 << 22;
pub const NUM_CYCLES: usize = DOMAIN_SIZE - 1;
pub const LDE_FACTOR: usize = 2;
pub const LDE_SOURCE_COSETS: &[usize] = &[0, 1];
pub const TREE_CAP_SIZE: usize = 32;
pub const MAX_ROM_SIZE: usize = 1 << 21; // bytes
pub const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize = (MAX_ROM_SIZE.trailing_zeros() - 16) as usize;

pub const ALLOWED_DELEGATION_CSRS: &[u32] =
    prover::risc_v_simulator::cycle::IMWithoutSignedMulDivIsaConfig::ALLOWED_DELEGATION_CSRS;

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub type Machine = FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv;

pub fn formal_machine_for_compilation() -> Machine {
    FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv
}

pub fn get_machine(
    bytecode: &[u32],
    delegation_csrs: &[u32],
) -> one_row_compiler::CompiledCircuitArtifact<field::Mersenne31Field> {
    get_machine_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode, delegation_csrs)
}

pub fn get_machine_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    bytecode: &[u32],
    delegation_csrs: &[u32],
) -> one_row_compiler::CompiledCircuitArtifact<field::Mersenne31Field> {
    assert_eq!(
        bytecode.len(),
        (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4
    );
    use crate::machine::machine_configurations::create_csr_table_for_delegation;
    use prover::cs::machine::machine_configurations::create_table_for_rom_image;
    use prover::cs::tables::TableType;

    let machine = FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv;
    let rom_table = create_table_for_rom_image::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        &bytecode,
        TableType::RomRead.to_table_id(),
    );
    let csr_table = create_csr_table_for_delegation(
        true,
        delegation_csrs,
        TableType::SpecialCSRProperties.to_table_id(),
    );

    let compiled_machine = default_compile_machine::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        machine,
        rom_table,
        Some(csr_table),
        DOMAIN_SIZE.trailing_zeros() as usize,
    );

    compiled_machine
}

/// Produce a RISC-V machine table driver taking into account the bytecode we want to prove and allowed
/// delegation implementations
pub fn get_table_driver(
    bytecode: &[u32],
    delegation_csrs: &[u32],
) -> prover::cs::tables::TableDriver<Mersenne31Field> {
    get_table_driver_for_rom_bound::<ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(bytecode, delegation_csrs)
}

pub fn get_table_driver_for_rom_bound<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
    bytecode: &[u32],
    delegation_csrs: &[u32],
) -> prover::cs::tables::TableDriver<Mersenne31Field> {
    assert_eq!(
        bytecode.len(),
        (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4
    );

    use crate::machine::machine_configurations::create_csr_table_for_delegation;
    use prover::cs::machine::machine_configurations::create_table_driver;
    use prover::cs::machine::machine_configurations::create_table_for_rom_image;
    use prover::cs::tables::LookupWrapper;
    use prover::cs::tables::TableType;

    let machine = FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv;
    let mut table_driver = create_table_driver::<_, _, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(machine);
    let rom_table = create_table_for_rom_image::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        &bytecode,
        TableType::RomRead.to_table_id(),
    );
    table_driver.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));
    let csr_table = create_csr_table_for_delegation(
        true,
        delegation_csrs,
        TableType::SpecialCSRProperties.to_table_id(),
    );
    table_driver.add_table_with_content(
        TableType::SpecialCSRProperties,
        LookupWrapper::Dimensional3(csr_table),
    );

    table_driver
}

mod sealed {
    use crate::Mersenne31Field;
    use prover::cs::cs::placeholder::Placeholder;
    use prover::cs::cs::witness_placer::*;
    use prover::witness_proxy::WitnessProxy;

    include!("../generated/witness_generation_fn.rs");
}

pub fn witness_eval_fn_for_gpu_tracer<'a, 'b>(
    proxy: &'_ mut SimpleWitnessProxy<
        'a,
        MainRiscVOracle<'b, IMWithoutSignedMulDivIsaConfig, impl GoodAllocator>,
    >,
) {
    use prover::cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<Mersenne31Field, true>,
        SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMWithoutSignedMulDivIsaConfig, _>>,
    >;
    (fn_ptr)(proxy);
}

/// This function will generate layout and quotient files for verifier
pub fn generate_artifacts() {
    use std::io::Write;

    // particular bytecode doesn't matter here, we only need length, that is anyway padded to upped bound
    let dummy_bytecode = vec![0u32; MAX_ROM_SIZE / 4];

    let compiled_machine = get_machine(&dummy_bytecode, ALLOWED_DELEGATION_CSRS);
    serialize_to_file(&compiled_machine, "generated/layout");

    let compiled_machine = get_machine(&dummy_bytecode, ALLOWED_DELEGATION_CSRS);
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
