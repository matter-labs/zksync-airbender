#![allow(type_alias_bounds)]
#![cfg_attr(not(feature = "compiler"), no_std)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(iter_advance_by)]
#![feature(ptr_as_ref_unchecked)]
#![feature(option_zip)]
#![feature(assert_matches)]

pub mod definitions;

#[cfg(feature = "compiler")]
pub mod constraint;
#[cfg(feature = "compiler")]
pub mod cs;
#[cfg(feature = "compiler")]
pub mod csr_properties;
#[cfg(feature = "compiler")]
pub mod delegation;
#[cfg(feature = "compiler")]
pub mod devices;
#[cfg(feature = "compiler")]
pub mod machine;
#[cfg(feature = "compiler")]
pub mod one_row_compiler;
#[cfg(feature = "compiler")]
pub mod tables;
#[cfg(feature = "compiler")]
pub mod types;
#[cfg(feature = "compiler")]
pub mod utils;

#[cfg(feature = "compiler")]
pub fn default_compile_machine<
    M: crate::machine::Machine<::field::Mersenne31Field>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    machine: M,
    bytecode_table: crate::tables::LookupTable<field::Mersenne31Field, 3>,
    csr_table: Option<crate::tables::LookupTable<field::Mersenne31Field, 3>>,
    trace_len_log2: usize,
) -> crate::one_row_compiler::CompiledCircuitArtifact<::field::Mersenne31Field>
where
    [(); { <M as crate::machine::Machine<::field::Mersenne31Field>>::ASSUME_TRUSTED_CODE }
        as usize]:,
    [(); { <M as crate::machine::Machine<::field::Mersenne31Field>>::OUTPUT_EXACT_EXCEPTIONS }
        as usize]:,
{
    use ::field::Mersenne31Field;
    // now test compilation into AIR
    use crate::cs::cs_reference::BasicAssembly;
    use crate::machine::machine_configurations::compile_machine;
    use crate::one_row_compiler::OneRowCompiler;
    use crate::tables::TableType;

    let mut cs_output = compile_machine::<
        Mersenne31Field,
        BasicAssembly<Mersenne31Field>,
        M,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(machine);
    // add the ROM table to account for size
    cs_output.table_driver.add_table_with_content(
        TableType::RomRead,
        crate::tables::LookupWrapper::Dimensional3(bytecode_table),
    );
    if let Some(csr_table) = csr_table {
        cs_output.table_driver.add_table_with_content(
            TableType::SpecialCSRProperties,
            crate::tables::LookupWrapper::Dimensional3(csr_table),
        );
    }
    let compiler = OneRowCompiler::default();
    let compiler_output =
        compiler.compile_output_for_chunked_memory_argument(cs_output, trace_len_log2);

    compiler_output
}

#[cfg(feature = "compiler")]
pub fn default_compile_delegation_circuit<T: Sized>(
    trace_len_log2: usize,
    definition_fn: impl Fn(&mut crate::cs::cs_reference::BasicAssembly<::field::Mersenne31Field>) -> T,
) -> crate::one_row_compiler::CompiledCircuitArtifact<::field::Mersenne31Field> {
    use crate::cs::circuit::Circuit;
    use crate::cs::cs_reference::BasicAssembly;
    use crate::one_row_compiler::OneRowCompiler;
    use ::field::Mersenne31Field;

    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    definition_fn(&mut cs);
    let (circuit_output, _) = cs.finalize();
    let compiler = OneRowCompiler::default();
    let circuit = compiler.compile_to_evaluate_delegations(circuit_output, trace_len_log2);

    circuit
}
