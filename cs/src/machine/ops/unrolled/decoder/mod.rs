use std::collections::{BTreeSet, HashMap};

use super::super::constants::*;
use crate::cs::oracle::ExecutorFamilyDecoderData;
use crate::definitions::*;
use crate::definitions::{
    formally_parse_rs1_rs2_rd_props_for_tracer, funct3_bits, funct7_bits, get_opcode_bits,
};
use crate::machine::machine_configurations::create_table_for_rom_image;
use crate::types::Num;
use crate::{
    cs::circuit::Circuit,
    definitions::Variable,
    devices::risc_v_types::{InstructionType, NUM_INSTRUCTION_TYPES},
};
use fft::GoodAllocator;
use field::PrimeField;

mod add_sub_lui_auipc_mop;
mod bytecode_preprocessor;
mod jump_slt_branch;
mod memory;
mod memory_subword_only;
mod memory_word_only;
mod mul_div;
mod reduced_machine_ops;
mod shift_binop_csrrw;

pub use self::add_sub_lui_auipc_mop::*;
pub use self::bytecode_preprocessor::*;
pub use self::jump_slt_branch::*;
pub use self::memory::*;
pub use self::memory_subword_only::*;
pub use self::memory_word_only::*;
pub use self::mul_div::*;
pub use self::reduced_machine_ops::*;
pub use self::shift_binop_csrrw::*;

mod decoder_circuit;

pub use decoder_circuit::describe_decoder_cycle;

pub type InstructionFamilyBitmaskRepr = u32;

pub const NUM_DEFAULT_DECODER_BITS: usize = 1 + (NUM_INSTRUCTION_TYPES - 1); // generic validity flag + maskers for instruction types except R-type

pub trait InstructionFamilyBitmaskCircuitParser: 'static + std::fmt::Debug {
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self;
}

pub const INVALID_OPCODE_DEFAULTS: (bool, InstructionType, InstructionFamilyBitmaskRepr) =
    (false, InstructionType::RType, 0); // We do not need info about instruciton being R-type for decoder

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExecutorFamilyDecoderExtendedData {
    pub data: ExecutorFamilyDecoderData,
    pub instruction_format: InstructionType,
    pub validate_csr_index_in_immediate: bool,
}

pub trait OpcodeFamilyDecoder: 'static + std::fmt::Debug {
    type BitmaskCircuitParser: InstructionFamilyBitmaskCircuitParser
    where
        Self: Sized;

    fn instruction_family_index(&self) -> u8;

    fn define_decoder_subspace(&self, opcode: u32)
        -> Result<ExecutorFamilyDecoderExtendedData, ()>; // either full decoder data, or "unsupported by this circuit"

    #[inline(always)]
    fn parse_for_oracle(&self, opcode: u32) -> ExecutorFamilyDecoderData {
        self.define_decoder_subspace(opcode)
            .map(|el| el.data)
            .unwrap_or(Default::default())
    }
}

pub fn create_decoder_circuit_table_driver_into_cs<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    image: &[u32],
) {
    use crate::tables::*;

    // manual call here, to later on easily control address bits
    let id = TableType::RomAddressSpaceSeparator.to_table_id();
    use crate::tables::create_rom_separator_table;
    let table = LookupWrapper::Dimensional3(create_rom_separator_table::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(id));
    cs.add_table_with_content(TableType::RomAddressSpaceSeparator, table);

    let rom_table = create_table_for_rom_image::<F, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        image,
        TableType::RomRead.to_table_id(),
    );
    cs.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));

    cs.materialize_table(TableType::QuickDecodeDecompositionCheck4x4x4);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck7x3x6);
    cs.materialize_table(TableType::RangeCheckSmall);
}

pub fn opcodes_for_full_machine() -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder::<true>),
        Box::new(ShiftBinaryCsrrwDecoder),
        Box::new(MemoryFamilyDecoder),
        Box::new(DivMulDecoder::<true>),
    ]
}

pub fn opcodes_for_full_machine_with_unsigned_mul_div_only() -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder::<true>),
        Box::new(ShiftBinaryCsrrwDecoder),
        Box::new(MemoryFamilyDecoder),
        Box::new(DivMulDecoder::<false>),
    ]
}

pub fn opcodes_for_full_machine_with_mem_word_access_specialization(
) -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder::<true>),
        Box::new(ShiftBinaryCsrrwDecoder),
        Box::new(WordOnlyMemoryFamilyDecoder),
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        Box::new(DivMulDecoder::<true>),
    ]
}

pub fn opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(
) -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder::<true>),
        Box::new(ShiftBinaryCsrrwDecoder),
        Box::new(WordOnlyMemoryFamilyDecoder),
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        Box::new(DivMulDecoder::<false>),
    ]
}

pub fn opcodes_for_reduced_machine() -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder::<true>),
        Box::new(ShiftBinaryCsrrwDecoder),
        Box::new(WordOnlyMemoryFamilyDecoder),
    ]
}

pub fn process_binary_into_separate_tables<F: PrimeField, A: GoodAllocator>(
    binary: &[u32],
    families: &[Box<dyn OpcodeFamilyDecoder>],
    max_bytecode_size_words: usize,
    supported_csrs: &[u16],
) -> HashMap<
    u8,
    (
        Vec<Option<DecoderTableEntry<F>>, A>,
        Vec<ExecutorFamilyDecoderData, A>,
    ),
> {
    process_binary_into_separate_tables_ext::<F, false, A>(
        binary,
        families,
        max_bytecode_size_words,
        supported_csrs,
    )
}

pub fn process_binary_into_separate_tables_ext<
    F: PrimeField,
    const ALLOW_UNSUPPORTED: bool,
    A: GoodAllocator,
>(
    binary: &[u32],
    families: &[Box<dyn OpcodeFamilyDecoder>],
    bytecode_size_words: usize,
    supported_csrs: &[u16],
) -> HashMap<
    u8,
    (
        Vec<Option<DecoderTableEntry<F>>, A>,
        Vec<ExecutorFamilyDecoderData, A>,
    ),
> {
    assert!(binary.len() <= bytecode_size_words, "bytecode is too long");
    let mut pc_set = BTreeSet::new();
    let mut result = HashMap::with_capacity(families.len());
    for family in families.iter() {
        let family_type = family.instruction_family_index();
        let (table, witness_eval_data) =
            preprocess_bytecode::<F, A>(&binary, bytecode_size_words, &family, supported_csrs);
        assert_eq!(table.len(), bytecode_size_words);
        assert_eq!(witness_eval_data.len(), bytecode_size_words);
        for (idx, entry) in table.iter().enumerate() {
            if entry.is_some() {
                let is_unique = pc_set.insert(idx);
                assert!(is_unique);
            }
        }

        result.insert(family_type, (table, witness_eval_data));
    }

    if ALLOW_UNSUPPORTED == false {
        if pc_set.len() != binary.len() {
            for i in 0..binary.len() {
                if pc_set.contains(&i) == false {
                    println!(
                        "PC = 0x{:08x}, opcode = 0x{:08x} is not supported",
                        i << 2,
                        binary[i]
                    );
                }
            }

            panic!("Not all the opcodes are supported");
        }
    }

    result
}

pub fn decoder_table_padding<F: PrimeField>() -> [F; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH] {
    [F::MINUS_ONE; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH]
}

pub fn materialize_flattened_decoder_table<F: PrimeField>(
    supported_entries_for_family: &[Option<DecoderTableEntry<F>>],
) -> Vec<[F; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH]> {
    assert!(supported_entries_for_family.len().is_power_of_two());

    // log-derivative based lookup argument doesn't require any special ordering of the table entries,
    // so we are free to pad "unsupported" entries with just all zeroes - the only requirement is that
    // "unsupported" PC values must not be in the table

    let mut result = Vec::with_capacity(supported_entries_for_family.len());
    for el in supported_entries_for_family.iter() {
        if let Some(supported) = el {
            let row = supported.flatten();
            result.push(row);
        } else {
            // NOTE: we do not use 0 here, but instead some value that doesn't pass range check and so can not be
            // a valid PC
            result.push([F::MINUS_ONE; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH]);
        }
    }

    result
}

#[cfg(test)]
mod test {
    use std::{alloc::Global, io::Read};

    use field::Mersenne31Field;

    use super::*;

    #[test]
    fn test_binary_preprocessing() {
        let mut file = std::fs::File::open("../examples/basic_fibonacci/app.text").unwrap();
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).unwrap();

        assert!(buffer.len() % 4 == 0, "text section is not aligned");

        let binary: Vec<u32> = buffer
            .as_chunks::<4>()
            .0
            .into_iter()
            .map(|el| u32::from_le_bytes(*el))
            .collect();

        let _ = process_binary_into_separate_tables::<Mersenne31Field, Global>(
            &binary,
            &opcodes_for_full_machine(),
            1 << 20,
            &[],
        );
    }
}
