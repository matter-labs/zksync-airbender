use std::collections::{BTreeSet, HashMap};

use field::PrimeField;

use super::super::constants::*;
use crate::cs::oracle::ExecutorFamilyDecoderData;
use crate::definitions::*;
use crate::definitions::{
    formally_parse_rs1_rs2_rd_props_for_tracer, funct3_bits, funct7_bits, get_opcode_bits,
};
use crate::machine::machine_configurations::create_table_for_rom_image;
use crate::tables::LookupTable;
use crate::types::Num;
use crate::{
    cs::circuit::Circuit,
    definitions::Variable,
    devices::risc_v_types::{InstructionType, NUM_INSTRUCTION_TYPES},
};

mod add_sub_lui_auipc_mop;
mod bytecode_preprocessor;
mod jump_slt_branch;
mod memory;
mod memory_subword_only;
mod memory_word_only;
mod mul_div;
mod shift_binop_csrrw;

pub use self::add_sub_lui_auipc_mop::*;
pub use self::bytecode_preprocessor::*;
pub use self::jump_slt_branch::*;
pub use self::memory::*;
pub use self::memory_subword_only::*;
pub use self::memory_word_only::*;
pub use self::mul_div::*;
pub use self::shift_binop_csrrw::*;

mod decoder_circuit;

pub use decoder_circuit::describe_decoder_cycle;

pub type InstructionFamilyBitmaskRepr = u8;

pub const NUM_DEFAULT_DECODER_BITS: usize = 1 + (NUM_INSTRUCTION_TYPES - 1); // generic validity flag + maskers for instruction types except R-type

pub trait InstructionFamilyBitmaskCircuitParser: 'static + std::fmt::Debug {
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self;
}

pub const INVALID_OPCODE_DEFAULTS: (bool, InstructionType, InstructionFamilyBitmaskRepr) =
    (false, InstructionType::RType, 0); // We do not need info about instruciton being R-type for decoder

pub trait OpcodeFamilyDecoder: 'static + std::fmt::Debug {
    type BitmaskCircuitParser: InstructionFamilyBitmaskCircuitParser
    where
        Self: Sized;

    fn instruction_family_index(&self) -> u8;

    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> (
        bool, // is valid instruction or not
        InstructionType,
        InstructionFamilyBitmaskRepr, // Instruction specific data
    );

    fn define_decoder_subspace_ext(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> (
        bool, // is valid instruction or not
        InstructionType,
        InstructionFamilyBitmaskRepr, // Instruction specific data
        (bool, bool), // (avoid sign extending for CSRRW (I-type formally), validate CSR)
    ) {
        let (a, b, c) = self.define_decoder_subspace(opcode, func3, func7);
        (a, b, c, (false, false))
    }

    fn parse_for_oracle(&self, opcode: u32) -> ExecutorFamilyDecoderData {
        let op = get_opcode_bits(opcode);
        let funct3 = funct3_bits(opcode);
        let funct7 = funct7_bits(opcode);
        let (is_valid, instr_type, opcode_family_bits, (avoid_i_type_sign_extend, _)) =
            self.define_decoder_subspace_ext(op, funct3, funct7);

        if is_valid == false {
            return Default::default();
        }

        let (rs1_index, rs2_index, rd_index) = formally_parse_rs1_rs2_rd_props_for_tracer(opcode);
        let funct3 = funct3_bits(opcode);
        let funct7 = funct7_bits(opcode);
        let rd_is_zero = rd_index == 0;
        let imm = instr_type.parse_imm(opcode, avoid_i_type_sign_extend);

        ExecutorFamilyDecoderData {
            imm,
            rs1_index,
            rs2_index,
            rd_index,
            rd_is_zero,
            funct3,
            funct7: Some(funct7),
            opcode_family_bits,
        }
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

pub fn decoder_data_for_opcodes(
    all_opcodes: &Vec<Box<dyn OpcodeFamilyDecoder>>,
) -> Vec<(bool, InstructionType, u8, InstructionFamilyBitmaskRepr)> {
    let mut result = vec![
        (
            true, // invalid
            InstructionType::RType,
            0,
            0,
        );
        1 << (7 + 3 + 7)
    ];

    for opcode in 0..(1u8 << 7) {
        for funct3 in 0..(1u8 << 3) {
            for funct7 in 0..(1u8 << 7) {
                let concatenated_key =
                    opcode as u32 + ((funct3 as u32) << 7) + ((funct7 as u32) << 10);

                let mut found = None;

                for supported_opcode in all_opcodes.iter() {
                    let (is_valid, instr_type, family_bitmask) =
                        supported_opcode.define_decoder_subspace(opcode, funct3, funct7);
                    if is_valid == false {
                        continue;
                    } else {
                        assert!(found.is_none());
                        let family = supported_opcode.instruction_family_index();
                        found = Some((false, instr_type, family, family_bitmask));
                    }
                }

                if let Some(data) = found {
                    result[concatenated_key as usize] = data;
                }
                // none of the opcodes could process such combination,
                // so we degrade to default one
            }
        }
    }

    result
}

pub fn produce_decoder_table_from_data<F: PrimeField>(
    data: Vec<(bool, InstructionType, u8, InstructionFamilyBitmaskRepr)>,
    id: u32,
) -> LookupTable<F, 3> {
    use crate::tables::*;

    let keys = key_for_continuous_log2_range(7 + 3 + 7);
    const TABLE_NAME: &'static str = "Decoder table";
    LookupTable::<F, 3>::create_table_from_key_and_key_generation_closure(
        &keys,
        TABLE_NAME.to_string(),
        1,
        move |key| {
            let input = key[0].as_u64_reduced();
            assert!(input < (1u64 << 17));

            let mut result = [F::ZERO; 3];
            // first result is just a family
            let (is_invalid, instr_type, opcode_family, family_bitmask) = data[input as usize];
            result[0] = F::from_u64_unchecked(opcode_family as u64);
            // next we form a bitmask - that is simply
            let mut bitmask = is_invalid as u64;
            if instr_type != InstructionType::RType {
                bitmask |= 1 << (instr_type as u64);
            }
            // and then family-specific part
            bitmask |= (family_bitmask as u64) << NUM_DEFAULT_DECODER_BITS;

            result[1] = F::from_u64_unchecked(bitmask);

            (input as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn full_machine_decoder_table<F: PrimeField>(table_id: u32) -> LookupTable<F, 3> {
    let all_opcodes = opcodes_for_full_machine();
    let data = decoder_data_for_opcodes(&all_opcodes);

    produce_decoder_table_from_data::<F>(data, table_id)
}

pub fn process_binary_into_separate_tables<F: PrimeField>(
    binary: &[u32],
    families: &[Box<dyn OpcodeFamilyDecoder>],
    max_bytecode_size_words: usize,
    supported_csrs: &[u16],
) -> HashMap<
    u8,
    (
        Vec<Option<DecoderTableEntry<F>>>,
        Vec<ExecutorFamilyDecoderData>,
    ),
> {
    assert!(
        binary.len() <= max_bytecode_size_words,
        "bytecode is too long"
    );
    let mut pc_set = BTreeSet::new();
    let mut result = HashMap::with_capacity(families.len());
    for family in families.iter() {
        let family_type = family.instruction_family_index();
        let (table, witness_eval_data) =
            preprocess_bytecode::<F>(&binary, max_bytecode_size_words, &family, supported_csrs);
        for (idx, entry) in table.iter().enumerate() {
            if entry.is_some() {
                let is_unique = pc_set.insert(idx);
                assert!(is_unique);
            }
        }

        result.insert(family_type, (table, witness_eval_data));
    }

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

    result
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
    use std::io::Read;

    use field::Mersenne31Field;

    use super::*;
    use crate::utils::serialize_to_file;

    const SECOND_WORD_BITS: usize = 4;

    #[test]
    fn compile_decoder_circuit() {
        use crate::tables::*;
        use ::field::Mersenne31Field;
        // now test compilation into AIR
        use crate::cs::cs_reference::BasicAssembly;
        use crate::one_row_compiler::OneRowCompiler;

        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        cs.add_table_with_content(
            TableType::OpTypeBitmask,
            LookupWrapper::Dimensional3(full_machine_decoder_table(
                TableType::OpTypeBitmask.to_table_id(),
            )),
        );
        create_decoder_circuit_table_driver_into_cs::<_, _, SECOND_WORD_BITS>(&mut cs, &[]); // particular image is not important here

        decoder_circuit::describe_decoder_cycle::<_, _, SECOND_WORD_BITS>(&mut cs);

        let (cs_output, _) = cs.finalize();

        dbg!(cs_output.num_of_variables);

        let compiler = OneRowCompiler::default();
        let compiled = compiler.compile_decoder_circuit(cs_output, 24);

        serialize_to_file(&compiled, "decoder_circuit_layout.json");
    }

    #[test]
    fn test_binary_preprocessing() {
        let mut file = std::fs::File::open("../examples/basic_fibonacci/app.text").unwrap();
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).unwrap();

        assert!(buffer.len() % 4 == 0, "text section is not aligned");

        let binary: Vec<u32> = buffer
            .array_chunks::<4>()
            .map(|el| u32::from_le_bytes(*el))
            .collect();

        let _ = process_binary_into_separate_tables::<Mersenne31Field>(
            &binary,
            &opcodes_for_full_machine(),
            1 << 20,
            &[],
        );
    }
}
