use super::*;
use std::collections::{BTreeSet, HashMap};

use fft::GoodAllocator;
use field::PrimeField;
use riscv_transpiler::ir::DecodingOptions;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct ExecutorFamilyDecoderData {
    pub imm: u32,
    pub rs2_index: u16,
    pub rs1_index: u8,
    pub rd_index: u8,
    pub opcode_family_bits: u32,
    pub funct3: Option<u8>,
    pub funct7: Option<u8>,
}

impl Default for ExecutorFamilyDecoderData {
    fn default() -> Self {
        // We make a value that is self-consistent, and as family-agnostic as possible
        ExecutorFamilyDecoderData {
            imm: 0,
            rs1_index: 0,
            rs2_index: 0,
            rd_index: 0,
            funct3: None,
            funct7: None,
            opcode_family_bits: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DecoderTableEntry<F: PrimeField> {
    pub pc: [F; 2],
    pub rs1_index: F,
    pub rs2_index: F,
    pub rd_index: F,
    pub imm: [F; REGISTER_SIZE],
    pub funct3: Option<F>,
    pub funct7: Option<F>,
    pub circuit_family_extra_mask: F,
}

impl<F: PrimeField> DecoderTableEntry<F> {
    pub fn from_executor_family_data(pc: u32, executor_data: &ExecutorFamilyDecoderData) -> Self {
        Self {
            pc: [
                F::from_u32_unchecked(pc as u16 as u32),
                F::from_u32_unchecked(pc >> 16),
            ],
            rs1_index: F::from_u32_unchecked(executor_data.rs1_index as u32),
            rs2_index: F::from_u32_unchecked(executor_data.rs2_index as u32),
            rd_index: F::from_u32_unchecked(executor_data.rd_index as u32),
            imm: [
                F::from_u32_unchecked(executor_data.imm as u16 as u32),
                F::from_u32_unchecked(executor_data.imm >> 16),
            ],
            funct3: executor_data
                .funct3
                .map(|el| F::from_u32_unchecked(el as u32)),
            funct7: None,
            circuit_family_extra_mask: F::from_u32_unchecked(
                executor_data.opcode_family_bits as u32,
            ),
        }
    }

    pub fn flatten(&self) -> arrayvec::ArrayVec<F, EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH> {
        let mut result =
            arrayvec::ArrayVec::<F, EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH>::new();
        unsafe {
            result.try_extend_from_slice(&self.pc).unwrap_unchecked();
            result.try_push(self.rs1_index).unwrap_unchecked();
            result.try_push(self.rs2_index).unwrap_unchecked();
            result.try_push(self.rd_index).unwrap_unchecked();
            result.try_extend_from_slice(&self.imm).unwrap_unchecked();
            result
                .try_push(self.funct3.unwrap_or(F::ZERO))
                .unwrap_unchecked();
            assert!(self.funct7.is_none(), "funct7 is unused");
            result
                .try_push(self.circuit_family_extra_mask)
                .unwrap_unchecked();
        }

        result
    }
}

pub trait OpcodeFamilyDecoder: 'static + std::fmt::Debug {
    type BitmaskCircuitParser
    where
        Self: Sized;

    fn instruction_family_index(&self) -> u8;

    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()>; // either full decoder data, or "unsupported by this circuit"

    #[inline(always)]
    fn parse_for_oracle(&self, preprocessed_opcode: Instruction) -> ExecutorFamilyDecoderData {
        self.define_decoder_subspace(preprocessed_opcode)
            .unwrap_or(Default::default())
    }
}

// pub fn opcodes_for_full_machine() -> Vec<Box<dyn OpcodeFamilyDecoder>> {
//     vec![
//         Box::new(AddSubLuiAuipcMopDecoder),
//         Box::new(JumpSltBranchDecoder),
//         Box::new(ShiftBinaryCsrrwDecoder),
//         Box::new(MemoryFamilyDecoder),
//         Box::new(DivMulDecoder::<true>),
//     ]
// }

// pub fn opcodes_for_full_machine_with_unsigned_mul_div_only() -> Vec<Box<dyn OpcodeFamilyDecoder>> {
//     vec![
//         Box::new(AddSubLuiAuipcMopDecoder),
//         Box::new(JumpSltBranchDecoder::<true>),
//         Box::new(ShiftBinaryDecoder),
//         Box::new(MemoryFamilyDecoder),
//         Box::new(DivMulDecoder::<false>),
//     ]
// }

pub fn opcodes_for_full_machine_with_mem_word_access_specialization(
) -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder),
        Box::new(ShiftBinaryDecoder),
        Box::new(WordOnlyMemoryFamilyDecoder),
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        Box::new(DivMulDecoder::<true>),
    ]
}

pub fn opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(
) -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder),
        Box::new(ShiftBinaryDecoder),
        Box::new(WordOnlyMemoryFamilyDecoder),
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        Box::new(DivMulDecoder::<false>),
    ]
}

pub fn opcodes_for_reduced_machine() -> Vec<Box<dyn OpcodeFamilyDecoder>> {
    vec![
        Box::new(AddSubLuiAuipcMopDecoder),
        Box::new(JumpSltBranchDecoder),
        Box::new(ShiftBinaryDecoder),
        Box::new(WordOnlyMemoryFamilyDecoder),
    ]
}

// pub fn process_binary_into_separate_tables<F: PrimeField, A: GoodAllocator>(
//     binary: &[u32],
//     families: &[Box<dyn OpcodeFamilyDecoder>],
//     max_bytecode_size_words: usize,
//     supported_csrs: &[u16],
// ) -> HashMap<
//     u8,
//     Vec<Option<ExecutorFamilyDecoderData>, A>,
// > {
//     process_binary_into_separate_tables_ext::<F, false, A>(
//         binary,
//         families,
//         max_bytecode_size_words,
//         supported_csrs,
//     )
// }

pub fn process_binary_into_separate_tables_ext<
    F: PrimeField,
    OPT: DecodingOptions,
    const ALLOW_UNSUPPORTED: bool,
    A: GoodAllocator,
>(
    binary: &[u32],
    families: &[Box<dyn OpcodeFamilyDecoder>],
    bytecode_size_words: usize,
    supported_csrs: &[u16],
) -> HashMap<u8, Vec<Option<ExecutorFamilyDecoderData>, A>> {
    assert!(binary.len() <= bytecode_size_words, "bytecode is too long");
    let mut pc_set = BTreeSet::new();
    let mut result = HashMap::with_capacity(families.len());
    for family in families.iter() {
        let family_type = family.instruction_family_index();
        let witness_eval_data =
            preprocess_bytecode::<F, OPT, A>(&binary, bytecode_size_words, &family, supported_csrs);
        assert_eq!(witness_eval_data.len(), bytecode_size_words);
        for (idx, entry) in witness_eval_data.iter().enumerate() {
            if entry.is_some() {
                let is_unique = pc_set.insert(idx);
                assert!(is_unique);
            }
        }

        result.insert(family_type, witness_eval_data);
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

pub fn materialize_flattened_decoder_table_with_bitmask<F: PrimeField>(
    supported_entries_for_family: &[Option<ExecutorFamilyDecoderData>],
    fields_bitmask: &[bool],
) -> Vec<arrayvec::ArrayVec<F, EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH>> {
    assert!(supported_entries_for_family.len().is_power_of_two());
    assert_eq!(
        fields_bitmask.len(),
        EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH
    );
    assert!(fields_bitmask[0]); // at least PCs should be there
    assert!(fields_bitmask[1]);

    // log-derivative based lookup argument doesn't require any special ordering of the table entries,
    // so we are free to pad "unsupported" entries with just all zeroes - the only requirement is that
    // "unsupported" PC values must not be in the table

    let mut result = Vec::with_capacity(supported_entries_for_family.len());
    for (idx, el) in supported_entries_for_family.iter().enumerate() {
        let pc = idx * core::mem::size_of::<u32>();
        if let Some(supported) = el {
            let row =
                DecoderTableEntry::<F>::from_executor_family_data(pc as u32, supported).flatten();
            let mut selected_row = arrayvec::ArrayVec::new();
            for (mask, value) in fields_bitmask.iter().zip(row.into_iter()) {
                if *mask {
                    selected_row.push(value);
                }
            }
            result.push(selected_row);
        } else {
            // NOTE: we do not use 0 here, but instead some value that doesn't pass range check and so can not be
            // a valid PC
            let mut selected_row = arrayvec::ArrayVec::new();
            for mask in fields_bitmask.iter() {
                if *mask {
                    selected_row.push(F::MINUS_ONE);
                }
            }

            result.push(selected_row);
        }
    }

    result
}

pub fn preprocess_bytecode<F: PrimeField, OPT: DecodingOptions, A: GoodAllocator>(
    binary: &[u32],
    bytecode_size_words: usize,
    family: &Box<dyn OpcodeFamilyDecoder>,
    supported_csrs: &[u16],
) -> Vec<Option<ExecutorFamilyDecoderData>, A> {
    assert!(binary.len() <= bytecode_size_words);

    let preprocessed_bytecode =
        riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode::<OPT, false>(binary);
    let mut witness_eval_decoder_data = Vec::with_capacity_in(bytecode_size_words, A::default());
    witness_eval_decoder_data.resize(bytecode_size_words, None);

    for (i, opcode) in preprocessed_bytecode.iter().copied().enumerate() {
        let Ok(data) = family.define_decoder_subspace(opcode) else {
            continue;
        };
        if opcode.name == InstructionName::ZicsrDelegation {
            assert!(
                supported_csrs.contains(&(opcode.imm as u32 as u16)),
                "unsupported CSR 0x{:04x} at PC = 0x{:08x}",
                opcode.imm,
                i * core::mem::size_of::<u32>()
            );
        }

        witness_eval_decoder_data[i] = Some(data);
    }

    assert_eq!(witness_eval_decoder_data.len(), bytecode_size_words);

    witness_eval_decoder_data
}

#[cfg(test)]
mod test {
    use std::{alloc::Global, io::Read};

    use field::Mersenne31Field;
    use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;

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

        let _ = process_binary_into_separate_tables_ext::<
            Mersenne31Field,
            FullUnsignedMachineDecoderConfig,
            true,
            Global,
        >(
            &binary,
            &opcodes_for_full_machine_with_mem_word_access_specialization(),
            1 << 20,
            &[],
        );
    }
}
