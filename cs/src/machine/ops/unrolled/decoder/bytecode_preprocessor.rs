use super::*;
use crate::definitions::{EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH, REGISTER_SIZE};
use field::PrimeField;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DecoderTableEntry<F: PrimeField> {
    pub pc: [F; 2],
    pub rs1_index: F,
    pub rs2_index: F,
    pub rd_index: F,
    pub rd_is_zero: F,
    pub imm: [F; REGISTER_SIZE],
    pub funct3: F,
    // pub funct7: F,
    pub circuit_family_extra_mask: F,
}

impl<F: PrimeField> DecoderTableEntry<F> {
    pub fn flatten(&self) -> [F; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH] {
        [
            self.pc[0],
            self.pc[1],
            self.rs1_index,
            self.rs2_index,
            self.rd_index,
            self.rd_is_zero,
            self.imm[0],
            self.imm[1],
            self.funct3,
            self.circuit_family_extra_mask,
        ]
    }
}

pub fn preprocess_bytecode<F: PrimeField, A: GoodAllocator>(
    binary: &[u32],
    bytecode_size_words: usize,
    family: &Box<dyn OpcodeFamilyDecoder>,
    supported_csrs: &[u16],
) -> (
    Vec<Option<DecoderTableEntry<F>>, A>,
    Vec<ExecutorFamilyDecoderData, A>,
) {
    let mut table = Vec::with_capacity_in(bytecode_size_words, A::default());
    table.resize(bytecode_size_words, None);
    let mut witness_eval_decoder_data = Vec::with_capacity_in(bytecode_size_words, A::default());
    witness_eval_decoder_data.resize(bytecode_size_words, ExecutorFamilyDecoderData::default());

    assert!(binary.len() <= table.len());

    for (i, opcode) in binary.iter().copied().enumerate() {
        let pc = i * 4;
        let Ok(data) = family.define_decoder_subspace(opcode) else {
            continue;
        };

        if data.validate_csr_index_in_immediate {
            let csr = data.data.imm as u16;
            if supported_csrs.contains(&csr) == false {
                // not supported
                continue;
            }
        }

        witness_eval_decoder_data[i] = data.data;
        let decoded = data.data;

        let entry = DecoderTableEntry {
            pc: [
                F::from_u64_unchecked((pc as u64) & 0xffff),
                F::from_u64_unchecked(((pc >> 16) as u64) & 0xffff),
            ],
            rs1_index: F::from_u64_unchecked(decoded.rs1_index as u64),
            rs2_index: F::from_u64_unchecked(decoded.rs2_index as u64),
            rd_index: F::from_u64_unchecked(decoded.rd_index as u64),
            rd_is_zero: F::from_boolean(decoded.rd_is_zero),
            imm: [
                F::from_u64_unchecked((decoded.imm as u64) & 0xffff),
                F::from_u64_unchecked(((decoded.imm >> 16) as u64) & 0xffff),
            ],
            funct3: F::from_u64_unchecked(decoded.funct3 as u64),
            // funct7: F::from_u64_unchecked(funct7 as u64),
            circuit_family_extra_mask: F::from_u64_unchecked(decoded.opcode_family_bits as u64),
        };

        table[i] = Some(entry);
    }

    assert_eq!(table.len(), bytecode_size_words);
    assert_eq!(witness_eval_decoder_data.len(), bytecode_size_words);

    (table, witness_eval_decoder_data)
}
