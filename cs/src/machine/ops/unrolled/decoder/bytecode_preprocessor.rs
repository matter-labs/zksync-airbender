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

pub fn preprocess_bytecode<F: PrimeField>(
    binary: &[u32],
    max_bytecode_size_words: usize,
    family: &Box<dyn OpcodeFamilyDecoder>,
    supported_csrs: &[u16],
) -> (
    Vec<Option<DecoderTableEntry<F>>>,
    Vec<ExecutorFamilyDecoderData>,
) {
    use crate::definitions::*;
    let mut table = vec![None; max_bytecode_size_words];
    let mut witness_eval_decoder_data =
        vec![ExecutorFamilyDecoderData::default(); max_bytecode_size_words];

    assert!(binary.len() < table.len());

    for (i, opcode) in binary.iter().copied().enumerate() {
        let pc = i * 4;
        let op = get_opcode_bits(opcode);
        let funct3 = funct3_bits(opcode);
        let funct7 = funct7_bits(opcode);
        let (is_valid, instr_type, mask, (avoid_i_type_sign_extend, validate_csr)) =
            family.define_decoder_subspace_ext(op, funct3, funct7);
        if avoid_i_type_sign_extend {
            assert!(instr_type == InstructionType::IType);
        }
        if is_valid == false {
            // not supported
            continue;
        }

        // now we need to get formal rs1/rs2/rd, check that rd is 0, parse formal immediate
        let (rs1, rs2, rd) = formally_parse_rs1_rs2_rd_props_for_tracer(opcode);
        let imm = instr_type.parse_imm(opcode, avoid_i_type_sign_extend);

        if validate_csr {
            let csr = imm as u16;
            if supported_csrs.contains(&csr) == false {
                // not supported
                continue;
            }
        }

        let decoder_entry = ExecutorFamilyDecoderData {
            imm,
            rs1_index: rs1,
            rs2_index: rs2,
            rd_index: rd,
            rd_is_zero: rd == 0,
            funct3,
            funct7: None,
            opcode_family_bits: mask,
        };
        witness_eval_decoder_data[i] = decoder_entry;

        let entry = DecoderTableEntry {
            pc: [
                F::from_u64_unchecked((pc as u64) & 0xffff),
                F::from_u64_unchecked(((pc >> 16) as u64) & 0xffff),
            ],
            rs1_index: F::from_u64_unchecked(rs1 as u64),
            rs2_index: F::from_u64_unchecked(rs2 as u64),
            rd_index: F::from_u64_unchecked(rd as u64),
            rd_is_zero: F::from_boolean(rd == 0),
            imm: [
                F::from_u64_unchecked((imm as u64) & 0xffff),
                F::from_u64_unchecked(((imm >> 16) as u64) & 0xffff),
            ],
            funct3: F::from_u64_unchecked(funct3 as u64),
            // funct7: F::from_u64_unchecked(funct7 as u64),
            circuit_family_extra_mask: F::from_u64_unchecked(mask as u64),
        };

        table[i] = Some(entry);
    }

    (table, witness_eval_decoder_data)
}
