use super::*;
use crate::types::Boolean;

const SHIFT_BIT: usize = 0;
const BINARY_OP_BIT: usize = 1;

pub(crate) const FORMAL_SLL_FUNCT3: u8 = 0b001;
pub(crate) const FORMAL_SRL_FUNCT3: u8 = 0b010;
pub(crate) const FORMAL_SRA_FUNCT3: u8 = 0b011;
pub(crate) const FORMAL_ROL_FUNCT3: u8 = 0b100;
pub(crate) const FORMAL_ROR_FUNCT3: u8 = 0b100;

#[derive(Clone, Copy, Debug)]
pub struct ShiftBinaryDecoder;

#[derive(Clone, Copy, Debug)]
pub struct ShiftBinaryFamilyCircuitMask {
    inner: [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS],
}

impl ShiftBinaryFamilyCircuitMask {
    pub fn from_mask(mask: [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS]) -> Self {
        Self { inner: mask }
    }

    // getters for our opcodes
    pub fn perform_shift(&self) -> Boolean {
        self.inner[SHIFT_BIT]
    }

    pub fn perform_binary_op(&self) -> Boolean {
        self.inner[BINARY_OP_BIT]
    }
}

fn modify_immediate_for_binary_ops(imm: u32) -> u32 {
    let lowest_byte = imm as u8;
    let next_byte = (imm >> 8) as u8;

    (lowest_byte as u32) | ((next_byte as u32) << 16)
}

impl OpcodeFamilyDecoder for ShiftBinaryDecoder {
    type BitmaskCircuitParser = ShiftBinaryFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::SHIFT_BINARY_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        let (mut rs1_index, mut rs2_index, mut rd_index) = (0, 0u16, 0);
        let mut imm = 0;
        let mut bitmask = 0u32;
        let mut funct3 = None;

        match preprocessed_opcode.name {
            InstructionName::And => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                imm = modify_immediate_for_binary_ops(preprocessed_opcode.imm);
                funct3 = Some(AND_TABLE_ID as u8);
                bitmask |= 1 << BINARY_OP_BIT;
            }
            InstructionName::Or => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                imm = modify_immediate_for_binary_ops(preprocessed_opcode.imm);
                funct3 = Some(OR_TABLE_ID as u8);
                bitmask |= 1 << BINARY_OP_BIT;
            }
            InstructionName::Xor => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                imm = modify_immediate_for_binary_ops(preprocessed_opcode.imm);
                funct3 = Some(XOR_TABLE_ID as u8);
                bitmask |= 1 << BINARY_OP_BIT;
            }
            InstructionName::Sll => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                assert!(preprocessed_opcode.imm < 32);
                imm = preprocessed_opcode.imm;
                funct3 = Some(FORMAL_SLL_FUNCT3);
                bitmask |= 1 << SHIFT_BIT;
            }
            InstructionName::Srl => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                assert!(preprocessed_opcode.imm < 32);
                imm = preprocessed_opcode.imm;
                funct3 = Some(FORMAL_SRL_FUNCT3);
                bitmask |= 1 << SHIFT_BIT;
            }
            InstructionName::Sra => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                assert!(preprocessed_opcode.imm < 32);
                imm = preprocessed_opcode.imm;
                funct3 = Some(FORMAL_SRA_FUNCT3);
                bitmask |= 1 << SHIFT_BIT;
            }
            _ => {
                return Err(());
            }
        }

        let decoded = ExecutorFamilyDecoderData {
            imm,
            rs1_index,
            rs2_index,
            rd_index,
            funct3,
            funct7: None,
            opcode_family_bits: bitmask,
        };

        Ok(decoded)
    }
}
