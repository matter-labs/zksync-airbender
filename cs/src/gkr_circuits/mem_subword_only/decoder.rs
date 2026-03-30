use super::*;
use crate::types::Boolean;

const WRITE_BIT: usize = 0;
const BYTE_BIT: usize = 1;
const SIGNEXTEND_BIT: usize = 2;

const LB_FUNCT3: u8 = 0b000;
const LH_FUNCT3: u8 = 0b001;
const LBU_FUNCT3: u8 = 0b100;
const LHU_FUNCT3: u8 = 0b101;
const SB_FUNCT3: u8 = 0b000;
const SH_FUNCT3: u8 = 0b001;

#[derive(Clone, Copy, Debug)]
pub struct SubwordOnlyMemoryFamilyDecoder;

#[derive(Clone, Copy, Debug)]
pub struct SubwordOnlyMemoryFamilyCircuitMask {
    inner: [Boolean; SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS],
}

impl SubwordOnlyMemoryFamilyCircuitMask {
    pub fn from_mask(mask: [Boolean; SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS]) -> Self {
        Self { inner: mask }
    }

    // getters for our opcodes
    pub fn perform_write(&self) -> Boolean {
        self.inner[WRITE_BIT]
    }

    pub fn perform_byte_operation(&self) -> Boolean {
        self.inner[BYTE_BIT]
    }

    pub fn perform_sign_extension(&self) -> Boolean {
        self.inner[SIGNEXTEND_BIT]
    }
}

impl OpcodeFamilyDecoder for SubwordOnlyMemoryFamilyDecoder {
    type BitmaskCircuitParser = SubwordOnlyMemoryFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX
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
            InstructionName::Lb => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);

                rs1_index = preprocessed_opcode.rs1;
                rd_index = preprocessed_opcode.rd;
                funct3 = Some(LB_FUNCT3);
                imm = preprocessed_opcode.imm;
                bitmask |= 1 << BYTE_BIT;
                bitmask |= 1 << SIGNEXTEND_BIT;
            }
            InstructionName::Lbu => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);

                rs1_index = preprocessed_opcode.rs1;
                rd_index = preprocessed_opcode.rd;
                funct3 = Some(LBU_FUNCT3);
                imm = preprocessed_opcode.imm;
                bitmask |= 1 << BYTE_BIT;
            }
            InstructionName::Lh => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);

                rs1_index = preprocessed_opcode.rs1;
                rd_index = preprocessed_opcode.rd;
                funct3 = Some(LH_FUNCT3);
                imm = preprocessed_opcode.imm;
                bitmask |= 1 << SIGNEXTEND_BIT;
            }
            InstructionName::Lhu => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);

                rs1_index = preprocessed_opcode.rs1;
                rd_index = preprocessed_opcode.rd;
                funct3 = Some(LHU_FUNCT3);
                imm = preprocessed_opcode.imm;
            }
            InstructionName::Sb => {
                assert_eq!(preprocessed_opcode.rd, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                imm = preprocessed_opcode.imm;
                funct3 = Some(SB_FUNCT3);
                bitmask |= 1 << WRITE_BIT;
                bitmask |= 1 << BYTE_BIT;
            }
            InstructionName::Sh => {
                assert_eq!(preprocessed_opcode.rd, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                imm = preprocessed_opcode.imm;
                funct3 = Some(SH_FUNCT3);
                bitmask |= 1 << WRITE_BIT;
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
