use super::*;
use crate::types::Boolean;

const ADD_OP_BIT: usize = 0;
const SUB_OP_BIT: usize = 1;
const AUIPC_OP_BIT: usize = 2;
const ADDMOD_BIT: usize = 3;
const SUBMOD_BIT: usize = 4;
const MULMOD_BIT: usize = 5;
const DELEGATION_BIT: usize = 6;
const NON_DETERMINISM_READ_BIT: usize = 7;

#[derive(Clone, Copy, Debug)]
pub struct AddSubLuiAuipcMopDecoder;

#[derive(Clone, Copy, Debug)]
pub struct AddSubLuiAuipcMopFamilyCircuitMask {
    inner: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS],
}

impl AddSubLuiAuipcMopFamilyCircuitMask {
    pub fn from_mask(mask: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS]) -> Self {
        Self { inner: mask }
    }

    // getters for our opcodes
    pub fn perform_add_addi_lui(&self) -> Boolean {
        self.inner[ADD_OP_BIT]
    }

    pub fn perform_sub(&self) -> Boolean {
        self.inner[SUB_OP_BIT]
    }

    pub fn perform_auipc(&self) -> Boolean {
        self.inner[AUIPC_OP_BIT]
    }

    pub fn perform_addmod(&self) -> Boolean {
        self.inner[ADDMOD_BIT]
    }

    pub fn perform_submod(&self) -> Boolean {
        self.inner[SUBMOD_BIT]
    }

    pub fn perform_mulmod(&self) -> Boolean {
        self.inner[MULMOD_BIT]
    }

    pub fn perform_delegation_call(&self) -> Boolean {
        self.inner[DELEGATION_BIT]
    }

    pub fn perform_non_determinism_read(&self) -> Boolean {
        self.inner[NON_DETERMINISM_READ_BIT]
    }
}

impl OpcodeFamilyDecoder for AddSubLuiAuipcMopDecoder {
    type BitmaskCircuitParser = AddSubLuiAuipcMopFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        let (mut rs1_index, mut rs2_index, mut rd_index) = (0, 0u16, 0);
        let mut imm = 0;
        let mut bitmask = 0u32;

        match preprocessed_opcode.name {
            InstructionName::Nop => {
                // still modeled as ADD, but registers and imm are 0
                bitmask |= 1 << ADD_OP_BIT;
            }
            InstructionName::Add => {
                assert_ne!(preprocessed_opcode.rd, 0);
                if preprocessed_opcode.imm != 0 {
                    assert_eq!(preprocessed_opcode.rs2, 0);
                }

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                imm = preprocessed_opcode.imm;
                bitmask |= 1 << ADD_OP_BIT;
            }
            InstructionName::Sub => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                bitmask |= 1 << SUB_OP_BIT;
            }
            InstructionName::Auipc => {
                assert_eq!(preprocessed_opcode.rs1, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);
                assert_ne!(preprocessed_opcode.rd, 0);

                rd_index = preprocessed_opcode.rd;
                imm = preprocessed_opcode.imm;
                bitmask |= 1 << AUIPC_OP_BIT;
            }
            InstructionName::ZimopAdd => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                bitmask |= 1 << ADDMOD_BIT;
            }
            InstructionName::ZimopSub => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                bitmask |= 1 << SUBMOD_BIT;
            }
            InstructionName::ZimopMul => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;
                bitmask |= 1 << MULMOD_BIT;
            }
            InstructionName::ZicsrDelegation => {
                assert_eq!(preprocessed_opcode.rs1, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);
                assert_eq!(preprocessed_opcode.rd, 0);
                assert_ne!(preprocessed_opcode.imm, 0);
                assert!(preprocessed_opcode.imm < 1 << 16);

                rs2_index = preprocessed_opcode.imm as u16;

                bitmask |= 1 << DELEGATION_BIT;
            }
            InstructionName::ZicsrNonDeterminismWrite => {
                assert_eq!(preprocessed_opcode.rs2, 0);
                assert_eq!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);
                // still modeled as ADD, but registers and imm are 0
                bitmask |= 1 << ADD_OP_BIT;
            }
            InstructionName::ZicsrNonDeterminismRead => {
                assert_eq!(preprocessed_opcode.rs1, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rd_index = preprocessed_opcode.rd;
                bitmask |= 1 << NON_DETERMINISM_READ_BIT;
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
            funct3: None,
            funct7: None,
            opcode_family_bits: bitmask,
        };

        Ok(decoded)
    }
}
