use super::*;
use crate::types::Boolean;

pub const ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS: usize = 8;

const ADD_OP_BIT: usize = 0;
const ADDI_OP_BIT: usize = 1;
const SUB_OP_BIT: usize = 2;
const LUI_OP_BIT: usize = 3;
const AUIPC_OP_BIT: usize = 4;
const ADDMOD_BIT: usize = 5;
const SUBMOD_BIT: usize = 6;
const MULMOD_BIT: usize = 7;

#[derive(Clone, Copy, Debug)]
pub struct AddSubLuiAuipcMopDecoder;

#[derive(Clone, Copy, Debug)]
pub struct AddSubLuiAuipcMopFamilyCircuitMask {
    inner: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS],
}

impl InstructionFamilyBitmaskCircuitParser for AddSubLuiAuipcMopFamilyCircuitMask {
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self {
        let inner = Boolean::split_into_bitmask::<_, _, ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS>(
            cs,
            Num::Var(input),
        );
        Self { inner }
    }
}

impl AddSubLuiAuipcMopFamilyCircuitMask {
    // getters for our opcodes
    pub fn perform_add(&self) -> Boolean {
        self.inner[ADD_OP_BIT]
    }

    pub fn perform_addi(&self) -> Boolean {
        self.inner[ADDI_OP_BIT]
    }

    pub fn perform_sub(&self) -> Boolean {
        self.inner[SUB_OP_BIT]
    }

    pub fn perform_lui(&self) -> Boolean {
        self.inner[LUI_OP_BIT]
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
}

impl OpcodeFamilyDecoder for AddSubLuiAuipcMopDecoder {
    type BitmaskCircuitParser = AddSubLuiAuipcMopFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> (
        bool, // is valid instruction or not
        InstructionType,
        InstructionFamilyBitmaskRepr, // Instruction specific data
    ) {
        let mut repr = 0u32;
        let instruction_type;
        match (opcode, func3, func7) {
            (OPERATION_OP, 0b000, 0b000_0000) => {
                // ADD
                instruction_type = InstructionType::RType;
                repr |= 1 << ADD_OP_BIT;
            }
            (OPERATION_OP_IMM, 0b000, _) => {
                // ADDI
                instruction_type = InstructionType::IType;
                repr |= 1 << ADDI_OP_BIT;
            }
            (OPERATION_OP, 0b000, 0b010_0000) => {
                // SUB
                instruction_type = InstructionType::RType;
                repr |= 1 << SUB_OP_BIT;
            }
            (OPERATION_LUI, _, _) => {
                // LUI
                instruction_type = InstructionType::UType;
                repr |= 1 << LUI_OP_BIT;
            }
            (OPERATION_AUIPC, _, _) => {
                // AUIPC
                instruction_type = InstructionType::UType;
                repr |= 1 << AUIPC_OP_BIT;
            }
            (OPERATION_SYSTEM, 0b100, 0b1000001) => {
                // ADDMOD
                instruction_type = InstructionType::RType;
                repr |= 1 << ADDMOD_BIT;
            }
            (OPERATION_SYSTEM, 0b100, 0b1000011) => {
                // SUBMOD
                instruction_type = InstructionType::RType;
                repr |= 1 << SUBMOD_BIT;
            }
            (OPERATION_SYSTEM, 0b100, 0b1000101) => {
                // MULMOD
                instruction_type = InstructionType::RType;
                repr |= 1 << MULMOD_BIT;
            }
            _ => return INVALID_OPCODE_DEFAULTS,
        };

        return (true, instruction_type, repr);
    }
}
