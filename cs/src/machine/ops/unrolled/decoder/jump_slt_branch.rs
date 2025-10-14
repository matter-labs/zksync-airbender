use super::*;
use crate::types::Boolean;

const JAL_BIT: usize = 0;
const JALR_BIT: usize = 1;
const SLT_BIT: usize = 2;
const SLTI_BIT: usize = 3;
const BRANCH_BIT: usize = 4;

#[derive(Clone, Copy, Debug)]
pub struct JumpSltBranchDecoder<const SUPPORT_SIGNED: bool>;

#[derive(Clone, Copy, Debug)]
pub struct JumpSltBranchFamilyCircuitMask<const SUPPORT_SIGNED: bool> {
    inner: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
}

impl<const SUPPORT_SIGNED: bool> InstructionFamilyBitmaskCircuitParser
    for JumpSltBranchFamilyCircuitMask<SUPPORT_SIGNED>
{
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self {
        let inner = Boolean::split_into_bitmask::<_, _, JUMP_SLT_BRANCH_FAMILY_NUM_BITS>(
            cs,
            Num::Var(input),
        );
        Self { inner }
    }
}

impl<const SUPPORT_SIGNED: bool> JumpSltBranchFamilyCircuitMask<SUPPORT_SIGNED> {
    // getters for our opcodes
    pub fn perform_jal(&self) -> Boolean {
        self.inner[JAL_BIT]
    }

    pub fn perform_jalr(&self) -> Boolean {
        self.inner[JALR_BIT]
    }

    pub fn perform_slt(&self) -> Boolean {
        self.inner[SLT_BIT]
    }

    pub fn perform_slti(&self) -> Boolean {
        self.inner[SLTI_BIT]
    }

    pub fn perform_branch(&self) -> Boolean {
        self.inner[BRANCH_BIT]
    }
}

impl<const SUPPORT_SIGNED: bool> OpcodeFamilyDecoder for JumpSltBranchDecoder<SUPPORT_SIGNED> {
    type BitmaskCircuitParser = JumpSltBranchFamilyCircuitMask<SUPPORT_SIGNED>;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX
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
            (OPERATION_JAL, _, _) => {
                // JAL
                instruction_type = InstructionType::JType;
                repr |= 1 << JAL_BIT;
            }
            (OPERATION_JALR, 0b000, _) => {
                // JALR
                instruction_type = InstructionType::IType;
                repr |= 1 << JALR_BIT;
            }
            (OPERATION_OP_IMM, 0b010, _) if SUPPORT_SIGNED => {
                // SLTI
                instruction_type = InstructionType::IType;
                repr |= 1 << SLTI_BIT;
            }
            (OPERATION_OP_IMM, 0b011, _) => {
                // SLTIU
                instruction_type = InstructionType::IType;
                repr |= 1 << SLTI_BIT;
            }
            (OPERATION_OP, 0b010, 0) if SUPPORT_SIGNED => {
                // SLT
                instruction_type = InstructionType::RType;
                repr |= 1 << SLT_BIT;
            }
            (OPERATION_OP, 0b011, 0) => {
                // SLTU
                instruction_type = InstructionType::RType;
                repr |= 1 << SLT_BIT;
            }
            (OPERATION_BRANCH, 0b000, _) => {
                // BEQ
                instruction_type = InstructionType::BType;
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b001, _) => {
                // BNE
                instruction_type = InstructionType::BType;
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b100, _) if SUPPORT_SIGNED => {
                // BLT
                instruction_type = InstructionType::BType;
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b101, _) if SUPPORT_SIGNED => {
                // BGE
                instruction_type = InstructionType::BType;
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b110, _) => {
                // BLTU
                instruction_type = InstructionType::BType;
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b111, _) => {
                // BGEU
                instruction_type = InstructionType::BType;
                repr |= 1 << BRANCH_BIT;
            }
            _ => return INVALID_OPCODE_DEFAULTS,
        };

        return (true, instruction_type, repr);
    }
}
