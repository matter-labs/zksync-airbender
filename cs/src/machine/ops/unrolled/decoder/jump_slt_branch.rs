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
        opcode: u32,
    ) -> Result<ExecutorFamilyDecoderExtendedData, ()> {
        let mut repr = 0u32;
        let op = get_opcode_bits(opcode);
        let func3 = funct3_bits(opcode);
        let func7 = funct7_bits(opcode);
        let mut imm = 0;
        let (mut rs1_index, mut rs2_index, mut rd_index) =
            formally_parse_rs1_rs2_rd_props_for_tracer(opcode);
        let instruction_type;

        match (op, func3, func7) {
            (OPERATION_JAL, _, _) => {
                // JAL
                rs1_index = 0;
                rs2_index = 0;
                instruction_type = InstructionType::JType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << JAL_BIT;
            }
            (OPERATION_JALR, 0b000, _) => {
                // JALR
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << JALR_BIT;
            }
            (OPERATION_OP_IMM, 0b010, _) if SUPPORT_SIGNED => {
                // SLTI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << SLTI_BIT;
            }
            (OPERATION_OP_IMM, 0b011, _) => {
                // SLTIU
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
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
                rd_index = 0;
                instruction_type = InstructionType::BType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b001, _) => {
                // BNE
                rd_index = 0;
                instruction_type = InstructionType::BType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b100, _) if SUPPORT_SIGNED => {
                // BLT
                rd_index = 0;
                instruction_type = InstructionType::BType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b101, _) if SUPPORT_SIGNED => {
                // BGE
                rd_index = 0;
                instruction_type = InstructionType::BType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b110, _) => {
                // BLTU
                rd_index = 0;
                instruction_type = InstructionType::BType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BRANCH_BIT;
            }
            (OPERATION_BRANCH, 0b111, _) => {
                // BGEU
                rd_index = 0;
                instruction_type = InstructionType::BType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BRANCH_BIT;
            }
            _ => {
                return Err(());
            }
        };

        let rd_is_zero = rd_index == 0;

        let decoded = ExecutorFamilyDecoderData {
            imm,
            rs1_index,
            rs2_index,
            rd_index,
            rd_is_zero,
            funct3: func3,
            funct7: Some(func7),
            opcode_family_bits: repr,
        };
        let extended = ExecutorFamilyDecoderExtendedData {
            data: decoded,
            instruction_format: instruction_type,
            validate_csr_index_in_immediate: false,
        };
        Ok(extended)
    }
}
