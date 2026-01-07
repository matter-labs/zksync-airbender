use super::*;
use crate::types::Boolean;

const SLL_BIT: usize = 0;
const SRL_BIT: usize = 1;
const SRA_BIT: usize = 2;
const BINARY_OP_BIT: usize = 3;
const CSRRW_BIT: usize = 4;
const USE_IMM_BIT: usize = 5;

#[derive(Clone, Copy, Debug)]
pub struct ShiftBinaryCsrrwDecoder;

#[derive(Clone, Copy, Debug)]
pub struct ShiftBinaryCsrrwFamilyCircuitMask {
    inner: [Boolean; SHIFT_BINARY_CSRRW_FAMILY_NUM_FLAGS],
}

impl InstructionFamilyBitmaskCircuitParser for ShiftBinaryCsrrwFamilyCircuitMask {
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self {
        let inner = Boolean::split_into_bitmask::<_, _, SHIFT_BINARY_CSRRW_FAMILY_NUM_FLAGS>(
            cs,
            Num::Var(input),
        );
        Self { inner }
    }
}

impl ShiftBinaryCsrrwFamilyCircuitMask {
    // getters for our opcodes
    pub fn perform_sll(&self) -> Boolean {
        self.inner[SLL_BIT]
    }

    pub fn perform_srl(&self) -> Boolean {
        self.inner[SRL_BIT]
    }

    pub fn perform_sra(&self) -> Boolean {
        self.inner[SRA_BIT]
    }

    pub fn perform_binary_op(&self) -> Boolean {
        self.inner[BINARY_OP_BIT]
    }

    pub fn perform_csrrw(&self) -> Boolean {
        self.inner[CSRRW_BIT]
    }

    pub fn use_imm(&self) -> Boolean {
        self.inner[USE_IMM_BIT]
    }
}

impl OpcodeFamilyDecoder for ShiftBinaryCsrrwDecoder {
    type BitmaskCircuitParser = ShiftBinaryCsrrwFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
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
        let (rs1_index, mut rs2_index, rd_index) =
            formally_parse_rs1_rs2_rd_props_for_tracer(opcode);
        let instruction_type;
        let mut validate_csr = false;

        match (op, func3, func7) {
            (OPERATION_OP_IMM, 0b001, 0) => {
                // SLLI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << SLL_BIT;
                repr |= 1 << USE_IMM_BIT;
            }
            (OPERATION_OP_IMM, 0b101, 0) => {
                // SRLI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << SRL_BIT;
                repr |= 1 << USE_IMM_BIT;
            }
            (OPERATION_OP_IMM, 0b101, 0b010_0000) => {
                // SRAI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << SRA_BIT;
                repr |= 1 << USE_IMM_BIT;
            }
            // (OPERATION_OP_IMM, 0b101, 0b011_0000) if SUPPORT_ROT => {
            //     // RORI
            // }
            (OPERATION_OP, 0b001, 0) => {
                // SLL
                instruction_type = InstructionType::RType;
                repr |= 1 << SLL_BIT;
            }
            (OPERATION_OP, 0b101, 0) => {
                // SRL
                instruction_type = InstructionType::RType;
                repr |= 1 << SRL_BIT;
            }
            (OPERATION_OP, 0b101, 0b010_0000) => {
                // SRA
                instruction_type = InstructionType::RType;
                repr |= 1 << SRA_BIT;
            }
            // (OPERATION_OP, 0b001, 0b011_0000) if SUPPORT_ROT => {
            //     // ROL
            // }
            // (OPERATION_OP, 0b101, 0b011_0000) if SUPPORT_ROT => {
            //     // ROR
            // }
            (OPERATION_OP, 0b111, 0b000_0000) => {
                // AND
                instruction_type = InstructionType::RType;
                repr |= 1 << BINARY_OP_BIT;
            }
            (OPERATION_OP_IMM, 0b111, _) => {
                // ANDI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BINARY_OP_BIT;
                repr |= 1 << USE_IMM_BIT;
            }
            (OPERATION_OP, 0b110, 0b000_0000) => {
                // OR
                instruction_type = InstructionType::RType;
                repr |= 1 << BINARY_OP_BIT;
            }
            (OPERATION_OP_IMM, 0b110, _) => {
                // ORI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BINARY_OP_BIT;
                repr |= 1 << USE_IMM_BIT;
            }
            (OPERATION_OP, 0b100, 0b000_0000) => {
                // XOR
                instruction_type = InstructionType::RType;
                repr |= 1 << BINARY_OP_BIT;
            }
            (OPERATION_OP_IMM, 0b100, _) => {
                // XORI
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << BINARY_OP_BIT;
                repr |= 1 << USE_IMM_BIT;
            }
            (OPERATION_SYSTEM, 0b001, _) => {
                // it's formallt I type, but we do not need sign-extension, so we will take
                // everything from funct7 from decoder

                // CSRRW
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, true);
                repr |= 1 << CSRRW_BIT;

                validate_csr = true;
                // also check that we only have rs1 == 0 or rd == 0, or both
                if imm == NON_DETERMINISM_CSR {
                    assert!(rs1_index == 0 || rs2_index == 0);
                } else {
                    // works for all our precompiles, and UNIMP opcode
                    assert!(rs1_index == 0);
                    assert!(rs2_index == 0);
                }
            }
            // (OPERATION_SYSTEM, 0b001, func7) if func7 & 0x40 == 0 => {
            //     // NOTE: we could avoid support CSR indexes that have top bit == 1 (and would be sign-extended by decoder)
            //     // into full integer. For that it's enough to enforce that top-word of immediate from decoder is 0,
            //     // or we can just check that top bit of func7 is 0 here

            //     // CSRRW
            //     instruction_type = InstructionType::IType;
            //     repr |= 1 << CSRRW_BIT;
            // }
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
            validate_csr_index_in_immediate: validate_csr,
        };
        Ok(extended)
    }
}
