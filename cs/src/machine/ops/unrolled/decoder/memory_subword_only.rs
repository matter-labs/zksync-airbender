use super::*;
use crate::types::Boolean;

const WRITE_BIT: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct SubwordOnlyMemoryFamilyDecoder;

#[derive(Clone, Copy, Debug)]
pub struct SubwordOnlyMemoryFamilyCircuitMask {
    inner: [Boolean; SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS],
}

impl InstructionFamilyBitmaskCircuitParser for SubwordOnlyMemoryFamilyCircuitMask {
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self {
        use crate::constraint::Term;
        // NOTE: even though it's 1-bit mask, we still constraint that input is indeed boolean
        // as in case of padding rows malicious prover can substitute garbage here,
        // while we assume that it's a true bit everywhere
        cs.add_constraint((Term::from(1) - Term::from(input)) * Term::from(input));
        Self {
            inner: [Boolean::Is(input)],
        }
    }
}

impl SubwordOnlyMemoryFamilyCircuitMask {
    // getters for our opcodes
    pub fn perform_write(&self) -> Boolean {
        self.inner[WRITE_BIT]
    }
}

impl OpcodeFamilyDecoder for SubwordOnlyMemoryFamilyDecoder {
    type BitmaskCircuitParser = SubwordOnlyMemoryFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX
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
        let (rs1_index, mut rs2_index, mut rd_index) =
            formally_parse_rs1_rs2_rd_props_for_tracer(opcode);
        let instruction_type;

        match (op, func3, func7) {
            (OPERATION_LOAD, 0b000, _) => {
                // LB
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
            }
            (OPERATION_LOAD, 0b001, _) => {
                // LH
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
            }
            (OPERATION_LOAD, 0b100, _) => {
                // LBU
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
            }
            (OPERATION_LOAD, 0b101, _) => {
                // LHU
                rs2_index = 0;
                instruction_type = InstructionType::IType;
                imm = instruction_type.parse_imm(opcode, false);
            }
            (OPERATION_STORE, 0b000, _) => {
                // SB
                rd_index = 0;
                instruction_type = InstructionType::SType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << WRITE_BIT;
            }
            (OPERATION_STORE, 0b001, _) => {
                // SH
                rd_index = 0;
                instruction_type = InstructionType::SType;
                imm = instruction_type.parse_imm(opcode, false);
                repr |= 1 << WRITE_BIT;
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
