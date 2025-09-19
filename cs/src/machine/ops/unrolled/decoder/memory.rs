use super::*;
use crate::types::Boolean;

const WRITE_BIT: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct MemoryFamilyDecoder;

#[derive(Clone, Copy, Debug)]
pub struct MemoryFamilyCircuitMask {
    inner: [Boolean; MEMORY_FAMILY_NUM_FLAGS],
}

impl InstructionFamilyBitmaskCircuitParser for MemoryFamilyCircuitMask {
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

impl MemoryFamilyCircuitMask {
    // getters for our opcodes
    pub fn perform_write(&self) -> Boolean {
        self.inner[WRITE_BIT]
    }
}

impl OpcodeFamilyDecoder for MemoryFamilyDecoder {
    type BitmaskCircuitParser = MemoryFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::LOAD_STORE_CIRCUIT_FAMILY_IDX
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
            (OPERATION_LOAD, 0b000, _) => {
                // LB
                instruction_type = InstructionType::IType;
            }
            (OPERATION_LOAD, 0b001, _) => {
                // LH
                instruction_type = InstructionType::IType;
            }
            (OPERATION_LOAD, 0b010, _) => {
                // LW
                instruction_type = InstructionType::IType;
            }
            (OPERATION_LOAD, 0b100, _) => {
                // LBU
                instruction_type = InstructionType::IType;
            }
            (OPERATION_LOAD, 0b101, _) => {
                // LHU
                instruction_type = InstructionType::IType;
            }
            (OPERATION_STORE, 0b000, _) => {
                // SB
                instruction_type = InstructionType::SType;
                repr |= 1 << WRITE_BIT;
            }
            (OPERATION_STORE, 0b001, _) => {
                // SH
                instruction_type = InstructionType::SType;
                repr |= 1 << WRITE_BIT;
            }
            (OPERATION_STORE, 0b010, _) => {
                // SW
                instruction_type = InstructionType::SType;
                repr |= 1 << WRITE_BIT;
            }
            // (OPERATION_LOAD, 0b000, _) if SUPPORT_SIGNED & SUPPORT_LESS_THAN_WORD => {
            //     // LB
            //     instruction_type = InstructionType::IType;
            //     repr |= 1 << SIGN_EXTEND_BIT;
            //     repr |= 1 << BYTE_ACCESS_BIT;
            // }
            // (OPERATION_LOAD, 0b001, _) if SUPPORT_SIGNED & SUPPORT_LESS_THAN_WORD => {
            //     // LH
            //     instruction_type = InstructionType::IType;
            //     repr |= 1 << SIGN_EXTEND_BIT;
            //     repr |= 1 << HALF_WORD_ACCESS_BIT;
            // }
            // (OPERATION_LOAD, 0b010, _) => {
            //     // LW
            //     instruction_type = InstructionType::IType;
            //     if SUPPORT_LESS_THAN_WORD {
            //         repr |= 1 << WORD_ACCESS_BIT;
            //     }
            // }
            // (OPERATION_LOAD, 0b100, _) if SUPPORT_LESS_THAN_WORD => {
            //     // LBU
            //     instruction_type = InstructionType::IType;
            //     repr |= 1 << BYTE_ACCESS_BIT;
            // }
            // (OPERATION_LOAD, 0b101, _) if SUPPORT_LESS_THAN_WORD => {
            //     // LHU
            //     instruction_type = InstructionType::IType;
            //     repr |= 1 << HALF_WORD_ACCESS_BIT;
            // }
            // (OPERATION_STORE, 0b000, _) if SUPPORT_LESS_THAN_WORD => {
            //     // SB
            //     instruction_type = InstructionType::SType;
            //     repr |= 1 << WRITE_BIT;
            //     repr |= 1 << BYTE_ACCESS_BIT;
            // }
            // (OPERATION_STORE, 0b001, _) if SUPPORT_LESS_THAN_WORD => {
            //     // SH
            //     instruction_type = InstructionType::SType;
            //     repr |= 1 << WRITE_BIT;
            //     repr |= 1 << HALF_WORD_ACCESS_BIT;
            // }
            // (OPERATION_STORE, 0b010, _) => {
            //     // SW
            //     instruction_type = InstructionType::SType;
            //     repr |= 1 << WRITE_BIT;
            //     if SUPPORT_LESS_THAN_WORD {
            //         repr |= 1 << WORD_ACCESS_BIT;
            //     }
            // }
            _ => return INVALID_OPCODE_DEFAULTS,
        };

        return (true, instruction_type, repr);
    }
}
