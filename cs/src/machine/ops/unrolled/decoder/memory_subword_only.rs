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
        SUBWORD_ONLY_MEMORY_FAMILY_INDEX
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
        let mut repr = 0u8;
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
            _ => return INVALID_OPCODE_DEFAULTS,
        };

        return (true, instruction_type, repr);
    }
}
