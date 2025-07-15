use super::*;
use crate::types::Boolean;

const WRITE_BIT: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct WordOnlyMemoryFamilyDecoder;

#[derive(Clone, Copy, Debug)]
pub struct WordOnlyMemoryFamilyCircuitMask {
    inner: [Boolean; WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS],
}

impl InstructionFamilyBitmaskCircuitParser for WordOnlyMemoryFamilyCircuitMask {
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

impl WordOnlyMemoryFamilyCircuitMask {
    // getters for our opcodes
    pub fn perform_write(&self) -> Boolean {
        self.inner[WRITE_BIT]
    }
}

impl OpcodeFamilyDecoder for WordOnlyMemoryFamilyDecoder {
    type BitmaskCircuitParser = WordOnlyMemoryFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        WORD_ONLY_MEMORY_FAMILY_INDEX
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
            (OPERATION_LOAD, 0b010, _) => {
                // LW
                instruction_type = InstructionType::IType;
            }
            (OPERATION_STORE, 0b010, _) => {
                // SW
                instruction_type = InstructionType::SType;
                repr |= 1 << WRITE_BIT;
            }
            _ => return INVALID_OPCODE_DEFAULTS,
        };

        return (true, instruction_type, repr);
    }
}
