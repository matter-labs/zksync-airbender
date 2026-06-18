use super::*;
use crate::types::Boolean;

const WRITE_BIT: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct WordOnlyMemoryFamilyDecoder;

#[derive(Clone, Copy, Debug)]
pub struct WordOnlyMemoryFamilyCircuitMask {
    inner: [Boolean; WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS],
}

impl WordOnlyMemoryFamilyCircuitMask {
    pub fn from_mask(mask: [Boolean; WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS]) -> Self {
        Self { inner: mask }
    }

    // getters for our opcodes
    pub fn perform_write(&self) -> Boolean {
        self.inner[WRITE_BIT]
    }
}

impl OpcodeFamilyDecoder for WordOnlyMemoryFamilyDecoder {
    type BitmaskCircuitParser = WordOnlyMemoryFamilyCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        let (mut rs1_index, mut rs2_index, mut rd_index) = (0, 0u16, 0);
        let mut imm = 0;
        let mut bitmask = 0u32;

        match preprocessed_opcode.name {
            InstructionName::Lw => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.rs2, 0);

                rs1_index = preprocessed_opcode.rs1;
                rd_index = preprocessed_opcode.rd;
                imm = preprocessed_opcode.imm;
            }
            InstructionName::Sw => {
                assert_eq!(preprocessed_opcode.rd, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                imm = preprocessed_opcode.imm;
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
            funct3: None,
            funct7: None,
            opcode_family_bits: bitmask,
        };

        Ok(decoded)
    }
}
