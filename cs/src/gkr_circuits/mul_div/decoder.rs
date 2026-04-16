use super::*;
use crate::types::Boolean;

const IS_MUL_BIT: usize = 0;
const IS_MULHU_BIT: usize = 1;
const IS_DIVU_BIT: usize = 2;
const IS_REMU_BIT: usize = 3;

#[derive(Clone, Copy, Debug)]
pub struct DivMulDecoder<const SUPPORT_SIGNED: bool>;

#[derive(Clone, Copy, Debug)]
pub struct DivMulFamilyCircuitMask<const SUPPORT_SIGNED: bool> {
    inner: [Boolean; MUL_DIV_FAMILY_NUM_FLAGS],
}

impl<const SUPPORT_SIGNED: bool> DivMulFamilyCircuitMask<SUPPORT_SIGNED> {
    pub fn from_mask(mask: &[Boolean]) -> Self {
        if SUPPORT_SIGNED {
            assert_eq!(mask.len(), MUL_DIV_FAMILY_NUM_FLAGS);
            Self {
                inner: mask.try_into().unwrap(),
            }
        } else {
            assert_eq!(mask.len(), UNSIGNED_MUL_DIV_FAMILY_NUM_FLAGS);
            Self {
                inner: core::array::from_fn(|i| {
                    if i < mask.len() {
                        mask[i]
                    } else {
                        Boolean::Constant(false)
                    }
                }),
            }
        }
    }
}

impl<const SUPPORT_SIGNED: bool> DivMulFamilyCircuitMask<SUPPORT_SIGNED> {
    // getters for our opcodes
    pub fn is_mul(&self) -> Boolean {
        self.inner[IS_MUL_BIT]
    }

    pub fn is_mulhu(&self) -> Boolean {
        self.inner[IS_MULHU_BIT]
    }

    pub fn is_divu(&self) -> Boolean {
        self.inner[IS_DIVU_BIT]
    }

    pub fn is_remu(&self) -> Boolean {
        self.inner[IS_REMU_BIT]
    }
}

// NOTE: even though signed division has a convention on RD value in cases of overflows,
// they are still pure, so we do not care if rd == 0
impl<const SUPPORT_SIGNED: bool> OpcodeFamilyDecoder for DivMulDecoder<SUPPORT_SIGNED> {
    type BitmaskCircuitParser = DivMulFamilyCircuitMask<SUPPORT_SIGNED>;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        let (mut rs1_index, mut rs2_index, mut rd_index) = (0, 0u16, 0);
        let imm = 0;
        let mut bitmask = 0u32;

        match preprocessed_opcode.name {
            InstructionName::Mul => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                bitmask |= 1 << IS_MUL_BIT;
            }
            InstructionName::Mulh if SUPPORT_SIGNED => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                todo!();
            }
            InstructionName::Mulhsu if SUPPORT_SIGNED => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                todo!();
            }
            InstructionName::Mulhu => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                bitmask |= 1 << IS_MULHU_BIT;
            }
            InstructionName::Div if SUPPORT_SIGNED => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                todo!();
            }
            InstructionName::Divu => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                bitmask |= 1 << IS_DIVU_BIT;
            }
            InstructionName::Rem if SUPPORT_SIGNED => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                todo!();
            }
            InstructionName::Remu => {
                assert_ne!(preprocessed_opcode.rd, 0);
                assert_eq!(preprocessed_opcode.imm, 0);

                rs1_index = preprocessed_opcode.rs1;
                rs2_index = preprocessed_opcode.rs2 as u16;
                rd_index = preprocessed_opcode.rd;

                bitmask |= 1 << IS_REMU_BIT;
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
