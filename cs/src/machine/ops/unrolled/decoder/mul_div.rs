use super::*;
use crate::types::Boolean;

const IS_DIVISION_BIT: usize = 0;
const MUL_DIV_DIVU: usize = 1; // SIGNED
const UNSIGNED_MUL_DIVU: usize = 1; // UNSIGNED
const MUL_MULH_MULHSU_DIV_REM: usize = 2;
const MUL_MULH_DIV_REM: usize = 3;

#[derive(Clone, Copy, Debug)]
pub struct DivMulDecoder<const SUPPORT_SIGNED: bool>;

#[derive(Clone, Copy, Debug)]
pub struct DivMulFamilyCircuitMask<const SUPPORT_SIGNED: bool> {
    inner: [Boolean; MUL_DIV_FAMILY_NUM_FLAGS],
}

impl<const SUPPORT_SIGNED: bool> InstructionFamilyBitmaskCircuitParser
    for DivMulFamilyCircuitMask<SUPPORT_SIGNED>
{
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self {
        if SUPPORT_SIGNED {
            let inner =
                Boolean::split_into_bitmask::<_, _, MUL_DIV_FAMILY_NUM_FLAGS>(cs, Num::Var(input));
            Self { inner }
        } else {
            let mut inner = [Boolean::Constant(false); MUL_DIV_FAMILY_NUM_FLAGS];
            let [is_div_bit, mul_low_or_divu_bit] =
                Boolean::split_into_bitmask::<_, _, 2>(cs, Num::Var(input));
            inner[IS_DIVISION_BIT] = is_div_bit;
            inner[UNSIGNED_MUL_DIVU] = mul_low_or_divu_bit;
            Self { inner }
        }
    }
}

impl<const SUPPORT_SIGNED: bool> DivMulFamilyCircuitMask<SUPPORT_SIGNED> {
    // getters for our opcodes
    pub fn perform_division_group(&self) -> Boolean {
        self.inner[IS_DIVISION_BIT]
    }

    pub fn perform_rs1_signed(&self) -> Boolean {
        assert!(SUPPORT_SIGNED);
        self.inner[MUL_MULH_MULHSU_DIV_REM]
    }

    pub fn perform_rs2_signed(&self) -> Boolean {
        assert!(SUPPORT_SIGNED);
        self.inner[MUL_MULH_DIV_REM]
    }

    pub fn perform_mul_div_divu(&self) -> Boolean {
        assert!(SUPPORT_SIGNED);
        self.inner[MUL_DIV_DIVU]
    }

    pub fn perform_mul_divu(&self) -> Boolean {
        assert!(!SUPPORT_SIGNED);
        self.inner[UNSIGNED_MUL_DIVU]
    }
}

impl<const SUPPORT_SIGNED: bool> OpcodeFamilyDecoder for DivMulDecoder<SUPPORT_SIGNED> {
    type BitmaskCircuitParser = DivMulFamilyCircuitMask<SUPPORT_SIGNED>;

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX
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
        // const IS_DIVISION_BIT: usize = 0;
        // const MUL_MULH_MULHSU_DIV_REM: usize = 1;
        // const MUL_MULH_DIV_REM: usize = 2;
        // const MUL_DIV_DIVU: usize = 3;
        match (opcode, func3, func7) {
            (OPERATION_OP, 0b000, M_EXT_FUNCT7) => {
                // MUL
                instruction_type = InstructionType::RType;
                if SUPPORT_SIGNED {
                    repr |= 1 << MUL_MULH_MULHSU_DIV_REM;
                    repr |= 1 << MUL_MULH_DIV_REM;
                    repr |= 1 << MUL_DIV_DIVU;
                } else {
                    repr |= 1 << UNSIGNED_MUL_DIVU;
                }
            }
            (OPERATION_OP, 0b001, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // MULH
                instruction_type = InstructionType::RType;
                repr |= 1 << MUL_MULH_MULHSU_DIV_REM;
                repr |= 1 << MUL_MULH_DIV_REM;
            }
            (OPERATION_OP, 0b010, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // MULHSU
                instruction_type = InstructionType::RType;
                repr |= 1 << MUL_MULH_MULHSU_DIV_REM;
            }
            (OPERATION_OP, 0b011, M_EXT_FUNCT7) => {
                // MULHU
                // We avoid setting any bits, as this is always the default/negative case for all bits
                instruction_type = InstructionType::RType;
            }
            (OPERATION_OP, 0b100, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // DIV
                instruction_type = InstructionType::RType;
                repr |= 1 << IS_DIVISION_BIT;
                repr |= 1 << MUL_MULH_MULHSU_DIV_REM;
                repr |= 1 << MUL_MULH_DIV_REM;
                repr |= 1 << MUL_DIV_DIVU;
            }
            (OPERATION_OP, 0b101, M_EXT_FUNCT7) => {
                // DIVU
                instruction_type = InstructionType::RType;
                if SUPPORT_SIGNED {
                    repr |= 1 << IS_DIVISION_BIT;
                    repr |= 1 << MUL_DIV_DIVU;
                } else {
                    repr |= 1 << IS_DIVISION_BIT;
                    repr |= 1 << UNSIGNED_MUL_DIVU; // it's the same anyway
                }
            }
            (OPERATION_OP, 0b110, M_EXT_FUNCT7) if SUPPORT_SIGNED => {
                // REM
                instruction_type = InstructionType::RType;
                repr |= 1 << IS_DIVISION_BIT;
                repr |= 1 << MUL_MULH_MULHSU_DIV_REM;
                repr |= 1 << MUL_MULH_DIV_REM;
            }
            (OPERATION_OP, 0b111, M_EXT_FUNCT7) => {
                // REMU
                // same as for MULHU, it's the default case
                // except that it belongs to division group
                instruction_type = InstructionType::RType;
                repr |= 1 << IS_DIVISION_BIT;
            }
            _ => return INVALID_OPCODE_DEFAULTS,
        };

        return (true, instruction_type, repr);
    }
}
