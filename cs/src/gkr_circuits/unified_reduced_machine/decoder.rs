use super::*;
use crate::gkr_circuits::add_sub_family::{
    AddSubLuiAuipcMopDecoder, AddSubLuiAuipcMopFamilyCircuitMask,
};
use crate::gkr_circuits::binary_shifts_family::{ShiftBinaryDecoder, ShiftBinaryFamilyCircuitMask};
use crate::gkr_circuits::jump_branch_slt_family::{
    JumpSltBranchDecoder, JumpSltBranchFamilyCircuitMask,
};
use crate::gkr_circuits::mem_word_only::WordOnlyMemoryFamilyDecoder;
use crate::types::Boolean;

use super::circuit::{
    FAMILY_1_FLAG_OFFSET as F1_OFFSET, FAMILY_2_FLAG_OFFSET as F2_OFFSET,
    FAMILY_3_FLAG_OFFSET as F3_OFFSET, FAMILY_4_FLAG_OFFSET as F4_OFFSET,
    UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};

/// Family 4 in the unified bitmask is one-hot LW/SW (2 bits), not the standalone
/// 1-bit `is_store` encoding. See `circuit.rs` doc comment for rationale.
const F4_LW_BIT: usize = F4_OFFSET;
const F4_SW_BIT: usize = F4_OFFSET + 1;

/// The Family-4 standalone decoder produces `opcode_family_bits = 0` for LW and
/// `= 1` for SW (bit 0 = is_store).
const F4_STANDALONE_IS_STORE_BIT: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct UnifiedReducedMachineDecoder;

#[derive(Clone, Copy, Debug)]
pub struct UnifiedReducedMachineFamilyCircuitMask {
    add_sub_lui_auipc_mop_bits: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS],
    jump_branch_slt_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
    binary_shifts_bits: [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS],
    is_lw: Boolean,
    is_sw: Boolean,
}

impl UnifiedReducedMachineFamilyCircuitMask {
    pub fn from_full_mask(bitmask: [Boolean; UNIFIED_REDUCED_MACHINE_NUM_FLAGS]) -> Self {
        Self {
            add_sub_lui_auipc_mop_bits: std::array::from_fn(|i| bitmask[F1_OFFSET + i]),
            jump_branch_slt_bits: std::array::from_fn(|i| bitmask[F2_OFFSET + i]),
            binary_shifts_bits: std::array::from_fn(|i| bitmask[F3_OFFSET + i]),
            is_lw: bitmask[F4_LW_BIT],
            is_sw: bitmask[F4_SW_BIT],
        }
    }

    pub fn add_sub_lui_auipc_mop(&self) -> AddSubLuiAuipcMopFamilyCircuitMask {
        AddSubLuiAuipcMopFamilyCircuitMask::from_mask(self.add_sub_lui_auipc_mop_bits)
    }

    pub fn jump_branch_slt(&self) -> JumpSltBranchFamilyCircuitMask {
        JumpSltBranchFamilyCircuitMask::from_mask(self.jump_branch_slt_bits)
    }

    pub fn binary_shifts(&self) -> ShiftBinaryFamilyCircuitMask {
        ShiftBinaryFamilyCircuitMask::from_mask(self.binary_shifts_bits)
    }

    pub fn is_lw(&self) -> Boolean {
        self.is_lw
    }

    pub fn is_sw(&self) -> Boolean {
        self.is_sw
    }

    pub fn add_sub_lui_auipc_mop_bits(&self) -> [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS] {
        self.add_sub_lui_auipc_mop_bits
    }

    pub fn jump_branch_slt_bits(&self) -> [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS] {
        self.jump_branch_slt_bits
    }

    pub fn binary_shifts_bits(&self) -> [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS] {
        self.binary_shifts_bits
    }
}

impl OpcodeFamilyDecoder for UnifiedReducedMachineDecoder {
    /// The unified circuit has no per-instance circuit mask parser since the bitmask
    /// layout spans all four reduced-machine families; downstream code constructs
    /// per-family `FamilyCircuitMask` views by slicing the unified bitmask.
    type BitmaskCircuitParser = ();

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX
    }

    /// Dispatch the opcode to whichever family decoder accepts it, then shift the
    /// per-family bits into the appropriate region of the unified bitmask. For
    /// Family 4, also translates the 1-bit `is_store` standalone encoding into the
    /// 2-bit one-hot `LW`/`SW` encoding the unified body expects.
    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        // Try Family 1.
        if let Ok(mut decoded) =
            AddSubLuiAuipcMopDecoder.define_decoder_subspace(preprocessed_opcode)
        {
            decoded.opcode_family_bits <<= F1_OFFSET;
            return Ok(decoded);
        }
        // Try Family 2.
        if let Ok(mut decoded) = JumpSltBranchDecoder.define_decoder_subspace(preprocessed_opcode) {
            decoded.opcode_family_bits <<= F2_OFFSET;
            return Ok(decoded);
        }
        // Try Family 3.
        if let Ok(mut decoded) = ShiftBinaryDecoder.define_decoder_subspace(preprocessed_opcode) {
            decoded.opcode_family_bits <<= F3_OFFSET;
            return Ok(decoded);
        }
        // Try Family 4 — needs the 1-bit → 2-bit one-hot conversion.
        if let Ok(mut decoded) =
            WordOnlyMemoryFamilyDecoder.define_decoder_subspace(preprocessed_opcode)
        {
            // Sanity-check the standalone encoding to catch upstream drift.
            assert!(
                decoded.opcode_family_bits == 0 || decoded.opcode_family_bits == 1,
                "WordOnlyMemoryFamilyDecoder.opcode_family_bits expected 0 (Lw) or 1 (Sw), got {}",
                decoded.opcode_family_bits
            );
            let is_store = (decoded.opcode_family_bits >> F4_STANDALONE_IS_STORE_BIT) & 1;
            // One-hot in the unified bitmask:
            //   Lw → bit F4_LW_BIT
            //   Sw → bit F4_SW_BIT
            decoded.opcode_family_bits = if is_store == 1 {
                1u32 << F4_SW_BIT
            } else {
                1u32 << F4_LW_BIT
            };
            return Ok(decoded);
        }
        Err(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::circuit::UNIFIED_REDUCED_MACHINE_NUM_FLAGS;
    use super::*;

    /// The unified bitmask layout must accommodate every per-family bit plus the
    /// 2-bit one-hot LW/SW. Sanity check the offsets against the constants in
    /// `circuit.rs`. (Keep this in lockstep with `FAMILY_*_FLAG_OFFSET` there.)
    #[test]
    fn flag_offsets_consistent() {
        assert_eq!(F1_OFFSET, 0);
        assert_eq!(F2_OFFSET, ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS);
        assert_eq!(
            F3_OFFSET,
            ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS + JUMP_SLT_BRANCH_FAMILY_NUM_BITS
        );
        assert_eq!(
            F4_OFFSET,
            ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS
                + JUMP_SLT_BRANCH_FAMILY_NUM_BITS
                + SHIFT_BINARY_FAMILY_NUM_FLAGS
        );
        // 2-bit one-hot Family-4 region fits within the bitmask.
        assert!(F4_SW_BIT < UNIFIED_REDUCED_MACHINE_NUM_FLAGS);
    }

    /// LW maps to bit F4_LW_BIT (= 15); SW maps to bit F4_SW_BIT (= 16). Use real
    /// preprocessed instructions to exercise the full path through the standalone
    /// decoder.
    #[test]
    fn family_4_lw_sw_one_hot() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        let lw = Instruction::new(
            InstructionName::Lw,
            /* rs1 */ 1,
            /* rs2 */ 0,
            /* rd */ 2,
            /* imm */ 0,
        );
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(lw)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            1u32 << F4_LW_BIT,
            "LW should set exactly bit F4_LW_BIT"
        );

        let sw = Instruction::new(
            InstructionName::Sw,
            /* rs1 */ 1,
            /* rs2 */ 2,
            /* rd */ 0,
            /* imm */ 0,
        );
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(sw)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            1u32 << F4_SW_BIT,
            "SW should set exactly bit F4_SW_BIT"
        );
    }

    /// Family 1's ADD lands in the bottom region with no shift.
    #[test]
    fn family_1_add_lands_in_low_region() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        let add = Instruction::new(
            InstructionName::Add,
            /* rs1 */ 1,
            /* rs2 */ 2,
            /* rd */ 3,
            /* imm */ 0,
        );
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(add)
            .unwrap();
        // Family 1 ADD sets bit 0 in its private bitmask; with F1_OFFSET = 0 it stays
        // at bit 0 in the unified bitmask.
        assert_eq!(decoded.opcode_family_bits, 1u32 << 0);
    }
}
