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
    FAMILY_1_FLAG_OFFSET as F1_OFFSET, FAMILY_1_TRI_ADD_BIT, FAMILY_2_FLAG_OFFSET as F2_OFFSET,
    FAMILY_3_FLAG_OFFSET as F3_OFFSET, FAMILY_3_XOR_ROT_BIT, FAMILY_4_FLAG_OFFSET as F4_OFFSET,
    FAMILY_4_LW_BIT as F4_LW_BIT, FAMILY_4_SW_BIT as F4_SW_BIT, UNIFIED_F1_NUM_FLAGS,
    UNIFIED_F3_NUM_FLAGS, UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use crate::tables::TableType;

// Family 4 in the unified bitmask is one-hot LW/SW (2 bits), not the standalone
// 1-bit `is_store` encoding. The bit positions live in `circuit.rs` as the
// canonical FAMILY_4_LW_BIT / FAMILY_4_SW_BIT (re-aliased above for brevity).

/// The Family-4 standalone decoder produces `opcode_family_bits = 0` for LW and
/// `= 1` for SW (bit 0 = is_store).
const F4_STANDALONE_IS_STORE_BIT: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct UnifiedReducedMachineDecoder;

#[derive(Clone, Copy, Debug)]
pub struct UnifiedReducedMachineFamilyCircuitMask {
    // UNIFIED_F1_NUM_FLAGS = standalone NUM_FLAGS + 1: bits [0..9) are the standalone
    // add_sub family flags, bit [9] is the unified-only 3-input-add (tri-add) flag.
    add_sub_lui_auipc_mop_bits: [Boolean; UNIFIED_F1_NUM_FLAGS],
    jump_branch_slt_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
    // UNIFIED_F3_NUM_FLAGS = standalone NUM_FLAGS + 1: bits [0..2) are the standalone
    // shift/binop flags, bit [2] is the unified-only xor-rotate flag.
    binary_shifts_bits: [Boolean; UNIFIED_F3_NUM_FLAGS],
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
        // The shared mask carries only the 9 standalone flags; the tri-add bit [9] is
        // threaded separately via `perform_tri_add()`.
        let standalone: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS] =
            std::array::from_fn(|i| self.add_sub_lui_auipc_mop_bits[i]);
        AddSubLuiAuipcMopFamilyCircuitMask::from_mask(standalone)
    }

    /// Unified-only 3-input-add (`ZimopTriAdd`) flag (F1 region bit [9]).
    pub fn perform_tri_add(&self) -> Boolean {
        self.add_sub_lui_auipc_mop_bits[ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS]
    }

    pub fn jump_branch_slt(&self) -> JumpSltBranchFamilyCircuitMask {
        JumpSltBranchFamilyCircuitMask::from_mask(self.jump_branch_slt_bits)
    }

    pub fn binary_shifts(&self) -> ShiftBinaryFamilyCircuitMask {
        // The shared mask carries only the 2 standalone flags; the xor-rotate bit [2] is
        // threaded separately via `perform_xor_rot()`.
        let standalone: [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS] =
            std::array::from_fn(|i| self.binary_shifts_bits[i]);
        ShiftBinaryFamilyCircuitMask::from_mask(standalone)
    }

    /// Unified-only xor-rotate (`ZimopIXorRot`) flag (F3 region bit [2]).
    pub fn perform_xor_rot(&self) -> Boolean {
        self.binary_shifts_bits[SHIFT_BINARY_FAMILY_NUM_FLAGS]
    }

    pub fn is_lw(&self) -> Boolean {
        self.is_lw
    }

    pub fn is_sw(&self) -> Boolean {
        self.is_sw
    }

    pub fn add_sub_lui_auipc_mop_bits(&self) -> [Boolean; UNIFIED_F1_NUM_FLAGS] {
        self.add_sub_lui_auipc_mop_bits
    }

    pub fn jump_branch_slt_bits(&self) -> [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS] {
        self.jump_branch_slt_bits
    }

    pub fn binary_shifts_bits(&self) -> [Boolean; UNIFIED_F3_NUM_FLAGS] {
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
        // `ZimopTriAdd` (rd += rs1 + rs2) is a UNIFIED-ONLY add_sub-family opcode: the
        // standalone `AddSubLuiAuipcMopDecoder` returns `Err` for it, so decode it here.
        // Addressing mirrors fmamod (rd is read as the third addend); the flag lands on
        // the unified-only F1 tri-add bit. funct3 is lifted to Some(0) like every opcode.
        if preprocessed_opcode.name == InstructionName::ZimopTriAdd {
            assert_ne!(preprocessed_opcode.rd, 0);
            assert_eq!(preprocessed_opcode.imm, 0);
            return Ok(ExecutorFamilyDecoderData {
                imm: 0,
                rs1_index: preprocessed_opcode.rs1,
                rs2_index: preprocessed_opcode.rs2 as u16,
                rd_index: preprocessed_opcode.rd,
                funct3: Some(0),
                funct7: None,
                opcode_family_bits: 1u32 << FAMILY_1_TRI_ADD_BIT,
            });
        }

        // `ZimopIXorRot` (rd = (rs1 ^ rd_old) >>> rot) is a UNIFIED-ONLY shift/binop-family opcode;
        // the standalone `ShiftBinaryDecoder` returns `Err`. The VM keeps rs2 = x0 and reads rd_old
        // via the rd slot (like fma), so rd_index = rd; the rotation amount (only the 4 Blake2 values
        // {16,12,8,7}) is mapped to the per-rotation xor-rotate table id and carried in `funct3`
        // (table_id = funct3). `imm` is zeroed (the rotation now lives in funct3).
        if preprocessed_opcode.name == InstructionName::ZimopIXorRot {
            assert_ne!(preprocessed_opcode.rd, 0);
            assert_eq!(preprocessed_opcode.rs2, 0);
            let rotation_table_id = match preprocessed_opcode.imm {
                16 => TableType::XorRotate16,
                12 => TableType::XorRotate12,
                8 => TableType::XorRotate8,
                7 => TableType::XorRotate7,
                other => panic!(
                    "unsupported xor-rotate rotation amount {other} (only Blake2 {{16,12,8,7}})"
                ),
            } as u32;
            return Ok(ExecutorFamilyDecoderData {
                imm: 0,
                rs1_index: preprocessed_opcode.rs1,
                rs2_index: 0,
                rd_index: preprocessed_opcode.rd,
                funct3: Some(rotation_table_id as u8),
                funct7: None,
                opcode_family_bits: 1u32 << FAMILY_3_XOR_ROT_BIT,
            });
        }

        let mut decoded: ExecutorFamilyDecoderData;

        // Try Family 1.
        if let Ok(d) = AddSubLuiAuipcMopDecoder.define_decoder_subspace(preprocessed_opcode) {
            decoded = d;
            decoded.opcode_family_bits <<= F1_OFFSET;
        }
        // Try Family 2.
        else if let Ok(d) = JumpSltBranchDecoder.define_decoder_subspace(preprocessed_opcode) {
            decoded = d;
            decoded.opcode_family_bits <<= F2_OFFSET;
        }
        // Try Family 3.
        else if let Ok(d) = ShiftBinaryDecoder.define_decoder_subspace(preprocessed_opcode) {
            decoded = d;
            decoded.opcode_family_bits <<= F3_OFFSET;
        }
        // Try Family 4 — needs the 1-bit → 2-bit one-hot conversion.
        else if let Ok(d) =
            WordOnlyMemoryFamilyDecoder.define_decoder_subspace(preprocessed_opcode)
        {
            decoded = d;
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
        } else {
            return Err(());
        }

        // Post-process: unified circuit's uniform funct3 column needs a defined
        // value for every opcode. Families that don't use funct3 report None;
        // lift to Some(0) here
        if decoded.funct3.is_none() {
            decoded.funct3 = Some(0);
        }
        Ok(decoded)
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
        // The unified F1 region is one wider than the standalone family (extra tri-add bit),
        // so F2 starts at UNIFIED_F1_NUM_FLAGS, not the standalone NUM_FLAGS.
        assert_eq!(F2_OFFSET, UNIFIED_F1_NUM_FLAGS);
        assert_eq!(
            F3_OFFSET,
            UNIFIED_F1_NUM_FLAGS + JUMP_SLT_BRANCH_FAMILY_NUM_BITS
        );
        assert_eq!(
            F4_OFFSET,
            UNIFIED_F1_NUM_FLAGS + JUMP_SLT_BRANCH_FAMILY_NUM_BITS + UNIFIED_F3_NUM_FLAGS
        );
        // The tri-add bit is the last bit of the F1 region (just past the 9 standalone flags).
        assert_eq!(FAMILY_1_TRI_ADD_BIT, ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS);
        assert!(FAMILY_1_TRI_ADD_BIT < F2_OFFSET);
        assert_eq!(FAMILY_3_XOR_ROT_BIT, F3_OFFSET + SHIFT_BINARY_FAMILY_NUM_FLAGS);
        assert!(FAMILY_3_XOR_ROT_BIT < F4_OFFSET);
        // 2-bit one-hot Family-4 region fits within the bitmask.
        assert!(F4_SW_BIT < UNIFIED_REDUCED_MACHINE_NUM_FLAGS);
    }

    #[test]
    fn xor_rot_unified_only() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        // rd = (rs1 ^ rd_old) >>> 12 : rs1=1, rs2=0 (formal), rd=3, imm=rotation=12.
        let xr = Instruction::new(InstructionName::ZimopIXorRot, 1, 0, 3, 12);

        // Standalone shift/binop decoder rejects it (unified-only opcode).
        assert!(ShiftBinaryDecoder.define_decoder_subspace(xr).is_err());

        // Unified decoder accepts it and sets exactly the xor-rotate bit.
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(xr)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            1u32 << FAMILY_3_XOR_ROT_BIT,
            "ZimopIXorRot should set exactly bit FAMILY_3_XOR_ROT_BIT"
        );
        assert_eq!(decoded.rs1_index, 1);
        assert_eq!(decoded.rs2_index, 0, "rs2 is formal x0");
        assert_eq!(decoded.rd_index, 3);
        assert_eq!(decoded.imm, 0, "imm zeroed; rotation lives in funct3");
        assert_eq!(
            decoded.funct3,
            Some(TableType::XorRotate12 as u8),
            "rotation 12 maps to the XorRotate12 table id"
        );
    }

    /// `ZimopTriAdd` is decoded only by the unified decoder (standalone returns `Err`),
    /// and lands on exactly the unified-only tri-add flag bit.
    #[test]
    fn tri_add_unified_only() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        // rd += rs1 + rs2 : rd != 0, imm == 0.
        let tri = Instruction::new(InstructionName::ZimopTriAdd, 1, 2, 3, 0);

        // Standalone add_sub decoder rejects it (unified-only opcode).
        assert!(AddSubLuiAuipcMopDecoder
            .define_decoder_subspace(tri)
            .is_err());

        // Unified decoder accepts it and sets exactly the tri-add bit.
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(tri)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            1u32 << FAMILY_1_TRI_ADD_BIT,
            "ZimopTriAdd should set exactly bit FAMILY_1_TRI_ADD_BIT"
        );
        assert_eq!(decoded.rs1_index, 1);
        assert_eq!(decoded.rs2_index, 2);
        assert_eq!(decoded.rd_index, 3);
    }

    /// LW maps to bit F4_LW_BIT (= 15); SW maps to bit F4_SW_BIT (= 16). Use real
    /// preprocessed instructions to exercise the full path through the standalone
    /// decoder.
    #[test]
    fn family_4_lw_sw_one_hot() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        let lw = Instruction::new(InstructionName::Lw, 1, 0, 2, 0);
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(lw)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            1u32 << F4_LW_BIT,
            "LW should set exactly bit F4_LW_BIT"
        );

        let sw = Instruction::new(InstructionName::Sw, 1, 2, 0, 0);
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(sw)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            1u32 << F4_SW_BIT,
            "SW should set exactly bit F4_SW_BIT"
        );
    }
}
