use super::*;
use crate::gkr_circuits::add_sub_family::{
    AddSubLuiAuipcMopDecoder, AddSubLuiAuipcMopFamilyCircuitMask,
};
use crate::gkr_circuits::binary_shifts_family::{ShiftBinaryDecoder, ShiftBinaryFamilyCircuitMask};
use crate::gkr_circuits::jump_branch_slt_family::{
    JumpSltBranchDecoder, JumpSltBranchFamilyCircuitMask, BRANCH_BIT, RD_IS_ZERO_BIT, SLT_BIT,
};
use crate::gkr_circuits::mem_word_only::WordOnlyMemoryFamilyDecoder;
use crate::types::Boolean;

use super::circuit::{
    FAMILY_1_FLAG_OFFSET as F1_OFFSET, FAMILY_1_TRI_ADD_BIT, FAMILY_2_FLAG_OFFSET as F2_OFFSET,
    FAMILY_3_BINARY_OP_BIT, FAMILY_3_FLAG_OFFSET as F3_OFFSET, FAMILY_4_LW_BIT as F4_LW_BIT,
    FAMILY_4_SW_BIT as F4_SW_BIT, UNIFIED_F1_NUM_FLAGS, UNIFIED_F3_NUM_FLAGS,
    UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use crate::tables::TableType;

// Family 4 in the unified bitmask is one-hot LW/SW (2 bits), not the standalone
// 1-bit `is_store` encoding. The bit positions live in `circuit.rs` as the
// canonical FAMILY_4_LW_BIT / FAMILY_4_SW_BIT (re-aliased above for brevity).

/// The Family-4 standalone decoder produces `opcode_family_bits = 0` for LW and
/// `= 1` for SW (bit 0 = is_store).
const F4_STANDALONE_IS_STORE_BIT: usize = 0;

/// Unified position of the Family-2 auxiliary RD_IS_ZERO flag; every other flag is a
/// dispatch bit.
pub const UNIFIED_RD_IS_ZERO_BIT: usize = F2_OFFSET + RD_IS_ZERO_BIT;

/// The first decoder-mask fact a unified decoder entry violates, or `None`. The unified
/// circuit's linear dispatch tie, PC-bump gate and affine F2 rd-write gates equal the
/// helper columns they replace on masks that pass this.
pub(super) fn unified_decoder_mask_violation(bits: u32) -> Option<&'static str> {
    if bits >> UNIFIED_REDUCED_MACHINE_NUM_FLAGS != 0 {
        return Some("flag bits beyond the unified bitmask");
    }
    let rd_is_zero = bits & (1 << UNIFIED_RD_IS_ZERO_BIT) != 0;
    let dispatch = bits & !(1 << UNIFIED_RD_IS_ZERO_BIT);
    if dispatch.count_ones() != 1 {
        return Some("not exactly one dispatch bit");
    }
    let f2_sub_opcodes = ((1u32 << RD_IS_ZERO_BIT) - 1) << F2_OFFSET;
    if rd_is_zero && dispatch & f2_sub_opcodes == 0 {
        return Some("RD_IS_ZERO without a Family-2 sub-opcode");
    }
    if dispatch == 1 << (F2_OFFSET + BRANCH_BIT) && !rd_is_zero {
        return Some("BRANCH without RD_IS_ZERO");
    }
    if dispatch == 1 << (F2_OFFSET + SLT_BIT) && rd_is_zero {
        return Some("SLT/SLTU with RD_IS_ZERO");
    }
    None
}

#[derive(Clone, Copy, Debug)]
pub struct UnifiedReducedMachineDecoder;

#[derive(Clone, Copy, Debug)]
pub struct UnifiedReducedMachineFamilyCircuitMask {
    // UNIFIED_F1_NUM_FLAGS = standalone NUM_FLAGS + 1: bits [0..9) are the standalone
    // add_sub family flags, bit [9] is the unified-only 3-input-add (tri-add) flag.
    add_sub_lui_auipc_mop_bits: [Boolean; UNIFIED_F1_NUM_FLAGS],
    jump_branch_slt_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
    // UNIFIED_F3_NUM_FLAGS = standalone NUM_FLAGS (2): shift + binary-op. ZimopIXorRot rides
    // the binary-op bit (it differs from a plain binop only by funct3 = XorRotate{r} table id).
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
        ShiftBinaryFamilyCircuitMask::from_mask(self.binary_shifts_bits)
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
    ///
    /// # Panics
    /// Panics if a `ZimopIXorRot` carries a rotation amount outside the 4 Blake2 values
    /// {16,12,8,7} — only those have a corresponding `XorRotate{r}` lookup table — or if a
    /// decoded mask violates [`unified_decoder_mask_violation`]. Panicking (rather than
    /// `Err`) is deliberate: the caller treats `Err` as "not my family" and skips the
    /// instruction, which would silently drop an illegal opcode.
    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        let decoded = decode_unified(preprocessed_opcode)?;
        assert_unified_decoder_mask(&decoded, preprocessed_opcode);
        Ok(decoded)
    }
}

fn assert_unified_decoder_mask(decoded: &ExecutorFamilyDecoderData, opcode: Instruction) {
    if let Some(violation) = unified_decoder_mask_violation(decoded.opcode_family_bits) {
        panic!(
            "unified decoder mask {:#b} for {opcode:?}: {violation}",
            decoded.opcode_family_bits
        );
    }
}

fn decode_unified(preprocessed_opcode: Instruction) -> Result<ExecutorFamilyDecoderData, ()> {
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
    // the standalone `ShiftBinaryDecoder` returns `Err`. `preprocess_bytecode` sets rs2 := rd,
    // so rd's old value flows through the rs2 read port (sub-slot +1) and the circuit reuses
    // the rs2 byte decomposition. The opcode rides the ORDINARY binary-op dispatch bit — its
    // only difference from a plain binop is the table id: the rotation amount (only the 4
    // Blake2 values {16,12,8,7}) maps to the per-rotation XorRotate{r} table id carried in
    // `funct3` (table_id = funct3, like the Wide{Xor,Or,And} remap below). `imm` is zeroed
    // (the rotation lives in funct3), so the binop path's `rs2_byte + imm` inputs and its
    // imm sign-extension lookup both see zeros on these rows.
    if preprocessed_opcode.name == InstructionName::ZimopIXorRot {
        assert_ne!(preprocessed_opcode.rd, 0);
        assert_eq!(preprocessed_opcode.rs2, preprocessed_opcode.rd);
        let rotation_table_id = match preprocessed_opcode.imm {
            16 => TableType::XorRotate16,
            12 => TableType::XorRotate12,
            8 => TableType::XorRotate8,
            7 => TableType::XorRotate7,
            other => {
                panic!("unsupported xor-rotate rotation amount {other} (only Blake2 {{16,12,8,7}})")
            }
        } as u32;
        // table_id is carried in the u8 funct3 column; guard against future TableType drift
        // pushing the XorRotate discriminants past 255.
        assert!(
            rotation_table_id <= u8::MAX as u32,
            "XorRotate table id {rotation_table_id} does not fit in the funct3 u8 column"
        );
        return Ok(ExecutorFamilyDecoderData {
            imm: 0,
            rs1_index: preprocessed_opcode.rs1,
            rs2_index: preprocessed_opcode.rs2 as u16,
            rd_index: preprocessed_opcode.rd,
            funct3: Some(rotation_table_id as u8),
            funct7: None,
            opcode_family_bits: 1u32 << FAMILY_3_BINARY_OP_BIT,
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
        if decoded.opcode_family_bits == 1u32 << FAMILY_3_BINARY_OP_BIT {
            let wide_id = match decoded.funct3 {
                Some(f) if f as u32 == XOR_TABLE_ID => TableType::WideXor,
                Some(f) if f as u32 == OR_TABLE_ID => TableType::WideOr,
                Some(f) if f as u32 == AND_TABLE_ID => TableType::WideAnd,
                other => panic!("binary-op row with unexpected funct3 {other:?}"),
            } as u32;
            assert!(
                wide_id <= u8::MAX as u32,
                "wide binop table id {wide_id} does not fit in the funct3 u8 column"
            );
            decoded.funct3 = Some(wide_id as u8);
        }
    }
    // Try Family 4 — needs the 1-bit → 2-bit one-hot conversion.
    else if let Ok(d) = WordOnlyMemoryFamilyDecoder.define_decoder_subspace(preprocessed_opcode) {
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

/// Every preprocessed instruction kind the unified decoder can see, and the decoder-mask
/// row classes they produce.
#[cfg(test)]
pub(super) mod row_classes {
    use super::*;
    use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};
    use std::collections::BTreeSet;

    /// Every `InstructionName`, in discriminant order.
    pub const ALL_INSTRUCTION_NAMES: [InstructionName; 46] = [
        InstructionName::Illegal,
        InstructionName::Nop,
        InstructionName::Add,
        InstructionName::Sub,
        InstructionName::Auipc,
        InstructionName::ZimopAdd,
        InstructionName::ZimopSub,
        InstructionName::ZimopMul,
        InstructionName::ZimopFMA,
        InstructionName::ZimopTriAdd,
        InstructionName::Slt,
        InstructionName::Sltu,
        InstructionName::Jal,
        InstructionName::Jalr,
        InstructionName::Branch,
        InstructionName::Sll,
        InstructionName::Srl,
        InstructionName::Sra,
        InstructionName::Rol,
        InstructionName::Ror,
        InstructionName::Xor,
        InstructionName::Or,
        InstructionName::And,
        InstructionName::ZimopIXorRot,
        InstructionName::Rev8,
        InstructionName::Mul,
        InstructionName::Mulh,
        InstructionName::Mulhsu,
        InstructionName::Mulhu,
        InstructionName::Div,
        InstructionName::Divu,
        InstructionName::Rem,
        InstructionName::Remu,
        InstructionName::Lw,
        InstructionName::Sw,
        InstructionName::Lhu,
        InstructionName::Lbu,
        InstructionName::Lh,
        InstructionName::Lb,
        InstructionName::Sb,
        InstructionName::Sh,
        InstructionName::ZicsrDelegation,
        InstructionName::ZicsrNonDeterminismRead,
        InstructionName::ZicsrNonDeterminismWrite,
        InstructionName::ZicsrMarkerCsr,
        InstructionName::FormalEnd,
    ];

    /// Preprocessed operand shapes of `name` that satisfy the family decoders'
    /// preconditions (rd = x0 only where preprocessing keeps it: JAL/JALR, Branch, SW,
    /// delegation, the non-determinism write and NOP); empty for names no unified family
    /// decodes.
    pub fn accepted_shapes(name: InstructionName) -> Vec<Instruction> {
        use InstructionName as N;
        let i = |rs1, rs2, rd, imm| Instruction::new(name, rs1, rs2, rd, imm);
        match name {
            N::Nop => vec![i(0, 0, 0, 0)],
            N::Add => vec![i(1, 2, 3, 0), i(1, 0, 3, 0x123), i(0, 0, 3, 0xfffff000)],
            N::Sub => vec![i(1, 2, 3, 0)],
            N::Auipc => vec![i(0, 0, 3, 0x1000)],
            N::ZimopAdd | N::ZimopSub | N::ZimopMul | N::ZimopFMA | N::ZimopTriAdd => {
                vec![i(1, 2, 3, 0)]
            }
            N::ZicsrDelegation => [
                common_constants::BLAKE2S_DELEGATION_CSR_REGISTER,
                common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
                common_constants::KECCAK_SPECIAL5_CSR_REGISTER,
                common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
            ]
            .into_iter()
            .map(|csr| i(0, 0, 0, csr as u32))
            .collect(),
            N::ZicsrNonDeterminismWrite => vec![i(1, 0, 0, 0)],
            N::ZicsrNonDeterminismRead => vec![i(0, 0, 3, 0)],
            N::Slt | N::Sltu => vec![i(1, 2, 3, 0), i(1, 0, 3, 5), i(1, 0, 3, 0xfffffffb)],
            N::Jal => vec![i(0, 0, 1, 8), i(0, 0, 0, 8), i(0, 0, 1, 0xfffffff8)],
            N::Jalr => vec![i(1, 0, 1, 0), i(1, 0, 0, 0), i(1, 0, 5, 8)],
            // Branch carries funct3 in the rd field.
            N::Branch => [0b000, 0b001, 0b100, 0b101, 0b110, 0b111]
                .into_iter()
                .map(|funct3| i(1, 2, funct3, 8))
                .collect(),
            N::Xor | N::Or | N::And => vec![i(1, 2, 3, 0), i(1, 0, 3, 7)],
            N::Sll | N::Srl | N::Sra => vec![i(1, 2, 3, 0), i(1, 0, 3, 5)],
            N::Rev8 => vec![i(1, 0, 3, 0)],
            N::ZimopIXorRot => [16, 12, 8, 7].into_iter().map(|r| i(1, 3, 3, r)).collect(),
            N::Lw => vec![i(1, 0, 2, 0), i(1, 0, 2, 4)],
            N::Sw => vec![i(1, 2, 0, 0), i(1, 2, 0, 4)],
            _ => vec![],
        }
    }

    /// The executing decoder-mask classes, derived by decoding every accepted shape.
    pub fn unified_row_classes() -> BTreeSet<u32> {
        ALL_INSTRUCTION_NAMES
            .into_iter()
            .flat_map(accepted_shapes)
            .map(|instr| {
                UnifiedReducedMachineDecoder
                    .define_decoder_subspace(instr)
                    .unwrap_or_else(|_| panic!("decoder must accept {instr:?}"))
                    .opcode_family_bits
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::super::circuit::FAMILY_4_FLAG_OFFSET as F4_OFFSET;
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
        const { assert!(FAMILY_1_TRI_ADD_BIT < F2_OFFSET) };
        // The F3 region is exactly the standalone shift/binop flags (no unified extra bit).
        assert_eq!(UNIFIED_F3_NUM_FLAGS, SHIFT_BINARY_FAMILY_NUM_FLAGS);
        const { assert!(FAMILY_3_BINARY_OP_BIT < F4_OFFSET) };
        // 2-bit one-hot Family-4 region fits within the bitmask.
        const { assert!(F4_SW_BIT < UNIFIED_REDUCED_MACHINE_NUM_FLAGS) };
    }

    #[test]
    fn xor_rot_unified_only() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        // All 4 Blake2 rotations map to their own XorRotate{r} table id (catches arm transposition).
        let cases = [
            (16u32, TableType::XorRotate16),
            (12, TableType::XorRotate12),
            (8, TableType::XorRotate8),
            (7, TableType::XorRotate7),
        ];
        for (rot, expected_table) in cases {
            // rd = (rs1 ^ rd_old) >>> rot : rs1=1, rs2=rd=3 (decode aliases rs2 to rd so
            // rd_old flows through the rs2 read port), imm=rotation.
            let xr = Instruction::new(InstructionName::ZimopIXorRot, 1, 3, 3, rot);

            // Standalone shift/binop decoder rejects it (unified-only opcode).
            assert!(ShiftBinaryDecoder.define_decoder_subspace(xr).is_err());

            // Unified decoder accepts it; post-merge it rides the ordinary binary-op dispatch
            // bit (the only difference from a plain binop is funct3 = XorRotate{r} table id).
            let decoded = UnifiedReducedMachineDecoder
                .define_decoder_subspace(xr)
                .unwrap();
            assert_eq!(
                decoded.opcode_family_bits,
                1u32 << FAMILY_3_BINARY_OP_BIT,
                "ZimopIXorRot should set exactly bit FAMILY_3_BINARY_OP_BIT"
            );
            assert_eq!(decoded.rs1_index, 1);
            assert_eq!(
                decoded.rs2_index, 3,
                "rs2 aliases rd (rd_old via the rs2 port)"
            );
            assert_eq!(decoded.rd_index, 3);
            assert_eq!(decoded.imm, 0, "imm zeroed; rotation lives in funct3");
            assert_eq!(
                decoded.funct3,
                Some(expected_table as u8),
                "rotation {rot} must map to the {expected_table:?} table id"
            );
        }
    }

    #[test]
    fn byte_swap_rides_shift_path_in_both_decoders() {
        use crate::gkr_circuits::binary_shifts_family::FORMAL_BSWAP_FUNCT3;
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        // rd = rs1.swap_bytes() : rs1=1, formal rs2=x0, rd=3, imm=0.
        let bswap = Instruction::new(InstructionName::Rev8, 1, 0, 3, 0);

        // Standalone (per-family) decoder accepts it on the shift bit.
        let standalone = ShiftBinaryDecoder.define_decoder_subspace(bswap).unwrap();
        assert_eq!(standalone.opcode_family_bits, 1u32 << 0, "shift bit");
        assert_eq!(standalone.funct3, Some(FORMAL_BSWAP_FUNCT3));
        assert_eq!(standalone.rs1_index, 1);
        assert_eq!(standalone.rs2_index, 0);
        assert_eq!(standalone.rd_index, 3);
        assert_eq!(standalone.imm, 0, "imm = 0 pins the shift amount key to 0");

        // Unified decoder: same row shifted into the F3 region, funct3 NOT remapped.
        let decoded = UnifiedReducedMachineDecoder
            .define_decoder_subspace(bswap)
            .unwrap();
        assert_eq!(
            decoded.opcode_family_bits,
            standalone.opcode_family_bits << F3_OFFSET
        );
        assert_eq!(decoded.funct3, standalone.funct3);
        assert_eq!(decoded.imm, standalone.imm);
        assert_eq!(decoded.rs1_index, standalone.rs1_index);
        assert_eq!(decoded.rs2_index, standalone.rs2_index);
        assert_eq!(decoded.rd_index, standalone.rd_index);
    }

    #[test]
    fn binop_funct3_remapped_to_wide_tables() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        let cases = [
            (InstructionName::Xor, TableType::WideXor),
            (InstructionName::Or, TableType::WideOr),
            (InstructionName::And, TableType::WideAnd),
        ];
        for (name, wide) in cases {
            let instr = Instruction::new(name, 1, 2, 3, 0);
            let standalone = ShiftBinaryDecoder.define_decoder_subspace(instr).unwrap();
            let decoded = UnifiedReducedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap();
            // Lockstep: the unified F3 region is exactly the standalone bits shifted.
            assert_eq!(
                decoded.opcode_family_bits,
                standalone.opcode_family_bits << F3_OFFSET,
                "unified F3 bits must be the standalone bits shifted by F3_OFFSET"
            );
            assert_eq!(
                decoded.opcode_family_bits,
                1u32 << FAMILY_3_BINARY_OP_BIT,
                "{name:?} must land on the binary-op dispatch bit"
            );
            assert_eq!(
                decoded.funct3,
                Some(wide as u8),
                "{name:?} funct3 must be remapped to the wide table id"
            );
            // The remap must not alter addressing or the immediate.
            assert_eq!(decoded.imm, standalone.imm);
            assert_eq!(decoded.rs1_index, standalone.rs1_index);
            assert_eq!(decoded.rs2_index, standalone.rs2_index);
            assert_eq!(decoded.rd_index, standalone.rd_index);
        }

        // Shift rows keep the standalone funct3.
        for name in [
            InstructionName::Sll,
            InstructionName::Srl,
            InstructionName::Sra,
        ] {
            let instr = Instruction::new(name, 1, 2, 3, 0);
            let standalone = ShiftBinaryDecoder.define_decoder_subspace(instr).unwrap();
            let decoded = UnifiedReducedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap();
            assert_eq!(
                decoded.funct3, standalone.funct3,
                "{name:?} funct3 must pass through unchanged"
            );
        }
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

    /// Every instruction the unified decoder accepts must set AT MOST ONE DISPATCH bit per
    /// family region (a global one-hot does NOT hold: F2 adds the auxiliary RD_IS_ZERO bit on
    /// Branch / rd=0-JALR rows).
    #[test]
    fn decoder_family_dispatch_bits_exclusive() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

        let f1_mask: u32 = ((1u32 << UNIFIED_F1_NUM_FLAGS) - 1) << F1_OFFSET;
        let f3_mask: u32 = ((1u32 << UNIFIED_F3_NUM_FLAGS) - 1) << F3_OFFSET;
        let f4_mask: u32 = (1u32 << F4_LW_BIT) | (1u32 << F4_SW_BIT);

        // One representative per accepted opcode (operand shapes follow each family
        // decoder's asserts); rd=0 Jal/Jalr rows exercise the F2 auxiliary RD_IS_ZERO
        // bit alongside the dispatch bit. Extend when opcodes are added.
        let cases = vec![
            Instruction::new(InstructionName::Nop, 0, 0, 0, 0),
            Instruction::new(InstructionName::Add, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sub, 1, 2, 3, 0),
            Instruction::new(InstructionName::Auipc, 0, 0, 3, 0x1000),
            Instruction::new(InstructionName::ZimopAdd, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopSub, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopMul, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopFMA, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopTriAdd, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZicsrDelegation, 0, 0, 0, 0x7C0),
            Instruction::new(InstructionName::ZicsrNonDeterminismWrite, 1, 0, 0, 0),
            Instruction::new(InstructionName::ZicsrNonDeterminismRead, 0, 0, 3, 0),
            Instruction::new(InstructionName::Jal, 0, 0, 1, 8),
            Instruction::new(InstructionName::Jal, 0, 0, 0, 8),
            Instruction::new(InstructionName::Jalr, 1, 0, 1, 0),
            Instruction::new(InstructionName::Jalr, 1, 0, 0, 0),
            Instruction::new(InstructionName::Branch, 1, 2, 0, 8),
            Instruction::new(InstructionName::Slt, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sltu, 1, 2, 3, 0),
            Instruction::new(InstructionName::Xor, 1, 2, 3, 0),
            Instruction::new(InstructionName::Or, 1, 2, 3, 0),
            Instruction::new(InstructionName::And, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sll, 1, 2, 3, 0),
            Instruction::new(InstructionName::Srl, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sra, 1, 2, 3, 0),
            Instruction::new(InstructionName::Lw, 1, 0, 2, 0),
            Instruction::new(InstructionName::Sw, 1, 2, 0, 0),
            Instruction::new(InstructionName::ZimopIXorRot, 1, 3, 3, 16),
        ];
        for instr in cases {
            let decoded = UnifiedReducedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap_or_else(|_| panic!("decoder must accept {instr:?}"));
            let bits = decoded.opcode_family_bits;
            assert_ne!(bits, 0, "no family bits for {instr:?}");
            for (region, mask) in [("F1", f1_mask), ("F3", f3_mask), ("F4", f4_mask)] {
                assert!(
                    (bits & mask).count_ones() <= 1,
                    "{region} dispatch bits not exclusive for {instr:?}: {bits:#b}"
                );
            }
        }
    }

    #[test]
    fn instruction_name_list_is_complete() {
        use riscv_transpiler::ir::simple_instruction_set::InstructionName;
        assert_eq!(
            row_classes::ALL_INSTRUCTION_NAMES.len(),
            InstructionName::FormalEnd as usize + 1
        );
        for (i, name) in row_classes::ALL_INSTRUCTION_NAMES.iter().enumerate() {
            assert_eq!(
                *name as u8 as usize, i,
                "{name:?} out of discriminant order"
            );
        }
    }

    /// The unified decoder accepts exactly the 27 preprocessed instruction kinds of the
    /// four families, rejects every other kind, and maps the accepted ones onto exactly 20
    /// executing mask classes.
    #[test]
    fn unified_decoder_accepts_exactly_the_enumerated_kinds() {
        use riscv_transpiler::ir::simple_instruction_set::Instruction;
        use std::collections::BTreeSet;

        let mut accepted = BTreeSet::new();
        for name in row_classes::ALL_INSTRUCTION_NAMES {
            let shapes = row_classes::accepted_shapes(name);
            if shapes.is_empty() {
                assert!(
                    UnifiedReducedMachineDecoder
                        .define_decoder_subspace(Instruction::new(name, 1, 2, 3, 0))
                        .is_err(),
                    "{name:?} must not decode"
                );
                continue;
            }
            for instr in shapes {
                let decoded = UnifiedReducedMachineDecoder
                    .define_decoder_subspace(instr)
                    .unwrap_or_else(|_| panic!("decoder must accept {instr:?}"));
                assert_eq!(
                    unified_decoder_mask_violation(decoded.opcode_family_bits),
                    None
                );
            }
            accepted.insert(name as u8);
        }
        assert_eq!(accepted.len(), 27);

        let z = 1u32 << UNIFIED_RD_IS_ZERO_BIT;
        let f2 = |bit: usize| 1u32 << (F2_OFFSET + bit);
        let mut expected: BTreeSet<u32> = (0..UNIFIED_F1_NUM_FLAGS).map(|b| 1u32 << b).collect();
        use crate::gkr_circuits::jump_branch_slt_family::{JALR_BIT, JAL_BIT};
        expected.extend([
            f2(JAL_BIT),
            f2(JAL_BIT) | z,
            f2(JALR_BIT),
            f2(JALR_BIT) | z,
            f2(SLT_BIT),
            f2(BRANCH_BIT) | z,
        ]);
        expected.extend((0..UNIFIED_F3_NUM_FLAGS).map(|b| 1u32 << (F3_OFFSET + b)));
        expected.extend([1u32 << F4_LW_BIT, 1u32 << F4_SW_BIT]);
        assert_eq!(expected.len(), 20);
        assert_eq!(row_classes::unified_row_classes(), expected);
    }

    /// Over all 2^19 masks the validator accepts exactly the decoder's row classes, so
    /// every invalid shape (no or two dispatch bits, RD_IS_ZERO alone or with a non-F2
    /// bit, BRANCH without RD_IS_ZERO, SLT with it) is rejected.
    #[test]
    fn unified_decoder_mask_validator_is_exact() {
        let classes = row_classes::unified_row_classes();
        for bits in 0..1u32 << UNIFIED_REDUCED_MACHINE_NUM_FLAGS {
            assert_eq!(
                unified_decoder_mask_violation(bits).is_none(),
                classes.contains(&bits),
                "mask {bits:#b}"
            );
        }
        assert!(unified_decoder_mask_violation(1 << UNIFIED_REDUCED_MACHINE_NUM_FLAGS).is_some());
    }

    #[test]
    #[should_panic(expected = "SLT/SLTU with RD_IS_ZERO")]
    fn invalid_decoded_mask_panics() {
        use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};
        let decoded = ExecutorFamilyDecoderData {
            imm: 0,
            rs1_index: 1,
            rs2_index: 2,
            rd_index: 3,
            funct3: Some(0),
            funct7: None,
            opcode_family_bits: (1 << (F2_OFFSET + SLT_BIT)) | (1 << UNIFIED_RD_IS_ZERO_BIT),
        };
        assert_unified_decoder_mask(&decoded, Instruction::new(InstructionName::Slt, 1, 2, 3, 0));
    }
}
