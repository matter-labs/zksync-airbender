use super::*;
use crate::gkr_circuits::add_sub_family::{
    AddSubLuiAuipcMopDecoder, AddSubLuiAuipcMopFamilyCircuitMask,
};
use crate::gkr_circuits::binary_shifts_family::{ShiftBinaryDecoder, ShiftBinaryFamilyCircuitMask};
use crate::gkr_circuits::jump_branch_slt_family::{
    JumpSltBranchDecoder, JumpSltBranchFamilyCircuitMask, BRANCH_BIT, RD_IS_ZERO_BIT, SLT_BIT,
};
use crate::gkr_circuits::unified_reduced_machine::{
    FAMILY_1_TRI_ADD_BIT, FAMILY_3_BINARY_OP_BIT, UNIFIED_F1_NUM_FLAGS, UNIFIED_F3_NUM_FLAGS,
};
use crate::tables::TableType;
use crate::types::Boolean;

use super::circuit::{
    FAMILY_1_FLAG_OFFSET as F1_OFFSET, FAMILY_2_FLAG_OFFSET as F2_OFFSET,
    FAMILY_3_FLAG_OFFSET as F3_OFFSET, MEM_LOAD_BIT, MEM_LOAD_SUBWORD_BIT, MEM_STORE_BIT,
    MEM_STORE_SUBWORD_BIT, MULHU_BIT, MUL_BIT, UNIFIED_EXTENDED_MACHINE_NUM_FLAGS,
};

/// Unified position of the Family-2 auxiliary RD_IS_ZERO flag.
pub const EXTENDED_RD_IS_ZERO_BIT: usize = F2_OFFSET + RD_IS_ZERO_BIT;

/// `funct3` the memory family carries for sub-word ops: bit 0 = byte-sized access, bit 1 =
/// sign-extend (loads only). Word ops carry 0. The sub-word lookup tables take this value
/// directly as their mode key bits (`LOAD_SUBWORD_LIMB_MODE_SHIFT` / `STORE_SUBWORD_BYTE_SHIFT`).
pub const MEM_FUNCT3_BYTE_BIT: u8 = 1 << 0;
pub const MEM_FUNCT3_SEXT_BIT: u8 = 1 << 1;

/// The auxiliary (non-dispatch) flags of the extended bitmask: Family 2's RD_IS_ZERO and the
/// memory family's sub-word markers.
pub const EXTENDED_AUX_FLAGS_MASK: u32 =
    (1 << EXTENDED_RD_IS_ZERO_BIT) | (1 << MEM_LOAD_SUBWORD_BIT) | (1 << MEM_STORE_SUBWORD_BIT);

/// The first decoder-mask fact an extended decoder entry violates, or `None`. The circuit's
/// linear dispatch tie, PC-bump gate, affine F2 rd-write gates and the memory family's
/// word/sub-word split take their flag semantics on executing rows whose mask passes this.
pub(super) fn extended_decoder_mask_violation(bits: u32) -> Option<&'static str> {
    if bits >> UNIFIED_EXTENDED_MACHINE_NUM_FLAGS != 0 {
        return Some("flag bits beyond the extended bitmask");
    }
    let rd_is_zero = bits & (1 << EXTENDED_RD_IS_ZERO_BIT) != 0;
    let dispatch = bits & !EXTENDED_AUX_FLAGS_MASK;
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
    if bits & (1 << MEM_LOAD_SUBWORD_BIT) != 0 && dispatch != 1 << MEM_LOAD_BIT {
        return Some("LOAD_SUBWORD without LOAD");
    }
    if bits & (1 << MEM_STORE_SUBWORD_BIT) != 0 && dispatch != 1 << MEM_STORE_BIT {
        return Some("STORE_SUBWORD without STORE");
    }
    None
}

#[derive(Clone, Copy, Debug)]
pub struct UnifiedExtendedMachineDecoder;

#[derive(Clone, Copy, Debug)]
pub struct UnifiedExtendedMachineFamilyCircuitMask {
    add_sub_lui_auipc_mop_bits: [Boolean; UNIFIED_F1_NUM_FLAGS],
    jump_branch_slt_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
    binary_shifts_bits: [Boolean; UNIFIED_F3_NUM_FLAGS],
    is_load: Boolean,
    is_store: Boolean,
    is_load_subword: Boolean,
    is_store_subword: Boolean,
    is_mul: Boolean,
    is_mulhu: Boolean,
}

impl UnifiedExtendedMachineFamilyCircuitMask {
    pub fn from_full_mask(bitmask: [Boolean; UNIFIED_EXTENDED_MACHINE_NUM_FLAGS]) -> Self {
        Self {
            add_sub_lui_auipc_mop_bits: std::array::from_fn(|i| bitmask[F1_OFFSET + i]),
            jump_branch_slt_bits: std::array::from_fn(|i| bitmask[F2_OFFSET + i]),
            binary_shifts_bits: std::array::from_fn(|i| bitmask[F3_OFFSET + i]),
            is_load: bitmask[MEM_LOAD_BIT],
            is_store: bitmask[MEM_STORE_BIT],
            is_load_subword: bitmask[MEM_LOAD_SUBWORD_BIT],
            is_store_subword: bitmask[MEM_STORE_SUBWORD_BIT],
            is_mul: bitmask[MUL_BIT],
            is_mulhu: bitmask[MULHU_BIT],
        }
    }

    pub fn add_sub_lui_auipc_mop(&self) -> AddSubLuiAuipcMopFamilyCircuitMask {
        let standalone: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS] =
            std::array::from_fn(|i| self.add_sub_lui_auipc_mop_bits[i]);
        AddSubLuiAuipcMopFamilyCircuitMask::from_mask(standalone)
    }

    pub fn perform_tri_add(&self) -> Boolean {
        self.add_sub_lui_auipc_mop_bits[ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS]
    }

    pub fn jump_branch_slt(&self) -> JumpSltBranchFamilyCircuitMask {
        JumpSltBranchFamilyCircuitMask::from_mask(self.jump_branch_slt_bits)
    }

    pub fn binary_shifts(&self) -> ShiftBinaryFamilyCircuitMask {
        ShiftBinaryFamilyCircuitMask::from_mask(self.binary_shifts_bits)
    }

    /// Memory family dispatch bit: any load (LW/LH/LHU/LB/LBU).
    pub fn is_load(&self) -> Boolean {
        self.is_load
    }

    /// Memory family dispatch bit: any store (SW/SH/SB).
    pub fn is_store(&self) -> Boolean {
        self.is_store
    }

    /// Auxiliary: the load is LH/LHU/LB/LBU (comes only with `is_load`).
    pub fn is_load_subword(&self) -> Boolean {
        self.is_load_subword
    }

    /// Auxiliary: the store is SH/SB (comes only with `is_store`).
    pub fn is_store_subword(&self) -> Boolean {
        self.is_store_subword
    }

    pub fn is_mul(&self) -> Boolean {
        self.is_mul
    }

    pub fn is_mulhu(&self) -> Boolean {
        self.is_mulhu
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

    /// Every flag of the memory family, dispatch and auxiliary.
    pub fn memory_bits(&self) -> [Boolean; 4] {
        [
            self.is_load,
            self.is_store,
            self.is_load_subword,
            self.is_store_subword,
        ]
    }

    pub fn mul_bits(&self) -> [Boolean; 2] {
        [self.is_mul, self.is_mulhu]
    }
}

impl OpcodeFamilyDecoder for UnifiedExtendedMachineDecoder {
    /// Like the reduced machine: the bitmask spans every family, so per-family views are
    /// produced by slicing the full mask.
    type BitmaskCircuitParser = ();

    fn instruction_family_index(&self) -> u8 {
        common_constants::circuit_families::EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX
    }

    /// Dispatch the opcode to whichever family decoder accepts it and shift the per-family
    /// bits into the family's region of the extended bitmask. Memory ops and `MUL`/`MULHU`
    /// are decoded here (their standalone decoders use a different flag encoding, and the
    /// standalone mul/div family also accepts division, which this machine does not).
    ///
    /// # Panics
    /// Same contract as the reduced machine's decoder: an illegal `ZimopIXorRot` rotation or
    /// a mask that violates [`extended_decoder_mask_violation`] panics rather than returning
    /// `Err`, because `Err` means "not my family" and would silently drop the instruction.
    fn define_decoder_subspace(
        &self,
        preprocessed_opcode: Instruction,
    ) -> Result<ExecutorFamilyDecoderData, ()> {
        let decoded = decode_extended(preprocessed_opcode)?;
        if let Some(violation) = extended_decoder_mask_violation(decoded.opcode_family_bits) {
            panic!(
                "extended decoder mask {:#b} for {preprocessed_opcode:?}: {violation}",
                decoded.opcode_family_bits
            );
        }
        Ok(decoded)
    }
}

fn decode_memory(preprocessed_opcode: Instruction) -> Result<ExecutorFamilyDecoderData, ()> {
    use InstructionName::*;

    // (is_store, subword, byte, sign-extend)
    let (is_store, subword, byte, sext) = match preprocessed_opcode.name {
        Lw => (false, false, false, false),
        Lh => (false, true, false, true),
        Lhu => (false, true, false, false),
        Lb => (false, true, true, true),
        Lbu => (false, true, true, false),
        Sw => (true, false, false, false),
        Sh => (true, true, false, false),
        Sb => (true, true, true, false),
        _ => return Err(()),
    };

    let (rs2_index, rd_index, mut bitmask) = if is_store {
        assert_eq!(preprocessed_opcode.rd, 0);
        (preprocessed_opcode.rs2 as u16, 0u8, 1u32 << MEM_STORE_BIT)
    } else {
        // Loads into x0 are preprocessed away, so rd never needs masking.
        assert_ne!(preprocessed_opcode.rd, 0);
        assert_eq!(preprocessed_opcode.rs2, 0);
        (0u16, preprocessed_opcode.rd, 1u32 << MEM_LOAD_BIT)
    };
    if subword {
        bitmask |= if is_store {
            1 << MEM_STORE_SUBWORD_BIT
        } else {
            1 << MEM_LOAD_SUBWORD_BIT
        };
    }
    let funct3 = (byte as u8) * MEM_FUNCT3_BYTE_BIT + (sext as u8) * MEM_FUNCT3_SEXT_BIT;

    Ok(ExecutorFamilyDecoderData {
        imm: preprocessed_opcode.imm,
        rs1_index: preprocessed_opcode.rs1,
        rs2_index,
        rd_index,
        funct3: Some(funct3),
        funct7: None,
        opcode_family_bits: bitmask,
    })
}

fn decode_mul(preprocessed_opcode: Instruction) -> Result<ExecutorFamilyDecoderData, ()> {
    let bit = match preprocessed_opcode.name {
        InstructionName::Mul => MUL_BIT,
        InstructionName::Mulhu => MULHU_BIT,
        _ => return Err(()),
    };
    assert_ne!(preprocessed_opcode.rd, 0);
    assert_eq!(preprocessed_opcode.imm, 0);

    Ok(ExecutorFamilyDecoderData {
        imm: 0,
        rs1_index: preprocessed_opcode.rs1,
        rs2_index: preprocessed_opcode.rs2 as u16,
        rd_index: preprocessed_opcode.rd,
        funct3: Some(0),
        funct7: None,
        opcode_family_bits: 1u32 << bit,
    })
}

fn decode_extended(preprocessed_opcode: Instruction) -> Result<ExecutorFamilyDecoderData, ()> {
    // Unified-only opcodes decoded exactly as in the reduced machine (same F1/F3 regions).
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
        assert!(rotation_table_id <= u8::MAX as u32);
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

    if let Ok(d) = AddSubLuiAuipcMopDecoder.define_decoder_subspace(preprocessed_opcode) {
        decoded = d;
        decoded.opcode_family_bits <<= F1_OFFSET;
    } else if let Ok(d) = JumpSltBranchDecoder.define_decoder_subspace(preprocessed_opcode) {
        decoded = d;
        decoded.opcode_family_bits <<= F2_OFFSET;
    } else if let Ok(d) = ShiftBinaryDecoder.define_decoder_subspace(preprocessed_opcode) {
        decoded = d;
        decoded.opcode_family_bits <<= F3_OFFSET;
        if decoded.opcode_family_bits == 1u32 << FAMILY_3_BINARY_OP_BIT {
            let wide_id = match decoded.funct3 {
                Some(f) if f as u32 == XOR_TABLE_ID => TableType::WideXor,
                Some(f) if f as u32 == OR_TABLE_ID => TableType::WideOr,
                Some(f) if f as u32 == AND_TABLE_ID => TableType::WideAnd,
                other => panic!("binary-op row with unexpected funct3 {other:?}"),
            } as u32;
            assert!(wide_id <= u8::MAX as u32);
            decoded.funct3 = Some(wide_id as u8);
        }
    } else if let Ok(d) = decode_memory(preprocessed_opcode) {
        decoded = d;
    } else if let Ok(d) = decode_mul(preprocessed_opcode) {
        decoded = d;
    } else {
        return Err(());
    }

    // The uniform funct3 column needs a defined value for every opcode.
    if decoded.funct3.is_none() {
        decoded.funct3 = Some(0);
    }
    Ok(decoded)
}

#[cfg(test)]
mod tests {
    use super::super::circuit::{MEM_FLAG_OFFSET, MUL_FLAG_OFFSET};
    use super::*;
    use crate::gkr_circuits::unified_reduced_machine::{
        UnifiedReducedMachineDecoder, UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
    };
    use riscv_transpiler::ir::simple_instruction_set::{Instruction, InstructionName};

    #[test]
    fn flag_offsets_consistent() {
        assert_eq!(F1_OFFSET, 0);
        assert_eq!(F2_OFFSET, UNIFIED_F1_NUM_FLAGS);
        assert_eq!(
            F3_OFFSET,
            UNIFIED_F1_NUM_FLAGS + JUMP_SLT_BRANCH_FAMILY_NUM_BITS
        );
        assert_eq!(MEM_FLAG_OFFSET, F3_OFFSET + UNIFIED_F3_NUM_FLAGS);
        assert_eq!(MEM_LOAD_BIT, MEM_FLAG_OFFSET);
        assert_eq!(MUL_FLAG_OFFSET, MEM_FLAG_OFFSET + 4);
        assert_eq!(MULHU_BIT + 1, UNIFIED_EXTENDED_MACHINE_NUM_FLAGS);
        // The reduced machine's F1/F2/F3 regions are shared verbatim, so every reduced
        // non-memory opcode decodes identically in both machines.
        assert_eq!(
            UNIFIED_REDUCED_MACHINE_NUM_FLAGS - 2,
            MEM_FLAG_OFFSET,
            "reduced machine F4 starts where the extended memory region starts"
        );
    }

    #[test]
    fn non_memory_opcodes_decode_as_in_reduced_machine() {
        let cases = vec![
            Instruction::new(InstructionName::Nop, 0, 0, 0, 0),
            Instruction::new(InstructionName::Add, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sub, 1, 2, 3, 0),
            Instruction::new(InstructionName::Auipc, 0, 0, 3, 0x1000),
            Instruction::new(InstructionName::ZimopMul, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopFMA, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopTriAdd, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZicsrDelegation, 0, 0, 0, 0x7C0),
            Instruction::new(InstructionName::ZicsrNonDeterminismRead, 0, 0, 3, 0),
            Instruction::new(InstructionName::Jal, 0, 0, 1, 8),
            Instruction::new(InstructionName::Jal, 0, 0, 0, 8),
            Instruction::new(InstructionName::Jalr, 1, 0, 0, 0),
            Instruction::new(InstructionName::Branch, 1, 2, 0, 8),
            Instruction::new(InstructionName::Slt, 1, 2, 3, 0),
            Instruction::new(InstructionName::Xor, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sll, 1, 2, 3, 0),
            Instruction::new(InstructionName::Sra, 1, 2, 3, 0),
            Instruction::new(InstructionName::ZimopIXorRot, 1, 3, 3, 16),
        ];
        for instr in cases {
            let reduced = UnifiedReducedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap();
            let extended = UnifiedExtendedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap();
            assert_eq!(reduced, extended, "{instr:?}");
        }
    }

    #[test]
    fn memory_opcodes() {
        use InstructionName::*;
        let loads = [
            (Lw, 0u32, 0u8),
            (Lh, 1 << MEM_LOAD_SUBWORD_BIT, MEM_FUNCT3_SEXT_BIT),
            (Lhu, 1 << MEM_LOAD_SUBWORD_BIT, 0),
            (
                Lb,
                1 << MEM_LOAD_SUBWORD_BIT,
                MEM_FUNCT3_BYTE_BIT | MEM_FUNCT3_SEXT_BIT,
            ),
            (Lbu, 1 << MEM_LOAD_SUBWORD_BIT, MEM_FUNCT3_BYTE_BIT),
        ];
        for (name, aux, funct3) in loads {
            let instr = Instruction::new(name, 1, 0, 2, 12);
            let d = UnifiedExtendedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap();
            assert_eq!(d.opcode_family_bits, (1 << MEM_LOAD_BIT) | aux, "{name:?}");
            assert_eq!(d.funct3, Some(funct3), "{name:?}");
            assert_eq!((d.rs1_index, d.rs2_index, d.rd_index, d.imm), (1, 0, 2, 12));
        }
        let stores = [
            (Sw, 0u32, 0u8),
            (Sh, 1 << MEM_STORE_SUBWORD_BIT, 0),
            (Sb, 1 << MEM_STORE_SUBWORD_BIT, MEM_FUNCT3_BYTE_BIT),
        ];
        for (name, aux, funct3) in stores {
            let instr = Instruction::new(name, 1, 2, 0, 12);
            let d = UnifiedExtendedMachineDecoder
                .define_decoder_subspace(instr)
                .unwrap();
            assert_eq!(d.opcode_family_bits, (1 << MEM_STORE_BIT) | aux, "{name:?}");
            assert_eq!(d.funct3, Some(funct3), "{name:?}");
            assert_eq!((d.rs1_index, d.rs2_index, d.rd_index, d.imm), (1, 2, 0, 12));
        }
    }

    #[test]
    fn mul_opcodes_and_no_division() {
        let d = UnifiedExtendedMachineDecoder
            .define_decoder_subspace(Instruction::new(InstructionName::Mul, 1, 2, 3, 0))
            .unwrap();
        assert_eq!(d.opcode_family_bits, 1 << MUL_BIT);
        let d = UnifiedExtendedMachineDecoder
            .define_decoder_subspace(Instruction::new(InstructionName::Mulhu, 1, 2, 3, 0))
            .unwrap();
        assert_eq!(d.opcode_family_bits, 1 << MULHU_BIT);
        assert_eq!((d.rs1_index, d.rs2_index, d.rd_index), (1, 2, 3));
        for name in [
            InstructionName::Divu,
            InstructionName::Remu,
            InstructionName::Div,
            InstructionName::Rem,
            InstructionName::Mulh,
            InstructionName::Mulhsu,
        ] {
            assert!(
                UnifiedExtendedMachineDecoder
                    .define_decoder_subspace(Instruction::new(name, 1, 2, 3, 0))
                    .is_err(),
                "{name:?} must not be accepted"
            );
        }
    }

    /// Every admitted mask has exactly one dispatch bit; the auxiliary bits ride only with
    /// their dispatch bit.
    #[test]
    fn admitted_masks() {
        let admitted: Vec<u32> = (0..1u32 << UNIFIED_EXTENDED_MACHINE_NUM_FLAGS)
            .filter(|&m| extended_decoder_mask_violation(m).is_none())
            .collect();
        // 20 reduced-machine F1/F2/F3 masks (18 one-hot dispatch + 2 RD_IS_ZERO variants,
        // minus the 2 memory bits that moved) + memory 4 + mul 2.
        assert_eq!(admitted.len(), 18 + 4 + 2);
        for m in admitted {
            let dispatch = m & !EXTENDED_AUX_FLAGS_MASK;
            assert_eq!(dispatch.count_ones(), 1);
        }
        assert!(extended_decoder_mask_violation(1 << MEM_LOAD_SUBWORD_BIT).is_some());
        assert!(extended_decoder_mask_violation(
            (1 << MEM_STORE_BIT) | (1 << MEM_LOAD_SUBWORD_BIT)
        )
        .is_some());
        assert!(extended_decoder_mask_violation((1 << MUL_BIT) | (1 << MULHU_BIT)).is_some());
    }
}
