//! ISA vocabulary for the forward-eval VM (spec §6, §7). No encoding here.

pub const TYPE_BITS: u32 = 2;
pub const SLOT_BITS: u32 = 4;      // ≤16 backings/layer
pub const COL_BITS: u32 = 10;      // ≤1024 cols
pub const CELL_BITS: u32 = 14;     // smem cell index
pub const LDC_SUB_BITS: u32 = 2;
pub const LDC_IDX_BITS: u32 = 12;  // ldc_idx < 4096
pub const DESC_BITS: u32 = 14;     // special-source descriptor index
pub const MAX_SLOTS: u32 = 1 << SLOT_BITS;   // 16
pub const MAX_COLS: u32 = 1 << COL_BITS;     // 1024
pub const MAX_LDC_IDX: u32 = 1 << LDC_IDX_BITS; // 4096
pub const MAX_CELL: u32 = 1 << CELL_BITS;
pub const MAX_DESC: u32 = 1 << DESC_BITS;
pub const MAX_ARITY: usize = 127;  // 7-bit arity

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Opcode { Add = 0, Mul = 1, Fma = 2, Mov = 3 }

/// Per-instruction operand field bit(s) (spec §5). The field of the operands
/// consumed by THIS instruction — not the result field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperandField { Base = 0, Ext = 1 }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign { Plus = 0, Minus = 1 }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MovDir { AccFromSrc = 0, DstFromAcc = 1, DstFromSrc = 2 } // 3 reserved

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LdcSub { Const = 0, ConstChallenge = 1, ArgChallenge = 2, Special = 3 }

/// `LdcSub::Special` payloads. Only `NegOne` is ever emitted in v1 (negate);
/// `Zero`/`One` are never produced (zero-arity Add/Mul are NOPs, §Global-Constraints) —
/// kept for wire completeness and rejected by validation if seen in an emitted operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Special { Zero = 0, One = 1, NegOne = 2 }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperandLine {
    Global { slot: u8, col: u16 },
    Smem { cell: u16 },
    Ldc { sub: LdcSub, idx: u16 },
    Special { desc: u16 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DstLine {
    Smem { cell: u16 },
    GlobalMaterialize { slot: u8, col: u16 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Add { field: OperandField, sign: Sign, operands: Vec<OperandLine> },
    Mul { field: OperandField, operands: Vec<OperandLine> },
    Fma { field_lhs: OperandField, field_rhs: OperandField, sign: Sign, pairs: Vec<(OperandLine, OperandLine)> },
    Mov { dir: MovDir, field: OperandField, dst: Option<DstLine>, src: Option<OperandLine> },
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program { pub instrs: Vec<Instr> }

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn constants_fit_lanes() {
        assert_eq!(MAX_SLOTS, 16);
        assert_eq!(MAX_COLS, 1024);
        assert_eq!(MAX_LDC_IDX, 4096);
        assert!(MAX_ARITY < (1 << 7));
        assert!(SLOT_BITS + COL_BITS <= 14);
    }
}
