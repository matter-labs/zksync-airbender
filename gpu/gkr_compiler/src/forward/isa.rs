//! Instruction and operand types for the forward-eval VM.
//!
//! These constants define the Rust side of the 16-bit wire format;
//! `eval_vm_isa.cuh` mirrors them for CUDA.

pub(crate) const TYPE_BITS: u32 = 2;
pub(crate) const SOURCE_WINDOW_SHIFT: u32 = TYPE_BITS;
pub(crate) const SOURCE_WINDOW_BITS: u32 = 6;
#[cfg(test)]
pub(crate) const SOURCE_COLUMN_SHIFT: u32 = SOURCE_WINDOW_SHIFT + SOURCE_WINDOW_BITS;
pub(crate) const SOURCE_COLUMN_BITS: u32 = 7;
pub(crate) const MAX_SOURCE_WINDOWS: u32 = 1 << SOURCE_WINDOW_BITS;
pub const SOURCE_WINDOW_COLUMNS: u32 = 1 << SOURCE_COLUMN_BITS;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceLayout {
    window_bits: u32,
    column_bits: u32,
}

impl SourceLayout {
    pub const fn new(window_bits: u32, column_bits: u32) -> Option<Self> {
        if window_bits > 0 && column_bits > 0 && window_bits + column_bits == 13 {
            Some(Self {
                window_bits,
                column_bits,
            })
        } else {
            None
        }
    }

    pub(crate) const fn window_bits(self) -> u32 {
        self.window_bits
    }

    pub(crate) const fn column_bits(self) -> u32 {
        self.column_bits
    }
}

pub const DEFAULT_SOURCE_LAYOUT: SourceLayout = SourceLayout {
    window_bits: SOURCE_WINDOW_BITS,
    column_bits: SOURCE_COLUMN_BITS,
};
// Compiler-private backing and destination coordinates. These are not source-lane fields.
pub(crate) const SLOT_BITS: u32 = 4; // ≤16 logical backings/layer
pub(crate) const COL_BITS: u32 = 10; // ≤1024 logical cols/backing
pub(crate) const CELL_BITS: u32 = 14; // smem cell index
pub(crate) const LDC_SUB_BITS: u32 = 2;
pub(crate) const LDC_IDX_BITS: u32 = 12; // ldc_idx < 4096
pub(crate) const DESC_BITS: u32 = 14; // special-source descriptor index
pub(crate) const MAX_SLOTS: u32 = 1 << SLOT_BITS; // 16
pub const MAX_COLS: u32 = 1 << COL_BITS; // 1024
pub(crate) const MAX_LDC_IDX: u32 = 1 << LDC_IDX_BITS; // 4096
pub(crate) const MAX_CELL: u32 = 1 << CELL_BITS;
pub(crate) const MAX_DESC: u32 = 1 << DESC_BITS;
pub(crate) const MAX_ARITY: usize = 127; // 7-bit arity

// Operand-lane type tags ([tag:2] at bit 0; payload starts at TYPE_BITS).
pub(crate) const TAG_SOURCE: u16 = 0b00; // Source { [window:6 @2][column:7 @8] }
pub(crate) const TAG_SMEM: u16 = 0b01; // Smem { [cell @2] }
pub(crate) const TAG_LDC: u16 = 0b10; // Ldc { [sub:2 @2][idx @4] }
pub(crate) const TAG_SPECIAL: u16 = 0b11; // Special { [desc @2] }

// Dst lane: [tag:1 @0]; tag 0 = Smem { [cell @1] },
// tag 1 = GlobalMaterialize { [slot:4 @1][col @5] }.
pub(crate) const DST_TAG_BITS: u32 = 1;
pub(crate) const DST_TAG_SMEM: u16 = 0;
pub(crate) const DST_TAG_GLOBAL: u16 = 1;

// Arith header:
// [op:2][arity:7 @2][f0:1 @9][f1:1 @10][sign:1 @11][rsvd @12+].
pub(crate) const OPCODE_BITS: u32 = 2;
pub(crate) const ARITY_SHIFT: u32 = OPCODE_BITS; // 2
pub(crate) const ARITY_BITS: u32 = 7;
pub(crate) const F0_SHIFT: u32 = ARITY_SHIFT + ARITY_BITS; // 9
pub(crate) const F1_SHIFT: u32 = F0_SHIFT + 1; // 10
pub(crate) const SIGN_SHIFT: u32 = F1_SHIFT + 1; // 11

// Mov header: [op=3:2][dir:2 @2][field:1 @4][rsvd @5+].
pub(crate) const MOV_DIR_SHIFT: u32 = OPCODE_BITS; // 2
pub(crate) const MOV_DIR_BITS: u32 = 2;
pub(crate) const MOV_FIELD_SHIFT: u32 = MOV_DIR_SHIFT + MOV_DIR_BITS; // 4

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Opcode {
    Add = 0,
    Mul = 1,
    Fma = 2,
    Mov = 3,
}

/// Field of the operands consumed by an instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OperandField {
    Base = 0,
    Ext = 1,
}

impl OperandField {
    pub(crate) const fn lanes(self) -> usize {
        match self {
            Self::Base => 1,
            Self::Ext => super::BF_LANES_PER_E4_BUCKET,
        }
    }
}

impl From<gkr_eval_ir::FieldKind> for OperandField {
    fn from(value: gkr_eval_ir::FieldKind) -> Self {
        match value {
            gkr_eval_ir::FieldKind::Base => Self::Base,
            gkr_eval_ir::FieldKind::Ext => Self::Ext,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    Plus = 0,
    Minus = 1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MovDir {
    AccFromSrc = 0,
    DstFromAcc = 1,
    DstFromSrc = 2,
} // 3 reserved

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LdcSub {
    Const = 0,
    ConstDerivedE4 = 1,
    ArgDerivedE4 = 2,
    Special = 3,
}

/// Field elements encoded inline instead of occupying constant-bank slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Special {
    Zero = 0,
    One = 1,
    NegOne = 2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperandLine {
    /// Compiler-private source coordinate. Final encoding must bind this first.
    LogicalGlobal {
        slot: u8,
        col: u16,
    },
    /// Final physical source coordinate carried by the 16-bit program lane.
    Source {
        window: u8,
        column: u16,
    },
    Smem {
        cell: u16,
    },
    Ldc {
        sub: LdcSub,
        idx: u16,
    },
    Special {
        desc: u16,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DstLine {
    Smem { cell: u16 },
    GlobalMaterialize { slot: u8, col: u16 },
}

/// `Mul::negate_acc` rides the sign bit and means "negate the acc first";
/// zero-arity Mul is legal iff set
/// (pure acc negation). Zero-arity Add stays illegal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Add {
        field: OperandField,
        sign: Sign,
        operands: Vec<OperandLine>,
    },
    Mul {
        field: OperandField,
        negate_acc: bool,
        operands: Vec<OperandLine>,
    },
    Fma {
        field_lhs: OperandField,
        field_rhs: OperandField,
        sign: Sign,
        pairs: Vec<(OperandLine, OperandLine)>,
    },
    Mov {
        dir: MovDir,
        field: OperandField,
        dst: Option<DstLine>,
        src: Option<OperandLine>,
    },
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub instrs: Vec<Instr>,
}

#[cfg(test)]
mod tests {
    use super::*;

    const CUDA_ISA: &str = include_str!("../../../gkr/native/gkr/eval_vm_isa.cuh");

    fn cpp_expr(name: &str) -> &str {
        CUDA_ISA
            .lines()
            .find_map(|line| {
                let line = line.trim();
                let prefix = format!("constexpr u32 {name} = ");
                line.strip_prefix(&prefix)?
                    .split_once(';')
                    .map(|(value, _)| value)
            })
            .unwrap_or_else(|| panic!("missing CUDA ISA constant {name}"))
    }

    fn assert_literal(name: &str, value: u32) {
        assert_eq!(cpp_expr(name), value.to_string(), "{name}");
    }

    #[test]
    fn cpu_forward_cuda_isa_matches_rust() {
        for (name, value) in [
            ("FWD_VM_OP_BITS", OPCODE_BITS),
            ("FWD_VM_HDR_ARITY_BITS", ARITY_BITS),
            ("FWD_VM_MOV_DIR_BITS", MOV_DIR_BITS),
            ("FWD_VM_OPERAND_TAG_BITS", TYPE_BITS),
            ("FWD_VM_SOURCE_WINDOW_BITS", SOURCE_WINDOW_BITS),
            ("FWD_VM_SOURCE_COLUMN_BITS", SOURCE_COLUMN_BITS),
            ("FWD_VM_LDC_SUB_BITS", LDC_SUB_BITS),
            ("FWD_VM_DST_TAG_BITS", DST_TAG_BITS),
            ("FWD_VM_DST_SLOT_BITS", SLOT_BITS),
            ("FWD_VM_OP_ADD", Opcode::Add as u32),
            ("FWD_VM_OP_MUL", Opcode::Mul as u32),
            ("FWD_VM_OP_FMA", Opcode::Fma as u32),
            ("FWD_VM_OP_MOV", Opcode::Mov as u32),
            ("FWD_VM_MOV_ACC_FROM_SRC", MovDir::AccFromSrc as u32),
            ("FWD_VM_MOV_DST_FROM_ACC", MovDir::DstFromAcc as u32),
            ("FWD_VM_MOV_DST_FROM_SRC", MovDir::DstFromSrc as u32),
            ("FWD_VM_OPERAND_SOURCE", TAG_SOURCE as u32),
            ("FWD_VM_OPERAND_SMEM", TAG_SMEM as u32),
            ("FWD_VM_OPERAND_LDC", TAG_LDC as u32),
            ("FWD_VM_OPERAND_SPECIAL", TAG_SPECIAL as u32),
            ("FWD_VM_DST_SMEM", DST_TAG_SMEM as u32),
            ("FWD_VM_DST_GLOBAL", DST_TAG_GLOBAL as u32),
        ] {
            assert_literal(name, value);
        }

        for (name, expression) in [
            ("FWD_VM_HDR_ARITY_SHIFT", "FWD_VM_OP_BITS"),
            (
                "FWD_VM_HDR_F0_SHIFT",
                "FWD_VM_HDR_ARITY_SHIFT + FWD_VM_HDR_ARITY_BITS",
            ),
            ("FWD_VM_HDR_F1_SHIFT", "FWD_VM_HDR_F0_SHIFT + 1"),
            ("FWD_VM_HDR_SIGN_SHIFT", "FWD_VM_HDR_F1_SHIFT + 1"),
            ("FWD_VM_MOV_DIR_SHIFT", "FWD_VM_OP_BITS"),
            (
                "FWD_VM_MOV_FIELD_SHIFT",
                "FWD_VM_MOV_DIR_SHIFT + FWD_VM_MOV_DIR_BITS",
            ),
            ("FWD_VM_SOURCE_WINDOW_SHIFT", "FWD_VM_OPERAND_TAG_BITS"),
            (
                "FWD_VM_SOURCE_COLUMN_SHIFT",
                "FWD_VM_SOURCE_WINDOW_SHIFT + FWD_VM_SOURCE_WINDOW_BITS",
            ),
            ("FWD_VM_OPERAND_CELL_SHIFT", "FWD_VM_OPERAND_TAG_BITS"),
            ("FWD_VM_OPERAND_DESC_SHIFT", "FWD_VM_OPERAND_TAG_BITS"),
            ("FWD_VM_LDC_SUB_SHIFT", "FWD_VM_OPERAND_TAG_BITS"),
            (
                "FWD_VM_LDC_IDX_SHIFT",
                "FWD_VM_LDC_SUB_SHIFT + FWD_VM_LDC_SUB_BITS",
            ),
            ("FWD_VM_DST_CELL_SHIFT", "FWD_VM_DST_TAG_BITS"),
            ("FWD_VM_DST_SLOT_SHIFT", "FWD_VM_DST_TAG_BITS"),
            (
                "FWD_VM_DST_COL_SHIFT",
                "FWD_VM_DST_SLOT_SHIFT + FWD_VM_DST_SLOT_BITS",
            ),
        ] {
            assert_eq!(cpp_expr(name), expression, "{name}");
        }

        assert_eq!(ARITY_SHIFT, OPCODE_BITS);
        assert_eq!(F0_SHIFT, ARITY_SHIFT + ARITY_BITS);
        assert_eq!(F1_SHIFT, F0_SHIFT + 1);
        assert_eq!(SIGN_SHIFT, F1_SHIFT + 1);
        assert_eq!(
            SOURCE_COLUMN_SHIFT,
            SOURCE_WINDOW_SHIFT + SOURCE_WINDOW_BITS
        );
    }
}
