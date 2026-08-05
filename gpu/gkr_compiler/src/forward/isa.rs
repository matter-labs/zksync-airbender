//! ISA vocabulary for the forward-eval VM (spec §6, §7). No encoding here.
//!
//! The lane-layout constants below are the SINGLE Rust definition site for the
//! 16-bit wire format (`encode.rs` routes every pack/unpack through them). The
//! CUDA interpreter mirrors them as the `FWD_VM_*` lane-layout constexpr block
//! in `gpu/circuit_prover/native/prover/gkr/forward/fwd_vm.cuh` — the two
//! sides cannot share a header, so keep the blocks in sync.

pub const TYPE_BITS: u32 = 2;
pub const TYPE_MASK: u16 = (1 << TYPE_BITS) - 1;
pub const FIRST_ACCESS_SHIFT: u32 = TYPE_BITS;
pub const SOURCE_WINDOW_SHIFT: u32 = FIRST_ACCESS_SHIFT + 1;
pub const SOURCE_WINDOW_BITS: u32 = 6;
pub const SOURCE_WINDOW_MASK: u16 = (1 << SOURCE_WINDOW_BITS) - 1;
pub const SOURCE_COLUMN_SHIFT: u32 = SOURCE_WINDOW_SHIFT + SOURCE_WINDOW_BITS;
pub const SOURCE_COLUMN_BITS: u32 = 7;
pub const SOURCE_COLUMN_MASK: u16 = (1 << SOURCE_COLUMN_BITS) - 1;
pub const MAX_SOURCE_WINDOWS: u32 = 1 << SOURCE_WINDOW_BITS;
pub const SOURCE_WINDOW_COLUMNS: u32 = 1 << SOURCE_COLUMN_BITS;
// Compiler-private backing and destination coordinates. These are not source-lane fields.
pub const SLOT_BITS: u32 = 4; // ≤16 logical backings/layer
pub const COL_BITS: u32 = 10; // ≤1024 logical cols/backing
pub const CELL_BITS: u32 = 14; // smem cell index
pub const LDC_SUB_BITS: u32 = 2;
pub const LDC_SUB_MASK: u16 = (1 << LDC_SUB_BITS) - 1;
pub const LDC_IDX_BITS: u32 = 12; // ldc_idx < 4096
pub const DESC_BITS: u32 = 14; // special-source descriptor index
pub const MAX_SLOTS: u32 = 1 << SLOT_BITS; // 16
pub const MAX_COLS: u32 = 1 << COL_BITS; // 1024
pub const MAX_LDC_IDX: u32 = 1 << LDC_IDX_BITS; // 4096
pub const MAX_CELL: u32 = 1 << CELL_BITS;
pub const MAX_DESC: u32 = 1 << DESC_BITS;
pub const MAX_ARITY: usize = 127; // 7-bit arity

// Operand-lane type tags ([tag:2] at bit 0; payload starts at TYPE_BITS).
pub const TAG_SOURCE: u16 = 0b00; // Source { [first @2][window:6 @3][column:7 @9] }
pub const TAG_SMEM: u16 = 0b01; // Smem { [cell @2] }
pub const TAG_LDC: u16 = 0b10; // Ldc { [sub:2 @2][idx @4] }
pub const TAG_SPECIAL: u16 = 0b11; // Special { [desc @2] }

// Dst lane: [tag:1 @0]; tag 0 = Smem { [cell @1] },
// tag 1 = GlobalMaterialize { [slot:4 @1][col @5] }.
pub const DST_TAG_BITS: u32 = 1;
pub const DST_TAG_MASK: u16 = (1 << DST_TAG_BITS) - 1;
pub const DST_TAG_SMEM: u16 = 0;
pub const DST_TAG_GLOBAL: u16 = 1;

// Arith header:
// [op:2][arity:7 @2][f0:1 @9][f1:1 @10][promote:1 @11][sign:1 @12][rsvd @13+].
pub const OPCODE_BITS: u32 = 2;
pub const OPCODE_MASK: u16 = (1 << OPCODE_BITS) - 1;
pub const ARITY_SHIFT: u32 = OPCODE_BITS; // 2
pub const ARITY_BITS: u32 = 7;
pub const ARITY_MASK: u16 = (1 << ARITY_BITS) - 1; // 0x7f; MAX_ARITY fits
pub const F0_SHIFT: u32 = ARITY_SHIFT + ARITY_BITS; // 9
pub const F1_SHIFT: u32 = F0_SHIFT + 1; // 10
pub const PROMOTE_SHIFT: u32 = F1_SHIFT + 1; // 11
pub const SIGN_SHIFT: u32 = PROMOTE_SHIFT + 1; // 12
pub const ARITH_RSVD_SHIFT: u32 = SIGN_SHIFT + 1; // 13

// Mov header: [op=3:2][dir:2 @2][field:1 @4][rsvd @5+].
pub const MOV_DIR_SHIFT: u32 = OPCODE_BITS; // 2
pub const MOV_DIR_BITS: u32 = 2;
pub const MOV_DIR_MASK: u16 = (1 << MOV_DIR_BITS) - 1;
pub const MOV_FIELD_SHIFT: u32 = MOV_DIR_SHIFT + MOV_DIR_BITS; // 4
pub const MOV_RSVD_SHIFT: u32 = MOV_FIELD_SHIFT + 1; // 5

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Opcode {
    Add = 0,
    Mul = 1,
    Fma = 2,
    Mov = 3,
}

/// Per-instruction operand field bit(s) (spec §5). The field of the operands
/// consumed by THIS instruction — not the result field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OperandField {
    Base = 0,
    Ext = 1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

/// `LdcSub::Special` payloads — the special field elements, encoded inline instead
/// of via the const bank (so they never occupy GPU `__constant__` storage). `NegOne`
/// (negate / additive −1) and `One` (additive 1) ARE emitted; `Zero` is never emitted
/// — additive 0 is identity and multiplicative 0 is an annihilator, so it is always
/// elided, and validation rejects a `Zero` operand if one ever leaks through.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Special {
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
    /// Compiler-private backward fold of a logical read source.
    LogicalFold {
        slot: u8,
        col: u16,
        desc: u16,
    },
    /// Final physical source coordinate carried by the 16-bit program lane.
    Source {
        window: u8,
        column: u8,
        first_access: bool,
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

/// `promote` (arith header bit 11) marks the instruction at which the acc lifts
/// base→ext (design §1.1); encode/decode round-trip it faithfully, the iff
/// canonicality rule is validation's job. `Mul::negate_acc` rides the sign bit
/// (bit 12) and means "negate the acc first"; zero-arity Mul is legal iff set
/// (pure acc negation). Zero-arity Add stays illegal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Add {
        field: OperandField,
        sign: Sign,
        promote: bool,
        operands: Vec<OperandLine>,
    },
    Mul {
        field: OperandField,
        promote: bool,
        negate_acc: bool,
        operands: Vec<OperandLine>,
    },
    Fma {
        field_lhs: OperandField,
        field_rhs: OperandField,
        sign: Sign,
        promote: bool,
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
