//! ISA-v2 types and width constants (spec §5). Reform of v1 `isa.rs`:
//! two header families (Arith / Macro), typed operand lanes, footer dsts,
//! NO opaque payload, NO e4_result bit (store-width is a relation, §5).
//!
//! `RoutineId` lives HERE (not in routines.rs) because the ISA types reference
//! it; `routines.rs` (Task 1.4) reads it via `super::RoutineId` and owns the
//! descriptor table/lowering. `pub mod routines;` (Task 1.4) is declared below;
//! `pub mod encode;` (Task 1.5) is added when that file is created — do NOT
//! declare a module before its file exists (finding F1: hard
//! `error[E0583] file not found`).

pub mod routines;
pub use routines::{
    lowering_kind, routine_for_cache, routine_for_gate, routine_table, ChallengeUse, FieldRole,
    LoweringKind, RoutineSchema, Shape,
};

/// Macro routine id (7-bit wire id). Discriminants are dense and stable; the
/// full descriptor table + lowering live in `routines.rs` (Task 1.4), which
/// references this enum via `super::RoutineId`. Seeded with the routines the
/// 1.3/1.5 tests touch; Task 1.4 extends it to the full §3/§4/§9 set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RoutineId {
    GateOutputFold = 0,      // gkr_forward_generation.cuh E_FMA_ALPHA fold
    LookupNumDen = 1,        // lookup num/den, lookup_helpers.cuh
    GrandProductStep = 2,    // permutation grand-product step
    AggregateLookupPair = 3, // AggregateLookupRationalPair cascade
    SingleColumnLookup = 4,  // base gather + base store, cache_relation.rs:347
    MemoryTuple = 5,         // cache_relation.rs:91, role-tagged + as-arm
    // --- Task 1.4 extension: the remaining §3/§4/§9 corpus routines, dense
    // (id == index) after MemoryTuple. ids 0..=5 above are STABLE (the 1.3/1.5
    // round-trip vectors reference LookupNumDen + MemoryTuple by name).
    VectorizedLookup = 6,    // VectorizedLookup cache gather, cache_relation.rs:382
    VectorizedLookupSetup = 7, // row-indexed setup gather, gkr_forward_generation.cuh LOOKUP_SETUP
    ProductStep = 8,         // per-row product / mask-identity, lookup_helpers.cuh gkr_eval_product
    MemoryInitTeardownPair = 9, // inits/teardowns initial num/den pair, lookup_helpers.cuh
}

// --- Width constants (the 16-bit lanes, spec §5) ---
pub const MATRIX_SLOT_BITS: u32 = 4; // GKR_MAX_SLOTS = 16 backings/layer
pub const COL_BITS: u32 = 10;        // R3 option (c): 1024-col cap (cap-guarded)
pub const SLOT_CELL_BITS: u32 = 7;   // smem cell index (e4 = 4 consecutive)
pub const LDC_SUB_BITS: u32 = 2;
pub const LDC_IDX_BITS: u32 = 12;
pub const GATHER_DESC_BITS: u32 = 13; // field:1 + desc:13
pub const MAX_ARITY: u32 = 127;       // 7-bit arity (clears the 64-lane MaxQuad cliff)
pub const MAX_ROUTINE_ID: u8 = 127;   // 7-bit routine-id

// LdcSub::Special indices:
pub const SPECIAL_ZERO: u16 = 0;
pub const SPECIAL_ONE: u16 = 1;
pub const SPECIAL_NEG_ONE: u16 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithOp { Sum = 0, Prod = 1, Dot = 2, Fma = 3 }

/// LDC sub-bank (kind 10): which constant-cache region the idx addresses.
/// The axis is TRANSFER CHANNEL, not provenance (spec §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LdcSub {
    /// bf constant table (raw coeffs; never 0/1/-1).
    Const = 0,
    /// device `__constant__` bank: α-powers (column-indexed) + γ forms [γ,γ²,2γ].
    ConstChallenge = 1,
    /// kernel-arg constant bank: perm-linearization + additive-seed challenges.
    ArgChallenge = 2,
    /// idx selects Zero/One/NegOne (SPECIAL_* above).
    Special = 3,
}

/// Which gather variant an IndirectSource descriptor selects (spec §4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IndirectKind {
    MappedVirtualBf = 0,   // SingleColumnLookup: virtual_setup[mapping[gid]], base
    MappedGenericE4 = 1,   // VectorizedLookup plain: n[mapping[gid]], ext
    DecoderMappedE4 = 2,   // VectorizedLookup w/ decoder: predicate + fill
    RowIndexedSetupE4 = 3, // VectorizedLookupSetup: n[gid] + length guard
}

/// 16-bit operand lane: `[kind:2][payload:14]` (spec §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    /// kind 00 LDG: matrix-slot + column. Field implied by the slot's logical key.
    Affine { slot: u8, col: u16 },
    /// kind 01 smem: explicit field + cell.
    Slot { e4: bool, cell: u8 },
    /// kind 10 LDC: sub-bank + index.
    Ldc { sub: LdcSub, idx: u16 },
    /// kind 11 gather: explicit field + descriptor index.
    Indirect { e4: bool, desc: u16 },
}

/// 16-bit footer dst lane: `[kind:1][addr:14]` (+1 spare) (spec §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dst {
    /// kind 0 smem: transient multi-use base intermediate.
    Slot { e4: bool, cell: u8 },
    /// kind 1 committed store (cache backing / gate-output / inner-layer).
    /// Field implied by the matrix-slot. Mandatory for backward.
    Materialize { slot: u8, col: u16 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Header {
    Arith { op: ArithOp, arity: u8 },
    Macro { routine: u8 },
}

/// Memory-tuple macro's variable shape (spec §5): role-tagged operands + an
/// address-space arm/payload. Present only for the memory-tuple routine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemTup {
    /// 0..=8 counted linear terms, each tagged with its production role index
    /// (addr lo/hi, timestamp lo/hi, value parts — forward/kernels/mod.rs:31).
    pub roles: Vec<(u8, Operand)>,
    /// address-space arm: 0 Empty, 1 Constant, 2 IsRegister, 3 IsRam.
    pub as_arm: u8,
    /// dynamic base-column source (IsRegister/IsRam) or Const lane (Constant);
    /// None for Empty.
    pub as_payload: Option<Operand>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instr2 {
    pub header: Header,
    /// Arith: `arity` operands (Dot = 2·k consecutive pairs). Macro-fixed:
    /// routine-defined count. Macro-memtup: empty here (carried in `memtup`).
    pub operands: Vec<Operand>,
    /// 1 (arith) or routine-defined count (macro multi-output, e.g. num/den).
    pub dsts: Vec<Dst>,
    /// Some(..) only for the memory-tuple routine.
    pub memtup: Option<MemTup>,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Program2 {
    pub instrs: Vec<Instr2>,
    /// Deduplicated bf constants (never 0/1/-1), indexed by `LdcSub::Const`.
    pub consts: Vec<u32>,
    pub n_slot_cells: u16,
    /// Distinct matrix-slot backings used (<= 16).
    pub n_matrix_slots: u8,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn width_constants_consistent() {
        // operand: kind(2) + payload(14) = 16
        assert_eq!(MATRIX_SLOT_BITS + COL_BITS, 14);
        assert_eq!(SLOT_CELL_BITS + 1, 8); // field:1 + cell:7
        assert_eq!(LDC_SUB_BITS + LDC_IDX_BITS, 14);
        // routine-id fits 7 bits; arity fits 7 bits
        assert!(MAX_ROUTINE_ID < (1 << 7));
        assert!(MAX_ARITY < (1 << 7));
        // col cap = 2^10 (R3 option c)
        assert_eq!(1u32 << COL_BITS, 1024);
    }

    #[test]
    fn build_one_of_each_family() {
        let arith = Instr2 {
            header: Header::Arith { op: ArithOp::Sum, arity: 3 },
            operands: vec![
                Operand::Affine { slot: 0, col: 7 },
                Operand::Ldc { sub: LdcSub::Const, idx: 2 },
                Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_NEG_ONE },
            ],
            dsts: vec![Dst::Slot { e4: false, cell: 1 }],
            memtup: None,
        };
        assert_eq!(arith.operands.len(), 3);

        let mac = Instr2 {
            header: Header::Macro { routine: RoutineId::LookupNumDen as u8 },
            operands: vec![Operand::Indirect { e4: true, desc: 0 }],
            dsts: vec![
                Dst::Materialize { slot: 1, col: 10 },
                Dst::Materialize { slot: 1, col: 11 },
            ],
            memtup: None,
        };
        assert_eq!(mac.dsts.len(), 2);
    }
}
