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
pub mod encode;
pub use routines::{
    lowering_kind, routine_for_cache, routine_for_gate, routine_table, ChallengeUse, FieldRole,
    LoweringKind, RoutineSchema, Shape,
};

/// Macro routine id (7-bit wire id). Discriminants are dense (id == index) and
/// 1:1 with the FORWARD FORMULA — there is exactly one `RoutineId` per distinct
/// per-row math, mirroring the production primitive-kind tags `PK_*`
/// (`gpu/circuit_prover/src/prover/gkr/forward/bench_interp/lower.rs:173-188`).
/// The earlier v2 ids (Task 1.3/1.4) were LOSSY — `LookupNumDen` collapsed ~15
/// distinct lookup formulas onto one id and `ProductStep` collapsed a·b with
/// `(v−1)·m+1`. This set restores the 1:1 discriminator (Task R1) without any
/// bit-layout change (still 7-bit, `MAX_ROUTINE_ID = 127`). The full descriptor
/// table + per-GateKind/CacheKind mapping live in `routines.rs`, which reads the
/// ids via `super::RoutineId`.
///
/// Each variant names its forward formula + the `PK_*` anchor it mirrors (or
/// "no PK" when the formula is real corpus math that the GPU bench census in
/// `lower.rs:387-439` does not yet cover — those stay `todo!` until R3, exactly
/// like the PK-anchored ids). `g` = lookup additive challenge γ; `sh(x)=x+g`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RoutineId {
    /// `acc = Σ_k α^k · col_k` per-layer GateOutput fold (compiler-emitted; no
    /// GateKind maps here). PK: none (E_FMA_ALPHA, not a payload kind).
    GateOutputFold = 0,
    /// `out = a·b` (two ext factors). PK_PRODUCT. Gates: `TrivialProduct`,
    /// `InitialGrandProductFromCaches`, `UnbalancedGrandProductWithCache`
    /// (`scalar·input`).
    Product = 1,
    /// `out = (v−1)·m + 1` (mask into identity). PK_MASK_IDENTITY. Gate:
    /// `MaskIntoIdentityProduct`.
    MaskIdentity = 2,
    /// `num = a·d + c·b; den = b·d` (aggregate two rational pairs). PK_LOOKUP_PAIR4.
    /// Gate: `AggregateLookupRationalPair`.
    AggregateLookupPair = 3,
    /// `num = sh(b)+sh(d); den = sh(b)·sh(d)`, BASE inputs. PK_LOOKUP_BASE_PAIR.
    /// Gates: `LookupPairFromMaterializedBaseInputs`, `LookupPairFromBaseInputs`.
    LookupBasePair = 4,
    /// Same symmetric-pair formula, EXT inputs. PK_LOOKUP_EXT_PAIR. Gates:
    /// `LookupPairFromMaterializedVectorInputs`, `LookupPairFromVectorInputs`,
    /// `LookupPairFromCachedVectorInputs`.
    LookupExtPair = 5,
    /// `num = sh(d) − c·sh(b); den = sh(b)·sh(d)`, BASE input + setup multiplicity.
    /// PK_LOOKUP_BASE_MINUS_MULT. Gate: `LookupFromMaterializedBaseInputWithSetup`.
    LookupBaseMinusMult = 6,
    /// Same minus-multiplicity formula, EXT input. PK_LOOKUP_EXT_MINUS_MULT.
    /// Gates: `LookupFromMaterializedVectorInputWithSetup`,
    /// `LookupFromVectorInputWithSetup`.
    LookupExtMinusMult = 7,
    /// `num = a·sh(d) − c·sh(b); den = sh(b)·sh(d)` (all four lanes cached).
    /// PK_LOOKUP_CACHED_DENS. Gate: `LookupWithCachedDensAndSetup`.
    LookupCachedDens = 8,
    /// `num = a·sh(d) + b; den = b·sh(d)` (unbalanced), BASE inputs.
    /// PK_LOOKUP_UNBALANCED_BASE. Gate: `LookupUnbalancedPairWithMaterializedBaseInputs`.
    LookupUnbalancedBase = 9,
    /// Same unbalanced formula, EXT inputs. PK_LOOKUP_UNBALANCED_EXT. Gates:
    /// `LookupUnbalancedPairWithMaterializedVectorInputs`,
    /// `LookupUnbalancedPairWithVectorInputs`.
    LookupUnbalancedExt = 10,
    /// Single ext value = the α-folded vector-lookup affine combination (with
    /// decoder-fill select). PK_VEC_LOOKUP_GATE. Gate: `MaterializedVectorLookupInput`.
    VectorLookupGate = 11,
    /// Single BASE value = a column's linear combination (gate form of the
    /// single-column lookup). PK: none for the gate (the CACHE form is
    /// PK_CACHE_SINGLE_COLUMN); distinct forward formula from everything else.
    /// Gate: `MaterializeSingleLookupInput`.
    MaterializeSingleLookup = 12,
    /// `num = a·sh(d) − c·sh(b); den = sh(b)·sh(d)` with `a` = decoder predicate
    /// and `b` derived inline from a vector input (dens NOT cached). Same closed
    /// form as `LookupCachedDens` but DISTINCT operand provenance, so a distinct
    /// routine. PK: none (decoder-specific, outside the GPU bench census). Gates:
    /// `LookupWithDensAndCachedSetup`, `LookupWithDensAndSetupExpressions`.
    LookupDecoderDensSetup = 13,
    /// `out = tuple(a)·tuple(b)` — product of two INLINED memory-tuple affine
    /// combinations (not raw operand factors). PK: none (outside the GPU bench
    /// census). Gate: `InitialGrandProductWithoutCaches`.
    GrandProductWithoutCaches = 14,
    /// `out = tuple(input)` — materialize ONE memory-tuple affine combination
    /// (NOT a product). PK: none (outside the GPU bench census). Gate:
    /// `MaterializeGrandProductTermExpression`.
    MaterializeGrandProductTerm = 15,
    /// SingleColumnLookup cache: base gather (virtual_setup[mapping[gid]]) + base
    /// store. PK_CACHE_SINGLE_COLUMN. Cache: `SingleColumnLookup`.
    SingleColumnLookup = 16,
    /// VectorizedLookup cache: ext gather over a column vector, optionally
    /// decoder-mapped. PK_CACHE_VECTORIZED_LOOKUP. Cache: `VectorizedLookup`.
    VectorizedLookup = 17,
    /// VectorizedLookupSetup cache: row-indexed setup gather, zero-padded beyond
    /// generic_lookup_len. PK_CACHE_LOOKUP_SETUP. Cache: `VectorizedLookupSetup`.
    VectorizedLookupSetup = 18,
    /// MemoryTuple cache: role-tagged linear terms + address-space arm/payload.
    /// PK_CACHE_MEMORY_TUPLE. Cache: `MemoryTuple`.
    MemoryTuple = 19,
    /// Memory inits/teardowns initial `(num,den)` pair from a setup tuple. PK:
    /// none (not in the GPU bench census). Gate: `InitsOrTeardownsInitialPair`.
    MemoryInitTeardownPair = 20,
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
    /// `n_operands` is the operand count, carried in the header's spare bits
    /// (family(1)+routine(7) leaves a full byte) — exactly like arith `arity`.
    /// There is NO separate count lane and NO `Fixed/Variable` shape split —
    /// every macro states its operand count here. 7-bit (≤127). For the
    /// memory-tuple macro, `n_operands` = the number of role-tagged terms; the
    /// as-arm/payload still ride their own small lane.
    Macro { routine: u8, n_operands: u8 },
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
            header: Header::Macro { routine: RoutineId::LookupExtPair as u8, n_operands: 1 },
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
