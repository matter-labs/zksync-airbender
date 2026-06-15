//! Macro routine + descriptor table (spec §9 phase-1 gate). One row per
//! hardcoded per-row eval. The decoder, CPU oracle, static report, and CUDA
//! interpreter all read this table so they agree on ids/shapes/fields.

use cs::gkr_compiler::codegen_ir::{CacheKind, GateKind};

/// Field behaviour of an operand/output lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldRole { Base, Ext, /// lub of operands, per-operand lift at read
    Mixed }

/// Operand WIRE STRUCTURE of a routine (drives decode, Task 1.5). The operand
/// COUNT is NOT part of the shape — it is carried in `Header::Macro.n_operands`
/// for every macro (no count lane, no `Fixed(n)`/`Variable` split). Shape now
/// only distinguishes the two wire structures: plain operands vs the
/// memory-tuple role-tagged form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// Plain: `n_operands` (from the header) consecutive operand lanes.
    Plain,
    /// Memory-tuple: an as-arm lane, then `n_operands` role-tagged
    /// `(role, operand)` pairs, then an optional as-payload lane (§5).
    MemTuple,
}

/// How a forward gate lowers (finding 3). Only `Macro` requires a routine;
/// arithmetic shapes lower through the arith family, aliases/scratch emit no
/// instruction. Keeping these separate prevents bogus routines for arith gates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoweringKind {
    /// base arithmetic (e.g. LinearBaseField) → Header::Arith (Task 2.4)
    Arith,
    /// per-row macro (fold / lookup / grand-product / mapped lookup) → routine
    Macro,
    /// `CopyInBaseField`/`CopyInExtensionField` column copy aliased to an input
    /// backing → no instruction (Task 2.6). NOT for constraint gates.
    Alias,
    /// constraint gate (Enforce*): empty dst, no forward output, emits no
    /// instruction — NOT an alias-to-input.
    Constraint,
    /// scratch-prefilled (MaxQuadratic) → no instruction (Task 1.2 / §4)
    ScratchSkip,
    /// a kind no lowering handles — hard failure at the phase-1 gate
    Unsupported,
}

/// Which challenge bank(s) a routine reads (spec §5 transfer channel).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeUse { None, ConstAlphaGamma, ArgPermAdditive, Both }

#[derive(Clone, Debug)]
pub struct RoutineSchema {
    pub id: u8,
    pub name: &'static str,
    pub shape: Shape,
    pub operand_field: FieldRole,
    pub output_count: u8,
    pub output_field: FieldRole,
    pub challenge: ChallengeUse,
    /// reference impl anchor (flat.cuh / lookup_helpers.cuh / cache_relation.rs).
    pub reference: &'static str,
}

// RoutineId is defined in `isa_v2/mod.rs` (Task 1.3, finding F1) because the
// ISA types reference it. Task 1.4 EXTENDS that enum (in mod.rs) to the full
// §3/§4/§9 set, keeping it dense; routines.rs only owns the schema/table/
// lowering and reads the ids via `super::RoutineId`. Linear/quadratic axis:
// the low discriminant bit (lookup_helpers.cuh `_quadratic` variants) —
// documented per-row in the table.
use super::RoutineId;

pub fn routine_table() -> &'static [RoutineSchema] {
    // One row per RoutineId (Task R1: the FINER 1:1 id↔forward-formula set —
    // see the per-variant doc comments in isa_v2/mod.rs for each row's formula +
    // PK_* anchor + the GateKind/CacheKind(s) it owns). Dense (id == index); the
    // (B) decode-soundness gate asserts this. `output_count` is load-bearing:
    // `macros::macro_gate_dsts` reads it to size the footer (lookup num/den ids
    // → 2; product / single-value / cache ids → 1). The math is implemented in
    // the interpreter only for the two pinned ids (Product, AggregateLookupPair),
    // R3 fills the rest; the schema is final regardless.
    use ChallengeUse::*;
    use FieldRole::*;
    use Shape::*;
    const T: &[RoutineSchema] = &[
        // 0 — per-layer GateOutput fold: ∑ α^k · col_k accumulator (Task 2.5
        // reads α-powers column-indexed + γ as [γ,γ²,2γ]). Per-gate column count
        // rides the header → Plain. No GateKind maps here (compiler-emitted for
        // the output combine).
        RoutineSchema { id: 0, name: "GateOutputFold", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ConstAlphaGamma,
            reference: "gkr_forward_generation.cuh E_FMA_ALPHA" },
        // 1 — Product: `out = a·b` (PK_PRODUCT, gkr_eval_product). Two ext factors
        // → 1 ext. Gates: TrivialProduct, InitialGrandProductFromCaches,
        // UnbalancedGrandProductWithCache.
        RoutineSchema { id: 1, name: "Product", shape: Plain, operand_field: Ext,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "lookup_helpers.cuh gkr_eval_product (PK_PRODUCT)" },
        // 2 — MaskIdentity: `out = (v−1)·m + 1` (PK_MASK_IDENTITY,
        // gkr_eval_mask_identity). Two operands → 1 ext. Gate:
        // MaskIntoIdentityProduct.
        RoutineSchema { id: 2, name: "MaskIdentity", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "lookup_helpers.cuh gkr_eval_mask_identity (PK_MASK_IDENTITY)" },
        // 3 — AggregateLookupPair: `num = a·d + c·b; den = b·d` (PK_LOOKUP_PAIR4).
        // 4 ext operands → 2 ext (aggregated num,den). Gate:
        // AggregateLookupRationalPair.
        RoutineSchema { id: 3, name: "AggregateLookupPair", shape: Plain, operand_field: Ext,
            output_count: 2, output_field: Ext, challenge: ConstAlphaGamma,
            reference: "lookup_helpers.cuh aggregate rational pair (PK_LOOKUP_PAIR4)" },
        // 4 — LookupBasePair: `num = sh(b)+sh(d); den = sh(b)·sh(d)`, BASE inputs
        // (PK_LOOKUP_BASE_PAIR; sh(x)=x+γ). 2 outputs. Gates:
        // LookupPairFromMaterializedBaseInputs, LookupPairFromBaseInputs.
        RoutineSchema { id: 4, name: "LookupBasePair", shape: Plain, operand_field: Base,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh gkr_eval_lookup_pair base (PK_LOOKUP_BASE_PAIR)" },
        // 5 — LookupExtPair: same symmetric-pair formula, EXT inputs
        // (PK_LOOKUP_EXT_PAIR). 2 outputs. Gates:
        // LookupPairFromMaterializedVectorInputs, LookupPairFromVectorInputs,
        // LookupPairFromCachedVectorInputs.
        RoutineSchema { id: 5, name: "LookupExtPair", shape: Plain, operand_field: Ext,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh gkr_eval_lookup_pair ext (PK_LOOKUP_EXT_PAIR)" },
        // 6 — LookupBaseMinusMult: `num = sh(d) − c·sh(b); den = sh(b)·sh(d)`,
        // BASE input + setup multiplicity (PK_LOOKUP_BASE_MINUS_MULT). 2 outputs.
        // Gate: LookupFromMaterializedBaseInputWithSetup.
        RoutineSchema { id: 6, name: "LookupBaseMinusMult", shape: Plain, operand_field: Mixed,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh lookup base minus-mult (PK_LOOKUP_BASE_MINUS_MULT)" },
        // 7 — LookupExtMinusMult: same minus-multiplicity formula, EXT input
        // (PK_LOOKUP_EXT_MINUS_MULT). 2 outputs. Gates:
        // LookupFromMaterializedVectorInputWithSetup, LookupFromVectorInputWithSetup.
        RoutineSchema { id: 7, name: "LookupExtMinusMult", shape: Plain, operand_field: Ext,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh lookup ext minus-mult (PK_LOOKUP_EXT_MINUS_MULT)" },
        // 8 — LookupCachedDens: `num = a·sh(d) − c·sh(b); den = sh(b)·sh(d)`, all
        // four lanes cached (PK_LOOKUP_CACHED_DENS). 2 outputs. Gate:
        // LookupWithCachedDensAndSetup.
        RoutineSchema { id: 8, name: "LookupCachedDens", shape: Plain, operand_field: Ext,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh lookup cached-dens (PK_LOOKUP_CACHED_DENS)" },
        // 9 — LookupUnbalancedBase: `num = a·sh(d) + b; den = b·sh(d)`
        // (unbalanced), BASE inputs (PK_LOOKUP_UNBALANCED_BASE). 2 outputs. Gate:
        // LookupUnbalancedPairWithMaterializedBaseInputs.
        RoutineSchema { id: 9, name: "LookupUnbalancedBase", shape: Plain, operand_field: Base,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh lookup unbalanced base (PK_LOOKUP_UNBALANCED_BASE)" },
        // 10 — LookupUnbalancedExt: same unbalanced formula, EXT inputs
        // (PK_LOOKUP_UNBALANCED_EXT). 2 outputs. Gates:
        // LookupUnbalancedPairWithMaterializedVectorInputs,
        // LookupUnbalancedPairWithVectorInputs.
        RoutineSchema { id: 10, name: "LookupUnbalancedExt", shape: Plain, operand_field: Ext,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh lookup unbalanced ext (PK_LOOKUP_UNBALANCED_EXT)" },
        // 11 — VectorLookupGate: single ext value = α-folded vector-lookup affine
        // combination with decoder-fill select (PK_VEC_LOOKUP_GATE). 1 output.
        // Gate: MaterializedVectorLookupInput.
        RoutineSchema { id: 11, name: "VectorLookupGate", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ConstAlphaGamma,
            reference: "gkr_forward_setup_generic_lookup vec gate (PK_VEC_LOOKUP_GATE)" },
        // 12 — MaterializeSingleLookup: single BASE value = a column's linear
        // combination (gate form of the single-column lookup; cache form is id
        // 16). 1 base output. Gate: MaterializeSingleLookupInput.
        RoutineSchema { id: 12, name: "MaterializeSingleLookup", shape: Plain, operand_field: Base,
            output_count: 1, output_field: Base, challenge: ArgPermAdditive,
            reference: "cache_relation.rs SingleColumnLookup (gate form)" },
        // 13 — LookupDecoderDensSetup: `num = a·sh(d) − c·sh(b); den = sh(b)·sh(d)`
        // with `a` = decoder predicate, `b` derived inline from a vector input
        // (dens NOT cached). Same closed form as id 8, distinct operand
        // provenance. 2 outputs. Gates: LookupWithDensAndCachedSetup,
        // LookupWithDensAndSetupExpressions.
        RoutineSchema { id: 13, name: "LookupDecoderDensSetup", shape: Plain, operand_field: Mixed,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh decoder dens+setup (no PK)" },
        // 14 — GrandProductWithoutCaches: `out = tuple(a)·tuple(b)` — product of
        // two INLINED memory-tuple affine combinations (not raw factors). 1 ext
        // output. Gate: InitialGrandProductWithoutCaches.
        RoutineSchema { id: 14, name: "GrandProductWithoutCaches", shape: MemTuple, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ArgPermAdditive,
            reference: "cache_relation.rs grand-product without caches (no PK)" },
        // 15 — MaterializeGrandProductTerm: `out = tuple(input)` — materialize ONE
        // memory-tuple affine combination (NOT a product). 1 ext output. Gate:
        // MaterializeGrandProductTermExpression.
        RoutineSchema { id: 15, name: "MaterializeGrandProductTerm", shape: MemTuple, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ArgPermAdditive,
            reference: "cache_relation.rs materialize grand-product term (no PK)" },
        // 16 — SingleColumnLookup cache: base gather (virtual_setup[mapping[gid]])
        // + base store (PK_CACHE_SINGLE_COLUMN). 1 base output. Cache:
        // SingleColumnLookup.
        RoutineSchema { id: 16, name: "SingleColumnLookup", shape: Plain, operand_field: Base,
            output_count: 1, output_field: Base, challenge: ArgPermAdditive,
            reference: "cache_relation.rs:347 SingleColumnLookup (PK_CACHE_SINGLE_COLUMN)" },
        // 17 — VectorizedLookup cache: ext gather over a column vector, optionally
        // decoder-mapped (PK_CACHE_VECTORIZED_LOOKUP). 1 ext output. Cache:
        // VectorizedLookup.
        RoutineSchema { id: 17, name: "VectorizedLookup", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "cache_relation.rs:382 VectorizedLookup gather (PK_CACHE_VECTORIZED_LOOKUP)" },
        // 18 — VectorizedLookupSetup cache: row-indexed setup gather, zero-padded
        // beyond generic_lookup_len (PK_CACHE_LOOKUP_SETUP). 1 ext output. Cache:
        // VectorizedLookupSetup.
        RoutineSchema { id: 18, name: "VectorizedLookupSetup", shape: Plain, operand_field: Ext,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "gkr_forward_generation.cuh LOOKUP_SETUP (PK_CACHE_LOOKUP_SETUP)" },
        // 19 — MemoryTuple cache: role-tagged linear terms (addr/ts/value, 8 max)
        // + address-space arm/payload (Empty/Constant/IsRegister/IsRam)
        // (PK_CACHE_MEMORY_TUPLE). MemTuple shape; 1 ext grand-product term.
        // Cache: MemoryTuple.
        RoutineSchema { id: 19, name: "MemoryTuple", shape: MemTuple, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ArgPermAdditive,
            reference: "cache_relation.rs:91 MemoryTuple address_space arm (PK_CACHE_MEMORY_TUPLE)" },
        // 20 — MemoryInitTeardownPair: `out = KEY(lhs) · KEY(rhs)`, a SINGLE ext
        // grand-product term (NOT a num/den pair). Each KEY is a memory-permutation
        // tuple: perm_additive + RAM + Σ_role chal[role]·col (+ the launcher-deferred
        // high-address bits as a folded ADDR_HIGH const). output_count 1 (cs lowering
        // is one_out; the prover forward ref computes lhs·rhs and stores one ext).
        // Gate: InitsOrTeardownsInitialPair.
        RoutineSchema { id: 20, name: "MemoryInitTeardownPair", shape: MemTuple, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ArgPermAdditive,
            reference: "prover forward_loop/inits_and_teardowns.rs evaluate_init/teardown + lhs*rhs" },
    ];
    T
}

/// Does this routine (by wire id) carry its operand structure in `Instr2.memtup`
/// (and, for the product-of-two-tuples ids, `Instr2.memtup2`) rather than the
/// flat operand lanes? True for id-19 MemoryTuple plus the three R4
/// structured-tuple routines id-14 GrandProductWithoutCaches, id-15
/// MaterializeGrandProductTerm, id-20 MemoryInitTeardownPair. The decoder uses
/// this to route the operand region.
pub fn routine_carries_memtup(routine: u8) -> bool {
    routine == RoutineId::MemoryTuple as u8
        || routine == RoutineId::GrandProductWithoutCaches as u8
        || routine == RoutineId::MaterializeGrandProductTerm as u8
        || routine == RoutineId::MemoryInitTeardownPair as u8
}

/// Does this routine (by wire id) carry TWO memory tuples whose values are
/// multiplied (`memtup` AND `memtup2`)? id-14 GrandProductWithoutCaches and
/// id-20 MemoryInitTeardownPair. id-15 / id-19 carry one tuple only.
pub fn routine_is_two_tuples(routine: u8) -> bool {
    routine == RoutineId::GrandProductWithoutCaches as u8
        || routine == RoutineId::MemoryInitTeardownPair as u8
}

/// Classify a forward gate's lowering (finding 3). EXHAUSTIVE over the 30
/// GateKind variants. Read codegen_ir.rs GateKind:
///   - Copy*/Enforce* are not forward-output gates (the v1 `fwd_eligible`
///     filter drops Copy*; Enforce* are empty-dst constraint gates). The
///     coverage test (A) does NOT pre-filter, so they are classified here as
///     `Alias` — operationally "no forward instruction emitted", the same
///     bucket Task 2.6 uses for pass-throughs (no routine).
///   - `LinearBaseField` (pure base arithmetic) → Arith.
///   - scratch-prefilled `MaxQuadratic` → ScratchSkip (the corpus is
///     all-scratch, pinned by `maxquadratic_all_scratch_prefilled`); v2 never
///     computes it forward.
///   - the folds / lookups / grand-product / aggregation / product / memory
///     init-teardown gates → Macro (per-row eval with challenges).
pub fn lowering_kind(kind: &GateKind) -> LoweringKind {
    use GateKind::*;
    use LoweringKind::*;
    match kind {
        // Pure base arithmetic: lowered through the arith family (Header::Arith).
        LinearBaseField { .. } => Arith,

        // Scratch-prefilled witness-stage value: read from scratch by address,
        // never computed forward (the corpus is all-scratch — pinned by
        // `maxquadratic_all_scratch_prefilled`). If a non-scratch MaxQuadratic
        // ever appears, that is a NEW design item (spec §9), not a silent
        // mis-lowering — classifying as ScratchSkip here matches production.
        MaxQuadratic { .. } => ScratchSkip,

        // Constraint gates: empty-dst, produce no forward output, emit no
        // instruction. Not output-bearing (v1 `gate_kind_bytes` marks them
        // `unreachable!` in the forward population). Distinct from Alias —
        // these are NOT column copies to an input backing.
        EnforceSingleMaxQuadraticConstraint { .. }
        | EnforceConstraintsMaxQuadratic { .. } => Constraint,

        // Host-side copy aliases: forward-INELIGIBLE per v1 `fwd_eligible`
        // (pass-through to an input backing) → no instruction.
        CopyInBaseField { .. } | CopyInExtensionField { .. } => Alias,

        // Grand-product accumulation steps (permutation/memory grand product).
        InitialGrandProductFromCaches { .. }
        | InitialGrandProductWithoutCaches { .. }
        | UnbalancedGrandProductWithCache { .. }
        | MaterializeGrandProductTermExpression { .. } => Macro,

        // Per-row product primitives (gkr_eval_product / gkr_eval_mask_identity).
        TrivialProduct { .. } | MaskIntoIdentityProduct { .. } => Macro,

        // Lookup num/den family (base/ext, balanced/unbalanced, cached-dens,
        // materialized vs vector inputs, with/without setup). All produce a
        // shifted-by-γ (num,den) pair.
        MaterializeSingleLookupInput { .. }
        | MaterializedVectorLookupInput { .. }
        | LookupWithCachedDensAndSetup { .. }
        | LookupWithDensAndSetupExpressions { .. }
        | LookupWithDensAndCachedSetup { .. }
        | LookupPairFromBaseInputs { .. }
        | LookupPairFromMaterializedBaseInputs { .. }
        | LookupFromMaterializedBaseInputWithSetup { .. }
        | LookupUnbalancedPairWithMaterializedBaseInputs { .. }
        | LookupPairFromVectorInputs { .. }
        | LookupPairFromMaterializedVectorInputs { .. }
        | LookupFromVectorInputWithSetup { .. }
        | LookupFromMaterializedVectorInputWithSetup { .. }
        | LookupPairFromCachedVectorInputs { .. }
        | LookupUnbalancedPairWithVectorInputs { .. }
        | LookupUnbalancedPairWithMaterializedVectorInputs { .. } => Macro,

        // Aggregate two rational (num,den) pairs into one.
        AggregateLookupRationalPair { .. } => Macro,

        // Memory inits/teardowns initial (num,den) pair.
        InitsOrTeardownsInitialPair { .. } => Macro,
    }
}

/// Some(routine) ONLY for `LoweringKind::Macro` gates; None otherwise (the
/// gate (A) test asserts non-Macro gates have no routine). The match here is
/// the dual of `lowering_kind`: every arm that returns `Some` must be a Macro
/// arm above, every other arm returns `None`.
pub fn routine_for_gate(kind: &GateKind) -> Option<RoutineId> {
    use GateKind::*;
    use RoutineId::*;
    Some(match kind {
        // Non-Macro → no routine.
        LinearBaseField { .. }
        | MaxQuadratic { .. }
        | EnforceSingleMaxQuadraticConstraint { .. }
        | EnforceConstraintsMaxQuadratic { .. }
        | CopyInBaseField { .. }
        | CopyInExtensionField { .. } => return None,

        // `out = a·b` (PK_PRODUCT). The two grand-product-from-caches gates feed
        // their two cache factors; UnbalancedGrandProductWithCache feeds
        // `[scalar, input]` — all the same a·b primitive.
        TrivialProduct { .. }
        | InitialGrandProductFromCaches { .. }
        | UnbalancedGrandProductWithCache { .. } => Product,

        // `out = (v−1)·m + 1` (PK_MASK_IDENTITY).
        MaskIntoIdentityProduct { .. } => MaskIdentity,

        // `out = tuple(a)·tuple(b)` over two inlined memory-tuple affine combos.
        InitialGrandProductWithoutCaches { .. } => GrandProductWithoutCaches,

        // `out = tuple(input)` — materialize ONE memory-tuple affine combo.
        MaterializeGrandProductTermExpression { .. } => MaterializeGrandProductTerm,

        // Aggregate two rational (num,den) pairs (PK_LOOKUP_PAIR4).
        AggregateLookupRationalPair { .. } => AggregateLookupPair,

        // Symmetric lookup pair `num = sh(b)+sh(d); den = sh(b)·sh(d)`, base/ext.
        LookupPairFromMaterializedBaseInputs { .. }
        | LookupPairFromBaseInputs { .. } => LookupBasePair,
        LookupPairFromMaterializedVectorInputs { .. }
        | LookupPairFromVectorInputs { .. }
        | LookupPairFromCachedVectorInputs { .. } => LookupExtPair,

        // Minus-multiplicity `num = sh(d) − c·sh(b); den = sh(b)·sh(d)`, base/ext.
        LookupFromMaterializedBaseInputWithSetup { .. } => LookupBaseMinusMult,
        LookupFromMaterializedVectorInputWithSetup { .. }
        | LookupFromVectorInputWithSetup { .. } => LookupExtMinusMult,

        // Cached-dens `num = a·sh(d) − c·sh(b); den = sh(b)·sh(d)` (all cached).
        LookupWithCachedDensAndSetup { .. } => LookupCachedDens,

        // Unbalanced `num = a·sh(d) + b; den = b·sh(d)`, base/ext.
        LookupUnbalancedPairWithMaterializedBaseInputs { .. } => LookupUnbalancedBase,
        LookupUnbalancedPairWithMaterializedVectorInputs { .. }
        | LookupUnbalancedPairWithVectorInputs { .. } => LookupUnbalancedExt,

        // Decoder-predicate dens+setup (same closed form as cached-dens, distinct
        // operand provenance).
        LookupWithDensAndCachedSetup { .. }
        | LookupWithDensAndSetupExpressions { .. } => LookupDecoderDensSetup,

        // α-folded vector-lookup affine combination (gate form, decoder-fill).
        MaterializedVectorLookupInput { .. } => VectorLookupGate,

        // Single-column lookup gate form (one base linear combination).
        MaterializeSingleLookupInput { .. } => MaterializeSingleLookup,

        // Memory inits/teardowns initial (num,den) pair.
        InitsOrTeardownsInitialPair { .. } => MemoryInitTeardownPair,
    })
}

pub fn routine_for_cache(kind: &CacheKind) -> Option<RoutineId> {
    // No glob import of RoutineId here: CacheKind and RoutineId share variant
    // names (SingleColumnLookup / VectorizedLookup{,Setup} / MemoryTuple), so
    // CacheKind arms are matched plainly and RoutineId targets are qualified.
    use CacheKind::*;
    Some(match kind {
        SingleColumnLookup { .. } => RoutineId::SingleColumnLookup,
        VectorizedLookup { .. } => RoutineId::VectorizedLookup,
        VectorizedLookupSetup => RoutineId::VectorizedLookupSetup,
        MemoryTuple { .. } => RoutineId::MemoryTuple,
    })
}
