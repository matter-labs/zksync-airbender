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
    // One entry per RoutineId, fields filled from the cuh/rs references. Dense
    // (id == index); the (B) decode-soundness gate asserts this.
    use ChallengeUse::*;
    use FieldRole::*;
    use Shape::*;
    const T: &[RoutineSchema] = &[
        // 0 — per-layer GateOutput fold: ∑ α^k · b accumulator (Task 2.5 reads
        // α-powers column-indexed + γ as [γ,γ²,2γ]). Reads a per-gate column
        // count (carried in the header's `n_operands`) → Plain. The
        // output-accumulation routine; no GateKind maps here (the compiler
        // emits it for the output combine), kept stable for the 1.5 round-trip
        // vector + Task 2.5.
        RoutineSchema { id: 0, name: "GateOutputFold", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ConstAlphaGamma,
            reference: "gkr_forward_generation.cuh E_FMA_ALPHA" },
        // 1 — LookupNumDen folds a variable column count into num+den → Plain,
        // 2 outputs. The shifted-by-γ lookup pair (gkr_eval_lookup_*pair, base &
        // ext, balanced/unbalanced, cached-dens, minus-multiplicity). (The
        // round-trip test's 2 operands ride consecutive operand lanes; the count
        // is in the header.)
        RoutineSchema { id: 1, name: "LookupNumDen", shape: Plain, operand_field: Mixed,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh num/den" },
        // 2 — grand-product accumulation step: a single product node folded into
        // the running grand product (PRODUCT macro). Two ext factors → 1 ext.
        RoutineSchema { id: 2, name: "GrandProductStep", shape: Plain, operand_field: Ext,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "gkr_forward_generation.cuh PRODUCT (gkr_eval_product)" },
        // 3 — AggregateLookupRationalPair: combine two (num,den) rational pairs
        // into one, batched by the α/γ const challenges. 4 ext operands → 2 ext
        // (aggregated num,den).
        RoutineSchema { id: 3, name: "AggregateLookupPair", shape: Plain, operand_field: Ext,
            output_count: 2, output_field: Ext, challenge: ConstAlphaGamma,
            reference: "lookup_helpers.cuh aggregate rational pair" },
        // 4 — SingleColumnLookup cache: base gather (virtual_setup[mapping[gid]])
        // + base store. Linear-comb column count in the header → 1 base output.
        // Uses the perm-linearization / additive-seed arg challenges.
        RoutineSchema { id: 4, name: "SingleColumnLookup", shape: Plain, operand_field: Base,
            output_count: 1, output_field: Base, challenge: ArgPermAdditive,
            reference: "cache_relation.rs:347 SingleColumnLookup" },
        // 5 — MemoryTuple cache: role-tagged linear terms (addr/ts/value, 8 max)
        // + address-space arm/payload (Empty/Constant/IsRegister/IsRam). MemTuple
        // shape; 1 ext grand-product term output.
        RoutineSchema { id: 5, name: "MemoryTuple", shape: MemTuple, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: ArgPermAdditive,
            reference: "cache_relation.rs:91 MemoryTuple (address_space_kind arm)" },
        // 6 — VectorizedLookup cache gather: n[mapping[gid]] over a column vector,
        // optionally decoder-mapped. Header-carried column count → 1 ext output.
        RoutineSchema { id: 6, name: "VectorizedLookup", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "cache_relation.rs:382 VectorizedLookup gather" },
        // 7 — VectorizedLookupSetup cache: row-indexed setup gather, zero-padded
        // beyond generic_lookup_len (LOOKUP_SETUP). Few operands (row gid
        // index + length guard, count in the header) → Plain, 1 ext output.
        RoutineSchema { id: 7, name: "VectorizedLookupSetup", shape: Plain, operand_field: Ext,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "gkr_forward_generation.cuh LOOKUP_SETUP" },
        // 8 — per-row product primitive (gkr_eval_product) / mask-into-identity
        // (gkr_eval_mask_identity): TrivialProduct + MaskIntoIdentityProduct.
        // Two operands → 1 ext. Distinct from GrandProductStep (id 2) which is the
        // structural grand-product accumulation, not a leaf product.
        RoutineSchema { id: 8, name: "ProductStep", shape: Plain, operand_field: Mixed,
            output_count: 1, output_field: Ext, challenge: None,
            reference: "lookup_helpers.cuh gkr_eval_product / gkr_eval_mask_identity" },
        // 9 — InitsOrTeardownsInitialPair: memory inits/teardowns initial (num,den)
        // pair from a setup tuple, batched by the perm/additive arg + const
        // challenges. Header-carried timestamp/value term count → 2 ext outputs.
        RoutineSchema { id: 9, name: "MemoryInitTeardownPair", shape: Plain, operand_field: Mixed,
            output_count: 2, output_field: Ext, challenge: Both,
            reference: "lookup_helpers.cuh inits/teardowns num/den" },
    ];
    T
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

        // Grand-product accumulation.
        InitialGrandProductFromCaches { .. }
        | InitialGrandProductWithoutCaches { .. }
        | UnbalancedGrandProductWithCache { .. }
        | MaterializeGrandProductTermExpression { .. } => GrandProductStep,

        // Leaf product primitives.
        TrivialProduct { .. } | MaskIntoIdentityProduct { .. } => ProductStep,

        // Lookup num/den family.
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
        | LookupUnbalancedPairWithMaterializedVectorInputs { .. } => LookupNumDen,

        // Aggregate rational pair.
        AggregateLookupRationalPair { .. } => AggregateLookupPair,

        // Memory inits/teardowns initial pair.
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
