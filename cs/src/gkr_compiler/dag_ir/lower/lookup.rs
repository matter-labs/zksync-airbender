//! Lookup-relation lowering for the DAG IR generator.
//!
//! Every lookup relation lowers to `LookupValue` source leaves plus ordinary
//! arithmetic over the lookup-additive challenge `gamma` and lookup-multiplicative
//! challenge powers `alpha^j` (per the companion design doc, sections "Lookup
//! Values", "Two-output Lookup Gates", "Lookup Minus Setup", and the rational-pair
//! part of "Product, Mask, And Rational-Pair Gates"). The extension-valued vector
//! lookup object is NOT a primitive source: it is alpha-folded base lookup values.
//!
//! # The two single-output materializations
//! - `MaterializeSingleLookupInput` → [`single_column_lookup`] (Base sink).
//! - `MaterializedVectorLookupInput` → [`folded_lookup`] (Ext sink).
//!
//! # The two-output (num, den) families
//! Each pair arm emits TWO adjacent `Output` roots, num to `output[0]` and den to
//! `output[1]`. The only difference between arms is how the rational operands
//! (`a`/`b`/`c`/`d`) are obtained — inline single/vector lookup, a materialized or
//! cached prior `Read`, or a setup expression — so the families share helpers:
//!
//! - PAIR (`1/(b+γ) + 1/(d+γ)`):
//!   `num = (b+γ) + (d+γ)`, `den = (b+γ)·(d+γ)`.
//! - LOOKUP-MINUS-SETUP (`1/(b+γ) − c/(d+γ)`):
//!   `num = (d+γ) − c·(b+γ)`, `den = (b+γ)·(d+γ)`.
//! - DENS-AND-SETUP / cached dens (`a/(b+γ) − c/(d+γ)`):
//!   `num = a·(d+γ) − c·(b+γ)`, `den = (b+γ)·(d+γ)`.
//! - UNBALANCED (`a/b + 1/(d+γ)`, i.e. a prior rational pair plus a single 1/(d+γ)):
//!   `num = a·(d+γ) + b`, `den = b·(d+γ)`.
//! - RATIONAL-PAIR aggregate (`a/b + c/d`):
//!   `num = a·d + c·b`, `den = b·d`.
//!
//! These match the prover's forward kernels (`gkr_eval_lookup_*` in
//! `support/lookup_helpers.cuh`), the authoritative arithmetic.
//!
//! # Subtraction
//! There is no `Sub`/`Neg` node: `a − b = a + (−1)·b`, where `−1` is the reduced
//! base-field constant `F::CHARACTERISTICS − 1`, threaded in as `minus_one`.

use crate::definitions::gkr::{NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation};
use crate::definitions::GKRAddress;

use super::super::{
    ArenaBuilder, ChallengeKey, ChallengePower, ChallengeRef, ExprId, LookupValueKind, SourceKind,
};

/// Range-check single-column lookups with this width resolve a `RangeCheck16Index`;
/// any other width is a timestamp index.
const RANGE_CHECK_16_WIDTH: u32 = 16;

// ── primitive source builders ────────────────────────────────────────────────

/// `gamma = Challenge { LookupAdditive, One }`.
fn gamma(arena: &mut ArenaBuilder) -> ExprId {
    let src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        },
    });
    arena.source_expr(src)
}

/// `alpha^j = Challenge { LookupMultiplicative, Static(j) }`.
fn alpha_pow(arena: &mut ArenaBuilder, j: u32) -> ExprId {
    let src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef {
            key: ChallengeKey::LookupMultiplicative,
            power: ChallengePower::Static(j),
        },
    });
    arena.source_expr(src)
}

/// Read `addr` — for materialized / cached / setup operands.
///
/// A same-layer cache address resolves to the materialized value's shared
/// `ExprId` (in-layer reuse = DAG sharing); see [`super::util::read_expr`].
pub(super) fn read(arena: &mut ArenaBuilder, addr: GKRAddress) -> ExprId {
    super::util::read_expr(arena, addr)
}

/// Lower a linear relation query into an `ExprId` (`constant + Σ c_i·x_i`).
///
/// Reuses the Task-7 linear-lowering helper so the query arithmetic is identical
/// to `LinearBaseFieldRelation`. The returned field is always `Base`.
fn lower_query(arena: &mut ArenaBuilder, lin: &crate::definitions::gkr::NoFieldLinearRelation) -> ExprId {
    super::arithmetic::lower_linear(arena, lin).0
}

// ── public lookup-value building blocks ──────────────────────────────────────

/// `LookupValue { kind: RangeCheck16Index | TimestampIndex, set_index, query }`.
///
/// `width == 16` selects the range-check table column; any other width selects
/// the timestamp column. `set_index` is the relation's `lookup_set_index`.
pub(super) fn single_column_lookup(
    arena: &mut ArenaBuilder,
    rel: &NoFieldSingleColumnLookupRelation,
    range_check_width: u32,
) -> ExprId {
    let kind = if range_check_width == RANGE_CHECK_16_WIDTH {
        LookupValueKind::RangeCheck16Index
    } else {
        LookupValueKind::TimestampIndex
    };
    let query = lower_query(arena, &rel.input);
    let src = arena.intern_source(SourceKind::LookupValue {
        kind,
        set_index: rel.lookup_set_index,
        query,
    });
    arena.source_expr(src)
}

/// `Σ_j alpha^j · LookupValue { GenericColumn{j}, set_index, query_j }`.
///
/// Column 0's term carries no alpha factor (`alpha^0 = 1`), matching the companion
/// `folded_lookup` example; columns `j ≥ 1` are scaled by `alpha^j`. Every emitted
/// `LookupValue` carries the relation's `lookup_set_index`.
pub(super) fn folded_lookup(arena: &mut ArenaBuilder, rel: &NoFieldVectorLookupRelation) -> ExprId {
    let mut terms = Vec::with_capacity(rel.columns.len());
    for (j, column) in rel.columns.iter().enumerate() {
        let query = lower_query(arena, column);
        let lv = arena.intern_source(SourceKind::LookupValue {
            kind: LookupValueKind::GenericColumn { column: j },
            set_index: rel.lookup_set_index,
            query,
        });
        let lv_expr = arena.source_expr(lv);
        if j == 0 {
            // alpha^0 = 1: no scaling factor, per the companion example.
            terms.push(lv_expr);
        } else {
            let a = alpha_pow(arena, j as u32);
            terms.push(arena.mul(vec![a, lv_expr]));
        }
    }
    match terms.len() {
        0 => {
            // A zero-column vector lookup is degenerate; fold to the empty sum (0).
            let zero = arena.intern_source(SourceKind::Constant { value: 0 });
            arena.source_expr(zero)
        }
        1 => terms[0],
        // Multi-column fold: fence this Add so its ExprId survives as a single
        // operand in root-reachable nodes and is findable by the resolutions validator.
        _ => arena.fenced_add(terms),
    }
}

/// Alpha-fold a list of setup `Read`s: `Σ_j alpha^j · Read(setup_cols[j])`.
///
/// This is the "vector/generic lookup setup without a cache" `d` value from the
/// companion. Column 0 carries no alpha factor.
pub(super) fn folded_setup(arena: &mut ArenaBuilder, setup_cols: &[GKRAddress]) -> ExprId {
    let mut terms = Vec::with_capacity(setup_cols.len());
    for (j, addr) in setup_cols.iter().enumerate() {
        let r = read(arena, *addr);
        if j == 0 {
            terms.push(r);
        } else {
            let a = alpha_pow(arena, j as u32);
            terms.push(arena.mul(vec![a, r]));
        }
    }
    match terms.len() {
        0 => {
            let zero = arena.intern_source(SourceKind::Constant { value: 0 });
            arena.source_expr(zero)
        }
        1 => terms[0],
        // Multi-column fold: fence this Add so its ExprId survives as a single
        // operand in root-reachable nodes and is findable by the resolutions validator.
        _ => arena.fenced_add(terms),
    }
}

// ── num/den shapes (returned as `(num, den)` ExprIds) ─────────────────────────

/// `x + gamma`.
fn shift(arena: &mut ArenaBuilder, x: ExprId, g: ExprId) -> ExprId {
    arena.add(vec![x, g])
}

/// `(−1) · term` — negates `term` using the reduced base-field `−1` constant.
fn scale_minus_one(arena: &mut ArenaBuilder, minus_one: u32, term: ExprId) -> ExprId {
    let neg = arena.intern_source(SourceKind::Constant { value: minus_one });
    let neg_expr = arena.source_expr(neg);
    arena.mul(vec![neg_expr, term])
}

/// PAIR family: `num = (b+γ) + (d+γ)`, `den = (b+γ)·(d+γ)`.
pub(super) fn pair(arena: &mut ArenaBuilder, b: ExprId, d: ExprId) -> (ExprId, ExprId) {
    let g = gamma(arena);
    let sb = shift(arena, b, g);
    let sd = shift(arena, d, g);
    let num = arena.add(vec![sb, sd]);
    let den = arena.mul(vec![sb, sd]);
    (num, den)
}

/// LOOKUP-MINUS-SETUP family: `num = (d+γ) − c·(b+γ)`, `den = (b+γ)·(d+γ)`.
///
/// `c` is the multiplicity. Subtraction is `(d+γ) + (−1)·c·(b+γ)`.
pub(super) fn minus_multiplicity(
    arena: &mut ArenaBuilder,
    b: ExprId,
    c: ExprId,
    d: ExprId,
    minus_one: u32,
) -> (ExprId, ExprId) {
    let g = gamma(arena);
    let sb = shift(arena, b, g);
    let sd = shift(arena, d, g);
    let c_sb = arena.mul(vec![c, sb]);
    let neg_c_sb = scale_minus_one(arena, minus_one, c_sb);
    let num = arena.add(vec![sd, neg_c_sb]);
    let den = arena.mul(vec![sb, sd]);
    (num, den)
}

/// DENS-AND-SETUP family: `num = a·(d+γ) − c·(b+γ)`, `den = (b+γ)·(d+γ)`.
///
/// The cached/uncached dens-and-setup gates compute `a/(b+γ) − c/(d+γ)`.
pub(super) fn dens_and_setup(
    arena: &mut ArenaBuilder,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    d: ExprId,
    minus_one: u32,
) -> (ExprId, ExprId) {
    let g = gamma(arena);
    let sb = shift(arena, b, g);
    let sd = shift(arena, d, g);
    let a_sd = arena.mul(vec![a, sd]);
    let c_sb = arena.mul(vec![c, sb]);
    let neg_c_sb = scale_minus_one(arena, minus_one, c_sb);
    let num = arena.add(vec![a_sd, neg_c_sb]);
    let den = arena.mul(vec![sb, sd]);
    (num, den)
}

/// UNBALANCED family: prior rational pair `a/b` plus single `1/(d+γ)`.
///
/// `num = a·(d+γ) + b`, `den = b·(d+γ)`.
pub(super) fn unbalanced(
    arena: &mut ArenaBuilder,
    a: ExprId,
    b: ExprId,
    d: ExprId,
) -> (ExprId, ExprId) {
    let g = gamma(arena);
    let sd = shift(arena, d, g);
    let a_sd = arena.mul(vec![a, sd]);
    let num = arena.add(vec![a_sd, b]);
    let den = arena.mul(vec![b, sd]);
    (num, den)
}

/// RATIONAL-PAIR aggregate: `a/b + c/d`.
///
/// `num = a·d + c·b`, `den = b·d`. No gamma shift — operands are already full
/// (num, den) pairs.
pub(super) fn rational_pair(
    arena: &mut ArenaBuilder,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    d: ExprId,
) -> (ExprId, ExprId) {
    let a_d = arena.mul(vec![a, d]);
    let c_b = arena.mul(vec![c, b]);
    let num = arena.add(vec![a_d, c_b]);
    let den = arena.mul(vec![b, d]);
    (num, den)
}
