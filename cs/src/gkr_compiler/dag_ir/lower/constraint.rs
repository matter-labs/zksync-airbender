//! Constraint / enforce relation lowering for the DAG IR generator.
//!
//! Two `NoFieldGKRRelation` arms are handled:
//!
//! - `EnforceSingleMaxQuadraticConstraint` → one `Root::Constraint` whose expr is
//!   the flat MaxQuadratic lowering of the `input` field (same form as Task 7's
//!   arithmetic lowering). The `expression` structured field is NOT consumed,
//!   consistent with Task 7's MaxQuadratic arm.
//!
//! - `EnforceConstraintsMaxQuadratic` → one `Root::Constraint` whose expr is:
//!   ```text
//!   Σ_((a,b), terms) Σ_(c,p in terms) c · rho^p · a · b
//! + Σ_(a, terms)     Σ_(c,p in terms) c · rho^p · a
//! + Σ_(c,p)                           c · rho^p
//!   ```
//!   where `rho = Challenge(ConstraintAggregation, One)` (or `Static(p)` for
//!   `p != 1`).
//!
//! Neither arm produces a sink; `Root::Constraint` has no `SinkId`.

use super::super::{
    ArenaBuilder, ChallengeKey, ChallengeRef, ChallengePower, ExprId, Root, RootId,
    RootOrigin, RootSlot, SourceKind,
};
use super::{LayerOut, RootGroup};
use super::util::{apply_coeff, const_expr, read_expr, sum_terms};
use crate::gkr_compiler::{
    NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
};

/// Intern `Expr::Source(Challenge { key, power })`.
fn challenge_expr(arena: &mut ArenaBuilder, key: ChallengeKey, power: ChallengePower) -> ExprId {
    let src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef { key, power },
    });
    arena.source_expr(src)
}

/// Intern `rho^p` where `rho = Challenge(ConstraintAggregation, ·)`.
///
/// Per the companion "Enforce Gates" section:
/// - `p == 1` → `Challenge(ConstraintAggregation, One)`
/// - otherwise  → `Challenge(ConstraintAggregation, Static(p))`
fn rho_pow(arena: &mut ArenaBuilder, p: usize) -> ExprId {
    let power = if p == 1 {
        ChallengePower::One
    } else {
        ChallengePower::Static(p as u32)
    };
    challenge_expr(arena, ChallengeKey::ConstraintAggregation, power)
}

// ── Public entry points ───────────────────────────────────────────────────────

/// Lower `EnforceSingleMaxQuadraticConstraint { input, .. }`.
///
/// Emits one `Root::Constraint` whose expr is the flat MaxQuadratic form:
/// `constant + Σ c_ij·a_i·b_ij + Σ c_i·x_i`.
pub(super) fn lower_single_constraint(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    input: &NoFieldMaxQuadraticGKRRelation,
    group: RootGroup,
    relation_index: usize,
) {
    let expr = lower_flat_max_quadratic(arena, input);
    emit_constraint(out, expr, group, relation_index);
}

/// Lower `EnforceConstraintsMaxQuadratic { input }`.
///
/// Emits one `Root::Constraint` whose expr is the batched aggregation:
/// `Σ_quad c·rho^p·a·b  +  Σ_lin c·rho^p·a  +  Σ_const c·rho^p`.
pub(super) fn lower_batched_constraint(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    input: &NoFieldMaxQuadraticConstraintsGKRRelation,
    group: RootGroup,
    relation_index: usize,
) {
    let expr = lower_batched_expr(arena, input);
    emit_constraint(out, expr, group, relation_index);
}

// ── Private helpers ───────────────────────────────────────────────────────────

/// Flat MaxQuadratic lowering: `constant + Σ c_ij·a_i·b_ij + Σ c_i·x_i`.
fn lower_flat_max_quadratic(
    arena: &mut ArenaBuilder,
    rel: &NoFieldMaxQuadraticGKRRelation,
) -> ExprId {
    let mut terms = Vec::new();
    if rel.constant != 0 {
        terms.push(const_expr(arena, rel.constant));
    }
    for (a, set) in rel.quadratic_terms.iter() {
        let a_expr = read_expr(arena, *a);
        for (c, b) in set.iter() {
            let b_expr = read_expr(arena, *b);
            let prod = arena.mul(vec![a_expr, b_expr]);
            terms.push(apply_coeff(arena, *c, prod));
        }
    }
    for (c, a) in rel.linear_terms.iter() {
        let a_expr = read_expr(arena, *a);
        terms.push(apply_coeff(arena, *c, a_expr));
    }
    sum_terms(arena, terms)
}

/// Batched aggregation expression.
fn lower_batched_expr(
    arena: &mut ArenaBuilder,
    input: &NoFieldMaxQuadraticConstraintsGKRRelation,
) -> ExprId {
    let mut terms = Vec::new();

    // Quadratic terms: ((a, b), [(c, p)]) → Σ_(c,p) c · rho^p · (a·b)
    for ((a_addr, b_addr), coeff_powers) in input.quadratic_terms.iter() {
        let a_expr = read_expr(arena, *a_addr);
        let b_expr = read_expr(arena, *b_addr);
        let ab = arena.mul(vec![a_expr, b_expr]);
        for (c, p) in coeff_powers.iter() {
            let rho_p = rho_pow(arena, *p);
            // Build c · (a·b) first, then multiply by rho^p.
            // (Arena flattens nested Mul, so ordering does not matter for CSE.)
            let scaled_ab = apply_coeff(arena, *c, ab);
            terms.push(arena.mul(vec![rho_p, scaled_ab]));
        }
    }

    // Linear terms: (a, [(c, p)]) → Σ_(c,p) c · rho^p · a
    for (a_addr, coeff_powers) in input.linear_terms.iter() {
        let a_expr = read_expr(arena, *a_addr);
        for (c, p) in coeff_powers.iter() {
            let rho_p = rho_pow(arena, *p);
            let scaled_a = apply_coeff(arena, *c, a_expr);
            terms.push(arena.mul(vec![rho_p, scaled_a]));
        }
    }

    // Constant terms: (c, p) → c · rho^p
    for (c, p) in input.constants.iter() {
        let rho_p = rho_pow(arena, *p);
        terms.push(apply_coeff(arena, *c, rho_p));
    }

    sum_terms(arena, terms)
}

/// Push `Root::Constraint { expr }` and record `RootOrigin { slot: Constraint(0) }`.
///
/// No sink is created. The root is claim-bearing; Task 11 assembles the batching
/// order — this function only emits the root and records its origin.
fn emit_constraint(
    out: &mut LayerOut,
    expr: ExprId,
    group: RootGroup,
    relation_index: usize,
) {
    let root_id = RootId(out.roots.len() as u32);
    out.roots.push(Root::Constraint { expr });
    out.origins.insert(
        root_id,
        RootOrigin {
            group,
            relation_index,
            slot: RootSlot::Constraint(0),
        },
    );
}
