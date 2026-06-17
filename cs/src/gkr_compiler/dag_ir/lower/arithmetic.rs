//! Arithmetic / copy relation lowering for the DAG IR generator.
//!
//! Each function lowers ONE `NoFieldGKRRelation` arm into an `Expr` tree in the
//! shared [`ArenaBuilder`] and returns the root `ExprId` plus the sink
//! [`FieldKind`] dictated by the RELATION (never derived by field inference —
//! see [`super`]'s module docs on the cross-layer field subtlety).
//!
//! Expression shapes (coefficients are already-reduced `u32` base elements; a
//! coefficient of `1` is omitted, a `0` constant term is omitted):
//! - linear:        `constant + Σ c_i·x_i`
//! - max-quadratic: `constant + Σ_quad c_ij·a_i·b_ij + Σ_lin c_i·x_i`
//! - copy:          `read(input)` (base or extension field)

use crate::definitions::gkr::NoFieldLinearRelation;
use crate::definitions::GKRAddress;

use super::super::{ArenaBuilder, ExprId, FieldKind};
use super::util::{apply_coeff, const_expr, read_expr, sum_terms};

/// Lower `LinearBaseFieldRelation`: `constant + Σ c_i·x_i`.
///
/// Returns the root expr and `FieldKind::Base` (linear relations are base-field).
pub(super) fn lower_linear(
    arena: &mut ArenaBuilder,
    lin: &NoFieldLinearRelation,
) -> (ExprId, FieldKind) {
    let mut terms = Vec::new();
    if lin.constant != 0 {
        terms.push(const_expr(arena, lin.constant));
    }
    for (c, addr) in lin.linear_terms.iter() {
        let a = read_expr(arena, *addr);
        terms.push(apply_coeff(arena, *c, a));
    }
    (sum_terms(arena, terms), FieldKind::Base)
}

/// Lower `MaxQuadratic`: `constant + Σ_quad c_ij·a_i·b_ij + Σ_lin c_i·x_i`.
///
/// Returns the root expr and `FieldKind::Base` (max-quadratic is base-field).
pub(super) fn lower_max_quadratic(
    arena: &mut ArenaBuilder,
    rel: &crate::gkr_compiler::NoFieldMaxQuadraticGKRRelation,
) -> (ExprId, FieldKind) {
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
    (sum_terms(arena, terms), FieldKind::Base)
}

/// Lower `CopyInBaseField` / `CopyInExtensionField`: `read(input)`.
///
/// The `field` is the relation-dictated sink field (Base for base copy, Ext for
/// extension copy); it is returned so the caller records the right `SinkInfo`.
pub(super) fn lower_copy(
    arena: &mut ArenaBuilder,
    input: GKRAddress,
    field: FieldKind,
) -> (ExprId, FieldKind) {
    (read_expr(arena, input), field)
}
