//! Shared expression-building helpers for the DAG-IR lowering passes.
//!
//! These four primitives are used by both `arithmetic` and `constraint` lowering;
//! they live here to avoid verbatim duplication.

use crate::definitions::GKRAddress;
use super::super::{ArenaBuilder, ExprId, SourceKind};
use super::map_address;

/// Intern `Expr::Source(map_address(addr))`.
pub(super) fn read_expr(arena: &mut ArenaBuilder, addr: GKRAddress) -> ExprId {
    let src = arena.intern_source(map_address(addr));
    arena.source_expr(src)
}

/// Intern a `Constant`.
pub(super) fn const_expr(arena: &mut ArenaBuilder, value: u32) -> ExprId {
    let src = arena.intern_source(SourceKind::Constant { value });
    arena.source_expr(src)
}

/// Apply a reduced base-field coefficient to an already-interned term.
///
/// A coefficient of `1` is the multiplicative identity, so the term is returned
/// unchanged (no spurious `Mul` node). Otherwise `c·term` is interned.
pub(super) fn apply_coeff(arena: &mut ArenaBuilder, c: u32, term: ExprId) -> ExprId {
    if c == 1 {
        term
    } else {
        let cc = const_expr(arena, c);
        arena.mul(vec![cc, term])
    }
}

/// Collapse a list of additive terms into a single `ExprId`.
///
/// Empty → `Constant(0)`; one term → that term; otherwise an interned `Add`.
pub(super) fn sum_terms(arena: &mut ArenaBuilder, terms: Vec<ExprId>) -> ExprId {
    match terms.len() {
        0 => const_expr(arena, 0),
        1 => terms[0],
        _ => arena.add(terms),
    }
}
