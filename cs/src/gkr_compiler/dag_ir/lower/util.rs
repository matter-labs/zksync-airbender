//! Shared expression-building helpers for the DAG-IR lowering passes.
//!
//! These four primitives are used by both `arithmetic` and `constraint` lowering;
//! they live here to avoid verbatim duplication.

use crate::definitions::GKRAddress;
use super::super::{ArenaBuilder, ExprId, SourceKind};
use super::map_address;

/// The `SourceKind` for reading `addr`, preferring a `Prior` alias.
///
/// If `addr` is a `GKRAddress::Cached` materialized as a cache root in THIS
/// layer, the read aliases the materializing root via `SourceKind::Prior`;
/// otherwise it falls back to `map_address` (which yields `Read(CacheOutput)`
/// for genuine external/compat cache reads). Used by every lowering read helper
/// (`read_expr`, `lookup::read`, `memory::read`).
pub(crate) fn read_source(arena: &ArenaBuilder, addr: GKRAddress) -> SourceKind {
    match arena.cache_alias(addr) {
        Some(id) => SourceKind::Prior { id },
        None => map_address(addr),
    }
}

/// Intern `Expr::Source(read_source(addr))`.
pub(super) fn read_expr(arena: &mut ArenaBuilder, addr: GKRAddress) -> ExprId {
    let src = arena.intern_source(read_source(arena, addr));
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
