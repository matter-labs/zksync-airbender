//! Expression-level resolution lowering (spec §9): prune resolved fold subtrees to one Special.

use super::super::source::{SpecialTable, lower_resolution};
use gkr_eval_ir::{DagLayer, ExprId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolveOutcome {
    Special(u16),
    Descend,
}

/// If `expr_id` carries a ResolutionStrategy, emit one Special (carrying origin_expr) and prune.
pub fn resolve_or_descend(
    layer: &DagLayer,
    expr_id: ExprId,
    specials: &mut SpecialTable,
) -> ResolveOutcome {
    match layer.resolutions.get(&expr_id) {
        Some(strategy) => {
            ResolveOutcome::Special(specials.push(lower_resolution(strategy, expr_id)))
        }
        None => ResolveOutcome::Descend,
    }
}
