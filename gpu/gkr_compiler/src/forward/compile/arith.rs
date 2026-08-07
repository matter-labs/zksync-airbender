//! Field classification and arithmetic-lowering predicates.

use super::super::isa::{OperandField, Sign};
use gkr_eval_ir::{
    expr_field_with_resolver, Expr, ExprId, FieldKind, ReadPlace, ResolutionStrategy, SourceKind,
};
use std::collections::HashMap;

use crate::forward::BABYBEAR_NEG_ONE;

// ── field classification ──────────────────────────────────────────────────────

/// The operand field of a child expression for instruction-field selection.
///
pub(crate) fn child_operand_field(
    layer: &gkr_eval_ir::DagLayer,
    id: ExprId,
    map: &HashMap<ReadPlace, FieldKind>,
) -> OperandField {
    if let Some(strategy) = layer.resolutions.get(&id) {
        return match strategy {
            ResolutionStrategy::PeekSingleColumn { .. } => OperandField::Base,
            ResolutionStrategy::PeekAggregate { .. }
            | ResolutionStrategy::PeekSetup
            | ResolutionStrategy::PeekDecoder { .. } => OperandField::Ext,
        };
    }
    expr_field_with_resolver(&layer.exprs, &layer.sources, id, &|place| {
        map.get(place).copied()
    })
    .expect("cross-layer fields must be resolved before compilation")
    .into()
}

// ── small structural predicates ──────────────────────────────────────────────────

/// True if `id` is a `Source` whose value is the field element `−1` (= P−1 =
/// `BABYBEAR_NEG_ONE`). These factors are stripped from Mul children before
/// field-grouped reduction; their count's parity decides the unary negate.
pub(crate) fn is_neg_one_factor(layer: &gkr_eval_ir::DagLayer, id: ExprId) -> bool {
    let Expr::Source(src) = &layer.exprs[id.0 as usize] else {
        return false;
    };
    matches!(
        &layer.sources[src.0 as usize],
        SourceKind::Constant { value } if *value == BABYBEAR_NEG_ONE
    )
}

/// Decompose a `Mul` into `(negated_parity, surviving_factors)`: elide `Constant{1}`
/// factors, peel `-1` factors (tracking the odd/even parity of their count), and
/// return the remaining non-`±1` factors. `None` if `id` is not a `Mul`.
fn mul_surviving_factors(layer: &gkr_eval_ir::DagLayer, id: ExprId) -> Option<(bool, Vec<ExprId>)> {
    let Expr::Mul(factors) = &layer.exprs[id.0 as usize] else {
        return None;
    };
    let mut neg_one_count = 0usize;
    let mut kept: Vec<ExprId> = Vec::with_capacity(factors.len());
    for &f in factors {
        if is_constant_one(layer, f) {
            continue;
        }
        if is_neg_one_factor(layer, f) {
            neg_one_count += 1;
        } else {
            kept.push(f);
        }
    }
    Some((neg_one_count % 2 == 1, kept))
}

/// An additive child of a sum, classified for sign-aware lowering:
/// - `Product { sign, lhs, rhs }` — a (possibly negated) binary product → one FMA pair.
/// - `Addend { sign, id }` — an additive term to lower into a sign-keyed ADD group.
///   A negated single-factor `Mul([-1, x])` becomes `Addend { Minus, x }` (lower `x`,
///   NOT the wrapping Mul — folding the negate into the consuming ADD's sign bit).
pub(crate) enum AdditiveChild {
    Product {
        sign: Sign,
        lhs: ExprId,
        rhs: ExprId,
    },
    Addend {
        sign: Sign,
        id: ExprId,
    },
}

/// Classify an additive child of a sum into a product (FMA) or a sign-keyed addend.
pub(crate) fn classify_additive_child(layer: &gkr_eval_ir::DagLayer, id: ExprId) -> AdditiveChild {
    match mul_surviving_factors(layer, id) {
        Some((negated, kept)) if kept.len() == 2 => {
            let sign = if negated { Sign::Minus } else { Sign::Plus };
            AdditiveChild::Product {
                sign,
                lhs: kept[0],
                rhs: kept[1],
            }
        }
        Some((true, kept)) if kept.len() == 1 => {
            // Negated single surviving factor `(-1)·x`: lower `x` itself and fold the
            // negate into the consuming ADD's sign bit (no standalone unary negate).
            AdditiveChild::Addend {
                sign: Sign::Minus,
                id: kept[0],
            }
        }
        // Plain additive term (a source, a non-negated single-factor Mul, a compound
        // subtree, or any Mul whose surviving-factor count is not 1 or 2): no fold.
        _ => AdditiveChild::Addend {
            sign: Sign::Plus,
            id,
        },
    }
}

pub(crate) fn is_constant_one(layer: &gkr_eval_ir::DagLayer, id: ExprId) -> bool {
    let Expr::Source(src) = &layer.exprs[id.0 as usize] else {
        return false;
    };
    matches!(
        &layer.sources[src.0 as usize],
        SourceKind::Constant { value: 1 }
    )
}

fn is_constant_zero(layer: &gkr_eval_ir::DagLayer, id: ExprId) -> bool {
    let Expr::Source(src) = &layer.exprs[id.0 as usize] else {
        return false;
    };
    matches!(
        &layer.sources[src.0 as usize],
        SourceKind::Constant { value: 0 }
    )
}

/// True if `id` is a constant zero or a product with a zero factor.
pub(crate) fn is_zero_expr(layer: &gkr_eval_ir::DagLayer, id: ExprId) -> bool {
    match &layer.exprs[id.0 as usize] {
        Expr::Source(_) => is_constant_zero(layer, id),
        Expr::Mul(factors) => factors.iter().any(|&f| is_zero_expr(layer, f)),
        Expr::Add(_) => false,
    }
}
