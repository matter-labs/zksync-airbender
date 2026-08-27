//! Constraint / enforce relation lowering for the DAG IR generator.
//!
//! Lowering for the retained single max-quadratic constraint relation.

use super::super::{ArenaBuilder, ExprId, Root, RootOrigin};
use super::{arithmetic, LayerOut, RootGroup};
use cs::gkr_compiler::CompiledMaxQuadraticGKRRelation;
use field::PrimeField;

// ── Public entry points ───────────────────────────────────────────────────────

/// Lower `EnforceSingleMaxQuadraticConstraint { input, .. }`.
///
/// Emits one claim-only constraint root whose expr is the flat MaxQuadratic
/// form: `constant + Σ c_ij·a_i·b_ij + Σ c_i·x_i`.
pub(super) fn lower_single_constraint<F: PrimeField>(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    input: &CompiledMaxQuadraticGKRRelation<F>,
    group: RootGroup,
    relation_index: usize,
) {
    let (expr, _) = arithmetic::lower_max_quadratic(arena, input);
    emit_constraint(out, expr, group, relation_index);
}

fn emit_constraint(out: &mut LayerOut, expr: ExprId, group: RootGroup, relation_index: usize) {
    out.roots.push(Root {
        expr,
        materialize: None,
        claim: Some(RootOrigin {
            group,
            relation_index,
        }),
    });
}
