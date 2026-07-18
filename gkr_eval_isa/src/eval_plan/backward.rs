//! Closed symbolic adapter for normalized backward fragments.

use cs::gkr_compiler::dag_ir::{Expr, ExprId, FieldKind, expr_field, join};

use crate::bwd::compile::fragment_descs;
use crate::bwd::distill::DistilledLayer;
use crate::bwd::source::BwdSpecialTable;

use super::{
    EvalPlan, PackConfig, PackError, PackedEvalPlan, PlanError,
    elaborate_backward_fragments_driver, pack_plan,
};

/// Symbolic backward evaluation before descriptor binding. The special table is
/// cloned and extended only with descriptors actually emitted by the fragment
/// plan, leaving the distilled layer's binding namespace unchanged.
#[derive(Clone, Debug)]
pub struct BackwardSymbolicEvaluation {
    pub plan: EvalPlan,
    pub packed: PackedEvalPlan,
    pub specials: BwdSpecialTable,
}

#[derive(Clone, Debug, PartialEq)]
pub enum BackwardEvaluationError {
    Plan(PlanError),
    Pack(PackError),
    BudgetCellsOverflow {
        budget_cells: usize,
    },
    InvalidFragmentOrder {
        order: Vec<usize>,
        fragment_count: usize,
    },
    EmptyFragmentDecomposition,
}

impl From<PlanError> for BackwardEvaluationError {
    fn from(value: PlanError) -> Self {
        Self::Plan(value)
    }
}

impl From<PackError> for BackwardEvaluationError {
    fn from(value: PackError) -> Self {
        Self::Pack(value)
    }
}

/// Elaborate the complete normalized backward-fragment expression without
/// cache residency, then pack it. `budget_cells` is converted exactly once to
/// extension-field lane units before it reaches the shared elaborator.
pub fn elaborate_backward_fragments_uncached(
    d: &DistilledLayer,
    order: Option<&[usize]>,
    budget_cells: usize,
    stream_reductions: bool,
) -> Result<BackwardSymbolicEvaluation, BackwardEvaluationError> {
    let fragments = &d.fragments.fragments;
    if d.fragments.c_init.terms.is_empty() && fragments.is_empty() {
        return Err(BackwardEvaluationError::EmptyFragmentDecomposition);
    }
    let scheduled_fragments = validate_fragment_order(order, fragments.len())?;
    let budget_lanes = budget_cells
        .checked_mul(4)
        .ok_or(BackwardEvaluationError::BudgetCellsOverflow { budget_cells })?;
    let (specials, coefficient_descs, acc_init_desc) = fragment_descs(d);
    let expr_fields = backward_expr_fields(d);
    let plan = elaborate_backward_fragments_driver(
        &d.layer,
        d.root,
        &expr_fields,
        fragments,
        &scheduled_fragments,
        &coefficient_descs,
        acc_init_desc,
        budget_lanes,
        stream_reductions,
    )?;
    let packed = pack_plan(&plan, &d.layer, PackConfig::default())?;
    Ok(BackwardSymbolicEvaluation {
        plan,
        packed,
        specials,
    })
}

fn validate_fragment_order(
    order: Option<&[usize]>,
    fragment_count: usize,
) -> Result<Vec<usize>, BackwardEvaluationError> {
    let Some(order) = order else {
        return Ok((0..fragment_count).collect());
    };
    let mut sorted = order.to_vec();
    sorted.sort_unstable();
    if order.len() != fragment_count || sorted != (0..fragment_count).collect::<Vec<_>>() {
        return Err(BackwardEvaluationError::InvalidFragmentOrder {
            order: order.to_vec(),
            fragment_count,
        });
    }
    Ok(order.to_vec())
}

fn backward_expr_fields(d: &DistilledLayer) -> Vec<FieldKind> {
    let defaults: Vec<_> = (0..d.layer.exprs.len())
        .map(|index| {
            expr_field(&d.layer.exprs, &d.layer.sources, ExprId(index as u32))
                .expect("distilled layers preserve valid expression fields")
        })
        .collect();
    let mut fields = vec![None; d.layer.exprs.len()];
    for index in 0..d.layer.exprs.len() {
        backward_expr_field(ExprId(index as u32), d, &defaults, &mut fields);
    }
    fields.into_iter().map(Option::unwrap).collect()
}

fn backward_expr_field(
    expr: ExprId,
    d: &DistilledLayer,
    defaults: &[FieldKind],
    fields: &mut [Option<FieldKind>],
) -> FieldKind {
    if let Some(field) = fields[expr.0 as usize] {
        return field;
    }
    let field = if let Some(&field) = d.field_overrides.get(&expr) {
        field
    } else {
        match &d.layer.exprs[expr.0 as usize] {
            Expr::Source(_) => defaults[expr.0 as usize],
            Expr::Add(children) | Expr::Mul(children) => children
                .iter()
                .map(|&child| backward_expr_field(child, d, defaults, fields))
                .reduce(join)
                .unwrap_or(defaults[expr.0 as usize]),
        }
    };
    fields[expr.0 as usize] = Some(field);
    field
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
        RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };

    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::bwd::fragment::FragmentTable;
    use crate::bwd::source::BwdSpecial;

    use super::{BackwardEvaluationError, elaborate_backward_fragments_uncached};
    use crate::eval_plan::{ConcreteBindError, EvalOp, Operand, bind_packed_plan};

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column },
            },
        }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    fn backward_fixture() -> DistilledLayer {
        let roots = vec![
            claim_only_root(ExprId(0), 0),
            claim_only_root(ExprId(5), 1),
            claim_only_root(ExprId(3), 2),
        ];
        let layer = DagLayer {
            sources: vec![
                read_src(0),
                read_src(1),
                read_src(2),
                SourceInfo {
                    kind: SourceKind::Constant { value: 7 },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Add(vec![ExprId(1), ExprId(2)]),
                Expr::Mul(vec![ExprId(0), ExprId(4)]),
            ],
            batching: BatchingOrder {
                roots: (0..roots.len())
                    .map(|i| cs::gkr_compiler::dag_ir::RootId(i as u32))
                    .collect(),
            },
            roots,
            resolutions: BTreeMap::new(),
        };
        distill(&layer, BwdRegime::Ext, &HashMap::new(), None)
    }

    fn assert_single_uncached_terminal(out: &super::BackwardSymbolicEvaluation) {
        assert!(matches!(
            out.plan.ops.last(),
            Some(EvalOp::ReturnAcc { .. })
        ));
        assert_eq!(out.plan.stats.cache_stores, 0);
        assert_eq!(out.plan.stats.cache_hits, 0);
        assert_eq!(out.plan.stats.cache_drops, 0);
        assert_eq!(
            out.plan
                .ops
                .iter()
                .filter(|op| matches!(op, EvalOp::ReturnAcc { .. }))
                .count(),
            1
        );
    }

    #[test]
    fn backward_uncached_fragment_shape() {
        let d = backward_fixture();
        let identity: Vec<_> = (0..d.fragments.fragments.len()).collect();
        let out = elaborate_backward_fragments_uncached(&d, Some(&identity), 4, false).unwrap();
        assert_single_uncached_terminal(&out);

        let streamed = elaborate_backward_fragments_uncached(&d, Some(&identity), 4, true).unwrap();
        assert_single_uncached_terminal(&streamed);
        assert_eq!(
            out.plan.stats.dram_read_lanes,
            streamed.plan.stats.dram_read_lanes
        );
        assert_ne!(out.plan.ops, streamed.plan.ops);

        let mut reversed = identity;
        reversed.reverse();
        let out = elaborate_backward_fragments_uncached(&d, Some(&reversed), 4, false).unwrap();
        assert_single_uncached_terminal(&out);
    }

    #[test]
    fn backward_uncached_coeff_and_c_init() {
        let d = backward_fixture();
        assert!(!d.fragments.c_init.terms.is_empty());
        assert!(
            d.fragments
                .fragments
                .iter()
                .any(|fragment| !fragment.recipe.is_trivial())
        );

        let out = elaborate_backward_fragments_uncached(&d, None, 4, false).unwrap();
        let EvalOp::AccInit(Operand::BackwardSpecial { desc }) = out.plan.ops[0] else {
            panic!("non-empty c_init must initialize the accumulator through its descriptor")
        };
        assert_eq!(out.specials.get(desc), Some(&BwdSpecial::AccInit));
        assert_eq!(
            out.plan
                .ops
                .iter()
                .filter(|op| matches!(
                    op,
                    EvalOp::AccMul(Operand::BackwardSpecial { desc })
                        if matches!(out.specials.get(*desc), Some(BwdSpecial::Coefficient { .. }))
                ))
                .count(),
            1,
            "the non-trivial fragment recipe must use one coefficient operand"
        );
        assert!(matches!(
            bind_packed_plan(&out.packed, &d.layer, &[d.root], 0, 16),
            Err(ConcreteBindError::BackwardSpecialRequiresBindings { .. })
        ));
    }

    #[test]
    fn backward_uncached_rejects_invalid_order() {
        let d = backward_fixture();
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, Some(&[0, 0]), 4, false),
            Err(BackwardEvaluationError::InvalidFragmentOrder { .. })
        ));
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, Some(&[0, 2]), 4, false),
            Err(BackwardEvaluationError::InvalidFragmentOrder { .. })
        ));
    }

    #[test]
    fn backward_uncached_rejects_empty_decomposition() {
        let mut d = backward_fixture();
        d.fragments = FragmentTable::default();
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, None, 4, false),
            Err(BackwardEvaluationError::EmptyFragmentDecomposition)
        ));
    }
}
