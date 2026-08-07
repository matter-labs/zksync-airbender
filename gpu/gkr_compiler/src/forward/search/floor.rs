//! DAG-intrinsic traffic floor used by offline forward search.

use std::collections::HashMap;

use gkr_eval_ir::{DagLayer, Expr, ExprId, FieldKind, ReadPlace, RootId, SourceKind};

use crate::forward::compile::expr_operand_field;

/// Traffic floor over roots that emit forward instructions. Copy aliases and
/// skipped scratch prefills contribute no reads.
pub(super) fn dag_traffic_floor(
    layer: &DagLayer,
    cross: &HashMap<ReadPlace, FieldKind>,
    compute_roots: &std::collections::BTreeSet<RootId>,
) -> usize {
    floor_over_roots(
        layer,
        cross,
        layer
            .roots
            .iter()
            .enumerate()
            .filter_map(|(i, r)| {
                let lowered = r.materialize.is_some() && compute_roots.contains(&RootId(i as u32));
                lowered.then_some(r.expr.0)
            })
            .collect(),
    )
}

fn floor_over_roots(
    layer: &DagLayer,
    cross: &HashMap<ReadPlace, FieldKind>,
    roots: Vec<u32>,
) -> usize {
    use std::collections::HashSet;
    let mut seen_expr: HashSet<u32> = HashSet::new();
    let mut distinct_reads: HashSet<usize> = HashSet::new(); // SourceId index
    let mut total = 0usize;
    let mut stack: Vec<u32> = roots;
    while let Some(eid) = stack.pop() {
        if !seen_expr.insert(eid) {
            continue;
        }
        // Peeks are omitted from this conservative lower bound.
        if layer.resolutions.contains_key(&ExprId(eid)) {
            continue;
        }
        match &layer.exprs[eid as usize] {
            Expr::Source(sid) => {
                if let SourceKind::Read { .. } = &layer.sources[sid.0 as usize] {
                    if distinct_reads.insert(sid.0 as usize) {
                        let f = expr_operand_field(layer, ExprId(eid), cross);
                        total += f.lanes();
                    }
                }
                // Host values and virtual setup sources do not read DRAM.
            }
            Expr::Add(ch) | Expr::Mul(ch) => stack.extend(ch.iter().map(|c| c.0)),
        }
    }
    total
}
