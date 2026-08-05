//! DAG-intrinsic traffic floor used by offline forward search.

use std::collections::HashMap;

use gkr_eval_ir::{DagLayer, Expr, ExprId, FieldKind, ReadPlace, RootId, SourceKind};

use crate::forward::compile::expr_operand_field;
use crate::forward::context::ForwardAction;
use crate::forward::isa::OperandField;

/// [`dag_traffic_floor`] restricted to the roots the forward emitter actually
/// LOWERS (Task 6): `materialize.is_some()` AND classified
/// [`ForwardAction::Compute`]. A `CopyAlias` root emits ZERO program
/// instructions (`lower.rs`'s CopyAlias arm records a storage-alias
/// `RootOutput` and never lowers `root.expr` — "zero program lanes"), and a
/// `SkipScratchPrefill` root emits nothing at all, so their cones contribute no
/// compiled DRAM reads; counting them (as the plain DAG floor does) can push
/// "floor" ABOVE the achievable compile traffic on cross-layer aggregation
/// layers, inverting the bound. This variant is what the schedule producer
/// records as `LayerSchedule.floor` so `floor <= predicted_traffic` is a real
/// invariant of the compile metric.
pub fn dag_traffic_floor_with_actions(
    layer: &DagLayer,
    cross: &HashMap<ReadPlace, FieldKind>,
    actions: &HashMap<RootId, ForwardAction>,
) -> usize {
    floor_over_roots(
        layer,
        cross,
        layer
            .roots
            .iter()
            .enumerate()
            .filter_map(|(i, r)| {
                let lowered = r.materialize.is_some()
                    && matches!(actions.get(&RootId(i as u32)), Some(ForwardAction::Compute));
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
        // Resolution-pruned → special terminal: 0 traffic, do NOT descend.
        // MUST mirror Task-3 extraction's pruning so D and the instance agree.
        if layer.resolutions.contains_key(&ExprId(eid)) {
            continue;
        }
        match &layer.exprs[eid as usize] {
            Expr::Source(sid) => {
                if let SourceKind::Read { .. } = &layer.sources[sid.0 as usize].kind {
                    if distinct_reads.insert(sid.0 as usize) {
                        let f = expr_operand_field(layer, ExprId(eid), cross);
                        total += if f == OperandField::Ext { 4 } else { 1 };
                    }
                }
                // VirtualSetup / Constant / Challenge / LookupValue → 0 traffic.
            }
            Expr::Add(ch) | Expr::Mul(ch) => stack.extend(ch.iter().map(|c| c.0)),
        }
    }
    total
}
