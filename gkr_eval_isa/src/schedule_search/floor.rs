//! DAG-intrinsic traffic floor (Task 5 promotion).
//!
//! `dag_traffic_floor` moved here (verbatim, modulo the re-exported cross-map helper)
//! from the test-side `gkr_eval_isa/tests/s3_gap/floor.rs` prototype so the Stage-2b
//! schedule producer can record `LayerSchedule.floor` from production code.
//! `build_cross_layer_field_map` already lives in `fwd::compile` (production); it is
//! re-exported here so the schedule-search API surface is self-contained, per the
//! Task-5 interface (`schedule_search::floor::build_cross_layer_field_map`).

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{DagLayer, Expr, ExprId, FieldKind, ReadPlace, SourceKind};

use crate::fwd::compile::expr_operand_field;
use crate::fwd::isa::OperandField;

/// Cross-layer field map builder (production impl in `fwd::compile::arith`).
pub use crate::fwd::compile::build_cross_layer_field_map;

/// DAG-intrinsic width-weighted DRAM traffic floor `D`.
///
/// Σ width over **distinct `SourceKind::Read` leaves** reachable from
/// materialize-bearing top exprs (`root.materialize.is_some()` — Output + Cache,
/// skipping claim-only Constraint roots). `VirtualSetup`/`Constant`/`Challenge`/
/// `LookupValue` are zero traffic. (Part B: there is no `Prior` source any more —
/// same-layer cache reuse is a recomputed shared `ExprId`, reached transitively
/// through the cone that holds it.) Resolution-pruned exprs are treated as terminals
/// (contribute 0, not descended). Order/budget-independent.
pub fn dag_traffic_floor(layer: &DagLayer, cross: &HashMap<ReadPlace, FieldKind>) -> usize {
    use std::collections::HashSet;
    let mut seen_expr: HashSet<u32> = HashSet::new();
    let mut distinct_reads: HashSet<usize> = HashSet::new(); // SourceId index
    let mut total = 0usize;
    let mut stack: Vec<u32> = layer
        .roots
        .iter()
        // Materialize-bearing roots (Output + Cache); skip claim-only Constraint roots.
        .filter_map(|r| r.materialize.is_some().then_some(r.expr.0))
        .collect();
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
