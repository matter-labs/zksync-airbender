use std::collections::HashMap;
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, SinkInfo, SinkKind, SourceId,
    SourceInfo, SourceKind, BatchingOrder,
};
use gkr_eval_isa::fwd::compile::expr_operand_field;
use gkr_eval_isa::fwd::isa::OperandField;
use std::collections::BTreeMap;

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

// Module-level (OUTSIDE `mod tests`) so instance.rs / Task 3 can reuse by path
// `crate::s3_gap::floor::tests_support_two_reads_one_prior`.
//
// Builds a synthetic layer:
//   Root { materialize: Inner, claim: .., expr: Add([ext_A, base_B, ext_A_again]) }
//   - ext_A   = Read{LayerOutput{layer:1,offset:0}} + cross[..] = Ext → width 4
//   - base_B  = Read{BaseLayerWitness{column:3}}               → width 1
//   ext_A referenced twice in Add but counts only ONCE (distinct SourceId check).
//   Distinct real Reads = {A(ext,4), B(base,1)} → floor = 5.
//
// Part B: the original fixture carried a 0-traffic `Source(Prior{id: RootId(0)})` term
// (self-referential — its only root was the producer-less Output itself, not a cache
// producer). `Prior` is gone; the term is dropped and the source removed, preserving the
// expected metric (floor == 5).
#[cfg(test)]
pub fn tests_support_two_reads_one_prior() -> (DagLayer, HashMap<ReadPlace, FieldKind>) {
    use cs::gkr_compiler::dag_ir::{ClaimInfo, RootGroup, RootOrigin, RootSlot};
    // --- sources ---
    // src 0: ext cross-layer read A
    let src_ext_a = SourceInfo {
        kind: SourceKind::Read {
            place: ReadPlace::LayerOutput { layer: 1, offset: 0 },
        },
    };
    // src 1: base witness read B
    let src_base_b = SourceInfo {
        kind: SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column: 3 },
        },
    };

    // --- exprs ---
    // expr 0: Source(SourceId(0)) = ext_A
    let e_ext_a = Expr::Source(SourceId(0));
    // expr 1: Source(SourceId(1)) = base_B
    let e_base_b = Expr::Source(SourceId(1));
    // expr 2: Add([ext_A=0, base_B=1, ext_A again=0])
    let e_add = Expr::Add(vec![ExprId(0), ExprId(1), ExprId(0)]);

    let layer = DagLayer {
        sources: vec![src_ext_a, src_base_b],
        exprs: vec![e_ext_a, e_base_b, e_add],
        roots: vec![Root {
            expr: ExprId(2),
            materialize: Some(SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Ext, // top expr includes Ext leaf → Ext sink
            }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            }),
        }],
        batching: BatchingOrder { roots: vec![] },
        resolutions: BTreeMap::new(),
    };

    let mut cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
    cross.insert(ReadPlace::LayerOutput { layer: 1, offset: 0 }, FieldKind::Ext);

    (layer, cross)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_counts_distinct_reads_widthweighted_excludes_prior() {
        let (layer, cross) = tests_support_two_reads_one_prior();
        assert_eq!(dag_traffic_floor(&layer, &cross), 5);
    }

    /// Determinism guard: D is a pure function of the DAG — takes no order/budget.
    #[test]
    fn floor_is_pure_function_of_dag() {
        let (layer, cross) = tests_support_two_reads_one_prior();
        assert_eq!(dag_traffic_floor(&layer, &cross), dag_traffic_floor(&layer, &cross));
    }
}
