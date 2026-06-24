use std::collections::HashMap;
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, SinkId, SinkInfo, SinkKind, SourceId,
    SourceInfo, SourceKind, BatchingOrder,
};
use gkr_eval_isa::fwd::compile::expr_operand_field;
use gkr_eval_isa::fwd::isa::OperandField;
use std::collections::BTreeMap;

/// DAG-intrinsic width-weighted DRAM traffic floor `D`.
///
/// Σ width over **distinct `SourceKind::Read` leaves** reachable from
/// `Root::Output` top exprs. Excludes `Prior` (avoidable re-reads), and
/// `VirtualSetup`/`Constant`/`Challenge`/`LookupValue` (zero traffic).
/// Resolution-pruned exprs are treated as terminals (contribute 0, not descended).
/// Order/budget-independent.
pub fn dag_traffic_floor(layer: &DagLayer, cross: &HashMap<ReadPlace, FieldKind>) -> usize {
    use std::collections::HashSet;
    let mut seen_expr: HashSet<u32> = HashSet::new();
    let mut distinct_reads: HashSet<usize> = HashSet::new(); // SourceId index
    let mut total = 0usize;
    let mut stack: Vec<u32> = layer
        .roots
        .iter()
        .filter_map(|r| match r {
            Root::Output { expr, .. } => Some(expr.0),
            Root::Constraint { .. } => None,
        })
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
                // Prior / VirtualSetup / Constant / Challenge / LookupValue → 0 traffic.
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
//   Root::Output { expr: Add([ext_A, base_B, ext_A_again, prior]) }
//   - ext_A   = Read{LayerOutput{layer:1,offset:0}} + cross[..] = Ext → width 4
//   - base_B  = Read{BaseLayerWitness{column:3}}               → width 1
//   - prior   = Source(Prior{id: RootId(99)})                  → 0 traffic (excluded)
//   ext_A referenced twice in Add but counts only ONCE (distinct SourceId check).
//   Distinct real Reads = {A(ext,4), B(base,1)} → floor = 5.
#[cfg(test)]
pub fn tests_support_two_reads_one_prior() -> (DagLayer, HashMap<ReadPlace, FieldKind>) {
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
    // src 2: prior (avoidable — excluded from floor)
    let src_prior = SourceInfo {
        kind: SourceKind::Prior { id: cs::gkr_compiler::dag_ir::RootId(99) },
    };

    // --- exprs ---
    // expr 0: Source(SourceId(0)) = ext_A
    let e_ext_a = Expr::Source(SourceId(0));
    // expr 1: Source(SourceId(1)) = base_B
    let e_base_b = Expr::Source(SourceId(1));
    // expr 2: Source(SourceId(2)) = prior
    let e_prior = Expr::Source(SourceId(2));
    // expr 3: Add([ext_A=0, base_B=1, ext_A again=0, prior=2])
    let e_add = Expr::Add(vec![ExprId(0), ExprId(1), ExprId(0), ExprId(2)]);

    let layer = DagLayer {
        sources: vec![src_ext_a, src_base_b, src_prior],
        exprs: vec![e_ext_a, e_base_b, e_prior, e_add],
        roots: vec![Root::Output { expr: ExprId(3), sink: SinkId(0) }],
        sinks: vec![SinkInfo {
            kind: SinkKind::Inner { layer: 0, offset: 0 },
            field: FieldKind::Ext, // top expr includes Ext leaf → Ext sink
        }],
        batching: BatchingOrder { roots: vec![] },
        origins: BTreeMap::new(),
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
