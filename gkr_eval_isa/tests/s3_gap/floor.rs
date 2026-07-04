use std::collections::HashMap;
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, SinkInfo, SinkKind, SourceId,
    SourceInfo, SourceKind, BatchingOrder,
};
use std::collections::BTreeMap;

/// Promoted to production in Task 5 (`gkr_eval_isa::schedule_search::floor`);
/// this thin re-export keeps the test-side call sites alive until Task 7
/// retires the `s3_gap` tree (`dag_simplify_parity.rs` already imports the
/// promoted path directly).
pub use gkr_eval_isa::schedule_search::floor::dag_traffic_floor;

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
