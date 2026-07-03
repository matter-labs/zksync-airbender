//! Materialization map + implicit-drop helper for the Stage-3 forward-program
//! generator (spec §4 implicit cone-fit drops, §5 residency-vs-materialization
//! split).
//!
//! Pure, standalone — no dependency on `place.rs` or `arith.rs`. Consumes the
//! `cs::dag_ir` schedule/DAG types directly:
//!   - `build_materialize_map` indexes a `DagLayer`'s roots by `ExprId` so
//!     codegen can look up "does this value get a free streamed write, and
//!     where" without re-scanning `layer.roots` per value.
//!   - `implicit_drops` recovers the per-step "went-away-with-no-event" value
//!     set (spec §4): a value present in `resident_after` of step `p-1` but
//!     absent from `resident_before` of step `p` was dropped for free
//!     (cone-fit eviction) rather than via an explicit `ReplayEvent::Evict`.

use std::collections::{HashMap, HashSet};

use cs::gkr_compiler::dag_ir::{DagLayer, ExprId, SinkInfo, StepPlan};

/// `ExprId -> ` the free streamed writes (`SinkInfo`s) that materialize it.
/// Built from `DagLayer::roots`; a value with no materializing root has no
/// entry.
pub struct MaterializeMap(pub HashMap<ExprId, Vec<SinkInfo>>);

/// Index a layer's roots by `expr`, keeping every materializing `SinkInfo`
/// (a value may be written to more than one sink).
pub fn build_materialize_map(layer: &DagLayer) -> MaterializeMap {
    let mut m: HashMap<ExprId, Vec<SinkInfo>> = HashMap::new();
    for root in &layer.roots {
        if let Some(sink) = &root.materialize {
            m.entry(root.expr).or_default().push(sink.clone());
        }
    }
    MaterializeMap(m)
}

/// Per-step, event-less drops: `resident_after[p-1] \ resident_before[p]`
/// (step 0 diffs against the empty set). Index-aligned with `steps`.
pub fn implicit_drops(steps: &[StepPlan]) -> Vec<Vec<ExprId>> {
    let mut out = Vec::with_capacity(steps.len());
    let mut prev_after: HashSet<ExprId> = HashSet::new();
    for s in steps {
        let before: HashSet<ExprId> = s.resident_before.iter().copied().collect();
        let mut dropped: Vec<ExprId> = prev_after.difference(&before).copied().collect();
        dropped.sort_by_key(|e| e.0);
        out.push(dropped);
        prev_after = s.resident_after.iter().copied().collect();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, DagLayer, Expr, ExprId, FieldKind, Root, RootId, SinkInfo, SinkKind,
        SourceId, StepPlan,
    };
    use std::collections::BTreeMap;

    fn v(n: u32) -> ExprId {
        ExprId(n)
    }
    fn step(before: &[u32], after: &[u32]) -> StepPlan {
        StepPlan {
            resident_before: before.iter().map(|&x| v(x)).collect(),
            events: vec![],
            resident_after: after.iter().map(|&x| v(x)).collect(),
        }
    }

    #[test]
    fn implicit_drops_are_after_minus_before() {
        // step0 leaves {1,2,3} resident; step1 arrives with only {1,3} -> value 2 dropped implicitly.
        let steps = vec![step(&[], &[1, 2, 3]), step(&[1, 3], &[1, 3])];
        let drops = implicit_drops(&steps);
        assert_eq!(drops.len(), 2);
        assert!(drops[0].is_empty(), "step0 diffs against empty resident set");
        assert_eq!(drops[1], vec![v(2)], "value 2 is an event-less drop before step1");
    }

    #[test]
    fn build_materialize_map_indexes_cache_root_by_expr() {
        let sink = SinkInfo { kind: SinkKind::Cache { layer: 0, offset: 0 }, field: FieldKind::Ext };
        let layer = DagLayer {
            sources: vec![],
            exprs: vec![Expr::Source(SourceId(0))],
            roots: vec![Root { expr: ExprId(7), materialize: Some(sink.clone()), claim: None }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let map = build_materialize_map(&layer);
        assert_eq!(map.0.get(&ExprId(7)), Some(&vec![sink]));
    }
}
