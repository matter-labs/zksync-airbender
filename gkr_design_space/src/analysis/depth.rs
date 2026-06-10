//! ASAP/ALAP leveling, per-level widths, def→use reuse spans.

use crate::graph::{AnalysisGraph, Origin};
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Debug, Serialize)]
pub struct DepthStats {
    pub asap: Vec<u32>,
    pub alap: Vec<u32>,
    pub max_depth: u32,
    /// Per ASAP level: (computed-node count, computed bytes/row).
    pub level_widths: Vec<(u32, u64)>,
    /// def→use ASAP distance histogram over all edges.
    pub span_histogram: BTreeMap<u32, u32>,
    /// Fraction of edges with span <= 1 — the "unified-depth reuse" signal
    /// for the layered-fixed-register-assignment representation (spec §4).
    pub frac_span_le_1: f64,
}

pub fn depth_stats(g: &AnalysisGraph) -> DepthStats {
    let n = g.nodes.len();
    let mut asap = vec![0u32; n];
    for i in 0..n {
        // children precede parents in arena order (graph invariant)
        asap[i] = g.nodes[i]
            .children
            .iter()
            .map(|&c| asap[c] + 1)
            .max()
            .unwrap_or(0);
    }
    let max_depth = asap.iter().copied().max().unwrap_or(0);

    let mut alap = vec![max_depth; n];
    for i in (0..n).rev() {
        for &c in &g.nodes[i].children {
            alap[c] = alap[c].min(alap[i].saturating_sub(1));
        }
    }

    let mut level_widths = vec![(0u32, 0u64); max_depth as usize + 1];
    for (i, node) in g.nodes.iter().enumerate() {
        if matches!(node.origin, Origin::Computed) {
            let lw = &mut level_widths[asap[i] as usize];
            lw.0 += 1;
            lw.1 += node.width_bytes() as u64;
        }
    }

    let mut span_histogram = BTreeMap::new();
    let mut edges = 0u64;
    let mut close = 0u64;
    for (i, node) in g.nodes.iter().enumerate() {
        for &c in &node.children {
            let span = asap[i] - asap[c];
            *span_histogram.entry(span).or_insert(0) += 1;
            edges += 1;
            if span <= 1 {
                close += 1;
            }
        }
    }
    let frac_span_le_1 = if edges == 0 {
        1.0
    } else {
        close as f64 / edges as f64
    };

    DepthStats {
        asap,
        alap,
        max_depth,
        level_widths,
        span_histogram,
        frac_span_le_1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::AnalysisGraph;
    use crate::graph::tests::mini_layer;

    #[test]
    fn mini_layer_depth() {
        let g = AnalysisGraph::from_layer(&mini_layer());
        let d = depth_stats(&g);
        assert_eq!(d.asap, vec![0, 0, 1, 0, 2]);
        assert_eq!(d.max_depth, 2);
        // edges: 2->0 span1, 2->1 span1, 4->2 span1, 4->3 span2
        assert_eq!(d.span_histogram.get(&1), Some(&3));
        assert_eq!(d.span_histogram.get(&2), Some(&1));
        assert!((d.frac_span_le_1 - 0.75).abs() < 1e-9);
    }
}
