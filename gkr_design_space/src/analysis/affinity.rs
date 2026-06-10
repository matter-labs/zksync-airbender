//! Column-affinity structure (M2b): is the gate->input-column bipartite graph
//! clusterable, or a cross-product?
//!
//! Per-output input closures are compared pairwise (Jaccard) and per-column
//! output-fanout is histogrammed. A greedy clustering probe groups outputs
//! under a distinct-columns-per-cluster budget and reports the duplicate
//! column loads that clustering achieves — the lower bound the schedule-
//! contiguous partitioner should be compared against.

use crate::analysis::working_set::closure_load_nodes;
use crate::graph::{AnalysisGraph, NodeIdx};
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Debug, Serialize)]
pub struct ColumnAffinity {
    pub outputs: usize,
    pub distinct_cols: usize,
    pub mean_closure_cols: f64,
    /// outputs-per-column -> number of columns with that fanout.
    pub col_fanout_histogram: BTreeMap<u32, u32>,
    /// Pairwise closure Jaccard percentiles over all output pairs.
    pub jaccard_p10: f64,
    pub jaccard_p50: f64,
    pub jaccard_p90: f64,
    /// Greedy affinity-clustering probes at increasing column budgets.
    pub probes: Vec<ClusterProbe>,
}

#[derive(Debug, Serialize)]
pub struct ClusterProbe {
    pub max_cols_per_cluster: usize,
    pub clusters: usize,
    /// Sum over clusters of distinct columns minus global distinct columns —
    /// the duplicate column loads this clustering pays.
    pub dup_col_loads: usize,
    pub dup_col_load_bytes_per_row: u64,
}

/// Dense bitset over re-indexed load nodes.
#[derive(Clone)]
struct BitSet(Vec<u64>);

impl BitSet {
    fn new(bits: usize) -> Self {
        BitSet(vec![0; bits.div_ceil(64)])
    }
    fn set(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn count(&self) -> u32 {
        self.0.iter().map(|w| w.count_ones()).sum()
    }
    fn intersect_count(&self, other: &Self) -> u32 {
        self.0
            .iter()
            .zip(&other.0)
            .map(|(a, b)| (a & b).count_ones())
            .sum()
    }
    fn union_with(&mut self, other: &Self) {
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            *a |= b;
        }
    }
    fn union_count(&self, other: &Self) -> u32 {
        self.0
            .iter()
            .zip(&other.0)
            .map(|(a, b)| (a | b).count_ones())
            .sum()
    }
}

pub fn column_affinity(g: &AnalysisGraph, col_budgets: &[usize]) -> ColumnAffinity {
    // Re-index load nodes densely.
    let mut load_idx: Vec<Option<usize>> = vec![None; g.nodes.len()];
    let mut load_nodes: Vec<NodeIdx> = Vec::new();
    for (i, n) in g.nodes.iter().enumerate() {
        if n.is_load() {
            load_idx[i] = Some(load_nodes.len());
            load_nodes.push(i);
        }
    }
    let bits = load_nodes.len();

    // Per-output closure bitsets.
    let closures: Vec<BitSet> = g
        .outputs
        .iter()
        .map(|o| {
            let mut bs = BitSet::new(bits);
            for l in closure_load_nodes(g, o.node) {
                bs.set(load_idx[l].unwrap());
            }
            bs
        })
        .collect();

    // Column fanout across outputs.
    let mut col_fanout = vec![0u32; bits];
    for bs in &closures {
        for (w, word) in bs.0.iter().enumerate() {
            let mut m = *word;
            while m != 0 {
                let b = m.trailing_zeros() as usize;
                col_fanout[w * 64 + b] += 1;
                m &= m - 1;
            }
        }
    }
    let mut col_fanout_histogram = BTreeMap::new();
    for &f in col_fanout.iter().take(bits) {
        if f > 0 {
            *col_fanout_histogram.entry(f).or_insert(0) += 1;
        }
    }

    // Full pairwise Jaccard percentiles.
    let mut jacc: Vec<f64> = Vec::with_capacity(closures.len() * (closures.len() - 1) / 2);
    for i in 0..closures.len() {
        for j in (i + 1)..closures.len() {
            let inter = closures[i].intersect_count(&closures[j]) as f64;
            let union = closures[i].union_count(&closures[j]) as f64;
            jacc.push(if union == 0.0 { 0.0 } else { inter / union });
        }
    }
    jacc.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let pct = |p: f64| -> f64 {
        if jacc.is_empty() {
            0.0
        } else {
            jacc[((jacc.len() - 1) as f64 * p) as usize]
        }
    };

    let mean_closure_cols =
        closures.iter().map(|c| c.count() as f64).sum::<f64>() / closures.len().max(1) as f64;

    // Greedy clustering probe: assign each output (descending closure size) to
    // the cluster with the largest intersection that stays under the column
    // budget; open a new cluster otherwise.
    let probes = col_budgets
        .iter()
        .map(|&budget| {
            let mut order: Vec<usize> = (0..closures.len()).collect();
            order.sort_by_key(|&i| std::cmp::Reverse(closures[i].count()));
            let mut clusters: Vec<BitSet> = Vec::new();
            for &i in &order {
                let mut best: Option<(usize, u32)> = None;
                for (ci, cb) in clusters.iter().enumerate() {
                    let inter = cb.intersect_count(&closures[i]);
                    if cb.union_count(&closures[i]) as usize <= budget
                        && best.is_none_or(|(_, b)| inter > b)
                    {
                        best = Some((ci, inter));
                    }
                }
                match best {
                    Some((ci, _)) => clusters[ci].union_with(&closures[i]),
                    None => clusters.push(closures[i].clone()),
                }
            }
            let total: usize = clusters.iter().map(|c| c.count() as usize).sum();
            let dup = total.saturating_sub(bits);
            let dup_bytes: u64 = {
                // approximate dup bytes with the mean column width
                let total_bytes: u64 = load_nodes
                    .iter()
                    .map(|&l| g.nodes[l].width_bytes() as u64)
                    .sum();
                if bits == 0 {
                    0
                } else {
                    dup as u64 * total_bytes / bits as u64
                }
            };
            ClusterProbe {
                max_cols_per_cluster: budget,
                clusters: clusters.len(),
                dup_col_loads: dup,
                dup_col_load_bytes_per_row: dup_bytes,
            }
        })
        .collect();

    ColumnAffinity {
        outputs: closures.len(),
        distinct_cols: bits,
        mean_closure_cols,
        col_fanout_histogram,
        jaccard_p10: pct(0.10),
        jaccard_p50: pct(0.50),
        jaccard_p90: pct(0.90),
        probes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::AnalysisGraph;
    use crate::graph::tests::mini_layer;

    #[test]
    fn mini_layer_affinity() {
        let g = AnalysisGraph::from_layer(&mini_layer());
        let a = column_affinity(&g, &[8]);
        assert_eq!(a.outputs, 1);
        assert_eq!(a.distinct_cols, 3);
        assert_eq!(a.mean_closure_cols, 3.0);
        // single output, no pairs
        assert_eq!(a.jaccard_p50, 0.0);
        assert_eq!(a.probes[0].clusters, 1);
        assert_eq!(a.probes[0].dup_col_loads, 0);
    }
}
