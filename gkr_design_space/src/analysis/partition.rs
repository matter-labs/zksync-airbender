//! Budgeted DAG partitioning (M2): chunk the best schedule order under a
//! per-thread live-byte budget and account the extra DRAM traffic each cut
//! costs versus the single-kernel baseline.
//!
//! Import costs are origin-aware: a computed value crossing a boundary is
//! stored once and reloaded per consuming chunk; a column (`Place`) is never
//! stored — later chunks just re-load it (duplicate column load). Values are
//! imported lazily at first use per chunk and held until global death or the
//! chunk boundary, whichever first.

use crate::analysis::schedule::best_order;
use crate::graph::{AnalysisGraph, NodeIdx, Origin};
use serde::Serialize;

#[derive(Debug, Serialize)]
pub struct PartitionPoint {
    pub budget_bytes: u64,
    pub chunks: usize,
    /// Distinct computed values stored at a chunk boundary.
    pub cut_values: usize,
    pub cut_store_bytes_per_row: u64,
    pub cut_load_bytes_per_row: u64,
    /// Column loads repeated beyond their first chunk.
    pub dup_col_load_bytes_per_row: u64,
    /// Total traffic added vs the single-kernel baseline.
    pub extra_bytes_per_row: u64,
    /// Largest observed chunk-live bytes (> budget only for a single
    /// wider-than-budget node, which is placed alone in an oversize chunk).
    pub max_chunk_live_bytes: u64,
    pub max_chunk_input_cols: usize,
}

pub fn partition_curve(g: &AnalysisGraph, budgets: &[u64]) -> Vec<PartitionPoint> {
    let order = best_order(g);
    budgets.iter().map(|&b| partition(g, &order, b)).collect()
}

fn partition(g: &AnalysisGraph, order: &[NodeIdx], budget_bytes: u64) -> PartitionPoint {
    let n = g.nodes.len();
    let mut remaining = vec![0u32; n];
    for node in &g.nodes {
        for &c in &node.children {
            remaining[c] += 1;
        }
    }

    let mut live = vec![false; n];
    let mut live_bytes = 0u64;
    let mut stored = vec![false; n]; // computed value already cut-stored
    let mut col_loaded_once = vec![false; n]; // column already loaded in some prior chunk
    let mut in_chunk_cols: Vec<NodeIdx> = Vec::new(); // distinct columns loaded this chunk

    let mut point = PartitionPoint {
        budget_bytes,
        chunks: 1,
        cut_values: 0,
        cut_store_bytes_per_row: 0,
        cut_load_bytes_per_row: 0,
        dup_col_load_bytes_per_row: 0,
        extra_bytes_per_row: 0,
        max_chunk_live_bytes: 0,
        max_chunk_input_cols: 0,
    };

    // Flush the current chunk: still-live computed values with future uses are
    // cut (stored once); columns are simply dropped (reloaded on next use).
    let flush = |live: &mut Vec<bool>,
                 live_bytes: &mut u64,
                 stored: &mut Vec<bool>,
                 in_chunk_cols: &mut Vec<NodeIdx>,
                 point: &mut PartitionPoint,
                 g: &AnalysisGraph| {
        for i in 0..live.len() {
            if !live[i] {
                continue;
            }
            live[i] = false;
            if matches!(g.nodes[i].origin, Origin::Computed) && !stored[i] {
                stored[i] = true;
                point.cut_values += 1;
                point.cut_store_bytes_per_row += g.nodes[i].width_bytes() as u64;
            }
        }
        *live_bytes = 0;
        point.max_chunk_input_cols = point.max_chunk_input_cols.max(in_chunk_cols.len());
        in_chunk_cols.clear();
        point.chunks += 1;
    };

    for &i in order {
        if matches!(g.nodes[i].origin, Origin::Constant) {
            continue;
        }
        // Bytes this node needs on top of the current live set: lazily
        // imported operands + its own slot.
        let needed = |live: &[bool]| -> u64 {
            let imports: u64 = g.nodes[i]
                .children
                .iter()
                .filter(|&&c| !live[c] && !matches!(g.nodes[c].origin, Origin::Constant))
                .map(|&c| g.nodes[c].width_bytes() as u64)
                .sum();
            imports + g.nodes[i].width_bytes() as u64
        };
        if live_bytes + needed(&live) > budget_bytes && live_bytes > 0 {
            flush(
                &mut live,
                &mut live_bytes,
                &mut stored,
                &mut in_chunk_cols,
                &mut point,
                g,
            );
        }
        // Import operands (cost depends on origin and history).
        for &c in &g.nodes[i].children {
            if live[c] || matches!(g.nodes[c].origin, Origin::Constant) {
                continue;
            }
            let w = g.nodes[c].width_bytes() as u64;
            if g.nodes[c].is_load() {
                if col_loaded_once[c] {
                    point.dup_col_load_bytes_per_row += w;
                }
                col_loaded_once[c] = true;
                in_chunk_cols.push(c);
            } else {
                // computed value produced in an earlier chunk (cut-stored there)
                debug_assert!(stored[c], "import of never-stored computed value");
                point.cut_load_bytes_per_row += w;
            }
            live[c] = true;
            live_bytes += w;
        }
        // Define the node itself. `Place` defs count as first column loads.
        if g.nodes[i].is_load() {
            if col_loaded_once[i] {
                point.dup_col_load_bytes_per_row += g.nodes[i].width_bytes() as u64;
            }
            col_loaded_once[i] = true;
            in_chunk_cols.push(i);
        }
        live[i] = true;
        live_bytes += g.nodes[i].width_bytes() as u64;
        point.max_chunk_live_bytes = point.max_chunk_live_bytes.max(live_bytes);

        // Global deaths release slots within the chunk.
        for &c in &g.nodes[i].children {
            remaining[c] -= 1;
            if remaining[c] == 0 && live[c] {
                live[c] = false;
                live_bytes -= g.nodes[c].width_bytes() as u64;
            }
        }
        if remaining[i] == 0 {
            live[i] = false;
            live_bytes -= g.nodes[i].width_bytes() as u64;
        }
    }
    point.max_chunk_input_cols = point.max_chunk_input_cols.max(in_chunk_cols.len());
    point.extra_bytes_per_row = point.cut_store_bytes_per_row
        + point.cut_load_bytes_per_row
        + point.dup_col_load_bytes_per_row;
    point
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::schedule::{Order, simulate};
    use crate::graph::AnalysisGraph;
    use crate::graph::tests::mini_layer;

    #[test]
    fn unlimited_budget_is_one_chunk_no_extra_traffic() {
        let g = AnalysisGraph::from_layer(&mini_layer());
        let p = &partition_curve(&g, &[1 << 20])[0];
        assert_eq!(p.chunks, 1);
        assert_eq!(p.extra_bytes_per_row, 0);
        assert_eq!(
            p.max_chunk_live_bytes,
            simulate(&g, Order::PressureAware).max_live_bytes
        );
    }

    #[test]
    fn tight_budget_cuts_and_accounts_traffic() {
        // Order: p0,p1,sum,cached,gate. At the gate (needs sum + cached + own
        // = 36B) a 24B budget forces a cut: the bf sum is stored (4) and
        // reloaded (4), the cached column re-loaded (16). The gate node alone
        // exceeds the budget, so it sits in a documented oversize chunk.
        let g = AnalysisGraph::from_layer(&mini_layer());
        let p = &partition_curve(&g, &[24])[0];
        assert_eq!(p.chunks, 2);
        assert_eq!(p.cut_values, 1);
        assert_eq!(p.cut_store_bytes_per_row, 4);
        assert_eq!(p.cut_load_bytes_per_row, 4);
        assert_eq!(p.dup_col_load_bytes_per_row, 16);
        assert_eq!(p.extra_bytes_per_row, 24);
        assert_eq!(p.max_chunk_live_bytes, 36); // oversize single-node chunk
    }
}
