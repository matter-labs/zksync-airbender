//! Per-layer input/output working sets and per-output input closures.

use crate::graph::{ANode, AnalysisGraph, NodeIdx, Origin};
use cs::gkr_compiler::codegen_ir::Domain;
use serde::Serialize;

#[derive(Debug, Serialize)]
pub struct LayerWorkingSet {
    pub input_cols_bf: usize,
    pub input_cols_e4: usize,
    pub cached_cols_bf: usize,
    pub cached_cols_e4: usize,
    pub bytes_per_row_in: u64,
    pub outputs_bf: usize,
    pub outputs_e4: usize,
    pub bytes_per_row_out: u64,
    /// Distinct loaded columns in each output's transitive closure (outputs in IR order).
    pub per_output_closure_cols: Vec<usize>,
}

fn is_bf(n: &ANode) -> bool {
    matches!(n.domain, Domain::Base)
}

pub fn layer_working_set(g: &AnalysisGraph) -> LayerWorkingSet {
    let mut input_cols_bf = 0;
    let mut input_cols_e4 = 0;
    let mut cached_cols_bf = 0;
    let mut cached_cols_e4 = 0;
    let mut bytes_per_row_in = 0u64;
    for n in &g.nodes {
        match n.origin {
            Origin::InputColumn(_) => {
                if is_bf(n) {
                    input_cols_bf += 1
                } else {
                    input_cols_e4 += 1
                }
                bytes_per_row_in += n.width_bytes() as u64;
            }
            Origin::CachedColumn(_) => {
                if is_bf(n) {
                    cached_cols_bf += 1
                } else {
                    cached_cols_e4 += 1
                }
                bytes_per_row_in += n.width_bytes() as u64;
            }
            _ => {}
        }
    }

    let mut outputs_bf = 0;
    let mut outputs_e4 = 0;
    let mut bytes_per_row_out = 0u64;
    for o in &g.outputs {
        let n = &g.nodes[o.node];
        if is_bf(n) {
            outputs_bf += 1
        } else {
            outputs_e4 += 1
        }
        bytes_per_row_out += n.width_bytes() as u64;
    }

    let per_output_closure_cols = g.outputs.iter().map(|o| closure_cols(g, o.node)).collect();

    LayerWorkingSet {
        input_cols_bf,
        input_cols_e4,
        cached_cols_bf,
        cached_cols_e4,
        bytes_per_row_in,
        outputs_bf,
        outputs_e4,
        bytes_per_row_out,
        per_output_closure_cols,
    }
}

/// Number of distinct loaded columns (input + cached + scratch) reachable from `root`.
pub fn closure_cols(g: &AnalysisGraph, root: NodeIdx) -> usize {
    closure_load_nodes(g, root).len()
}

/// The loaded-column node set reachable from `root` (used again by `reuse`).
pub fn closure_load_nodes(g: &AnalysisGraph, root: NodeIdx) -> Vec<NodeIdx> {
    let mut seen = vec![false; g.nodes.len()];
    let mut stack = vec![root];
    let mut loads = Vec::new();
    while let Some(i) = stack.pop() {
        if std::mem::replace(&mut seen[i], true) {
            continue;
        }
        if g.nodes[i].is_load() {
            loads.push(i);
        }
        stack.extend(g.nodes[i].children.iter().copied());
    }
    loads
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::AnalysisGraph;
    use crate::graph::tests::mini_layer;

    #[test]
    fn mini_layer_working_set() {
        let g = AnalysisGraph::from_layer(&mini_layer());
        let ws = layer_working_set(&g);
        assert_eq!((ws.input_cols_bf, ws.input_cols_e4), (2, 0));
        assert_eq!((ws.cached_cols_bf, ws.cached_cols_e4), (0, 1));
        assert_eq!(ws.bytes_per_row_in, 2 * 4 + 16);
        assert_eq!(ws.bytes_per_row_out, 16);
        assert_eq!(ws.per_output_closure_cols, vec![3]); // w0, w1, cached
    }
}
