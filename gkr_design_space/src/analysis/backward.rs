//! Backward (sumcheck) pass cost model (M3).
//!
//! Implements the verified GPU execution model in
//! `.agents/specs/2026-06-10-gkr-backward-execution-model.md`:
//! - per layer, `fs = log2(trace_len)` committed rounds minus one
//!   (`last_step = fs - 1`) plus one explicit final step at acc = 1;
//! - round 0 reads raw operand columns (quadratic-referenced only) plus the
//!   forward OUTPUT columns for c0 (constraint gates contribute none) — no
//!   folds, no writes;
//! - base (bf) columns are re-read raw in rounds 1 AND 2 (round 2 bypasses
//!   the round-1 e4 cache: 4 bf < 2 e4); first persistent e4 of base data is
//!   the quarter-size after-two cache;
//! - rounds >= 3 are a uniform telescoping e4 fold tail;
//! - virtual-setup columns are synthesized in-kernel: zero bytes always;
//! - per-round accumulator IO: warp-partial pairs at acc >= 32, dense
//!   2*acc contributions below;
//! - the dim-reducing tower is synthesized from `global_output_map`
//!   (2 inputs per OutputType per layer, doubling domains,
//!   `log2(trace_len) - final_trace_log2` layers), all-e4, no warp-partial.
//!
//! Modeling assumptions (documented, revisit with measurements): compute-phase
//! `ld.ca` term reads of just-written fold caches are treated as cache-hot
//! (zero DRAM); eq/tail/transcript fixed work is ignored (<= tens of KB per
//! layer vs N-scaled traffic).

use crate::graph::{AnalysisGraph, NodeIdx, Origin};
use crate::import::LoadedCircuit;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::Domain;
use serde::Serialize;

const E4: u64 = 16;
const BF: u64 = 4;

#[derive(Clone, Copy, Debug, Serialize)]
pub struct BackwardParams {
    /// Production value 4 (gpu/execution_prover/src/workers/gpu.rs:336).
    pub final_trace_log2: u32,
}

impl Default for BackwardParams {
    fn default() -> Self {
        BackwardParams {
            final_trace_log2: 4,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct RoundCost {
    pub step: u32,
    pub acc_size: u64,
    pub read_bytes: u64,
    pub write_bytes: u64,
    /// Accumulator/partials round-trip (write by round kernel + read by finalize).
    pub partials_bytes: u64,
}

#[derive(Debug, Serialize)]
pub struct LayerBackwardCost {
    pub layer: usize,
    pub kind: &'static str, // "main" | "dim_reducing"
    pub folding_steps: u32,
    pub bf_cols: usize,
    pub e4_cols: usize,
    pub virtual_cols: usize,
    /// bf columns referenced only via linear terms — skipped in round 0.
    pub linear_only_bf_cols: usize,
    pub c0_cols_bf: usize,
    pub c0_cols_e4: usize,
    pub rounds: Vec<RoundCost>,
    pub total_read_bytes: u64,
    pub total_write_bytes: u64,
    /// Telescoping fold-backing allocation: N e4 per ext col + N/2 e4 per bf col.
    pub fold_backing_bytes: u64,
}

#[derive(Debug, Serialize)]
pub struct BackwardCost {
    pub params: BackwardParams,
    pub main_layers: Vec<LayerBackwardCost>,
    pub tower_layers: Vec<LayerBackwardCost>,
    pub total_bytes: u64,
}

/// Distinct backward source columns of one layer, classified.
struct LayerSources {
    bf: usize,
    e4: usize,
    virt: usize,
    linear_only_bf: usize,
    c0_bf: usize,
    c0_e4: usize,
}

fn is_virtual(addr: &GKRAddress) -> bool {
    matches!(addr, GKRAddress::VirtualSetup(_))
}

/// Resolve a gate-operand node to its column units: loads map to themselves,
/// GateOutput operands are materialized columns, Sum/Product expand to leaves.
fn column_units(g: &AnalysisGraph, root: NodeIdx, out: &mut Vec<NodeIdx>) {
    let n = &g.nodes[root];
    match n.origin {
        Origin::Constant => {}
        Origin::InputColumn(_) | Origin::CachedColumn(_) | Origin::Scratch(_) => out.push(root),
        Origin::Computed => {
            // GateOutput operands are read as materialized columns; Sum/Product
            // payload operands flatten to their leaves (LinearComb terms are
            // already column-level in the IR, this is a conservative fallback).
            if n.children.is_empty() {
                out.push(root);
            } else if g.outputs.iter().any(|o| o.node == root) {
                out.push(root);
            } else {
                for &c in &n.children.clone() {
                    column_units(g, c, out);
                }
            }
        }
    }
}

fn layer_sources(
    g: &AnalysisGraph,
    layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
) -> LayerSources {
    use cs::gkr_compiler::codegen_ir::{GateKind, gate_kind_input_nodes};

    let mut quad = vec![false; g.nodes.len()];
    let mut lin = vec![false; g.nodes.len()];
    let mut mark = |roots: &[NodeIdx], flag: &mut Vec<bool>, g: &AnalysisGraph| {
        let mut units = Vec::new();
        for &r in roots {
            column_units(g, r, &mut units);
        }
        for u in units {
            flag[u] = true;
        }
    };

    for gate in layer.gates_external.iter().chain(layer.gates.iter()) {
        match &gate.kind {
            GateKind::MaxQuadratic { flat, .. }
            | GateKind::EnforceSingleMaxQuadraticConstraint { flat, .. } => {
                let q: Vec<NodeIdx> = flat
                    .quadratic
                    .iter()
                    .flat_map(|(a, terms)| {
                        std::iter::once(a.0 as NodeIdx)
                            .chain(terms.iter().map(|(_, n)| n.0 as NodeIdx))
                    })
                    .collect();
                let l: Vec<NodeIdx> = flat.linear.iter().map(|(_, n)| n.0 as NodeIdx).collect();
                mark(&q, &mut quad, g);
                mark(&l, &mut lin, g);
            }
            GateKind::EnforceConstraintsMaxQuadratic {
                quadratic, linear, ..
            } => {
                let q: Vec<NodeIdx> = quadratic
                    .iter()
                    .flat_map(|((a, b), _)| [a.0 as NodeIdx, b.0 as NodeIdx])
                    .collect();
                let l: Vec<NodeIdx> = linear.iter().map(|(n, _)| n.0 as NodeIdx).collect();
                mark(&q, &mut quad, g);
                mark(&l, &mut lin, g);
            }
            kind => {
                let ops: Vec<NodeIdx> = gate_kind_input_nodes(kind)
                    .iter()
                    .map(|n| n.0 as NodeIdx)
                    .collect();
                mark(&ops, &mut quad, g);
            }
        }
    }
    // Cache materialization inputs participate as fold sources too (caches are
    // computed in forward; backward folds the materialized cache column itself,
    // already counted as a CachedColumn load if any gate consumes it).

    let (mut bf, mut e4, mut virt, mut linear_only_bf) = (0, 0, 0, 0);
    for i in 0..g.nodes.len() {
        if !quad[i] && !lin[i] {
            continue;
        }
        let n = &g.nodes[i];
        let virtual_col = match n.origin {
            Origin::InputColumn(a) | Origin::CachedColumn(a) | Origin::Scratch(a) => is_virtual(&a),
            _ => false,
        };
        if virtual_col {
            virt += 1;
            continue;
        }
        match n.domain {
            Domain::Base => {
                bf += 1;
                if !quad[i] {
                    linear_only_bf += 1;
                }
            }
            Domain::Ext => e4 += 1,
        }
    }

    let (mut c0_bf, mut c0_e4) = (0, 0);
    for o in &g.outputs {
        if o.from_cache {
            continue;
        }
        match g.nodes[o.node].domain {
            Domain::Base => c0_bf += 1,
            Domain::Ext => c0_e4 += 1,
        }
    }

    LayerSources {
        bf,
        e4,
        virt,
        linear_only_bf,
        c0_bf,
        c0_e4,
    }
}

/// Per-round byte model for one layer with N = 2^fs rows.
fn cost_layer(
    layer: usize,
    kind: &'static str,
    fs: u32,
    src: &LayerSources,
    warp_partial: bool,
) -> LayerBackwardCost {
    let n: u64 = 1 << fs;
    let last_step = fs - 1;
    let mut rounds = Vec::new();

    let bf = src.bf as u64;
    let bf_quad = (src.bf - src.linear_only_bf) as u64;
    let e4 = src.e4 as u64;

    for step in 0..=last_step {
        let acc = if step < last_step { n >> (step + 1) } else { 1 };
        let (read, write) = if step == last_step {
            // explicit final step: 2 endpoint values per source, 2 e4 per claim address
            let r = (bf + e4) * 2 * E4;
            let w = (src.c0_bf + src.c0_e4) as u64 * 2 * E4;
            (r, w)
        } else if step == 0 {
            // raw quadratic operand columns (full) + c0 output columns (lower half)
            let r = bf_quad * n * BF
                + e4 * n * E4
                + (src.c0_bf as u64 * (n / 2) * BF + src.c0_e4 as u64 * (n / 2) * E4);
            (r, 0)
        } else if step == 1 {
            // base: raw bf re-read + after-one e4 cache write; ext: original poly + after-one write
            let r = bf * n * BF + e4 * n * E4;
            let w = (bf + e4) * (n / 2) * E4;
            (r, w)
        } else if step == 2 {
            // base: raw bf re-read AGAIN (double fold, bypasses round-1 cache); ext: after-one read
            let r = bf * n * BF + e4 * (n / 2) * E4;
            let w = (bf + e4) * (n / 4) * E4;
            (r, w)
        } else {
            // uniform e4 telescoping tail: read segment k-1, write segment k
            let seg_in = n >> (step - 1);
            let r = (bf + e4) * seg_in * E4;
            let w = (bf + e4) * (seg_in / 2) * E4;
            (r, w)
        };
        let partials = if step == last_step {
            0
        } else if warp_partial && acc >= 32 {
            2 * (acc / 32) * E4 * 2
        } else {
            2 * acc * E4 * 2
        };
        rounds.push(RoundCost {
            step,
            acc_size: acc,
            read_bytes: read,
            write_bytes: write,
            partials_bytes: partials,
        });
    }

    let total_read_bytes = rounds
        .iter()
        .map(|r| r.read_bytes + r.partials_bytes / 2)
        .sum();
    let total_write_bytes = rounds
        .iter()
        .map(|r| r.write_bytes + r.partials_bytes / 2)
        .sum();
    let fold_backing_bytes = e4 * n * E4 + bf * (n / 2) * E4;

    LayerBackwardCost {
        layer,
        kind,
        folding_steps: fs,
        bf_cols: src.bf,
        e4_cols: src.e4,
        virtual_cols: src.virt,
        linear_only_bf_cols: src.linear_only_bf,
        c0_cols_bf: src.c0_bf,
        c0_cols_e4: src.c0_e4,
        rounds,
        total_read_bytes,
        total_write_bytes,
        fold_backing_bytes,
    }
}

pub fn backward_cost(c: &LoadedCircuit, params: BackwardParams) -> BackwardCost {
    let n = c.circuit.globals.trace_len as u64;
    let fs = n.trailing_zeros();
    assert!(
        n.is_power_of_two() && fs >= 4,
        "trace_len must be a power of two >= 16"
    );

    // Main layers, executed in reverse; all at the full trace hypercube.
    let main_layers: Vec<LayerBackwardCost> = c
        .circuit
        .layers
        .iter()
        .zip(&c.graphs)
        .enumerate()
        .map(|(i, (layer, g))| {
            let src = layer_sources(g, layer);
            cost_layer(i, "main", fs, &src, true)
        })
        .collect();

    // Dim-reducing tower: log2(trace_len) - final_trace_log2 layers, each with
    // 2 e4 input polys per OutputType record (extras.rs:227-283), domains
    // doubling backward from 2^final_trace_log2 up to trace_len / 2. All-e4,
    // 2 output claims per record, no warp-partial variant.
    let records = c.circuit.globals.global_output_map.len();
    let tower_layers: Vec<LayerBackwardCost> = (params.final_trace_log2..fs)
        .map(|k| {
            let src = LayerSources {
                bf: 0,
                e4: records * 2,
                virt: 0,
                linear_only_bf: 0,
                c0_bf: 0,
                c0_e4: records * 2,
            };
            cost_layer(k as usize, "dim_reducing", k.max(2), &src, false)
        })
        .collect();

    let total_bytes = main_layers
        .iter()
        .chain(&tower_layers)
        .map(|l| l.total_read_bytes + l.total_write_bytes)
        .sum();

    BackwardCost {
        params,
        main_layers,
        tower_layers,
        total_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::AnalysisGraph;
    use crate::graph::tests::mini_layer;

    #[test]
    fn mini_layer_round_bytes() {
        // mini_layer: 2 bf quadratic cols (w0,w1), 1 e4 cached col, 1 e4 output.
        let layer = mini_layer();
        let g = AnalysisGraph::from_layer(&layer);
        let src = layer_sources(&g, &layer);
        assert_eq!((src.bf, src.e4, src.virt, src.linear_only_bf), (2, 1, 0, 0));
        assert_eq!((src.c0_bf, src.c0_e4), (0, 1));

        let cost = cost_layer(0, "main", 4, &src, true); // N = 16
        // R0: 2 bf * 16 * 4 + 1 e4 * 16 * 16 + c0: 8 * 16 = 128 + 256 + 128
        assert_eq!(cost.rounds[0].read_bytes, 512);
        assert_eq!(cost.rounds[0].write_bytes, 0);
        // R1: bf 2*16*4 + e4 1*16*16 = 384 read; write (2+1)*8*16 = 384
        assert_eq!(cost.rounds[1].read_bytes, 384);
        assert_eq!(cost.rounds[1].write_bytes, 384);
        // R2: bf raw again 128 + e4 half 128 = 256; write 3*4*16 = 192
        assert_eq!(cost.rounds[2].read_bytes, 256);
        assert_eq!(cost.rounds[2].write_bytes, 192);
        // final explicit step: 3 sources * 2 e4 = 96 read; 1 claim * 2 e4 = 32 write
        assert_eq!(cost.rounds[3].read_bytes, 96);
        assert_eq!(cost.rounds[3].write_bytes, 32);
        // acc < 32 everywhere at N=16: dense partials 2*acc*16*2
        assert_eq!(cost.rounds[0].partials_bytes, 2 * 8 * 16 * 2);
    }

    #[test]
    fn fixture_backward_cost_sane() {
        use crate::import::load_circuit;
        use crate::import::tests::fixture;
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let bc = backward_cost(&c, BackwardParams::default());
        assert_eq!(bc.main_layers.len(), 4);
        assert!(!bc.tower_layers.is_empty());
        assert!(bc.total_bytes > 0);
        // round-0 traffic of layer 0 dominates its tail (geometric)
        let l0 = &bc.main_layers[0];
        let r0 = l0.rounds[0].read_bytes;
        let tail: u64 = l0.rounds[3..].iter().map(|r| r.read_bytes).sum();
        assert!(r0 > tail / 4, "r0 {} vs tail {}", r0, tail);
    }
}
