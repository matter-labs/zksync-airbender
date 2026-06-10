//! Aggregated per-circuit report: serde for JSON, compact markdown rendering.

use crate::analysis::depth::{DepthStats, depth_stats};
use crate::analysis::partition::{PartitionPoint, partition_curve};
use crate::analysis::reuse::{CircuitReuse, circuit_reuse};
use crate::analysis::schedule::{LiveStats, Order, simulate};
use crate::analysis::working_set::{LayerWorkingSet, layer_working_set};
use crate::import::LoadedCircuit;
use serde::Serialize;

/// Per-thread live-byte budgets swept by the partition pass. In register
/// terms: 128 B = 32 regs ... 2048 B = 512 regs (beyond the 255-reg ceiling,
/// as an asymptote check).
pub const PARTITION_BUDGETS: [u64; 7] = [128, 192, 256, 384, 512, 1024, 2048];

#[derive(Serialize)]
pub struct LayerReport {
    pub layer: usize,
    pub nodes: usize,
    pub gates: usize,
    pub caches: usize,
    pub working_set: LayerWorkingSet,
    pub max_depth: u32,
    pub frac_span_le_1: f64,
    pub live_arena: LiveStats,
    pub live_scheduled: LiveStats,
    /// Cut-cost curve; empty for layers already under the smallest budget.
    pub partition: Vec<PartitionPoint>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub depth_full: Option<DepthStats>, // JSON-only detail
}

#[derive(Serialize)]
pub struct CircuitReport {
    pub path: String,
    pub trace_len: usize,
    pub layers: Vec<LayerReport>,
    pub reuse: CircuitReuse,
}

pub fn build_report(path: &str, c: &LoadedCircuit, full: bool) -> CircuitReport {
    let layers = c
        .circuit
        .layers
        .iter()
        .zip(&c.graphs)
        .enumerate()
        .map(|(i, (layer, g))| {
            let d = depth_stats(g);
            let live_scheduled = simulate(g, Order::PressureAware);
            let partition = if live_scheduled.max_live_bytes > PARTITION_BUDGETS[0] {
                partition_curve(g, &PARTITION_BUDGETS)
            } else {
                vec![]
            };
            LayerReport {
                layer: i,
                nodes: g.nodes.len(),
                gates: layer.gates_external.len() + layer.gates.len(),
                caches: layer.caches.len(),
                working_set: layer_working_set(g),
                max_depth: d.max_depth,
                frac_span_le_1: d.frac_span_le_1,
                live_arena: simulate(g, Order::Arena),
                live_scheduled,
                partition,
                depth_full: full.then_some(d),
            }
        })
        .collect();
    CircuitReport {
        path: path.to_string(),
        trace_len: c.circuit.globals.trace_len,
        layers,
        reuse: circuit_reuse(c),
    }
}

pub fn to_markdown(r: &CircuitReport) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "## {} (trace_len {})\n", r.path, r.trace_len).unwrap();
    writeln!(s, "| layer | nodes | gates | caches | in cols bf/e4 | cached bf/e4 | B/row in | out bf/e4 | B/row out | depth | span<=1 | live arena bf/e4/B | live sched bf/e4/B |").unwrap();
    writeln!(s, "|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|").unwrap();
    for l in &r.layers {
        let w = &l.working_set;
        writeln!(
            s,
            "| {} | {} | {} | {} | {}/{} | {}/{} | {} | {}/{} | {} | {} | {:.2} | {}/{}/{} | {}/{}/{} |",
            l.layer,
            l.nodes,
            l.gates,
            l.caches,
            w.input_cols_bf,
            w.input_cols_e4,
            w.cached_cols_bf,
            w.cached_cols_e4,
            w.bytes_per_row_in,
            w.outputs_bf,
            w.outputs_e4,
            w.bytes_per_row_out,
            l.max_depth,
            l.frac_span_le_1,
            l.live_arena.max_live_bf,
            l.live_arena.max_live_e4,
            l.live_arena.max_live_bytes,
            l.live_scheduled.max_live_bf,
            l.live_scheduled.max_live_e4,
            l.live_scheduled.max_live_bytes,
        )
        .unwrap();
    }
    for l in &r.layers {
        if l.partition.is_empty() {
            continue;
        }
        let base = l.working_set.bytes_per_row_in + l.working_set.bytes_per_row_out;
        writeln!(
            s,
            "\n### partition curve — layer {} (baseline {} B/row in+out)\n",
            l.layer, base
        )
        .unwrap();
        writeln!(
            s,
            "| budget B | chunks | cut vals | store B | load B | dup col B | extra B/row | extra % | max chunk live | max chunk in-cols |"
        )
        .unwrap();
        writeln!(s, "|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|").unwrap();
        for p in &l.partition {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {:.1} | {} | {} |",
                p.budget_bytes,
                p.chunks,
                p.cut_values,
                p.cut_store_bytes_per_row,
                p.cut_load_bytes_per_row,
                p.dup_col_load_bytes_per_row,
                p.extra_bytes_per_row,
                100.0 * p.extra_bytes_per_row as f64 / base as f64,
                p.max_chunk_live_bytes,
                p.max_chunk_input_cols,
            )
            .unwrap();
        }
    }
    writeln!(s, "\n### caches ({})\n", r.reuse.caches.len()).unwrap();
    writeln!(
        s,
        "| layer | store B/row | uses | fan-in cols | fan-in B/row | max marginal B/row |"
    )
    .unwrap();
    writeln!(s, "|--:|--:|--:|--:|--:|--:|").unwrap();
    for ci in &r.reuse.caches {
        let max_marginal = ci
            .marginal_bytes_per_row
            .iter()
            .map(|&(_, b)| b)
            .max()
            .unwrap_or(0);
        writeln!(
            s,
            "| {} | {} | {} | {} | {} | {} |",
            ci.producing_layer,
            ci.store_bytes_per_row,
            ci.total_uses,
            ci.fanin_cols,
            ci.fanin_bytes_per_row,
            max_marginal,
        )
        .unwrap();
    }
    writeln!(
        s,
        "\nfan-out histogram (computed nodes): {:?}\n",
        r.reuse.fanout_histogram
    )
    .unwrap();
    s
}
