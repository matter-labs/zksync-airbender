//! Stage-2 static cost report, FORWARD SUBSET: per (circuit, layer, config)
//! compile stats for forward programs. The per-round-class dimension the spec
//! requires for full stage 2 lands with the 1b backward plan.

use crate::compiler::{CompileParams, CompileStats, OrderKind, compile_layer};
use gkr_design_space::import::LoadedCircuit;
use serde::Serialize;

/// (slot cells, fixed cells) grid swept by the report.
pub const CONFIG_GRID: [(usize, usize); 6] =
    [(64, 0), (64, 16), (128, 0), (128, 16), (256, 16), (4096, 0)];

/// Constant-bank tiers per spec §3/§5: 64 KB total, ~24 KB already reserved
/// by existing GKR symbols.
pub fn residency_tier(bytes: usize) -> &'static str {
    if bytes <= 36_000 {
        "const-coexist"
    } else if bytes <= 64_000 {
        "const-alone"
    } else {
        "global"
    }
}

#[derive(Serialize)]
pub struct LayerCost {
    pub layer: usize,
    pub slot_cells: usize,
    pub fixed_cells: usize,
    pub order: &'static str,
    pub stats: CompileStats,
    pub tier: &'static str,
}

#[derive(Serialize)]
pub struct CircuitCost {
    pub path: String,
    pub layers: Vec<LayerCost>,
}

pub fn circuit_cost(path: &str, c: &LoadedCircuit) -> CircuitCost {
    let mut layers = Vec::new();
    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
        for &(slots, fixed) in &CONFIG_GRID {
            // Arena order across the grid, PLUS a Pressure run at the
            // unbounded config — the order-validation comparison (the old
            // "zero ordering win" was measured on a different DAG, so we
            // re-measure on ProgramView).
            let mut runs = vec![OrderKind::Arena];
            if slots == 4096 {
                runs.push(OrderKind::Pressure);
            }
            for order in runs {
                let cl = compile_layer(
                    layer,
                    g,
                    CompileParams { slot_budget_cells: slots, fixed_reg_cells: fixed, order },
                );
                layers.push(LayerCost {
                    layer: li,
                    slot_cells: slots,
                    fixed_cells: fixed,
                    order: match order {
                        OrderKind::Arena => "arena",
                        OrderKind::Pressure => "pressure",
                    },
                    tier: residency_tier(cl.stats.bytes),
                    stats: cl.stats,
                });
            }
        }
    }
    CircuitCost { path: path.to_string(), layers }
}

pub fn to_markdown(costs: &[CircuitCost]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "# gkr_eval_isa static cost report — FORWARD SUBSET of stage 2\n").unwrap();
    writeln!(s, "(round-class variants land with the 1b backward plan; do not read these numbers as covering backward programs)\n").unwrap();
    writeln!(s, "| circuit | layer | slots | fixed | order | instrs | lanes | bytes | tier | Sum/Prod/Dot | src/slot/fix/const reads | gate-ins | max live | evict | remat | fix hits |").unwrap();
    writeln!(s, "|--|--:|--:|--:|--|--:|--:|--:|--|--|--|--:|--:|--:|--:|--:|").unwrap();
    for c in costs {
        let name = c.path.rsplit('/').next().unwrap_or(&c.path);
        for l in &c.layers {
            let h = &l.stats.operand_kind_hist;
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {}/{}/{} | {}/{}/{}/{} | {} | {} | {} | {} | {} |",
                name, l.layer, l.slot_cells, l.fixed_cells, l.order,
                l.stats.instrs, l.stats.lanes, l.stats.bytes, l.tier,
                l.stats.op_hist[0], l.stats.op_hist[1], l.stats.op_hist[2],
                h[0], h[1], h[2], h[3],
                l.stats.gate_in_roots,
                l.stats.max_live_cells, l.stats.spill_evictions,
                l.stats.remat_instrs, l.stats.fixed_reg_hits,
            )
            .unwrap();
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::residency_tier;

    #[test]
    fn tiers() {
        assert_eq!(residency_tier(10_000), "const-coexist");
        assert_eq!(residency_tier(40_000), "const-alone");
        assert_eq!(residency_tier(70_000), "global");
    }
}
