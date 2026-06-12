//! Stage-2 static cost report, FORWARD SUBSET, on the UNIFIED budget model:
//! registers + smem are one cell budget; the swept decision is the split
//! between pinned cache (hub inputs AND intermediates) and working set.
//! Which cell addresses physically land in smem vs decode-selected registers
//! is a later backend choice driven by the per-address access counts this
//! report carries (hot -> indexable smem, cold -> selector-tree registers).
//! Layers >=1 own at most a few dozen instructions (upper-layer gate-input
//! cones; zero for most circuits) and are reported, not swept. The
//! per-round-class dimension for full stage 2 lands with the 1b backward plan.

use crate::compiler::{CompileParams, CompileStats, OrderKind, compile_layer};
use cs::gkr_compiler::codegen_ir::CodegenLayer;
use gkr_design_space::graph::AnalysisGraph;
use gkr_design_space::import::LoadedCircuit;
use serde::Serialize;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// Unbounded reference budget (also `CompileParams::default()`).
pub const UNBOUNDED: usize = 4096;
/// Total cell budgets swept (bf cells per thread). 8 cells = 32 B/thread =
/// 8 KB per 256-thread block if all-smem; the register file extends that.
pub const SLOT_GRID: [usize; 9] = [8, 16, 24, 32, 40, 48, 56, 64, UNBOUNDED];

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

/// One point of the pin-vs-working-set sweep at a FIXED total cell budget.
/// Pinning absorbs hub re-reads (global -> guaranteed residency) but shrinks
/// the working set, raising remat — which itself re-reads cone leaves from
/// sources. `src_reads` therefore captures both sides of the trade in one
/// number (preloads included); `instrs` is the compute side.
#[derive(Serialize)]
pub struct PinTradePoint {
    pub budget_cells: usize,
    pub pin_request: usize,
    /// Cells the prefix actually uses (< request once hub candidates run out).
    pub pinned_cells: usize,
    /// Dynamic leaf residency (multi-use leaves load/evict like
    /// intermediates) instead of the static pinned prefix.
    pub leaf_cache: bool,
    pub feasible: bool,
    pub src_reads: usize,
    pub instrs: usize,
    pub bytes: usize,
    pub spill_evictions: usize,
    pub remat_instrs: usize,
    pub leaf_loads: usize,
    pub pinned_hits: usize,
    /// Total cell accesses and the share captured by the top {8,16,24,32}
    /// hottest addresses — the data for the smem-vs-register split.
    pub cell_accesses_total: usize,
    pub cell_accesses_top: [usize; 4],
}

#[derive(Serialize)]
pub struct UpperLayer {
    pub layer: usize,
    pub stats: CompileStats,
}

#[derive(Serialize)]
pub struct CircuitCost {
    pub path: String,
    /// Layer 0 at (∞, no pin).
    pub baseline: CompileStats,
    /// Layers >=1 that own instructions, at (∞, no pin).
    pub upper_layers: Vec<UpperLayer>,
    pub trade: Vec<PinTradePoint>,
}

fn trade_point(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    budget: usize,
    pin: usize,
    leaf_cache: bool,
) -> PinTradePoint {
    let params = CompileParams {
        budget_cells: budget,
        pinned_cells: pin,
        leaf_cache,
        order: OrderKind::Arena,
    };
    match catch_unwind(AssertUnwindSafe(|| compile_layer(layer, g, params))) {
        Ok(cl) => PinTradePoint {
            budget_cells: budget,
            pin_request: pin,
            pinned_cells: cl.stats.pinned_cells,
            leaf_cache,
            feasible: true,
            src_reads: cl.stats.operand_kind_hist[0],
            instrs: cl.stats.instrs,
            bytes: cl.stats.bytes,
            spill_evictions: cl.stats.spill_evictions,
            remat_instrs: cl.stats.remat_instrs,
            leaf_loads: cl.stats.leaf_loads,
            pinned_hits: cl.stats.pinned_hits,
            cell_accesses_total: cl.stats.cell_accesses_total,
            cell_accesses_top: cl.stats.cell_accesses_top,
        },
        Err(_) => PinTradePoint {
            budget_cells: budget,
            pin_request: pin,
            pinned_cells: pin,
            leaf_cache,
            feasible: false,
            src_reads: 0,
            instrs: 0,
            bytes: 0,
            spill_evictions: 0,
            remat_instrs: 0,
            leaf_loads: 0,
            pinned_hits: 0,
            cell_accesses_total: 0,
            cell_accesses_top: [0; 4],
        },
    }
}

pub fn circuit_cost(path: &str, c: &LoadedCircuit) -> CircuitCost {
    let layer0 = &c.circuit.layers[0];
    let g0 = &c.graphs[0];
    let baseline = compile_layer(layer0, g0, CompileParams::default()).stats;

    let mut upper_layers = Vec::new();
    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate().skip(1) {
        let cl = compile_layer(layer, g, CompileParams::default());
        if cl.stats.instrs != 0 {
            upper_layers.push(UpperLayer { layer: li, stats: cl.stats });
        }
    }

    let mut trade = Vec::new();
    for &budget in &SLOT_GRID {
        if budget == UNBOUNDED {
            // No pin (== baseline), saturated pin (max-absorbable bound), and
            // dynamic leaf residency (should match saturation's src reads:
            // every multi-use leaf loaded exactly once, never evicted).
            trade.push(trade_point(layer0, g0, budget, 0, false));
            trade.push(trade_point(layer0, g0, budget, UNBOUNDED, false));
            trade.push(trade_point(layer0, g0, budget, 0, true));
        } else {
            let mut pin = 0usize;
            while budget - pin >= 4 {
                trade.push(trade_point(layer0, g0, budget, pin, false));
                pin += 4;
            }
            // Dynamic leaf residency: same budget, no static split at all.
            trade.push(trade_point(layer0, g0, budget, 0, true));
        }
    }
    CircuitCost { path: path.to_string(), baseline, upper_layers, trade }
}

pub fn to_markdown(costs: &[CircuitCost]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "# gkr_eval_isa static cost report — unified-budget pin trade (forward subset)\n")
        .unwrap();
    writeln!(s, "Model: registers + smem are ONE cell budget; swept decision = pinned cache vs working set split (step 4). The smem-vs-register placement of each address is decided later from access counts.").unwrap();
    writeln!(s, "Trade lines: `pin→src reads/instrs`, `*` = min src reads (assumes reads are the binding cost — DRAM-bound). ✗ = infeasible split. `dyn` = dynamic leaf residency (no static pin; multi-use leaves load/evict like intermediates).").unwrap();
    writeln!(s, "Access lines: share of all cell accesses captured by the top 8/16/24/32 hottest addresses, at the starred split.\n").unwrap();
    for c in costs {
        let name = c.path.rsplit('/').next().unwrap_or(&c.path);
        writeln!(s, "## {name}\n").unwrap();
        let b = &c.baseline;
        writeln!(
            s,
            "baseline (∞, no pin): {} instrs, {} B ({}), max_live {} cells, src reads {}\n",
            b.instrs,
            b.bytes,
            residency_tier(b.bytes),
            b.max_live_cells,
            b.operand_kind_hist[0],
        )
        .unwrap();
        for u in &c.upper_layers {
            writeln!(
                s,
                "layer {}: {} instrs (Sum/Prod/Dot {}/{}/{}), max_live {} cells at ∞ — upper-layer gate-input cones",
                u.layer,
                u.stats.instrs,
                u.stats.op_hist[0],
                u.stats.op_hist[1],
                u.stats.op_hist[2],
                u.stats.max_live_cells,
            )
            .unwrap();
        }
        if b.instrs == 0 {
            writeln!(s, "(zero-instruction layer 0 — no trade to sweep)\n").unwrap();
            continue;
        }
        writeln!(s).unwrap();
        for &budget in &SLOT_GRID {
            let pts: Vec<&PinTradePoint> =
                c.trade.iter().filter(|p| p.budget_cells == budget).collect();
            let best_idx = pts
                .iter()
                .enumerate()
                .filter(|(_, p)| p.feasible)
                .min_by_key(|(_, p)| (p.src_reads, p.instrs))
                .map(|(i, _)| i);
            if budget == UNBOUNDED {
                write!(s, "- S=∞: ").unwrap();
            } else {
                write!(s, "- S={budget}: ").unwrap();
            }
            for (i, p) in pts.iter().enumerate() {
                if i > 0 {
                    write!(s, " | ").unwrap();
                }
                let label = if p.leaf_cache {
                    "dyn".to_string()
                } else if p.pin_request == UNBOUNDED {
                    "sat".to_string()
                } else {
                    p.pin_request.to_string()
                };
                if !p.feasible {
                    write!(s, "{label}→✗").unwrap();
                } else {
                    let star = if best_idx == Some(i) { "*" } else { "" };
                    write!(s, "{star}{label}→{}/{}", p.src_reads, p.instrs).unwrap();
                }
            }
            // Access concentration at the starred split.
            if let Some(bp) = pts
                .iter()
                .filter(|p| p.feasible)
                .min_by_key(|p| (p.src_reads, p.instrs))
            {
                if bp.cell_accesses_total > 0 {
                    let pct = |k: usize| 100 * bp.cell_accesses_top[k] / bp.cell_accesses_total;
                    write!(
                        s,
                        "  — top8/16/24/32 cells: {}/{}/{}/{}% of accesses",
                        pct(0),
                        pct(1),
                        pct(2),
                        pct(3)
                    )
                    .unwrap();
                }
            }
            writeln!(s).unwrap();
        }
        writeln!(s).unwrap();
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
