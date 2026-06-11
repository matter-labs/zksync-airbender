//! Stage-2 static cost report, FORWARD SUBSET: layer-0 compile stats swept
//! over realistic GPU budgets (smem slot cells × fixed registers, both bf
//! cells per thread). Layers >=1 compile to zero instructions (their arenas
//! hold only Place/GateOutput; gate arithmetic is fixed-shape native code),
//! so they are guarded, not swept. The per-round-class dimension the spec
//! requires for full stage 2 lands with the 1b backward plan.

use crate::compiler::{CompileParams, CompileStats, OrderKind, compile_layer};
use cs::gkr_compiler::codegen_ir::CodegenLayer;
use gkr_design_space::graph::AnalysisGraph;
use gkr_design_space::import::LoadedCircuit;
use serde::Serialize;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// Unbounded reference budget (also `CompileParams::default()`).
pub const UNBOUNDED: usize = 4096;
/// Slot budgets swept (bf cells per thread). 8 cells = 32 B/thread = 8 KB
/// per 256-thread block; 64 cells = 64 KB/block (the occupancy ceiling).
pub const SLOT_GRID: [usize; 9] = [8, 16, 24, 32, 40, 48, 56, 64, UNBOUNDED];
/// Fixed-register budgets swept (bf cells, decode-selected).
pub const FIXED_GRID: [usize; 4] = [0, 8, 16, 24];

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
    /// None when the budget is infeasible (compile panicked; reason kept).
    pub stats: Option<CompileStats>,
    pub tier: Option<&'static str>,
    pub infeasible_reason: Option<String>,
}

#[derive(Serialize)]
pub struct CircuitCost {
    pub path: String,
    pub layers: Vec<LayerCost>,
}

fn try_compile(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    li: usize,
    slots: usize,
    fixed: usize,
) -> LayerCost {
    let params =
        CompileParams { slot_budget_cells: slots, fixed_reg_cells: fixed, order: OrderKind::Arena };
    match catch_unwind(AssertUnwindSafe(|| compile_layer(layer, g, params))) {
        Ok(cl) => LayerCost {
            layer: li,
            slot_cells: slots,
            fixed_cells: fixed,
            order: "arena",
            tier: Some(residency_tier(cl.stats.bytes)),
            stats: Some(cl.stats),
            infeasible_reason: None,
        },
        Err(e) => {
            let reason = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "unknown panic".to_string());
            LayerCost {
                layer: li,
                slot_cells: slots,
                fixed_cells: fixed,
                order: "arena",
                tier: None,
                stats: None,
                infeasible_reason: Some(reason),
            }
        }
    }
}

pub fn circuit_cost(path: &str, c: &LoadedCircuit) -> CircuitCost {
    let mut layers = Vec::new();
    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
        if li > 0 {
            // Guard, not sweep: report a layer >=1 only if it unexpectedly
            // owns program instructions.
            let cl = compile_layer(layer, g, CompileParams::default());
            if cl.stats.instrs != 0 {
                layers.push(LayerCost {
                    layer: li,
                    slot_cells: UNBOUNDED,
                    fixed_cells: 0,
                    order: "arena",
                    tier: Some(residency_tier(cl.stats.bytes)),
                    stats: Some(cl.stats),
                    infeasible_reason: None,
                });
            }
            continue;
        }
        for &fixed in &FIXED_GRID {
            for &slots in &SLOT_GRID {
                layers.push(try_compile(layer, g, li, slots, fixed));
            }
        }
    }
    CircuitCost { path: path.to_string(), layers }
}

pub fn to_markdown(costs: &[CircuitCost]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "# gkr_eval_isa static cost report — layer-0 budget sweep (forward subset)\n")
        .unwrap();
    writeln!(s, "Grid: slot budget {{8..64 step 8, ∞}} × fixed regs {{0,8,16,24}}, bf cells/thread.")
        .unwrap();
    writeln!(
        s,
        "Cell: instr inflation vs the (∞, 0 fixed) baseline, then evictions e / remat instrs r / fixed-reg hits h. ✗ = infeasible budget."
    )
    .unwrap();
    writeln!(
        s,
        "Layers ≥1 compile to zero instructions everywhere and are omitted; any violation is listed per circuit.\n"
    )
    .unwrap();
    for c in costs {
        let name = c.path.rsplit('/').next().unwrap_or(&c.path);
        let l0: Vec<&LayerCost> = c.layers.iter().filter(|l| l.layer == 0).collect();
        let find = |slots: usize, fixed: usize| {
            l0.iter().find(|l| l.slot_cells == slots && l.fixed_cells == fixed)
        };
        let base = find(UNBOUNDED, 0)
            .and_then(|l| l.stats.as_ref())
            .expect("unbounded baseline must compile");
        writeln!(s, "## {name}\n").unwrap();
        writeln!(
            s,
            "baseline (∞, 0 fixed): {} instrs, {} B ({}), max_live {} cells\n",
            base.instrs,
            base.bytes,
            residency_tier(base.bytes),
            base.max_live_cells,
        )
        .unwrap();
        write!(s, "| slots \\ fixed |").unwrap();
        for f in FIXED_GRID {
            write!(s, " {f} |").unwrap();
        }
        writeln!(s).unwrap();
        write!(s, "|--:|").unwrap();
        for _ in FIXED_GRID {
            write!(s, "--|").unwrap();
        }
        writeln!(s).unwrap();
        for &slots in &SLOT_GRID {
            if slots == UNBOUNDED {
                write!(s, "| ∞ |").unwrap();
            } else {
                write!(s, "| {slots} |").unwrap();
            }
            for &fixed in &FIXED_GRID {
                match find(slots, fixed).and_then(|l| l.stats.as_ref()) {
                    Some(st) if base.instrs > 0 => {
                        let infl = (st.instrs as f64 - base.instrs as f64) * 100.0
                            / base.instrs as f64;
                        write!(
                            s,
                            " {infl:+.1}% ({}e/{}r/{}h) |",
                            st.spill_evictions, st.remat_instrs, st.fixed_reg_hits
                        )
                        .unwrap();
                    }
                    // Zero-instruction layer 0 (everything native): absolutes.
                    Some(st) => write!(s, " {} instrs |", st.instrs).unwrap(),
                    None => write!(s, " ✗ |").unwrap(),
                }
            }
            writeln!(s).unwrap();
        }
        writeln!(s).unwrap();
        for l in c.layers.iter().filter(|l| l.layer > 0) {
            writeln!(
                s,
                "**WARNING**: layer {} owns {} instrs (expected 0)",
                l.layer,
                l.stats.as_ref().map_or(0, |st| st.instrs),
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
