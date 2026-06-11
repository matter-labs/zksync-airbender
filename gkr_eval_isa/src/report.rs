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
pub const FIXED_GRID: [usize; 3] = [0, 8, 16];

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
    /// True for the auto-pin variant: spare slot capacity (budget minus the
    /// no-pin run's high water) is given to the pinned hub prefix.
    pub pin_auto: bool,
    pub pinned_cells: usize,
    pub order: &'static str,
    /// None when the budget is infeasible (compile panicked; reason kept).
    pub stats: Option<CompileStats>,
    pub tier: Option<&'static str>,
    pub infeasible_reason: Option<String>,
}

/// One point of the pin-vs-working-set sweep: at a FIXED total slot budget,
/// `pin_request` cells go to the pinned hub prefix and the rest stay working
/// set. Pinning absorbs repeated source reads (global -> guaranteed smem) but
/// shrinks the working set, raising remat — which itself re-reads cone leaves
/// from sources. `src_reads` therefore captures both sides of the trade in
/// one number (preloads included); `instrs` is the compute side.
#[derive(Serialize)]
pub struct PinTradePoint {
    pub slot_cells: usize,
    pub pin_request: usize,
    /// Cells the prefix actually uses (< request once hub candidates run out).
    pub pinned_cells: usize,
    pub feasible: bool,
    pub src_reads: usize,
    pub instrs: usize,
    pub spill_evictions: usize,
    pub remat_instrs: usize,
    pub pinned_hits: usize,
}

/// Total budgets at which the pin-vs-working-set split is swept (layer 0,
/// fixed regs 0, pin stepped by 4 leaving >=4 working cells).
pub const PIN_TRADE_SLOTS: [usize; 5] = [16, 24, 32, 48, 64];

#[derive(Serialize)]
pub struct CircuitCost {
    pub path: String,
    pub layers: Vec<LayerCost>,
    pub pin_trade: Vec<PinTradePoint>,
}

fn try_compile(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    li: usize,
    slots: usize,
    fixed: usize,
    pinned: usize,
    pin_auto: bool,
) -> LayerCost {
    let params = CompileParams {
        slot_budget_cells: slots,
        fixed_reg_cells: fixed,
        pinned_slot_cells: pinned,
        order: OrderKind::Arena,
    };
    match catch_unwind(AssertUnwindSafe(|| compile_layer(layer, g, params))) {
        Ok(cl) => LayerCost {
            layer: li,
            slot_cells: slots,
            fixed_cells: fixed,
            pin_auto,
            pinned_cells: cl.stats.pinned_cells,
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
                pin_auto,
                pinned_cells: pinned,
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
            // Layers >=1 own at most a few dozen instructions (gate-input
            // cones of upper-layer gates; zero for most circuits), so they
            // are reported at the unbounded config only, not swept.
            let cl = compile_layer(layer, g, CompileParams::default());
            if cl.stats.instrs != 0 {
                layers.push(LayerCost {
                    layer: li,
                    slot_cells: UNBOUNDED,
                    fixed_cells: 0,
                    pin_auto: false,
                    pinned_cells: 0,
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
                let base = try_compile(layer, g, li, slots, fixed, 0, false);
                // Auto-pin pass: hand the spare capacity (budget minus the
                // no-pin run's working high water) to the pinned hub prefix.
                let pin = match &base.stats {
                    Some(st) => slots.saturating_sub(st.max_live_cells),
                    None => 0,
                };
                let pin_run = if base.stats.is_some() {
                    try_compile(layer, g, li, slots, fixed, pin, true)
                } else {
                    LayerCost {
                        layer: li,
                        slot_cells: slots,
                        fixed_cells: fixed,
                        pin_auto: true,
                        pinned_cells: 0,
                        order: "arena",
                        tier: None,
                        stats: None,
                        infeasible_reason: Some("base run infeasible".to_string()),
                    }
                };
                layers.push(base);
                layers.push(pin_run);
            }
        }
    }
    let pin_trade = pin_trade_sweep(&c.circuit.layers[0], &c.graphs[0]);
    CircuitCost { path: path.to_string(), layers, pin_trade }
}

fn pin_trade_sweep(layer: &CodegenLayer, g: &AnalysisGraph) -> Vec<PinTradePoint> {
    let mut points = Vec::new();
    for &slots in &PIN_TRADE_SLOTS {
        let mut pin = 0usize;
        while slots - pin >= 4 {
            let params = CompileParams {
                slot_budget_cells: slots,
                fixed_reg_cells: 0,
                pinned_slot_cells: pin,
                order: OrderKind::Arena,
            };
            let p = match catch_unwind(AssertUnwindSafe(|| compile_layer(layer, g, params))) {
                Ok(cl) => PinTradePoint {
                    slot_cells: slots,
                    pin_request: pin,
                    pinned_cells: cl.stats.pinned_cells,
                    feasible: true,
                    src_reads: cl.stats.operand_kind_hist[0],
                    instrs: cl.stats.instrs,
                    spill_evictions: cl.stats.spill_evictions,
                    remat_instrs: cl.stats.remat_instrs,
                    pinned_hits: cl.stats.pinned_hits,
                },
                Err(_) => PinTradePoint {
                    slot_cells: slots,
                    pin_request: pin,
                    pinned_cells: pin,
                    feasible: false,
                    src_reads: 0,
                    instrs: 0,
                    spill_evictions: 0,
                    remat_instrs: 0,
                    pinned_hits: 0,
                },
            };
            points.push(p);
            pin += 4;
        }
    }
    points
}

pub fn to_markdown(costs: &[CircuitCost]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "# gkr_eval_isa static cost report — layer-0 budget sweep (forward subset)\n")
        .unwrap();
    writeln!(s, "Grid: slot budget {{8..64 step 8, ∞}} × fixed regs {{0,8,16}} × pin {{off, auto}}, bf cells/thread.")
        .unwrap();
    writeln!(
        s,
        "Cell: instr inflation vs the (∞, 0 fixed, no pin) baseline, then evictions e / remat instrs r / fixed-reg hits h; pin columns add pinned hits p @ pinned cells. ✗ = infeasible budget."
    )
    .unwrap();
    writeln!(
        s,
        "Auto-pin gives the spare capacity (budget − no-pin high water) to a preloaded, never-evicted hub prefix of the slot file.\n"
    )
    .unwrap();
    writeln!(
        s,
        "Layers ≥1 own zero instructions for most circuits and at most a few dozen (upper-layer gate-input cones) otherwise; nonzero ones are listed per circuit at the ∞ config instead of swept.\n"
    )
    .unwrap();
    for c in costs {
        let name = c.path.rsplit('/').next().unwrap_or(&c.path);
        let l0: Vec<&LayerCost> = c.layers.iter().filter(|l| l.layer == 0).collect();
        let find = |slots: usize, fixed: usize, pin: bool| {
            l0.iter()
                .find(|l| l.slot_cells == slots && l.fixed_cells == fixed && l.pin_auto == pin)
        };
        let base = find(UNBOUNDED, 0, false)
            .and_then(|l| l.stats.as_ref())
            .expect("unbounded baseline must compile");
        writeln!(s, "## {name}\n").unwrap();
        writeln!(
            s,
            "baseline (∞, 0 fixed, no pin): {} instrs, {} B ({}), max_live {} cells\n",
            base.instrs,
            base.bytes,
            residency_tier(base.bytes),
            base.max_live_cells,
        )
        .unwrap();
        write!(s, "| slots \\ fixed |").unwrap();
        for f in FIXED_GRID {
            write!(s, " {f} | {f}+pin |").unwrap();
        }
        writeln!(s).unwrap();
        write!(s, "|--:|").unwrap();
        for _ in FIXED_GRID {
            write!(s, "--|--|").unwrap();
        }
        writeln!(s).unwrap();
        for &slots in &SLOT_GRID {
            if slots == UNBOUNDED {
                write!(s, "| ∞ |").unwrap();
            } else {
                write!(s, "| {slots} |").unwrap();
            }
            for &fixed in &FIXED_GRID {
                for pin in [false, true] {
                    let l = find(slots, fixed, pin);
                    match l.and_then(|l| l.stats.as_ref()) {
                        Some(st) if base.instrs > 0 => {
                            let infl = (st.instrs as f64 - base.instrs as f64) * 100.0
                                / base.instrs as f64;
                            write!(
                                s,
                                " {infl:+.1}% ({}e/{}r/{}h",
                                st.spill_evictions, st.remat_instrs, st.fixed_reg_hits
                            )
                            .unwrap();
                            if pin {
                                write!(s, "/{}p@{}c", st.pinned_hits, st.pinned_cells).unwrap();
                            }
                            write!(s, ") |").unwrap();
                        }
                        // Zero-instruction layer 0 (everything native): absolutes.
                        Some(st) => write!(s, " {} instrs |", st.instrs).unwrap(),
                        None => write!(s, " ✗ |").unwrap(),
                    }
                }
            }
            writeln!(s).unwrap();
        }
        writeln!(s).unwrap();
        for l in c.layers.iter().filter(|l| l.layer > 0) {
            if let Some(st) = &l.stats {
                writeln!(
                    s,
                    "layer {}: {} instrs (Sum/Prod/Dot {}/{}/{}), max_live {} cells at ∞ — upper-layer gate-input cones",
                    l.layer, st.instrs, st.op_hist[0], st.op_hist[1], st.op_hist[2],
                    st.max_live_cells,
                )
                .unwrap();
            }
        }
        if !c.pin_trade.is_empty() {
            writeln!(
                s,
                "\nPin-vs-working-set at fixed TOTAL budget (layer 0, fixed regs 0; `pin→src reads/instrs`, `*` = min src reads):\n"
            )
            .unwrap();
            for &slots in &PIN_TRADE_SLOTS {
                let pts: Vec<&PinTradePoint> =
                    c.pin_trade.iter().filter(|p| p.slot_cells == slots).collect();
                let best = pts
                    .iter()
                    .filter(|p| p.feasible)
                    .min_by_key(|p| (p.src_reads, p.instrs))
                    .map(|p| p.pin_request);
                write!(s, "- S={slots}: ").unwrap();
                for (i, p) in pts.iter().enumerate() {
                    if i > 0 {
                        write!(s, " | ").unwrap();
                    }
                    if !p.feasible {
                        write!(s, "{}→✗", p.pin_request).unwrap();
                    } else {
                        let star = if best == Some(p.pin_request) { "*" } else { "" };
                        write!(s, "{star}{}→{}/{}", p.pin_request, p.src_reads, p.instrs).unwrap();
                    }
                }
                writeln!(s).unwrap();
            }
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
