//! Stage-2 static cost report for the ISA-v2 forward compiler (`compiler_v2`).
//! Mirrors the v1 `report` module's role — the artifact RR reviews at the
//! Phase-4 gate — but over the v2 fused single-pass program. The headline
//! numbers are PROGRAM SIZE (lanes/bytes), the op histogram
//! (arith/macros/gathers/materializes), and the joint matrix-table size. A
//! SLOT_GRID-style budget sweep of `max_live_cells` reuses the v1 grid +
//! `residency_tier` so the two reports read side-by-side. (Task 4.2 adds the R2
//! fused-vs-per-strand register-pressure proxy + the `isac --v2` arm.)

use crate::compiler_v2::{FwdParams2, compile_forward_v2};
use crate::report::{SLOT_GRID, UNBOUNDED, residency_tier};
use gkr_design_space::import::LoadedCircuit;
use serde::Serialize;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// One SLOT_GRID point: the bounded base-arith working set (`max_live_cells`)
/// the v2 emitter holds at a fixed total cell budget. Mirrors v1's `FwdPoint`
/// max_live measurement but on the fused v2 program. `feasible` is `false` if
/// compilation panicked at that budget (caught, like v1).
#[derive(Serialize)]
pub struct SweepPoint2 {
    pub budget_cells: usize,
    pub feasible: bool,
    pub max_live_cells: usize,
}

/// Per-layer v2 cost. `bytes == lanes * 2` (16-bit lanes). The op histogram
/// (`arith`/`macros`/`gathers`/`materializes`), `n_matrix_slots`, and
/// `max_live_cells` come straight from `CompileStats2`.
#[derive(Serialize)]
pub struct LayerCost2 {
    pub layer: usize,
    pub instrs: usize,
    pub lanes: usize,
    pub bytes: usize,
    pub arith: usize,
    pub macros: usize,
    pub gathers: usize,
    pub materializes: usize,
    pub n_matrix_slots: usize,
    /// `CompileStats2::max_live_cells` at the default budget (the fused
    /// simultaneously-live slot-cell high water).
    pub max_live_cells: usize,
}

/// One circuit's v2 static cost: per-layer rows + totals + the L0 budget sweep.
#[derive(Serialize)]
pub struct ReportV2 {
    pub name: String,
    pub layers: Vec<LayerCost2>,
    // Corpus/total rollups across all layers.
    pub program_instrs: usize,
    pub program_lanes: usize,
    pub program_bytes: usize,
    pub arith: usize,
    pub macros: usize,
    pub gathers: usize,
    pub materializes: usize,
    /// Joint matrix-table size = max distinct backings over the layers (each
    /// layer's table is independent; the cap is per-layer, <= 16).
    pub n_matrix_slots: usize,
    /// L0 budget sweep of the bounded working set (the residency story).
    pub sweep: Vec<SweepPoint2>,
}

/// Compile every (layer, graph) at `FwdParams2::default()`, aggregate the v2
/// static cost. The loaded-circuit type matches v1 `report::circuit_cost`, so
/// `isac` can call both arms over the same loaded fixtures.
pub fn circuit_cost_v2(name: &str, c: &LoadedCircuit) -> ReportV2 {
    let mut layers = Vec::new();
    let mut program_instrs = 0;
    let mut program_lanes = 0;
    let mut program_bytes = 0;
    let mut arith = 0;
    let mut macros = 0;
    let mut gathers = 0;
    let mut materializes = 0;
    let mut n_matrix_slots = 0;

    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
        let cf = compile_forward_v2(layer, g, FwdParams2::default());
        let s = &cf.stats;
        program_instrs += s.instrs;
        program_lanes += s.lanes;
        program_bytes += s.bytes;
        arith += s.arith;
        macros += s.macros;
        gathers += s.gathers;
        materializes += s.materializes;
        n_matrix_slots = n_matrix_slots.max(s.n_matrix_slots);
        layers.push(LayerCost2 {
            layer: li,
            instrs: s.instrs,
            lanes: s.lanes,
            bytes: s.bytes,
            arith: s.arith,
            macros: s.macros,
            gathers: s.gathers,
            materializes: s.materializes,
            n_matrix_slots: s.n_matrix_slots,
            max_live_cells: s.max_live_cells,
        });
    }

    // L0 budget sweep: the bounded working set as the cell budget varies.
    let sweep = if let (Some(layer0), Some(g0)) = (c.circuit.layers.first(), c.graphs.first()) {
        SLOT_GRID
            .iter()
            .map(|&budget| {
                let params = FwdParams2 { budget_cells: budget, ..FwdParams2::default() };
                match catch_unwind(AssertUnwindSafe(|| compile_forward_v2(layer0, g0, params))) {
                    Ok(cf) => SweepPoint2 {
                        budget_cells: budget,
                        feasible: true,
                        max_live_cells: cf.stats.max_live_cells,
                    },
                    Err(_) => {
                        SweepPoint2 { budget_cells: budget, feasible: false, max_live_cells: 0 }
                    }
                }
            })
            .collect()
    } else {
        Vec::new()
    };

    ReportV2 {
        name: name.to_string(),
        layers,
        program_instrs,
        program_lanes,
        program_bytes,
        arith,
        macros,
        gathers,
        materializes,
        n_matrix_slots,
        sweep,
    }
}

/// Readable markdown: per-circuit per-layer table rows + a corpus summary, with
/// the op histogram, matrix-table size, and the L0 budget sweep.
pub fn to_markdown(reports: &[ReportV2]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "# gkr_eval_isa ISA-v2 static cost report (forward, fused single-pass)\n").unwrap();
    writeln!(
        s,
        "Model: one fused v2 `Program2` per layer over all 3 strands. Sizes are \
         16-bit lanes (bytes = lanes*2). Op histogram: arith / macros / gathers \
         (inline `Indirect` operands) / materializes (`Dst::Materialize`). Matrix \
         table = distinct committed backings (<= 16/layer). `live` = fused max \
         simultaneously-live slot cells (the bounded base-arith working set)."
    )
    .unwrap();
    writeln!(
        s,
        "Sweep: bounded base-arith working set (`max_live_cells`) at total cell \
         budget S; `✗` = infeasible split.\n"
    )
    .unwrap();

    // Corpus summary table.
    writeln!(s, "## corpus summary\n").unwrap();
    writeln!(
        s,
        "| circuit | layers | instrs | lanes | bytes (tier) | arith | macros | gathers | mtrlz | matrix | live |"
    )
    .unwrap();
    writeln!(s, "|---|---|---|---|---|---|---|---|---|---|---|").unwrap();
    for r in reports {
        let live = r.layers.iter().map(|l| l.max_live_cells).max().unwrap_or(0);
        writeln!(
            s,
            "| {} | {} | {} | {} | {} ({}) | {} | {} | {} | {} | {} | {} |",
            r.name,
            r.layers.len(),
            r.program_instrs,
            r.program_lanes,
            r.program_bytes,
            residency_tier(r.program_bytes),
            r.arith,
            r.macros,
            r.gathers,
            r.materializes,
            r.n_matrix_slots,
            live,
        )
        .unwrap();
    }
    writeln!(s).unwrap();

    // Per-circuit detail.
    for r in reports {
        writeln!(s, "## {}\n", r.name).unwrap();
        writeln!(
            s,
            "| layer | instrs | lanes | bytes | arith | macros | gathers | mtrlz | matrix | live |"
        )
        .unwrap();
        writeln!(s, "|---|---|---|---|---|---|---|---|---|---|").unwrap();
        for l in &r.layers {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                l.layer,
                l.instrs,
                l.lanes,
                l.bytes,
                l.arith,
                l.macros,
                l.gathers,
                l.materializes,
                l.n_matrix_slots,
                l.max_live_cells,
            )
            .unwrap();
        }
        // L0 budget sweep line.
        write!(s, "\n- L0 sweep (max_live @ S): ").unwrap();
        for (i, p) in r.sweep.iter().enumerate() {
            if i > 0 {
                write!(s, " | ").unwrap();
            }
            let label = if p.budget_cells == UNBOUNDED {
                "S=∞".to_string()
            } else {
                format!("S={}", p.budget_cells)
            };
            if p.feasible {
                write!(s, "{label}→{}", p.max_live_cells).unwrap();
            } else {
                write!(s, "{label}→✗").unwrap();
            }
        }
        writeln!(s, "\n").unwrap();
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::fixture_path;
    use gkr_design_space::import::load_circuit;

    #[test]
    fn add_sub_report_shrinks_vs_v1() {
        let path = fixture_path("add_sub_lui_auipc_mop_codegen_ir_gkr.json");
        let c = load_circuit(&path).unwrap_or_else(|e| panic!("load add_sub: {e:?}"));
        let r = circuit_cost_v2("add_sub", &c);

        // Two sound invariants RR reads at the gate.
        assert!(r.program_bytes > 0, "add_sub: v2 program must have bytes");
        assert!(
            r.n_matrix_slots <= 16,
            "add_sub: matrix table {} slots exceeds the 16-backing cap",
            r.n_matrix_slots
        );

        // Headline shrink: compare the v2 forward-program byte total against the
        // v1 forward-program byte total (lane bytes + opaque payload bytes) for
        // the SAME L0. The v1 fwd report is L0-only, so we compare against the
        // v2 L0 layer entry to keep it apples-to-apples.
        let v1 = crate::report::circuit_cost(path.to_str().unwrap(), &c);
        let v1_fwd_bytes = v1.fwd.bytes_unbounded + v1.fwd.payload_bytes;
        let v2_l0 = r.layers.first().expect("at least L0");
        assert!(
            v2_l0.bytes < v1_fwd_bytes,
            "add_sub L0: v2 fwd bytes {} not smaller than v1 fwd bytes {} \
             (lanes {} + payload {})",
            v2_l0.bytes,
            v1_fwd_bytes,
            v1.fwd.bytes_unbounded,
            v1.fwd.payload_bytes
        );
    }
}
