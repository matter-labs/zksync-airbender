//! Stage-2 static cost report for the ISA-v2 forward compiler (`compiler_v2`).
//! Mirrors the v1 `report` module's role — the artifact RR reviews at the
//! Phase-4 gate — but over the v2 fused single-pass program. The headline
//! numbers are PROGRAM SIZE (lanes/bytes), the op histogram
//! (arith/macros/gathers/materializes), and the joint matrix-table size. A
//! SLOT_GRID-style budget sweep of `max_live_cells` reuses the v1 grid +
//! `residency_tier` so the two reports read side-by-side. (Task 4.2 adds the R2
//! fused-vs-per-strand register-pressure proxy + the `isac --v2` arm.)

use crate::compiler_v2::{FwdParams2, compile_forward_v2};
use crate::isa_v2::{Dst, Instr2, Operand, Program2};
use crate::report::{SLOT_GRID, UNBOUNDED, residency_tier};
use gkr_design_space::import::LoadedCircuit;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
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
    /// R2 register-pressure proxy (Task 4.2): max simultaneously-live cells of
    /// the FUSED 3-strand program (`emit_per_strand: true`). Equals
    /// `max_live_cells` (same compile, different param), kept distinct so the
    /// proxy intent is explicit in the artifact.
    pub fused_live: usize,
    /// R2 proxy: the max live-cell count over the per-strand programs. Fusion
    /// only ADDS live state, so `fused_live >= per_strand_live` always.
    pub per_strand_live: usize,
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

/// Slot cells an instruction READS (`Operand::Slot`, incl. memory-tuple roles
/// + payload). Mirrors the compiler's private `slot_reads`.
fn instr_slot_reads(instr: &Instr2) -> Vec<u8> {
    let mut cells = Vec::new();
    let mut scan = |op: &Operand| {
        if let Operand::Slot { cell, .. } = op {
            cells.push(*cell);
        }
    };
    for op in &instr.operands {
        scan(op);
    }
    if let Some(mt) = &instr.memtup {
        for (_role, op) in &mt.roles {
            scan(op);
        }
        if let Some(op) = &mt.as_payload {
            scan(op);
        }
    }
    cells
}

/// Slot cells an instruction WRITES (`Dst::Slot`). Mirrors the compiler's
/// private `slot_writes`.
fn instr_slot_writes(instr: &Instr2) -> Vec<u8> {
    instr
        .dsts
        .iter()
        .filter_map(|d| match d {
            Dst::Slot { cell, .. } => Some(*cell),
            Dst::Materialize { .. } => None,
        })
        .collect()
}

/// Simultaneously-live slot-cell high-water mark of an arbitrary `Program2`,
/// derived by a last-use liveness walk: a slot cell is live from the
/// instruction that WRITES it (`Dst::Slot`) through its LAST READ
/// (`Operand::Slot`). We compute this rather than reading `Program2.n_slot_cells`
/// because `split_into_strands` copies the FUSED `n_slot_cells` verbatim into
/// every per-strand program (it is not a per-strand figure), so a sound
/// per-strand count has to be re-derived. The walk does not touch the compiler.
/// Macros allocate no slot cells (they read Affine/Indirect, write Materialize),
/// so this only ever counts the base-arith working set — exactly what the fused
/// emitter's `max_live_cells` measures.
pub(crate) fn program_live_cells(p: &Program2) -> usize {
    // Last read position per cell (a cell stays live through its last read).
    let mut last_read: HashMap<u8, usize> = HashMap::new();
    for (i, instr) in p.instrs.iter().enumerate() {
        for c in instr_slot_reads(instr) {
            last_read.insert(c, i);
        }
    }
    // Forward walk: born on write, retired after its last read.
    let mut live: HashSet<u8> = HashSet::new();
    let mut high = 0usize;
    for (i, instr) in p.instrs.iter().enumerate() {
        for c in instr_slot_writes(instr) {
            live.insert(c);
        }
        if live.len() > high {
            high = live.len();
        }
        for c in instr_slot_reads(instr) {
            if last_read.get(&c) == Some(&i) {
                live.remove(&c);
            }
        }
    }
    high
}

/// R2 register-pressure proxy for one (layer, graph): the fused max-live cell
/// count and the max over the per-strand programs. Compiled with
/// `emit_per_strand: true` so `per_strand` is always populated. Fusion only
/// ADDS live state, so the returned pair always satisfies `fused >= strand`.
fn live_state_proxy(
    layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    g: &gkr_design_space::graph::AnalysisGraph,
) -> (usize, usize) {
    let cf = compile_forward_v2(layer, g, FwdParams2 { emit_per_strand: true, ..Default::default() });
    let fused = cf.stats.max_live_cells;
    let per_strand = cf
        .per_strand
        .as_ref()
        .map(|ps| ps.programs.iter().map(|(_, p)| program_live_cells(p)).max().unwrap_or(0))
        .unwrap_or(0);
    (fused, per_strand)
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
        let (fused_live, per_strand_live) = live_state_proxy(layer, g);
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
            fused_live,
            per_strand_live,
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
         table = distinct committed backings (<= 16/layer). R2 register-pressure \
         proxy: `fused live` = max simultaneously-live slot cells of the fused \
         3-strand program; `strand live` = max over the per-strand programs. \
         Fusion only ADDS live state, so fused >= strand."
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
        "| circuit | layers | instrs | lanes | bytes (tier) | arith | macros | gathers | mtrlz | matrix | fused live | strand live |"
    )
    .unwrap();
    writeln!(s, "|---|---|---|---|---|---|---|---|---|---|---|---|").unwrap();
    for r in reports {
        let fused = r.layers.iter().map(|l| l.fused_live).max().unwrap_or(0);
        let strand = r.layers.iter().map(|l| l.per_strand_live).max().unwrap_or(0);
        writeln!(
            s,
            "| {} | {} | {} | {} | {} ({}) | {} | {} | {} | {} | {} | {} | {} |",
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
            fused,
            strand,
        )
        .unwrap();
    }
    writeln!(s).unwrap();

    // Per-circuit detail.
    for r in reports {
        writeln!(s, "## {}\n", r.name).unwrap();
        writeln!(
            s,
            "| layer | instrs | lanes | bytes | arith | macros | gathers | mtrlz | matrix | fused live | strand live |"
        )
        .unwrap();
        writeln!(s, "|---|---|---|---|---|---|---|---|---|---|---|").unwrap();
        for l in &r.layers {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                l.layer,
                l.instrs,
                l.lanes,
                l.bytes,
                l.arith,
                l.macros,
                l.gathers,
                l.materializes,
                l.n_matrix_slots,
                l.fused_live,
                l.per_strand_live,
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

    /// R2 register-pressure proxy: fusion only ADDS live state, so the FUSED
    /// program's max simultaneously-live cells must be >= the max over the
    /// per-strand programs. Resolved on a fixture exercising all 3 strands
    /// (L0 with both a lookup cache AND a MemoryTuple cache), mirroring Task
    /// 2.7's dynamic rich-fixture selection.
    #[test]
    fn fused_live_state_at_least_per_strand() {
        use crate::compiler_v2::compile_forward_v2;
        use crate::test_support::all_fixtures;
        use cs::gkr_compiler::codegen_ir::CacheKind;

        let rich = all_fixtures()
            .into_iter()
            .find(|p| {
                let name = match p.file_name().and_then(|n| n.to_str()) {
                    Some(n) => n,
                    None => return false,
                };
                if name.contains("no_caches") {
                    return false;
                }
                let c = match load_circuit(p) {
                    Ok(c) => c,
                    Err(_) => return false,
                };
                let Some(layer) = c.circuit.layers.first() else { return false };
                let mut has_lookup = false;
                let mut has_memory = false;
                for cache in &layer.caches {
                    match cache.kind {
                        CacheKind::MemoryTuple { .. } => has_memory = true,
                        CacheKind::SingleColumnLookup { .. }
                        | CacheKind::VectorizedLookup { .. }
                        | CacheKind::VectorizedLookupSetup => has_lookup = true,
                    }
                }
                has_lookup && has_memory
            })
            .expect("a fixture whose L0 has BOTH a lookup cache AND a MemoryTuple cache");
        let name = rich.file_name().unwrap().to_str().unwrap().to_string();
        let c = load_circuit(&rich).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
        let layer = &c.circuit.layers[0];
        let g = &c.graphs[0];

        let cf =
            compile_forward_v2(layer, g, FwdParams2 { emit_per_strand: true, ..Default::default() });
        let fused = cf.stats.max_live_cells;
        let per = cf.per_strand.as_ref().expect("emit_per_strand => per_strand Some");
        let per_strand_max =
            per.programs.iter().map(|(_, p)| program_live_cells(p)).max().unwrap_or(0);

        assert!(
            fused >= per_strand_max,
            "{name} L0: fused live {fused} < per-strand max {per_strand_max} \
             (fusion only adds live state)"
        );
    }
}
