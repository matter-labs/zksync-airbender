//! Stage-3 verdict A/B report writer (spec §6.2(A)). Mirrors
//! `gkr_eval_isa/src/report.rs`: `#[derive(Serialize)]` row structs serialized
//! to pretty JSON, plus a hand-rolled `writeln!`-into-`String` markdown table.
//! Output goes to `.agents/audits/2026-06-12-gkr-eval-isa-stage3-bench.{md,json}`
//! (GITIGNORED — written, never committed).

use serde::Serialize;
use std::fmt::Write as _;

/// Device attributes queried once, recorded in the report header (spec §6.2).
#[derive(Serialize, Clone)]
pub(super) struct DeviceAttrs {
    pub max_shared_memory_per_multiprocessor: i32,
    pub max_shared_memory_per_block_optin: i32,
    pub sm_count: usize,
}

/// One timed side (flat or interpreter): median + min wall-clock over N
/// iterations, plus the launch count for the multi-launch-asymmetry column
/// (spec §9). Flat = a SUM of launches; interpreter = 1.
#[derive(Serialize, Clone)]
pub(super) struct SideTiming {
    pub median_ms: f32,
    pub min_ms: f32,
    pub launches: usize,
    pub iters: usize,
}

/// One row of the §6.2(A) verdict table: a (circuit, layer, best-feasible
/// budget, residency, launch config, filter shape) point with both timed sides
/// and the per-point context the spec mandates.
#[derive(Serialize, Clone)]
pub(super) struct AbRow {
    pub circuit: String,
    pub layer: usize,
    /// Best-feasible budget chosen by the pre-scan (min interpreter median).
    pub budget: usize,
    /// Residency of the timed interpreter side ("LDG" / "LDC").
    pub residency: String,
    /// Launch config: threads-per-block of the timed interpreter side.
    pub interp_threads: u32,
    /// `true` when this is the equal-work (MaxQuadratic-filtered) row.
    pub equal_work: bool,
    /// Set on circuits with zero fwd-eligible MaxQuadratic gates: the equal-work
    /// and production-shape rows coincide (timed once, not duplicated; spec §9).
    pub rows_coincide: bool,
    /// Element count both sides were timed at (capped per controller ruling;
    /// see `capped`). Always recorded.
    pub timed_count: usize,
    /// The circuit's native trace length (the full buffer size).
    pub trace_len: usize,
    /// `true` when `timed_count < trace_len` (the cap was applied).
    pub capped: bool,
    pub flat: SideTiming,
    pub interp: SideTiming,
    /// Interpreter ratio (interp median / flat median).
    pub interp_over_flat: f32,
    /// Dynamic smem the timed interpreter launch requested (padded sizing).
    pub interp_smem_bytes: usize,
    /// Static blocks-per-SM the timed config achieves (occupancy API).
    pub interp_blocks_per_sm: i32,
    /// Whether the timed config opted into the >48 KB dynamic-smem cap.
    pub interp_large_smem_optin: bool,
    /// Program (lanes*2 + consts*4) + payload-table bytes.
    pub program_bytes: usize,
    pub payload_bytes: usize,
    pub n_instr: u32,
    // Compiler per-point stats (recomputed for the EXACT timed program — i.e.
    // filtered-program stats on equal-work rows, never the unfiltered numbers).
    pub instrs: usize,
    pub src_reads: usize,
    pub cell_reads: usize,
    pub cache_refires: usize,
    pub max_live_cells: usize,
}

/// The full §6.2(A) report: queried device attrs, the per-point rows, and any
/// skip/infeasible markers (spec §6.2 output requirement).
#[derive(Serialize)]
pub(super) struct AbReport {
    pub device: DeviceAttrs,
    pub iters_full: usize,
    pub iters_prescan: usize,
    pub rows: Vec<AbRow>,
    /// Free-form skip/infeasible markers ("circuit L# budget: reason").
    pub skips: Vec<String>,
}

impl AbReport {
    /// Pretty JSON, mirroring `report.rs`'s `to_string_pretty` path.
    pub(super) fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("serialize AbReport")
    }

    /// Hand-rolled markdown: a header block of the queried device attrs, then the
    /// §6.2(A) table, then the skip/infeasible markers.
    pub(super) fn to_markdown(&self) -> String {
        let mut s = String::new();
        writeln!(s, "# GKR eval-ISA stage-3 verdict A/B (spec §6.2(A))\n").unwrap();
        writeln!(
            s,
            "Flat launch-sum vs single interpreter launch, per circuit × layer at \
             the best-feasible budget (min interpreter median from an N={} pre-scan), \
             timed N={} each side with CUDA events (median + min). Both sides timed \
             at the SAME element count; `capped`/`timed_count` record the controller \
             ruling. Launch-config fairness (spec §9): the interpreter's best config \
             is reported alongside the matched 128/4 when 256 threads wins the \
             pre-scan.\n",
            self.iters_prescan, self.iters_full,
        )
        .unwrap();
        writeln!(s, "## Device\n").unwrap();
        writeln!(
            s,
            "- MaxSharedMemoryPerMultiprocessor: {} bytes",
            self.device.max_shared_memory_per_multiprocessor
        )
        .unwrap();
        writeln!(
            s,
            "- MaxSharedMemoryPerBlockOptin: {} bytes",
            self.device.max_shared_memory_per_block_optin
        )
        .unwrap();
        writeln!(s, "- SM count: {}\n", self.device.sm_count).unwrap();

        writeln!(s, "## A. Verdict A/B\n").unwrap();
        writeln!(
            s,
            "| circuit | L | budget | resid | thr | shape | coincide | count (cap) | trace_len | \
             flat med/min ms (×launch) | interp med/min ms | interp/flat | smem B | blk/SM | \
             optin | prog B | payload B | n_instr | instr | src_rd | cell_rd | refires | live |"
        )
        .unwrap();
        writeln!(
            s,
            "|---|--:|--:|---|--:|---|---|--:|--:|---|---|--:|--:|--:|---|--:|--:|--:|--:|--:|--:|--:|--:|"
        )
        .unwrap();
        for r in &self.rows {
            let shape = if r.equal_work {
                "equal-work"
            } else {
                "production"
            };
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {}{} | {} | {:.4}/{:.4} (×{}) | {:.4}/{:.4} | {:.2}× | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                r.circuit,
                r.layer,
                r.budget,
                r.residency,
                r.interp_threads,
                shape,
                if r.rows_coincide { "yes" } else { "no" },
                r.timed_count,
                if r.capped { " (cap)" } else { "" },
                r.trace_len,
                r.flat.median_ms,
                r.flat.min_ms,
                r.flat.launches,
                r.interp.median_ms,
                r.interp.min_ms,
                r.interp_over_flat,
                r.interp_smem_bytes,
                r.interp_blocks_per_sm,
                if r.interp_large_smem_optin { "yes" } else { "no" },
                r.program_bytes,
                r.payload_bytes,
                r.n_instr,
                r.instrs,
                r.src_reads,
                r.cell_reads,
                r.cache_refires,
                r.max_live_cells,
            )
            .unwrap();
        }
        writeln!(s).unwrap();

        if !self.skips.is_empty() {
            writeln!(s, "## Skips / infeasible markers\n").unwrap();
            for sk in &self.skips {
                writeln!(s, "- {sk}").unwrap();
            }
            writeln!(s).unwrap();
        }
        s
    }
}

/// Write the report `.md` + `.json` to `.agents/audits/` (relative to the crate
/// manifest's repo root). Returns the two paths written. GITIGNORED location.
pub(super) fn write_report(report: &AbReport) -> (std::path::PathBuf, std::path::PathBuf) {
    // CARGO_MANIFEST_DIR = gpu/circuit_prover; the repo root is two up.
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonicalize repo root");
    let audits = root.join(".agents/audits");
    std::fs::create_dir_all(&audits).expect("create .agents/audits");
    let base = "2026-06-12-gkr-eval-isa-stage3-bench";
    let md_path = audits.join(format!("{base}.md"));
    let json_path = audits.join(format!("{base}.json"));
    std::fs::write(&md_path, report.to_markdown()).expect("write report .md");
    std::fs::write(&json_path, report.to_json()).expect("write report .json");
    (md_path, json_path)
}
