//! Task 7 fwd-VM A/B report writer. A lean mirror of `bench_interp::report`'s
//! `AbReport` trio (`to_json` / `to_markdown` / `write_report`), tailored to the
//! fwd-VM verdict: one row per (circuit, layer, config) with the replayed-flat
//! baseline vs the interpreter, plus a per-(circuit, layer) verdict (best config)
//! and a skips section. Output goes to
//! `.agents/audits/2026-07-05-fwd-vm-ab-report.{md,json}` (GITIGNORED — written,
//! never committed).

use serde::Serialize;
use std::fmt::Write as _;

/// Device attributes queried once, recorded in the report header.
#[derive(Serialize, Clone)]
pub(crate) struct FwdVmDeviceAttrs {
    pub max_shared_memory_per_multiprocessor: i32,
    pub max_shared_memory_per_block_optin: i32,
    pub sm_count: usize,
}

/// One (circuit, layer, config) A/B row: the replayed-flat baseline (a SUM of
/// launches) vs the single interpreter launch, plus the per-point device context.
#[derive(Serialize, Clone)]
pub(crate) struct FwdVmAbRow {
    pub circuit: String,
    pub layer: usize,
    /// `"<variant>/<residency>"`, e.g. `"static-s16/LDC"`.
    pub config: String,
    pub variant: String,
    pub residency: String,
    pub tpb: u32,
    pub flat_median_ms: f32,
    pub flat_min_ms: f32,
    /// Flat replayable launch count (interpreter is always 1).
    pub flat_launches: usize,
    pub interp_median_ms: f32,
    pub interp_min_ms: f32,
    /// interp median / flat median (< 1 means the interpreter is faster).
    pub interp_over_flat: f32,
    pub encoded_lanes: usize,
    pub n_instr: u32,
    pub budget: u32,
    /// Per-block shared-memory footprint (dynamic for the dynamic variants,
    /// the compile-time `__shared__` size for the static variant).
    pub smem_bytes: usize,
    pub blocks_per_sm: i32,
    pub timed_count: usize,
    pub trace_len: usize,
    pub capped: bool,
    /// `true` when this config is the min-interp-median config for its
    /// (circuit, layer) group.
    pub is_best: bool,
}

/// The per-(circuit, layer) verdict: the best (min interpreter median) config.
#[derive(Serialize, Clone)]
pub(crate) struct FwdVmVerdict {
    pub circuit: String,
    pub layer: usize,
    pub best_config: String,
    pub interp_median_ms: f32,
    pub interp_over_flat: f32,
    pub blocks_per_sm: i32,
    pub smem_bytes: usize,
}

/// The full Task-7 report: queried device attrs, the (circuit, layer, config)
/// A/B rows, the per-(circuit, layer) verdict summary, and skip markers.
#[derive(Serialize)]
pub(crate) struct FwdVmAbReport {
    pub device: FwdVmDeviceAttrs,
    pub iters: usize,
    pub timed_count_cap: usize,
    pub rows: Vec<FwdVmAbRow>,
    pub verdicts: Vec<FwdVmVerdict>,
    /// Free-form skip markers ("circuit L# config: reason").
    pub skips: Vec<String>,
}

impl FwdVmAbReport {
    /// Assemble a report from raw rows + skips: computes `is_best` per
    /// (circuit, layer) group and the verdict summary, then sorts rows.
    pub(crate) fn assemble(
        device: FwdVmDeviceAttrs,
        iters: usize,
        timed_count_cap: usize,
        mut rows: Vec<FwdVmAbRow>,
        skips: Vec<String>,
    ) -> Self {
        // Best (min interpreter median) config per (circuit, layer).
        let mut verdicts: Vec<FwdVmVerdict> = Vec::new();
        let mut groups: Vec<(String, usize)> = rows
            .iter()
            .map(|r| (r.circuit.clone(), r.layer))
            .collect();
        groups.sort();
        groups.dedup();
        for (circuit, layer) in groups {
            let best = rows
                .iter()
                .filter(|r| r.circuit == circuit && r.layer == layer)
                .min_by(|a, b| a.interp_median_ms.total_cmp(&b.interp_median_ms));
            if let Some(best) = best {
                let best_cfg = best.config.clone();
                verdicts.push(FwdVmVerdict {
                    circuit: circuit.clone(),
                    layer,
                    best_config: best.config.clone(),
                    interp_median_ms: best.interp_median_ms,
                    interp_over_flat: best.interp_over_flat,
                    blocks_per_sm: best.blocks_per_sm,
                    smem_bytes: best.smem_bytes,
                });
                for r in rows
                    .iter_mut()
                    .filter(|r| r.circuit == circuit && r.layer == layer)
                {
                    r.is_best = r.config == best_cfg;
                }
            }
        }
        rows.sort_by(|a, b| {
            (a.circuit.as_str(), a.layer, a.config.as_str()).cmp(&(
                b.circuit.as_str(),
                b.layer,
                b.config.as_str(),
            ))
        });
        FwdVmAbReport {
            device,
            iters,
            timed_count_cap,
            rows,
            verdicts,
            skips,
        }
    }

    /// Pretty JSON (mirrors `report.rs::to_json`).
    pub(crate) fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("serialize FwdVmAbReport")
    }

    /// Hand-rolled markdown: device header, the A/B table, the verdict summary,
    /// then the skip markers.
    pub(crate) fn to_markdown(&self) -> String {
        let mut s = String::new();
        writeln!(s, "# fwd-VM CUDA interpreter A/B report (Task 7)\n").unwrap();
        writeln!(
            s,
            "Replayed-flat baseline (a SUM of the production forward launches) vs the \
             single fwd-VM interpreter launch, per circuit × compiled layer × config. \
             Configs are the matrix `{{dynamic, static-s16}} × {{LDC, LDG}}`; the \
             static-s16 kernel is instantiated LDC-only (every corpus program fits the \
             `__constant__` array), so `static-s16/LDG` is a skip. Both sides timed \
             N={} with CUDA events (median + min) at the SAME element count \
             (`min(trace_len, {})`; `capped` records whether the cap applied). \
             `interp/flat` < 1 means the interpreter beats the flat replay.\n",
            self.iters, self.timed_count_cap,
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

        writeln!(s, "## A. Per-(circuit, layer, config) A/B\n").unwrap();
        writeln!(
            s,
            "| circuit | L | config | thr | count (cap) | trace_len | \
             flat med/min ms (×launch) | interp med/min ms | interp/flat | \
             lanes | n_instr | budget | smem B | blk/SM | best |"
        )
        .unwrap();
        writeln!(
            s,
            "|---|--:|---|--:|--:|--:|---|---|--:|--:|--:|--:|--:|--:|:--:|"
        )
        .unwrap();
        for r in &self.rows {
            writeln!(
                s,
                "| {} | {} | {} | {} | {}{} | {} | {:.4}/{:.4} (×{}) | {:.4}/{:.4} | {:.2}× | \
                 {} | {} | {} | {} | {} | {} |",
                r.circuit,
                r.layer,
                r.config,
                r.tpb,
                r.timed_count,
                if r.capped { " (cap)" } else { "" },
                r.trace_len,
                r.flat_median_ms,
                r.flat_min_ms,
                r.flat_launches,
                r.interp_median_ms,
                r.interp_min_ms,
                r.interp_over_flat,
                r.encoded_lanes,
                r.n_instr,
                r.budget,
                r.smem_bytes,
                r.blocks_per_sm,
                if r.is_best { "★" } else { "" },
            )
            .unwrap();
        }
        writeln!(s).unwrap();

        writeln!(s, "## B. Verdict — best config per (circuit, layer)\n").unwrap();
        writeln!(
            s,
            "The min-interpreter-median config for each (circuit, layer). This is the \
             MEASUREMENT, not a go/no-go: `interp/flat` is the interpreter's ratio vs the \
             replayed flat baseline at the best config.\n"
        )
        .unwrap();
        writeln!(
            s,
            "| circuit | L | best config | interp med ms | interp/flat | blk/SM | smem B |"
        )
        .unwrap();
        writeln!(s, "|---|--:|---|---|--:|--:|--:|").unwrap();
        for v in &self.verdicts {
            writeln!(
                s,
                "| {} | {} | {} | {:.4} | {:.2}× | {} | {} |",
                v.circuit,
                v.layer,
                v.best_config,
                v.interp_median_ms,
                v.interp_over_flat,
                v.blocks_per_sm,
                v.smem_bytes,
            )
            .unwrap();
        }
        writeln!(s).unwrap();

        writeln!(s, "## Skips\n").unwrap();
        if self.skips.is_empty() {
            writeln!(s, "_None._\n").unwrap();
        } else {
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
/// Mirrors `bench_interp::report::write_report`'s naming convention.
pub(crate) fn write_report(report: &FwdVmAbReport) -> (std::path::PathBuf, std::path::PathBuf) {
    // CARGO_MANIFEST_DIR = gpu/circuit_prover; the repo root is two up.
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonicalize repo root");
    let audits = root.join(".agents/audits");
    std::fs::create_dir_all(&audits).expect("create .agents/audits");
    let base = "2026-07-05-fwd-vm-ab-report";
    let md_path = audits.join(format!("{base}.md"));
    let json_path = audits.join(format!("{base}.json"));
    std::fs::write(&md_path, report.to_markdown()).expect("write report .md");
    std::fs::write(&json_path, report.to_json()).expect("write report .json");
    (md_path, json_path)
}
