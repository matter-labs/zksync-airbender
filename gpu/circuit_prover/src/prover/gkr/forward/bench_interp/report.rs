//! Stage-3 verdict A/B report writer (spec §6.2(A)). Mirrors
//! `gkr_eval_isa/src/report.rs`: `#[derive(Serialize)]` row structs serialized
//! to pretty JSON, plus a hand-rolled `writeln!`-into-`String` markdown table.
//! Output goes to `.agents/audits/2026-06-12-gkr-eval-isa-stage3-bench.{md,json}`
//! (GITIGNORED — written, never committed).

use serde::Serialize;
use std::fmt::Write as _;

use super::harness::BUDGET_GRID;

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
/// budget, residency, launch config) point with both timed sides and the
/// per-point context the spec mandates.
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
    // Compiler per-point stats (recomputed for the EXACT timed program — the
    // production-faithful program the compiler emits).
    pub instrs: usize,
    pub src_reads: usize,
    pub cell_reads: usize,
    pub cache_refires: usize,
    pub max_live_cells: usize,
}

/// One row of the §6.2(B) cost-decomposition table: a (circuit, layer, budget)
/// point timed at the FIXED LDG residency under a CONSTANT padded smem
/// (occupancy held constant across the budget grid; only per-thread work
/// varies). Per-point compiler stats are recomputed for the EXACT program timed.
/// `gated` records whether this point's budget was correctness-verified by set A
/// / `run_point` or is a timing-only sweep point (no implication that every
/// swept budget was checked).
#[derive(Serialize, Clone)]
pub(super) struct SetBRow {
    pub circuit: String,
    pub layer: usize,
    pub budget: usize,
    /// The constant padded dynamic-smem footprint every set-B launch used.
    pub padded_smem_bytes: usize,
    /// Static blocks-per-SM at the padded footprint (held constant by design).
    pub blocks_per_sm: i32,
    pub interp_median_ms: f32,
    pub interp_min_ms: f32,
    /// `true` when this budget was correctness-gated (set A's verdict or the
    /// 32/64 anchor); `false` = timing-only sweep point.
    pub gated: bool,
    // Per-point compiler stats for the EXACT timed program.
    pub n_instr: u32,
    pub instrs: usize,
    pub src_reads: usize,
    pub cell_reads: usize,
    pub cache_refires: usize,
    pub max_live_cells: usize,
    pub payload_bytes: usize,
}

/// One row of the §6.2(C) occupancy-curve table: a (circuit, layer, budget)
/// point at NATURAL smem sizing (the budget-implied footprint, swept up to 64
/// cells), recording blocks/SM and wall-clock vs budget — the carve-out trade.
/// `gated` annotated as in set B.
#[derive(Serialize, Clone)]
pub(super) struct SetCRow {
    pub circuit: String,
    pub layer: usize,
    pub budget: usize,
    /// Natural (budget-implied) dynamic-smem footprint.
    pub natural_smem_bytes: usize,
    pub blocks_per_sm: i32,
    /// Blocks/SM under a FORCED 100% shared-memory carveout (vs the
    /// driver-default split in `blocks_per_sm`). Equal to `blocks_per_sm` when
    /// the default split already grants enough smem; higher only if the default
    /// left occupancy on the table.
    pub blocks_per_sm_forced: i32,
    /// Whether the natural footprint opted into the >48 KB cap.
    pub large_smem_optin: bool,
    pub interp_median_ms: f32,
    pub interp_min_ms: f32,
    pub gated: bool,
}

/// One row of the §6.2(D) LDC-vs-LDG table: a single (circuit, layer, budget)
/// point timed BOTH ways at an identical config, with the LDG/LDC median and the
/// ratio. The program must fit `__constant__` for the LDC side.
#[derive(Serialize, Clone)]
pub(super) struct SetDRow {
    pub circuit: String,
    pub layer: usize,
    pub budget: usize,
    pub threads: u32,
    pub smem_bytes: usize,
    pub ldg_median_ms: f32,
    pub ldg_min_ms: f32,
    pub ldc_median_ms: f32,
    pub ldc_min_ms: f32,
    /// LDC median / LDG median (< 1 means LDC is faster).
    pub ldc_over_ldg: f32,
    pub gated: bool,
}

/// The pooled OLS "exploratory correlation" (spec §6.2(B) secondary). The
/// response is interpreter median wall-clock pooled across circuits × layers ×
/// budgets; the predictors are per-point compiler stats + circuit fixed-effect
/// dummies. Labeled exploratory/correlational, NOT causal. `error` is `Some`
/// when the fit was rank-deficient/unestimable (the coefficients are then
/// empty) — reported honestly rather than fabricated.
#[derive(Serialize, Clone)]
pub(super) struct RegressionBlock {
    /// Column labels aligned with `coefficients` (intercept first, then circuit
    /// dummies, then the numeric predictors).
    pub predictor_labels: Vec<String>,
    pub coefficients: Vec<f64>,
    pub r_squared: f64,
    pub n_obs: usize,
    pub n_coeffs: usize,
    pub residual_dof: isize,
    /// `Some(reason)` when the fit was unestimable; `coefficients` is then empty.
    pub error: Option<String>,
}

/// The full §6.2 report: §6.2(A) verdict A/B (always present), plus the §6.2
/// (B)/(C)/(D) sweep sections + the exploratory regression when the sweeps test
/// produced them (the set-A-only test leaves them empty/None). Includes queried
/// device attrs, the set-B constant padded-smem value, and skip/infeasible
/// markers (spec §6.2 output requirement).
#[derive(Serialize)]
pub(super) struct AbReport {
    pub device: DeviceAttrs,
    pub iters_full: usize,
    pub iters_prescan: usize,
    pub rows: Vec<AbRow>,
    /// §6.2(B) cost-decomposition rows (empty in the set-A-only report).
    #[serde(default)]
    pub set_b: Vec<SetBRow>,
    /// The constant padded-smem footprint set B held across the budget grid
    /// (`floor(MaxSharedMemoryPerMultiprocessor/4)` rounded to cell granularity).
    #[serde(default)]
    pub set_b_padded_smem_bytes: usize,
    /// §6.2(C) occupancy-curve rows (empty in the set-A-only report).
    #[serde(default)]
    pub set_c: Vec<SetCRow>,
    /// §6.2(D) LDC-vs-LDG rows (empty in the set-A-only report).
    #[serde(default)]
    pub set_d: Vec<SetDRow>,
    /// §6.2(B) secondary exploratory regression (None in the set-A-only report).
    #[serde(default)]
    pub regression: Option<RegressionBlock>,
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
            "| circuit | L | budget | resid | thr | shape | count (cap) | trace_len | \
             flat med/min ms (×launch) | interp med/min ms | interp/flat | smem B | blk/SM | \
             optin | prog B | payload B | n_instr | instr | src_rd | cell_rd | refires | live |"
        )
        .unwrap();
        writeln!(
            s,
            "|---|--:|--:|---|--:|---|--:|--:|---|---|--:|--:|--:|---|--:|--:|--:|--:|--:|--:|--:|--:|"
        )
        .unwrap();
        for r in &self.rows {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {}{} | {} | {:.4}/{:.4} (×{}) | {:.4}/{:.4} | {:.2}× | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                r.circuit,
                r.layer,
                r.budget,
                r.residency,
                r.interp_threads,
                "production",
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

        self.write_set_b(&mut s);
        self.write_set_c(&mut s);
        self.write_set_d(&mut s);

        if !self.skips.is_empty() {
            writeln!(s, "## Skips / infeasible markers\n").unwrap();
            for sk in &self.skips {
                writeln!(s, "- {sk}").unwrap();
            }
            writeln!(s).unwrap();
        }
        s
    }

    /// §6.2(B) cost-decomposition table + the exploratory regression block.
    /// Skipped entirely when the set-A-only test wrote the report.
    fn write_set_b(&self, s: &mut String) {
        if self.set_b.is_empty() {
            return;
        }
        writeln!(s, "## B. Cost decomposition (spec §6.2(B))\n").unwrap();
        writeln!(
            s,
            "Full feasible budget grid {BUDGET_GRID:?} ∩ feasible, FIXED LDG residency, \
             CONSTANT padded dynamic smem = {} bytes (= floor(MaxSharedMemoryPerMultiprocessor/4) \
             rounded to cell granularity — occupancy held constant across the grid so only \
             per-thread work varies, spec §4 + controller decision). Per-point compiler stats are \
             recomputed for the EXACT program timed. `gated` = the \
             budget was correctness-verified (set A's verdict or the 32/64 anchor); \
             un-gated rows are TIMING-ONLY sweep points (NOT correctness-checked at this budget — \
             correctness is anchored by set A's per-point gating + `stage3_run_point_correctness`).\n",
            self.set_b_padded_smem_bytes,
        )
        .unwrap();
        writeln!(
            s,
            "| circuit | L | budget | shape | gated | pad smem B | blk/SM | interp med/min ms | \
             n_instr | instr | src_rd | cell_rd | refires | live | payload B |"
        )
        .unwrap();
        writeln!(
            s,
            "|---|--:|--:|---|---|--:|--:|---|--:|--:|--:|--:|--:|--:|--:|"
        )
        .unwrap();
        for r in &self.set_b {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {:.4}/{:.4} | {} | {} | {} | {} | {} | {} | {} |",
                r.circuit,
                r.layer,
                r.budget,
                "production",
                if r.gated { "yes" } else { "timing-only" },
                r.padded_smem_bytes,
                r.blocks_per_sm,
                r.interp_median_ms,
                r.interp_min_ms,
                r.n_instr,
                r.instrs,
                r.src_reads,
                r.cell_reads,
                r.cache_refires,
                r.max_live_cells,
                r.payload_bytes,
            )
            .unwrap();
        }
        writeln!(s).unwrap();

        // The exploratory regression secondary.
        writeln!(
            s,
            "### B-secondary: pooled wall-clock regression (EXPLORATORY CORRELATION)\n"
        )
        .unwrap();
        writeln!(
            s,
            "Ordinary-least-squares fit of interpreter median (ms) ~ per-point compiler stats + \
             circuit fixed-effect dummies, pooled across circuits × layers × budgets. This is a \
             CORRELATION, not a causal/validated model: read the signs/magnitudes as descriptive \
             only. Rank-deficiency is reported, never fabricated.\n"
        )
        .unwrap();
        match &self.regression {
            None => {
                writeln!(s, "_No regression computed (set-A-only report)._\n").unwrap();
            }
            Some(reg) => {
                if let Some(err) = &reg.error {
                    writeln!(
                        s,
                        "**Unestimable**: {err}\n\n(n_obs = {}, attempted n_coeffs = {})\n",
                        reg.n_obs, reg.n_coeffs
                    )
                    .unwrap();
                } else {
                    writeln!(s, "| predictor | coefficient |").unwrap();
                    writeln!(s, "|---|--:|").unwrap();
                    for (label, c) in reg.predictor_labels.iter().zip(&reg.coefficients) {
                        writeln!(s, "| {label} | {c:.6e} |").unwrap();
                    }
                    writeln!(
                        s,
                        "\n- R²: {:.4}\n- observations: {}\n- coefficients: {}\n- residual dof: {}\n",
                        reg.r_squared, reg.n_obs, reg.n_coeffs, reg.residual_dof
                    )
                    .unwrap();
                }
            }
        }
    }

    /// §6.2(C) occupancy-curve table (natural smem sizing, blocks/SM + wall-clock
    /// vs budget). Skipped when the set-A-only test wrote the report.
    fn write_set_c(&self, s: &mut String) {
        if self.set_c.is_empty() {
            return;
        }
        writeln!(s, "## C. Occupancy curve (spec §6.2(C))\n").unwrap();
        writeln!(
            s,
            "NATURAL dynamic-smem sizing (budget-implied footprint) swept across the feasible \
             budget grid incl. 64 cells, FIXED LDG residency: static blocks/SM and interpreter \
             wall-clock vs budget — the carve-out trade. `blk/SM` is the driver-default L1/smem \
             split; `blk/SM 100%` forces a 100% shared-memory carveout for the occupancy query \
             (reset before timing) — a higher value means the default split left occupancy on \
             the table. `gated` annotated as in set B.\n"
        )
        .unwrap();
        writeln!(
            s,
            "| circuit | L | budget | shape | gated | nat smem B | optin | blk/SM | blk/SM 100% | interp med/min ms |"
        )
        .unwrap();
        writeln!(s, "|---|--:|--:|---|---|--:|---|--:|--:|---|").unwrap();
        for r in &self.set_c {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {:.4}/{:.4} |",
                r.circuit,
                r.layer,
                r.budget,
                "production",
                if r.gated { "yes" } else { "timing-only" },
                r.natural_smem_bytes,
                if r.large_smem_optin { "yes" } else { "no" },
                r.blocks_per_sm,
                r.blocks_per_sm_forced,
                r.interp_median_ms,
                r.interp_min_ms,
            )
            .unwrap();
        }
        writeln!(s).unwrap();
    }

    /// §6.2(D) LDC-vs-LDG table (one circuit/layer where both fit, identical
    /// config otherwise). Skipped when the set-A-only test wrote the report.
    fn write_set_d(&self, s: &mut String) {
        if self.set_d.is_empty() {
            return;
        }
        writeln!(s, "## D. LDC vs LDG (spec §6.2(D))\n").unwrap();
        writeln!(
            s,
            "One circuit/layer/budget where the program fits `__constant__`, timed BOTH ways at \
             an identical config (same threads, same natural smem). `ldc/ldg` < 1 means the \
             constant-resident program is faster. `gated` annotated as in set B.\n"
        )
        .unwrap();
        writeln!(
            s,
            "| circuit | L | budget | shape | gated | thr | smem B | LDG med/min ms | LDC med/min ms | LDC/LDG |"
        )
        .unwrap();
        writeln!(s, "|---|--:|--:|---|---|--:|--:|---|---|--:|").unwrap();
        for r in &self.set_d {
            writeln!(
                s,
                "| {} | {} | {} | {} | {} | {} | {} | {:.4}/{:.4} | {:.4}/{:.4} | {:.2}× |",
                r.circuit,
                r.layer,
                r.budget,
                "production",
                if r.gated { "yes" } else { "timing-only" },
                r.threads,
                r.smem_bytes,
                r.ldg_median_ms,
                r.ldg_min_ms,
                r.ldc_median_ms,
                r.ldc_min_ms,
                r.ldc_over_ldg,
            )
            .unwrap();
        }
        writeln!(s).unwrap();
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
