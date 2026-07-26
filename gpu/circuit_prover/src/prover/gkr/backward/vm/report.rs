//! Sweep-report rendering for the backward GPU benchmark.
//!
//! Task 12 replaces this module with the coefficient-ISA sweep; what survives
//! here is the shape of that report — the timing summary, the CSV, the
//! ranking and the NCU coordinate selector — each covered by its own unit test
//! below. `time_cuda_launches` and `upload_incumbent_coefficients` are the two
//! GPU-touching helpers Task 12's sweep will call.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use era_cudart::event::{CudaEvent, elapsed_time};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

use crate::primitives::field::E4;
use crate::prover::ProverContext;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::upstream::Field;

// TASK 12 rewires the sweep that consumes this; the retired VM's sweep test
// was its only caller. Scoped per item so nothing else in this module can go
// dead unnoticed in the meantime.
#[allow(dead_code)]
pub(super) const WARMUP_ITERS: usize = 10;
#[allow(dead_code)]
pub(super) const TIMING_ITERS: usize = 30;
#[allow(dead_code)]
pub(super) const SWEEP_LOG_PATH: &str = "/tmp/plan5-bwd-vm-sweep.log";
#[allow(dead_code)]
pub(super) const NCU_SELECTOR_ENV: &str = "PLAN5_BWD_VM_NCU_COORD";

/// An exact single coordinate for profiler collection, or the complete sweep.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SweepSelection {
    #[allow(dead_code)] // TASK 12: only `from_env` produces the whole sweep.
    All,
    R0 { budget_cells: usize },
    Ext { budget_cells: usize, round: u8 },
}

impl SweepSelection {
    #[allow(dead_code)] // TASK 12: driven by the sweep test.
    pub(super) fn from_env() -> Self {
        match std::env::var(NCU_SELECTOR_ENV) {
            Ok(value) => parse_ncu_selector(&value)
                .unwrap_or_else(|error| panic!("invalid {NCU_SELECTOR_ENV}={value:?}: {error}"))
                .expect("non-empty environment selector"),
            Err(std::env::VarError::NotPresent) => Self::All,
            Err(error) => panic!("read {NCU_SELECTOR_ENV}: {error}"),
        }
    }

    pub(super) fn includes(self, regime: &str, budget_cells: usize, round: u8) -> bool {
        match self {
            Self::All => true,
            Self::R0 {
                budget_cells: selected,
            } => regime == "R0" && budget_cells == selected && round == 0,
            Self::Ext {
                budget_cells: selected,
                round: selected_round,
            } => regime == "Ext" && budget_cells == selected && round == selected_round,
        }
    }

    #[allow(dead_code)] // TASK 12: driven by the sweep test.
    pub(super) fn needs_ext_setup(self) -> bool {
        !matches!(self, Self::R0 { .. })
    }

    #[allow(dead_code)] // TASK 12: driven by the sweep test.
    pub(super) fn needs_incumbent_round(self, round: u8) -> bool {
        match self {
            Self::All => round <= 3,
            Self::R0 { .. } => round == 0,
            Self::Ext {
                round: selected, ..
            } => round == selected,
        }
    }

    pub(super) fn prepares_ext_round(self, round: u8) -> bool {
        match self {
            Self::All => round <= 3,
            Self::R0 { .. } => false,
            Self::Ext {
                round: selected, ..
            } => round <= selected,
        }
    }

    #[allow(dead_code)] // TASK 12: driven by the sweep test.
    pub(super) fn stops_after_ext_round(self, round: u8) -> bool {
        match self {
            Self::All => round == 3,
            Self::Ext {
                round: selected, ..
            } => round == selected,
            Self::R0 { .. } => false,
        }
    }

    #[allow(dead_code)] // TASK 12: driven by the sweep test.
    pub(super) fn assert_report_rows(self, rows: &[SweepRow]) {
        if !matches!(self, Self::All) {
            assert_eq!(rows.len(), 1, "NCU selector must time one coordinate");
            let row = &rows[0];
            assert!(
                self.includes(row.regime, row.budget_cells, row.round),
                "NCU selector result must match its requested coordinate"
            );
        }
    }
}

pub(super) fn parse_ncu_selector(value: &str) -> Result<Option<SweepSelection>, String> {
    if value.is_empty() {
        return Ok(None);
    }
    let mut parts = value.split(':');
    let regime = parts.next().expect("split always yields first part");
    let budget = parts.next().ok_or("expected <r0|ext>:c<2..16>:r<0..3>")?;
    let round = parts.next().ok_or("expected <r0|ext>:c<2..16>:r<0..3>")?;
    if parts.next().is_some() {
        return Err("expected exactly <r0|ext>:c<2..16>:r<0..3>".to_owned());
    }
    let budget_cells = budget
        .strip_prefix('c')
        .ok_or("budget must use c<2..16>")?
        .parse::<usize>()
        .map_err(|_| "budget must use c<2..16>".to_owned())?;
    if !(2..=16).contains(&budget_cells) {
        return Err("budget must be c2 through c16".to_owned());
    }
    let round = round
        .strip_prefix('r')
        .ok_or("round must use r<0..3>")?
        .parse::<u8>()
        .map_err(|_| "round must use r<0..3>".to_owned())?;
    match regime {
        "r0" if round == 0 => Ok(Some(SweepSelection::R0 { budget_cells })),
        "r0" => Err("R0 selector requires r0".to_owned()),
        "ext" if (1..=3).contains(&round) => Ok(Some(SweepSelection::Ext {
            budget_cells,
            round,
        })),
        "ext" => Err("Ext selector requires r1 through r3".to_owned()),
        _ => Err("regime must be r0 or ext".to_owned()),
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct TimingSummary {
    pub(super) median_us: f32,
    pub(super) min_us: f32,
}

impl TimingSummary {
    fn from_milliseconds(mut samples: Vec<f32>) -> Self {
        assert!(!samples.is_empty(), "timing requires at least one sample");
        samples.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite CUDA timing"));
        let upper_middle = samples.len() / 2;
        let median_ms = if samples.len() % 2 == 0 {
            (samples[upper_middle - 1] + samples[upper_middle]) / 2.0
        } else {
            samples[upper_middle]
        };
        Self {
            median_us: median_ms * 1_000.0,
            min_us: samples[0] * 1_000.0,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct SweepRow {
    pub(super) budget_cells: usize,
    pub(super) regime: &'static str,
    pub(super) round: u8,
    pub(super) rows: usize,
    pub(super) dynamic_smem_bytes: usize,
    pub(super) active_blocks_per_sm: i32,
    pub(super) theoretical_occupancy: f32,
    pub(super) program_instructions: usize,
    pub(super) program_lanes: usize,
    pub(super) predicted_source_bytes: u128,
    pub(super) incumbent_sequence: &'static str,
    pub(super) vm: TimingSummary,
    pub(super) incumbent: TimingSummary,
}

impl SweepRow {
    pub(super) fn ratio(&self) -> f32 {
        self.vm.median_us / self.incumbent.median_us
    }
}

/// Time one already-prepared launch sequence. Poisoning is enqueued before the
/// start event, so output reset is deliberately outside every measured span.
#[allow(dead_code)] // TASK 12: called by the sweep test.
pub(super) fn time_cuda_launches(
    stream: &CudaStream,
    warmups: usize,
    iterations: usize,
    mut poison: impl FnMut() -> CudaResult<()>,
    mut launch: impl FnMut() -> CudaResult<()>,
) -> CudaResult<TimingSummary> {
    assert!(warmups >= WARMUP_ITERS, "at least {WARMUP_ITERS} warmups");
    assert!(
        iterations >= TIMING_ITERS,
        "at least {TIMING_ITERS} samples"
    );
    for _ in 0..warmups {
        poison()?;
        launch()?;
    }
    stream.synchronize()?;

    let start = CudaEvent::create()?;
    let end = CudaEvent::create()?;
    let mut samples = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        poison()?;
        start.record(stream)?;
        launch()?;
        end.record(stream)?;
        stream.synchronize()?;
        samples.push(elapsed_time(&start, &end)?);
    }
    Ok(TimingSummary::from_milliseconds(samples))
}

#[allow(dead_code)] // TASK 12: called by the sweep test.
pub(super) fn upload_incumbent_coefficients(
    coefficients: &[E4],
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(coefficients.len() <= FLAT_CONST_MAX);
    let bank: [E4; FLAT_CONST_MAX] =
        core::array::from_fn(|index| coefficients.get(index).copied().unwrap_or(E4::ZERO));
    // SAFETY: this Rust stub names the exact CUDA `e4[FLAT_CONST_MAX]`
    // coefficient symbol. The pageable source is staged by the helper and the
    // copy is ordered before subsequent launches on `exec_stream`.
    unsafe {
        crate::primitives::utils::memcpy_to_symbol_async(
            &super::ab_gkr_flat_coefficients,
            &bank,
            context.get_exec_stream(),
        )
    }
}

pub(super) fn render_full_report(rows: &[SweepRow]) -> String {
    let mut output = String::from(
        "budget,regime,round,rows,dynamic_smem_bytes,active_blocks_per_sm,theoretical_occupancy_percent,program_instructions,program_lanes,predicted_source_bytes,incumbent_sequence,vm_median_us,vm_min_us,incumbent_median_us,incumbent_min_us,vm_over_incumbent\n",
    );
    let mut aggregates = BTreeMap::<usize, (f32, f32, f32, f32)>::new();
    for row in rows {
        writeln!(
            output,
            "c{},{},{},{},{},{},{:.2},{},{},{},{},{:.3},{:.3},{:.3},{:.3},{:.6}",
            row.budget_cells,
            row.regime,
            row.round,
            row.rows,
            row.dynamic_smem_bytes,
            row.active_blocks_per_sm,
            row.theoretical_occupancy * 100.0,
            row.program_instructions,
            row.program_lanes,
            row.predicted_source_bytes,
            row.incumbent_sequence,
            row.vm.median_us,
            row.vm.min_us,
            row.incumbent.median_us,
            row.incumbent.min_us,
            row.ratio(),
        )
        .expect("write String");
        let aggregate = aggregates.entry(row.budget_cells).or_default();
        aggregate.0 += row.vm.median_us;
        aggregate.1 += row.vm.min_us;
        aggregate.2 += row.incumbent.median_us;
        aggregate.3 += row.incumbent.min_us;
    }
    output.push_str(
        "whole-layer,budget,vm_median_us,vm_min_us,incumbent_median_us,incumbent_min_us,vm_over_incumbent\n",
    );
    for (budget, (vm_median, vm_min, incumbent_median, incumbent_min)) in aggregates {
        writeln!(
            output,
            "whole-layer,c{budget},{vm_median:.3},{vm_min:.3},{incumbent_median:.3},{incumbent_min:.3},{:.6}",
            vm_median / incumbent_median,
        )
        .expect("write String");
    }
    output
}

pub(super) fn ranked_budgets(rows: &[SweepRow]) -> Vec<(f32, usize, f32, f32)> {
    let mut aggregates = BTreeMap::<usize, (f32, f32)>::new();
    for row in rows {
        let aggregate = aggregates.entry(row.budget_cells).or_default();
        aggregate.0 += row.vm.median_us;
        aggregate.1 += row.incumbent.median_us;
    }
    let mut ranked = aggregates
        .into_iter()
        .map(|(budget, (vm, incumbent))| (vm / incumbent, budget, vm, incumbent))
        .collect::<Vec<_>>();
    ranked.sort_by(|lhs, rhs| lhs.0.partial_cmp(&rhs.0).expect("finite aggregate ratio"));
    ranked
}

pub(super) fn publish_report(rows: &[SweepRow], path: &Path) {
    let report = render_full_report(rows);
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("sweep");
    let temporary = path.with_file_name(format!(".{file_name}.{}.tmp", std::process::id()));
    std::fs::write(&temporary, report)
        .unwrap_or_else(|error| panic!("write {}: {error}", temporary.display()));
    std::fs::rename(&temporary, path)
        .unwrap_or_else(|error| panic!("publish {}: {error}", path.display()));

    let ranked = ranked_budgets(rows);
    eprintln!(
        "[bwd-vm-sweep] complete coordinates={} full_log={}",
        rows.len(),
        path.display()
    );
    for (ratio, budget, vm, incumbent) in ranked.into_iter().take(4) {
        eprintln!(
            "[bwd-vm-sweep] best c{budget}: vm={vm:.3}us incumbent={incumbent:.3}us ratio={ratio:.4}"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timing_summary_uses_sorted_median_and_minimum() {
        let summary = TimingSummary::from_milliseconds(vec![4.0, 1.0, 3.0, 2.0, 5.0]);
        assert_eq!(summary.median_us, 3_000.0);
        assert_eq!(summary.min_us, 1_000.0);
    }

    #[test]
    fn timing_summary_averages_the_two_middle_even_samples() {
        let summary = TimingSummary::from_milliseconds(vec![4.0, 1.0, 3.0, 2.0]);
        assert_eq!(summary.median_us, 2_500.0);
        assert_eq!(summary.min_us, 1_000.0);
    }

    #[test]
    fn sweep_report_has_stable_metadata_columns_and_aggregate() {
        let rows = vec![SweepRow {
            budget_cells: 4,
            regime: "Ext",
            round: 2,
            rows: 16,
            dynamic_smem_bytes: 8_192,
            active_blocks_per_sm: 3,
            theoretical_occupancy: 0.75,
            program_instructions: 100,
            program_lanes: 150,
            predicted_source_bytes: 3_072,
            incumbent_sequence: "compact evaluator launcher",
            vm: TimingSummary {
                median_us: 12.0,
                min_us: 10.0,
            },
            incumbent: TimingSummary {
                median_us: 6.0,
                min_us: 5.0,
            },
        }];
        let rendered = render_full_report(&rows);
        assert!(rendered.contains("budget,regime,round,rows,dynamic_smem_bytes"));
        assert!(rendered.contains("c4,Ext,2,16,8192,3,75.00"));
        assert!(rendered.contains("whole-layer,c4"));
        assert!(rendered.contains(",2.000000"));
    }

    #[test]
    fn ncu_selector_accepts_only_unambiguous_representative_coordinates() {
        assert_eq!(
            parse_ncu_selector("r0:c4:r0"),
            Ok(Some(SweepSelection::R0 { budget_cells: 4 }))
        );
        assert_eq!(
            parse_ncu_selector("ext:c2:r1"),
            Ok(Some(SweepSelection::Ext {
                budget_cells: 2,
                round: 1,
            }))
        );
        assert_eq!(
            parse_ncu_selector("ext:c16:r3"),
            Ok(Some(SweepSelection::Ext {
                budget_cells: 16,
                round: 3,
            }))
        );
        assert!(parse_ncu_selector("r0:c5:r1").is_err());
        assert!(parse_ncu_selector("ext:c12:r0").is_err());
        assert!(parse_ncu_selector("ext:c12:r4").is_err());
        assert!(parse_ncu_selector("ext:c1:r1").is_err());
        assert!(parse_ncu_selector("ext:c12").is_err());
        assert!(parse_ncu_selector("ext:c12:r1:extra").is_err());
    }

    #[test]
    fn ext_selector_prepares_every_predecessor_round() {
        let selection = SweepSelection::Ext {
            budget_cells: 7,
            round: 3,
        };

        assert!((1..=3).all(|round| selection.prepares_ext_round(round)));
        assert!(!selection.prepares_ext_round(4));
        assert!(!selection.includes("Ext", 7, 1));
        assert!(selection.includes("Ext", 7, 3));
    }

    #[test]
    fn ranking_and_aggregation_cover_multiple_rounds_and_budgets() {
        let rows = vec![
            test_row(2, "R0", 0, 30.0, 10.0),
            test_row(4, "Ext", 1, 12.0, 10.0),
            test_row(4, "Ext", 2, 8.0, 10.0),
        ];
        let rendered = render_full_report(&rows);
        assert!(rendered.contains("whole-layer,c4,20.000,20.000,20.000,20.000,1.000000"));
        assert_eq!(ranked_budgets(&rows)[0].1, 4);
        assert_eq!(ranked_budgets(&rows)[1].1, 2);
        assert!(rendered.contains("program_instructions,program_lanes,predicted_source_bytes"));
        assert!(rendered.contains("incumbent_sequence"));
    }

    #[test]
    fn report_preserves_the_full_budget_range_and_distinct_round_coordinates() {
        let mut rows = (2..=16)
            .map(|budget| test_row(budget, "R0", 0, budget as f32, 1.0))
            .collect::<Vec<_>>();
        rows.push(test_row(2, "Ext", 1, 2.0, 1.0));
        rows.push(test_row(2, "Ext", 2, 3.0, 1.0));

        let rendered = render_full_report(&rows);
        assert_eq!(rendered.matches("\nwhole-layer,c").count(), 15);
        assert!(rendered.contains("c2,Ext,1,"));
        assert!(rendered.contains("c2,Ext,2,"));
        assert!(rendered.contains("c16,R0,0,"));
    }

    #[test]
    fn publication_writes_the_complete_table_to_its_own_path() {
        let path = std::env::temp_dir().join(format!(
            "bwd-vm-sweep-report-{}-{}.csv",
            std::process::id(),
            std::thread::current().name().unwrap_or("report-test")
        ));
        let rows = vec![test_row(2, "R0", 0, 20.0, 10.0)];
        publish_report(&rows, &path);
        assert_eq!(
            std::fs::read_to_string(&path).expect("published report"),
            render_full_report(&rows)
        );
        std::fs::remove_file(path).expect("remove published report");
    }

    fn test_row(
        budget_cells: usize,
        regime: &'static str,
        round: u8,
        vm_median_us: f32,
        incumbent_median_us: f32,
    ) -> SweepRow {
        SweepRow {
            budget_cells,
            regime,
            round,
            rows: 16,
            dynamic_smem_bytes: 8_192,
            active_blocks_per_sm: 3,
            theoretical_occupancy: 0.75,
            program_instructions: 100,
            program_lanes: 150,
            predicted_source_bytes: 3_072,
            incumbent_sequence: "compact evaluator launcher",
            vm: TimingSummary {
                median_us: vm_median_us,
                min_us: vm_median_us,
            },
            incumbent: TimingSummary {
                median_us: incumbent_median_us,
                min_us: incumbent_median_us,
            },
        }
    }
}
