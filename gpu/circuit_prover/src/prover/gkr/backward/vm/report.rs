use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

use crate::primitives::field::E4;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::ProverContext;
use crate::upstream::Field;

pub(super) const WARMUP_ITERS: usize = 10;
pub(super) const TIMING_ITERS: usize = 30;
pub(super) const SWEEP_LOG_PATH: &str = "/tmp/plan5-bwd-vm-sweep.log";

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
        "budget,regime,round,rows,dynamic_smem_bytes,active_blocks_per_sm,theoretical_occupancy_percent,program_instructions,program_lanes,predicted_source_bytes,vm_median_us,vm_min_us,incumbent_median_us,incumbent_min_us,vm_over_incumbent\n",
    );
    let mut aggregates = BTreeMap::<usize, (f32, f32, f32, f32)>::new();
    for row in rows {
        writeln!(
            output,
            "c{},{},{},{},{},{},{:.2},{},{},{},{:.3},{:.3},{:.3},{:.3},{:.6}",
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

pub(super) fn publish_report(rows: &[SweepRow], path: &Path) {
    let report = render_full_report(rows);
    std::fs::write(path, report)
        .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));

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
}
