//! Task 12's measurement harness: per-configuration timing, the sweep CSV, the
//! per-round-class budget SELECTION, and the kernel-attribute probe §15's release
//! gate is stated in terms of.
//!
//! This is a finite benchmark, not a search. The sweep walks a fixed coordinate
//! set — `(circuit, layer, regime, round class, budget)` — times each with three
//! warmups and ten samples, and reports median and min. Nothing here explores;
//! [`select_budgets`] reads off the fastest measured budget per
//! `(circuit, layer, round class)`, resolving the [`SELECTION_TIE_FRACTION`] band
//! of budgets that measure the same in favour of the smallest.
//!
//! # What is measured and what is modeled
//!
//! Two different kinds of number share one row, and the CSV names them apart:
//!
//!   * MEASURED on the device: median/min runtime, registers, local-memory
//!     spills, static/dynamic shared memory, and occupancy (blocks per SM from
//!     `cudaOccupancyMaxActiveBlocksPerMultiprocessor` against the real launch
//!     geometry).
//!   * MODELED by the compiler, exactly and not estimated: realized source-read
//!     bytes and the read floor, cell-file loads and stores, the BF/mixed/E4
//!     arithmetic classes, the term count, moves, and the encoded program's words
//!     and bytes. These come straight from [`ProgramReport`] — the same numbers
//!     Task 8's static sweep pins — so a runtime that moves without any of them
//!     moving is a scheduling or occupancy effect, not a program change.
//!
//! # §15's release gate
//!
//! "Release kernels must have zero validation work and zero local-memory spills."
//! [`KernelAttributes`] queries `cudaFuncGetAttributes` on the exact instantiation
//! a row launched, so the gate is asserted per instantiation against the loaded
//! module rather than read off a build log.

use std::collections::BTreeMap;
use std::ffi::c_void;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use era_cudart::event::{CudaEvent, elapsed_time};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{CudaFuncAttributes, cudaFuncGetAttributes};
use gkr_eval_isa::bwd::coeff::artifact::{
    ArtifactRegime, BwdRoundClass, ProgramReport, SELECTION_DIAGNOSTIC_CELLS, SelectedBudget,
};

use super::desc::BWD_COEFF_THREADS_PER_BLOCK;
use super::{BwdCoeffBank, bwd_coeff_blocks_per_sm, bwd_coeff_dynamic_smem_bytes};
use crate::primitives::field::E4;
use crate::prover::ProverContext;
use crate::upstream::BwdRegime;

/// §15's sample discipline: three warmups, ten timed samples, median and min.
pub(super) const WARMUP_ITERS: usize = 3;
pub(super) const TIMING_ITERS: usize = 10;

/// Every sweep artefact lands under `target/`, which is git-ignored on purpose:
/// these are machine measurements, not repository content.
pub(super) const SWEEP_OUTPUT_DIR: &str = "target/gkr";
pub(super) const FOCUSED_CSV: &str = "bwd_coeff_focused_layer0_sweep.csv";
pub(super) const CORPUS_CSV: &str = "bwd_coeff_corpus_sweep.csv";
pub(super) const SELECTION_JSON: &str = "bwd_coeff_selected_budgets.json";
pub(super) const SUMMARY_MD: &str = "bwd_coeff_profile_summary.md";

/// The budget the profiler test launches, overridable so a profiling session can
/// re-target without a rebuild.
///
/// This must equal the PERSISTED `add_sub` layer-0 R0 selection in
/// [`SELECTION_JSON`], which is the single authority for a production budget.
/// `assert_profile_cells_match_persisted_selection` enforces that whenever the
/// sidecar exists, so a stale pin is a test failure rather than three sources
/// disagreeing.
///
/// Note what the sweep found about that coordinate: c2 through c7 all run at 6
/// blocks per SM and their medians sit inside [`SELECTION_TIE_FRACTION`] of each
/// other, so the tier — not this exact member — is the finding.
pub(super) const PROFILE_CELLS_ENV: &str = "BWD_COEFF_PROFILE_CELLS";
pub(super) const PROFILE_DEFAULT_CELLS: u8 = 3;

/// Raw counters from the `add_sub` layer-0 R0 capture PAIR, pinned so the
/// generated head-to-head section can bound its own synthetic-source caveat.
///
/// These are the only profiler-only numbers this module restates, and they carry
/// a **re-pin duty**: the `.ncu-rep` files are the authority, and every value here
/// must be re-derived FROM them — never by hand, never from a previous session's
/// notes. Re-derive all six with exactly this, from the repository root:
///
/// ```text
/// for r in bwd_coeff_add_sub_l0_r0 bwd_coeff_add_sub_l0_r0_incumbent; do
///   ncu --import target/profiling/ncu/$r.ncu-rep --page raw --csv | python3 -c "
/// import csv,sys
/// rows=list(csv.reader(sys.stdin)); hdr,vals=rows[0],rows[-1]
/// g=lambda k: float(vals[hdr.index(k)])
/// dur=g('gpu__time_duration.sum')
/// print('dur_ms=%.6f dram_GB=%.6f l2_miss_M=%.4f inst=%.0f ipc_elapsed_sum=%.6f' % (
///     dur, g('dram__bytes.sum.per_second')*dur, g('lts__t_sectors_lookup_miss.sum')/1e6,
///     g('smsp__inst_executed.sum'), g('sm__inst_executed.sum.per_cycle_elapsed')))
/// "
/// done
/// ```
///
/// then `duration ratio = dur_new / dur_inc` and
/// `model ratio = (inst_new / ipc_new) / (inst_inc / ipc_inc)`.
///
/// A previous revision pinned these from an INTERMEDIATE capture that was later
/// overwritten, so four of them disagreed with the files they cited while the
/// prose quoted the files. That is why the command is written out here: the
/// failure mode is re-pinning from memory, and it is invisible unless someone
/// reads the captures back.
///
/// Why they are worth pinning at all: they are what turns "the cache-hit gap
/// might be a synthetic-layout artifact" from a hedge into a bound. The new
/// lineage moves FEWER DRAM bytes and misses L2 FEWER times than the incumbent,
/// so consolidating the source layout can only reduce traffic where the new side
/// is already ahead — it cannot be hiding a regression.
///
/// Current values, from the captures in the tree:
/// new `dur_ms=7.153984 dram_GB=8.674392 l2_miss_M=271.6137 inst=6808836096
/// ipc_elapsed_sum=412.528688`; incumbent `dur_ms=6.068544 dram_GB=8.844551
/// l2_miss_M=276.5579 inst=4971730944 ipc_elapsed_sum=354.995755`.
pub(super) const PINNED_DRAM_GB_NEW: f64 = 8.674;
pub(super) const PINNED_DRAM_GB_INCUMBENT: f64 = 8.845;
pub(super) const PINNED_L2_MISS_SECTORS_NEW_M: f64 = 271.6;
pub(super) const PINNED_L2_MISS_SECTORS_INCUMBENT_M: f64 = 276.6;
/// `(instructions / elapsed IPC)` new over incumbent, and the duration ratio the
/// same capture pair measured. The two agreeing is the claim that the occupancy
/// and instruction-count model accounts for the gap without a cache term.
///
/// ELAPSED IPC, not active: the thing being predicted is elapsed duration.
/// (6808836096 / 412.528688) / (4971730944 / 354.995755) = 1.178513, against a
/// measured 7.153984 / 6.068544 = 1.178863 — a residual of 0.03%.
pub(super) const PINNED_MODEL_RATIO: f64 = 1.1785;
pub(super) const PINNED_PROFILED_DURATION_RATIO: f64 = 1.1789;

/// Matching incumbent launches `ncu` must skip to reach the first TIMED one.
///
/// Derived, not hard-coded: `head_to_head_add_sub_l0_r0` runs exactly one untimed
/// correctness launch before handing the incumbent to `time_cuda_launches`, which
/// then runs [`WARMUP_ITERS`] warmups before the first timed sample. Changing the
/// warmup count therefore moves this number with it, instead of silently
/// profiling a cold warmup launch.
pub(super) const INCUMBENT_CORRECTNESS_LAUNCHES: usize = 1;
pub(super) const INCUMBENT_PROFILE_LAUNCH_SKIP: usize =
    INCUMBENT_CORRECTNESS_LAUNCHES + WARMUP_ITERS;

pub(super) fn sweep_output_path(file: &str) -> PathBuf {
    PathBuf::from(SWEEP_OUTPUT_DIR).join(file)
}

/// Reconcile the compiled pin against the persisted selection.
///
/// The corpus sweep writes [`SELECTION_JSON`]; that file, not this constant, is
/// what §13 calls the production choice, and Task 13 is required to consume it.
/// So whenever it exists, the pin must agree with it — otherwise "the profiled
/// budget", "the compiled default" and "the persisted selection" are three
/// different answers, which is exactly the confusion this guard exists to stop.
///
/// Absent sidecar means the sweep has not run on this machine yet; that is not a
/// failure, and the profile still runs at the pin.
pub(super) fn assert_profile_cells_match_persisted_selection(cells: u8, coordinate: &str) {
    let path = sweep_output_path(SELECTION_JSON);
    let Ok(text) = std::fs::read_to_string(&path) else {
        eprintln!(
            "[bwd-coeff-profile] no persisted selection at {}; profiling at the compiled pin c{cells}",
            path.display()
        );
        return;
    };
    // The sidecar is one object per line by construction (`render_selection_json`),
    // so the coordinate's line is its own record and a substring search over it
    // cannot cross into a neighbour.
    let Some(line) = text
        .lines()
        .find(|line| line.contains(coordinate) && line.contains("\"regime\": \"R0\""))
    else {
        panic!("{}: no R0 selection for {coordinate}", path.display());
    };
    let needle = "\"round_class\": \"R0\", \"cells\": ";
    let start = line
        .find(needle)
        .unwrap_or_else(|| panic!("{}: malformed R0 selection: {line}", path.display()))
        + needle.len();
    let persisted: u8 = line[start..]
        .trim_start()
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .and_then(|digits| digits.parse().ok())
        .unwrap_or_else(|| panic!("{}: malformed R0 cells: {line}", path.display()));
    assert_eq!(
        cells, persisted,
        "the profiled budget must be the persisted {coordinate} R0 selection from {}; \
         re-pin PROFILE_DEFAULT_CELLS (or set {PROFILE_CELLS_ENV} deliberately)",
        path.display()
    );
}

/// The profiled budget: [`PROFILE_CELLS_ENV`] when set, else
/// [`PROFILE_DEFAULT_CELLS`].
pub(super) fn profile_cells() -> u8 {
    match std::env::var(PROFILE_CELLS_ENV) {
        Ok(value) => {
            let cells = value
                .trim()
                .trim_start_matches('c')
                .parse::<u8>()
                .unwrap_or_else(|error| panic!("invalid {PROFILE_CELLS_ENV}={value:?}: {error}"));
            assert!(
                (2..=16).contains(&cells),
                "{PROFILE_CELLS_ENV} must name c2..c16, got c{cells}"
            );
            cells
        }
        Err(std::env::VarError::NotPresent) => PROFILE_DEFAULT_CELLS,
        Err(error) => panic!("read {PROFILE_CELLS_ENV}: {error}"),
    }
}

// ── Timing ───────────────────────────────────────────────────────────────────

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

/// Time one already-prepared launch sequence. Poisoning is enqueued before the
/// start event, so output reset is deliberately outside every measured span.
pub(super) fn time_cuda_launches(
    stream: &CudaStream,
    mut poison: impl FnMut() -> CudaResult<()>,
    mut launch: impl FnMut() -> CudaResult<()>,
) -> CudaResult<TimingSummary> {
    for _ in 0..WARMUP_ITERS {
        poison()?;
        launch()?;
    }
    stream.synchronize()?;

    let start = CudaEvent::create()?;
    let end = CudaEvent::create()?;
    let mut samples = Vec::with_capacity(TIMING_ITERS);
    for _ in 0..TIMING_ITERS {
        poison()?;
        start.record(stream)?;
        launch()?;
        end.record(stream)?;
        stream.synchronize()?;
        samples.push(elapsed_time(&start, &end)?);
    }
    Ok(TimingSummary::from_milliseconds(samples))
}

// ── Kernel attributes: §15's release gate, per instantiation ──────────────────

/// What the loaded module says about one instantiation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct KernelAttributes {
    pub(super) registers: i32,
    /// `localSizeBytes`. §15 requires this to be ZERO for every release kernel:
    /// it is the per-thread local frame, which is where a spill lands.
    pub(super) local_size_bytes: usize,
    /// Statically declared shared memory. The cell file is DYNAMIC, so a release
    /// executor's own static shared use is whatever the linked image declares.
    pub(super) static_smem_bytes: usize,
    pub(super) max_threads_per_block: i32,
}

impl KernelAttributes {
    /// Query the exact instantiation. `kernel` must be a `__global__` function
    /// pointer from one of the declared kernel symbols.
    fn of(kernel: *const c_void) -> Self {
        let mut attributes = std::mem::MaybeUninit::<CudaFuncAttributes>::zeroed();
        // SAFETY: `CudaFuncAttributes` is plain data and `kernel` is a valid
        // `__global__` entry point taken from a `KernelFunction::as_ptr`.
        unsafe { cudaFuncGetAttributes(attributes.as_mut_ptr(), kernel) }
            .wrap()
            .expect("cudaFuncGetAttributes for a backward coefficient executor");
        // SAFETY: the call above initialized it.
        let attributes = unsafe { attributes.assume_init() };
        Self {
            registers: attributes.numRegs,
            local_size_bytes: attributes.localSizeBytes,
            static_smem_bytes: attributes.sharedSizeBytes,
            max_threads_per_block: attributes.maxThreadsPerBlock,
        }
    }

    /// §15: zero local-memory traffic in a release kernel.
    pub(super) fn assert_no_spills(&self, label: &str) {
        assert_eq!(
            self.local_size_bytes, 0,
            "{label}: release executors must have zero local-memory spills, \
             cudaFuncGetAttributes reports {} bytes",
            self.local_size_bytes
        );
        assert!(
            self.max_threads_per_block >= BWD_COEFF_THREADS_PER_BLOCK as i32,
            "{label}: the executor cannot host its own {BWD_COEFF_THREADS_PER_BLOCK}-thread block"
        );
    }
}

/// The attributes of the exact `(regime, fold depth, bank)` executor.
pub(super) fn executor_attributes(
    regime: BwdRegime,
    fold_depth: u8,
    bank: BwdCoeffBank,
) -> KernelAttributes {
    use super::*;
    macro_rules! attributes {
        ($function:ident, $symbol:ident) => {
            KernelAttributes::of($function($symbol).as_ptr())
        };
    }
    match (regime, fold_depth, bank) {
        (BwdRegime::R0, _, BwdCoeffBank::Constant) => {
            attributes!(GkrBwdCoeffR0ConstFunction, ab_gkr_bwd_coeff_r0_const_kernel)
        }
        (BwdRegime::R0, _, BwdCoeffBank::DevicePointer) => {
            attributes!(GkrBwdCoeffR0PtrFunction, ab_gkr_bwd_coeff_r0_ptr_kernel)
        }
        (BwdRegime::Ext, 0, BwdCoeffBank::Constant) => attributes!(
            GkrBwdCoeffExtD0ConstFunction,
            ab_gkr_bwd_coeff_ext_d0_const_kernel
        ),
        (BwdRegime::Ext, 0, BwdCoeffBank::DevicePointer) => attributes!(
            GkrBwdCoeffExtD0PtrFunction,
            ab_gkr_bwd_coeff_ext_d0_ptr_kernel
        ),
        (BwdRegime::Ext, 1, BwdCoeffBank::Constant) => attributes!(
            GkrBwdCoeffExtD1ConstFunction,
            ab_gkr_bwd_coeff_ext_d1_const_kernel
        ),
        (BwdRegime::Ext, 1, BwdCoeffBank::DevicePointer) => attributes!(
            GkrBwdCoeffExtD1PtrFunction,
            ab_gkr_bwd_coeff_ext_d1_ptr_kernel
        ),
        (BwdRegime::Ext, 2, BwdCoeffBank::Constant) => attributes!(
            GkrBwdCoeffExtD2ConstFunction,
            ab_gkr_bwd_coeff_ext_d2_const_kernel
        ),
        (BwdRegime::Ext, 2, BwdCoeffBank::DevicePointer) => attributes!(
            GkrBwdCoeffExtD2PtrFunction,
            ab_gkr_bwd_coeff_ext_d2_ptr_kernel
        ),
        (BwdRegime::Ext, 3, BwdCoeffBank::Constant) => attributes!(
            GkrBwdCoeffExtD3ConstFunction,
            ab_gkr_bwd_coeff_ext_d3_const_kernel
        ),
        (BwdRegime::Ext, 3, BwdCoeffBank::DevicePointer) => attributes!(
            GkrBwdCoeffExtD3PtrFunction,
            ab_gkr_bwd_coeff_ext_d3_ptr_kernel
        ),
        (BwdRegime::Ext, depth, _) => panic!("continuation fold depth D{depth} is outside D0..D3"),
    }
}

// ── Launch geometry, as measured ──────────────────────────────────────────────

/// The occupancy and shared-memory facts of one launch.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct LaunchGeometry {
    pub(super) rows: usize,
    pub(super) blocks: u32,
    pub(super) dynamic_smem_bytes: usize,
    pub(super) active_blocks_per_sm: i32,
    /// `active_blocks_per_sm * threads_per_block / max_threads_per_sm`.
    pub(super) theoretical_occupancy: f32,
    /// Whether the grid covers at least one full wave of the device.
    pub(super) waves: f32,
}

impl LaunchGeometry {
    pub(super) fn of(
        regime: BwdRegime,
        fold_depth: u8,
        bank: BwdCoeffBank,
        cell_budget: u32,
        rows: usize,
        device: &DeviceFacts,
    ) -> Self {
        let blocks = (rows.max(1) as u32).div_ceil(BWD_COEFF_THREADS_PER_BLOCK);
        let active_blocks_per_sm = bwd_coeff_blocks_per_sm(regime, fold_depth, bank, cell_budget)
            .expect("query backward coefficient executor occupancy");
        let per_wave = (active_blocks_per_sm.max(1) as u32) * device.multiprocessors;
        Self {
            rows,
            blocks,
            dynamic_smem_bytes: bwd_coeff_dynamic_smem_bytes(cell_budget),
            active_blocks_per_sm,
            theoretical_occupancy: active_blocks_per_sm as f32
                * BWD_COEFF_THREADS_PER_BLOCK as f32
                / device.max_threads_per_sm as f32,
            waves: blocks as f32 / per_wave as f32,
        }
    }
}

/// The device constants every occupancy number is relative to.
#[derive(Clone, Copy, Debug)]
pub(super) struct DeviceFacts {
    pub(super) multiprocessors: u32,
    pub(super) max_threads_per_sm: i32,
    pub(super) total_global_bytes: usize,
}

impl DeviceFacts {
    pub(super) fn query() -> Self {
        use era_cudart::device::{device_get_attribute, get_device};
        use era_cudart_sys::CudaDeviceAttr;
        let device = get_device().expect("active CUDA device");
        Self {
            multiprocessors: device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device)
                .expect("query MultiProcessorCount") as u32,
            max_threads_per_sm: device_get_attribute(
                CudaDeviceAttr::MaxThreadsPerMultiProcessor,
                device,
            )
            .expect("query MaxThreadsPerMultiProcessor"),
            total_global_bytes: era_cudart::device::get_device_properties(device)
                .expect("query device properties")
                .totalGlobalMem,
        }
    }

    /// Rows that fill `waves` complete waves of `active_blocks_per_sm`-deep
    /// residency. This is the sweep's saturation target.
    pub(super) fn rows_for_waves(&self, active_blocks_per_sm: i32, waves: u32) -> usize {
        (self.multiprocessors as usize)
            * (active_blocks_per_sm.max(1) as usize)
            * (waves as usize)
            * BWD_COEFF_THREADS_PER_BLOCK as usize
    }
}

// ── One measured configuration ────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub(super) struct SweepRow {
    pub(super) circuit: String,
    pub(super) layer: usize,
    pub(super) regime: ArtifactRegime,
    pub(super) round_class: BwdRoundClass,
    /// The sumcheck round the binding was realized at.
    pub(super) round: u8,
    pub(super) budget_cells: u8,
    pub(super) bank: BwdCoeffBank,
    pub(super) geometry: LaunchGeometry,
    pub(super) attributes: KernelAttributes,
    /// Whether `geometry.rows` reached the saturation target, or memory capped it.
    pub(super) saturated: bool,
    /// The compiler's exact static cost model for this program.
    pub(super) program: ProgramReport,
    pub(super) timing: TimingSummary,
    /// Present only where an exact incumbent launch exists for the coordinate.
    pub(super) incumbent: Option<TimingSummary>,
    pub(super) incumbent_sequence: &'static str,
    /// Whether this row is a PRODUCTION selection candidate. False for a
    /// diagnostic row — the published steady state shares D1's executor, so it is
    /// measured and reported but never selected on, which keeps one round class
    /// from having two winners.
    pub(super) selects: bool,
}

impl SweepRow {
    pub(super) fn coordinate(&self) -> (String, usize, BwdRoundClass) {
        (self.circuit.clone(), self.layer, self.round_class)
    }

    pub(super) fn label(&self) -> String {
        format!(
            "{} L{} {} c{}",
            self.circuit,
            self.layer,
            self.round_class.label(),
            self.budget_cells
        )
    }

    /// New over incumbent, by median. `None` where no incumbent was timed.
    pub(super) fn ratio(&self) -> Option<f32> {
        self.incumbent
            .map(|incumbent| self.timing.median_us / incumbent.median_us)
    }
}

pub(super) const CSV_HEADER: &str = "circuit,layer,regime,round_class,round,budget_cells,bank,\
rows,blocks,waves,saturated,dynamic_smem_bytes,static_smem_bytes,registers,local_spill_bytes,\
active_blocks_per_sm,theoretical_occupancy_percent,terms,program_words,program_bytes,moves,\
realized_read_bytes,read_floor_bytes,percent_above_floor,materialization_write_bytes,\
shared_loads,shared_stores,bf_ops,mixed_ops,e4_ops,source_resolutions,hits,misses,fills,evictions,\
peak_resident_lanes,median_us,min_us,incumbent_median_us,incumbent_min_us,new_over_incumbent,\
incumbent_sequence\n";

fn bank_label(bank: BwdCoeffBank) -> &'static str {
    match bank {
        BwdCoeffBank::Constant => "const",
        BwdCoeffBank::DevicePointer => "ptr",
    }
}

/// The complete per-configuration table. One row per measured configuration, in
/// the order the sweep produced them, plus nothing aggregated — aggregation over
/// round classes is exactly the mistake §13 forbids, so it is not offered here.
pub(super) fn render_sweep_csv(rows: &[SweepRow]) -> String {
    let mut output = String::from(CSV_HEADER);
    for row in rows {
        let (incumbent_median, incumbent_min) = row
            .incumbent
            .map_or((f32::NAN, f32::NAN), |t| (t.median_us, t.min_us));
        let ratio = row.ratio().unwrap_or(f32::NAN);
        writeln!(
            output,
            "{},{},{},{},{},c{},{},{},{},{:.3},{},{},{},{},{},{},{:.2},{},{},{},{},\
             {},{},{:.4},{},{},{},{},{},{},{},{},{},{},{},{},{:.3},{:.3},{:.3},{:.3},{:.6},{}",
            row.circuit,
            row.layer,
            row.regime.label(),
            row.round_class.label(),
            row.round,
            row.budget_cells,
            bank_label(row.bank),
            row.geometry.rows,
            row.geometry.blocks,
            row.geometry.waves,
            row.saturated,
            row.geometry.dynamic_smem_bytes,
            row.attributes.static_smem_bytes,
            row.attributes.registers,
            row.attributes.local_size_bytes,
            row.geometry.active_blocks_per_sm,
            row.geometry.theoretical_occupancy * 100.0,
            row.program.terms,
            row.program.words,
            row.program.bytes,
            row.program.moves,
            row.program.realized_total_read_bytes,
            row.program.total_read_floor_bytes,
            row.program.percent_above_floor(),
            row.program.materialization_write_bytes,
            row.program.shared_loads,
            row.program.shared_stores,
            row.program.bf_ops,
            row.program.mixed_ops,
            row.program.e4_ops,
            row.program.source_resolutions,
            row.program.hits,
            row.program.misses,
            row.program.fills,
            row.program.evictions,
            row.program.peak_resident_lanes,
            row.timing.median_us,
            row.timing.min_us,
            incumbent_median,
            incumbent_min,
            ratio,
            row.incumbent_sequence,
        )
        .expect("write String");
    }
    output
}

// ── Selection ─────────────────────────────────────────────────────────────────

/// One `(circuit, layer, round class)`'s measured winner, with the diagnostic
/// `c16` reference beside it.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct BudgetChoice {
    pub(super) circuit: String,
    pub(super) layer: usize,
    pub(super) round_class: BwdRoundClass,
    /// The fastest measured PRODUCTION budget — `c16` excluded, §15.
    pub(super) cells: u8,
    pub(super) median_us: f32,
    pub(super) min_us: f32,
    /// `c16`'s median for the same coordinate. Reported so the distance to the
    /// diagnostic floor is visible, never selected.
    pub(super) diagnostic_c16_median_us: f32,
    /// `c2`'s median, §15's "does the compact path lose at the lowest budget"
    /// reference point.
    pub(super) c2_median_us: f32,
    pub(super) rows: usize,
}

impl BudgetChoice {
    pub(super) fn selected(&self) -> SelectedBudget {
        SelectedBudget {
            round_class: self.round_class,
            cells: self.cells,
        }
    }
}

/// How close to the fastest median a budget must be to count as tied with it.
///
/// Not a fudge factor — a measured property of the thing being selected. The
/// executor's runtime is a STEP function of the cell budget, because the budget
/// sets dynamic shared memory and therefore blocks per SM: `add_sub` layer-0 R0
/// runs at 6 blocks/SM for c2..c7, 5 for c8..c9, 4 for c10..c12 and 3 for
/// c13..c16, and the four medians in each tier land within a few CUDA-event ticks
/// of each other while the tiers themselves are 12% apart. Selecting on the raw
/// argmin therefore names an arbitrary member of the winning tier and names a
/// different one on the next run.
///
/// So the rule is "the SMALLEST budget that is not measurably slower than the
/// fastest": same measured speed, least shared memory, and a choice that does not
/// move when the clock does. One percent is above the event timer's resolution at
/// these durations (~1 microsecond on a ~500 microsecond launch) and well below a
/// one-block occupancy step.
pub(super) const SELECTION_TIE_FRACTION: f32 = 0.01;

/// The fastest measured budget for every `(circuit, layer, round class)` the rows
/// cover, INDEPENDENTLY per round class.
///
/// `c16` is excluded from candidacy by §15 and carried alongside as a diagnostic.
/// Among budgets tied with the fastest to within [`SELECTION_TIE_FRACTION`], the
/// SMALLEST wins.
pub(super) fn select_budgets(rows: &[SweepRow]) -> Vec<BudgetChoice> {
    let mut grouped: BTreeMap<(String, usize, BwdRoundClass), Vec<&SweepRow>> = BTreeMap::new();
    for row in rows {
        grouped.entry(row.coordinate()).or_default().push(row);
    }
    grouped
        .into_iter()
        .map(|((circuit, layer, round_class), mut candidates)| {
            candidates.sort_by_key(|row| row.budget_cells);
            let diagnostic = candidates
                .iter()
                .find(|row| row.budget_cells == SELECTION_DIAGNOSTIC_CELLS)
                .map_or(f32::NAN, |row| row.timing.median_us);
            let c2 = candidates
                .iter()
                .find(|row| row.budget_cells == 2)
                .map_or(f32::NAN, |row| row.timing.median_us);
            let production = candidates
                .iter()
                .filter(|row| row.budget_cells != SELECTION_DIAGNOSTIC_CELLS)
                .collect::<Vec<_>>();
            let fastest = production
                .iter()
                .map(|row| row.timing.median_us)
                .reduce(f32::min)
                .unwrap_or_else(|| {
                    panic!("{circuit} L{layer} {} has no production candidate", round_class.label())
                });
            let threshold = fastest * (1.0 + SELECTION_TIE_FRACTION);
            // `production` is ascending by budget, so the first row within the tie
            // band IS the smallest one.
            let winner = production
                .iter()
                .find(|row| row.timing.median_us <= threshold)
                .expect("the fastest row is within its own tie band");
            BudgetChoice {
                circuit,
                layer,
                round_class,
                cells: winner.budget_cells,
                median_us: winner.timing.median_us,
                min_us: winner.timing.min_us,
                diagnostic_c16_median_us: diagnostic,
                c2_median_us: c2,
                rows: winner.geometry.rows,
            }
        })
        .collect()
}

pub(super) const SELECTION_HEADER: &str =
    "circuit,layer,round_class,selected_cells,rows,selected_median_us,selected_min_us,\
c2_median_us,c16_diagnostic_median_us,selected_over_c2,selected_over_c16\n";

pub(super) fn render_selection_csv(choices: &[BudgetChoice]) -> String {
    let mut output = String::from(SELECTION_HEADER);
    for choice in choices {
        writeln!(
            output,
            "{},{},{},c{},{},{:.3},{:.3},{:.3},{:.3},{:.6},{:.6}",
            choice.circuit,
            choice.layer,
            choice.round_class.label(),
            choice.cells,
            choice.rows,
            choice.median_us,
            choice.min_us,
            choice.c2_median_us,
            choice.diagnostic_c16_median_us,
            choice.median_us / choice.c2_median_us,
            choice.median_us / choice.diagnostic_c16_median_us,
        )
        .expect("write String");
    }
    output
}

/// Persist the selection as EXPLICIT per-round-class choices, grouped by circuit
/// and layer, and validated against §15's diagnostic exclusion.
///
/// The shape mirrors [`SelectedBudget`], which is what a `CoordinateArtifact`
/// carries — so applying this file to an artifact family is a copy, never an
/// inference.
pub(super) fn render_selection_json(choices: &[BudgetChoice]) -> String {
    use gkr_eval_isa::bwd::coeff::artifact::validate_selected_budgets;

    let mut by_coordinate: BTreeMap<(&str, usize, ArtifactRegime), Vec<SelectedBudget>> =
        BTreeMap::new();
    for choice in choices {
        by_coordinate
            .entry((
                choice.circuit.as_str(),
                choice.layer,
                choice.round_class.regime(),
            ))
            .or_default()
            .push(choice.selected());
    }

    let mut output = String::from("[\n");
    let mut first = true;
    for ((circuit, layer, regime), mut selected) in by_coordinate {
        selected.sort_by_key(|entry| entry.round_class);
        validate_selected_budgets(regime, &selected).unwrap_or_else(|error| {
            panic!("{circuit} L{layer} {} selection: {error:?}", regime.label())
        });
        if !first {
            output.push_str(",\n");
        }
        first = false;
        write!(
            output,
            "  {{ \"circuit\": {circuit:?}, \"layer\": {layer}, \"regime\": {:?}, \
             \"selected_budgets\": [",
            regime.label()
        )
        .expect("write String");
        for (index, entry) in selected.iter().enumerate() {
            if index > 0 {
                output.push_str(", ");
            }
            write!(
                output,
                "{{ \"round_class\": {:?}, \"cells\": {} }}",
                entry.round_class.label(),
                entry.cells
            )
            .expect("write String");
        }
        output.push_str("] }");
    }
    output.push_str("\n]\n");
    output
}

// ── Publication ───────────────────────────────────────────────────────────────

/// Write `contents` to `path` through a process-unique temporary, so a reader
/// never observes a half-written table.
pub(super) fn publish(path: &Path, contents: &str) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
    }
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("sweep");
    let temporary = path.with_file_name(format!(".{file_name}.{}.tmp", std::process::id()));
    std::fs::write(&temporary, contents)
        .unwrap_or_else(|error| panic!("write {}: {error}", temporary.display()));
    std::fs::rename(&temporary, path)
        .unwrap_or_else(|error| panic!("publish {}: {error}", path.display()));
}

/// Append one section to `target/gkr/bwd_coeff_profile_summary.md`, the index the
/// brief requires for the sweep CSV and NCU report paths.
pub(super) fn record_summary_section(title: &str, body: &str) {
    let path = sweep_output_path(SUMMARY_MD);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
    }
    let mut existing = std::fs::read_to_string(&path).unwrap_or_default();
    if existing.is_empty() {
        existing.push_str("# Backward coefficient-ISA GPU profile summary\n");
    }
    // Replace an earlier run's identical section rather than stacking duplicates.
    let heading = format!("\n## {title}\n");
    if let Some(start) = existing.find(&heading) {
        let tail = existing[start + heading.len()..]
            .find("\n## ")
            .map(|offset| start + heading.len() + offset)
            .unwrap_or(existing.len());
        existing.replace_range(start..tail, "");
    }
    existing.push_str(&heading);
    existing.push_str(body);
    publish(&path, &existing);
}

/// Print the per-round-class winners and the c2/c16 reference points.
pub(super) fn log_selection(tag: &str, choices: &[BudgetChoice]) {
    for choice in choices {
        eprintln!(
            "[{tag}] {} L{} {}: selected c{} median={:.3}us (c2={:.3}us, c16 diagnostic={:.3}us) rows={}",
            choice.circuit,
            choice.layer,
            choice.round_class.label(),
            choice.cells,
            choice.median_us,
            choice.c2_median_us,
            choice.diagnostic_c16_median_us,
            choice.rows,
        );
    }
}

/// A contribution-buffer poisoner: the sweep resets both halves before every
/// measured launch so a kernel that wrote nothing cannot pass as fast.
pub(super) fn poison_contributions(
    ptr: *mut E4,
    rows: usize,
    value: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::slice::DeviceSlice;
    // SAFETY: every caller supplies a live device allocation of at least
    // `2 * rows` E4 values and serializes access on `exec_stream`.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(ptr, 2 * rows) };
    crate::ops::simple::set_by_val(value, slice, context.get_exec_stream())
}

#[cfg(test)]
mod tests {
    use super::*;
    use gkr_eval_isa::bwd::coeff::artifact::{SelectionError, validate_selected_budgets};

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

    /// The pinned capture counters must tell the story the generated caveat claims
    /// they tell. A mis-pin that inverted either comparison would print a
    /// self-contradicting paragraph — a caveat whose own evidence disagrees with it
    /// is worse than no caveat — and this is what makes that a test failure.
    ///
    /// It cannot check the constants against the `.ncu-rep` files (a unit test has
    /// no profiler), so it checks the two RELATIONS the paragraph asserts. The
    /// values themselves carry a documented re-derivation command.
    #[test]
    fn the_pinned_capture_counters_support_the_caveat_they_are_quoted_for() {
        assert!(
            PINNED_DRAM_GB_NEW < PINNED_DRAM_GB_INCUMBENT,
            "the caveat's bound rests on the new lineage moving FEWER DRAM bytes"
        );
        assert!(
            PINNED_L2_MISS_SECTORS_NEW_M < PINNED_L2_MISS_SECTORS_INCUMBENT_M,
            "and on it missing L2 fewer times"
        );
        // "The model closes the gap": within a quarter of a percent, which is far
        // tighter than the ~1% the report claims the ratio is good to.
        let residual = (PINNED_MODEL_RATIO / PINNED_PROFILED_DURATION_RATIO - 1.0).abs();
        assert!(
            residual < 0.0025,
            "the instruction/IPC model must reproduce the measured duration ratio; \
             residual is {:.4}%",
            residual * 100.0
        );
        // Both ratios describe the same measured slowdown, so they must agree on
        // its sign and rough size too.
        for ratio in [PINNED_MODEL_RATIO, PINNED_PROFILED_DURATION_RATIO] {
            assert!(
                (1.0..2.0).contains(&ratio),
                "a duration ratio outside 1..2 is a pinning error, not a measurement"
            );
        }
    }

    #[test]
    fn the_sample_discipline_is_three_warmups_and_ten_samples() {
        assert_eq!(WARMUP_ITERS, 3);
        assert_eq!(TIMING_ITERS, 10);
    }

    fn row(
        circuit: &str,
        layer: usize,
        round_class: BwdRoundClass,
        cells: u8,
        median_us: f32,
    ) -> SweepRow {
        SweepRow {
            circuit: circuit.to_owned(),
            layer,
            regime: round_class.regime(),
            round_class,
            round: round_class.fold_depth().unwrap_or(0),
            budget_cells: cells,
            bank: BwdCoeffBank::Constant,
            geometry: LaunchGeometry {
                rows: 4_096,
                blocks: 32,
                dynamic_smem_bytes: usize::from(cells) * 16 * 128,
                active_blocks_per_sm: 4,
                theoretical_occupancy: 0.25,
                waves: 1.5,
            },
            attributes: KernelAttributes {
                registers: 76,
                local_size_bytes: 0,
                static_smem_bytes: 0,
                max_threads_per_block: 1_024,
            },
            saturated: true,
            program: ProgramReport {
                cells,
                terms: 100,
                total_read_floor_bytes: 1_000,
                realized_total_read_bytes: 1_200,
                cacheable_reread_bytes: 200,
                words: 300,
                bytes: 600,
                ..Default::default()
            },
            timing: TimingSummary {
                median_us,
                min_us: median_us - 1.0,
            },
            incumbent: None,
            incumbent_sequence: "-",
            selects: true,
        }
    }

    #[test]
    fn selection_is_per_round_class_and_never_aggregated_over_the_layer() {
        // R0 is fastest at c4, D1 at c8. Aggregating the layer would pick one of
        // them for both, which is exactly what §13 forbids.
        let rows = vec![
            row("add_sub", 0, BwdRoundClass::R0, 2, 30.0),
            row("add_sub", 0, BwdRoundClass::R0, 4, 10.0),
            row("add_sub", 0, BwdRoundClass::R0, 8, 20.0),
            row("add_sub", 0, BwdRoundClass::D1, 2, 40.0),
            row("add_sub", 0, BwdRoundClass::D1, 4, 25.0),
            row("add_sub", 0, BwdRoundClass::D1, 8, 12.0),
        ];
        let choices = select_budgets(&rows);
        assert_eq!(choices.len(), 2);
        assert_eq!(choices[0].round_class, BwdRoundClass::R0);
        assert_eq!(choices[0].cells, 4);
        assert_eq!(choices[1].round_class, BwdRoundClass::D1);
        assert_eq!(choices[1].cells, 8);
    }

    #[test]
    fn c16_is_reported_as_a_diagnostic_and_never_selected() {
        let rows = vec![
            row("keccak_special5", 0, BwdRoundClass::R0, 2, 90.0),
            row("keccak_special5", 0, BwdRoundClass::R0, 15, 50.0),
            // The genuinely fastest budget IS c16 here, and it still loses.
            row("keccak_special5", 0, BwdRoundClass::R0, 16, 5.0),
        ];
        let choices = select_budgets(&rows);
        assert_eq!(choices[0].cells, 15);
        assert_eq!(choices[0].diagnostic_c16_median_us, 5.0);
        assert_eq!(
            validate_selected_budgets(ArtifactRegime::R0, &[choices[0].selected()]),
            Ok(())
        );
        assert_eq!(
            validate_selected_budgets(
                ArtifactRegime::R0,
                &[SelectedBudget {
                    round_class: BwdRoundClass::R0,
                    cells: 16
                }]
            ),
            Err(SelectionError::DiagnosticBudgetSelected {
                round_class: BwdRoundClass::R0
            })
        );
    }

    #[test]
    fn a_tie_breaks_to_the_smaller_budget() {
        let rows = vec![
            row("shift_binop", 3, BwdRoundClass::D3, 5, 12.0),
            row("shift_binop", 3, BwdRoundClass::D3, 9, 12.0),
        ];
        assert_eq!(select_budgets(&rows)[0].cells, 5);
    }

    #[test]
    fn a_budget_within_the_tie_band_of_the_fastest_wins_on_size() {
        // c9 is the raw argmin, but c4 is 0.5% behind it — inside the band — and
        // c3 is 4% behind, outside. So the selection is c4, and it stays c4 when
        // the whole run drifts by a constant factor.
        let rows = vec![
            row("mem_word_only", 1, BwdRoundClass::D1, 3, 104.0),
            row("mem_word_only", 1, BwdRoundClass::D1, 4, 100.5),
            row("mem_word_only", 1, BwdRoundClass::D1, 9, 100.0),
        ];
        assert_eq!(select_budgets(&rows)[0].cells, 4);

        let drifted = rows
            .iter()
            .map(|entry| {
                let mut copy = entry.clone();
                copy.timing.median_us *= 1.07;
                copy
            })
            .collect::<Vec<_>>();
        assert_eq!(select_budgets(&drifted)[0].cells, 4);
    }

    #[test]
    fn a_budget_outside_the_tie_band_never_wins_on_size() {
        let rows = vec![
            row("keccak_special5", 0, BwdRoundClass::D2, 2, 200.0),
            row("keccak_special5", 0, BwdRoundClass::D2, 10, 100.0),
        ];
        assert_eq!(select_budgets(&rows)[0].cells, 10);
    }

    #[test]
    fn the_csv_names_every_required_column_and_keeps_round_classes_distinct() {
        let mut rows = vec![
            row("add_sub", 0, BwdRoundClass::R0, 2, 30.0),
            row("add_sub", 0, BwdRoundClass::D2, 2, 40.0),
        ];
        rows[0].incumbent = Some(TimingSummary {
            median_us: 15.0,
            min_us: 14.0,
        });
        rows[0].incumbent_sequence = "compact evaluator launcher";
        let rendered = render_sweep_csv(&rows);
        for column in [
            "median_us",
            "min_us",
            "realized_read_bytes",
            "shared_loads",
            "shared_stores",
            "registers",
            "local_spill_bytes",
            "dynamic_smem_bytes",
            "theoretical_occupancy_percent",
            "program_words",
            "new_over_incumbent",
        ] {
            assert!(rendered.contains(column), "missing column {column}");
        }
        assert!(rendered.contains("add_sub,0,R0,R0,0,c2,const"));
        assert!(rendered.contains("add_sub,0,Ext,D2,2,c2,const"));
        assert!(rendered.contains("2.000000,compact evaluator launcher"));
        assert_eq!(rows[0].ratio(), Some(2.0));
        assert_eq!(rows[1].ratio(), None);
    }

    #[test]
    fn the_selection_json_is_grouped_by_coordinate_and_ascending_by_class() {
        let rows = vec![
            row("add_sub", 0, BwdRoundClass::D3, 7, 10.0),
            row("add_sub", 0, BwdRoundClass::D1, 4, 10.0),
            row("add_sub", 0, BwdRoundClass::R0, 3, 10.0),
        ];
        let json = render_selection_json(&select_budgets(&rows));
        let r0 = json.find("\"R0\"").expect("R0 class");
        let d1 = json.find("\"D1\"").expect("D1 class");
        let d3 = json.find("\"D3\"").expect("D3 class");
        assert!(r0 < d1 && d1 < d3, "classes must be ascending: {json}");
        assert!(json.contains("\"regime\": \"Ext\""));
        assert!(json.contains("\"regime\": \"R0\""));
        assert!(json.contains("\"cells\": 4"));
    }

    fn clean_attributes() -> KernelAttributes {
        KernelAttributes {
            registers: 76,
            local_size_bytes: 0,
            static_smem_bytes: 0,
            max_threads_per_block: 1_024,
        }
    }

    #[test]
    fn a_release_executor_without_spills_passes_the_gate() {
        clean_attributes().assert_no_spills("clean");
    }

    #[test]
    #[should_panic(expected = "zero local-memory spills")]
    fn one_spilled_byte_fails_the_release_gate() {
        KernelAttributes {
            local_size_bytes: 8,
            ..clean_attributes()
        }
        .assert_no_spills("spilling");
    }

    #[test]
    #[should_panic(expected = "cannot host its own")]
    fn an_executor_that_cannot_host_its_own_block_fails_the_gate() {
        KernelAttributes {
            max_threads_per_block: 64,
            ..clean_attributes()
        }
        .assert_no_spills("too narrow");
    }

    #[test]
    fn publication_writes_the_whole_table_to_its_own_path() {
        let path = std::env::temp_dir().join(format!(
            "bwd-coeff-sweep-{}-{}.csv",
            std::process::id(),
            std::thread::current().name().unwrap_or("report-test")
        ));
        let rows = vec![row("add_sub", 0, BwdRoundClass::R0, 2, 20.0)];
        let rendered = render_sweep_csv(&rows);
        publish(&path, &rendered);
        assert_eq!(
            std::fs::read_to_string(&path).expect("published report"),
            rendered
        );
        std::fs::remove_file(path).expect("remove published report");
    }
}
