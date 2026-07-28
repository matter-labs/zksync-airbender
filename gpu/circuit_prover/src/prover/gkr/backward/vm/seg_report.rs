//! Task 9's spike harness for the SEGMENTED lean VM: interleaved paired timing
//! against the incumbent compact evaluator, the Stage-A `(epilogue, K)` matrix,
//! and the launch-attribute probe the spec's register gate is stated in terms of.
//!
//! # What this is, and what it deliberately is not
//!
//! It is a finite MATRIX, not a search. Every coordinate is enumerated up front —
//! `K` × epilogue × coefficient loader × program source × `D2Policy` — every cell
//! is probed for launchability BEFORE it is timed, and a cell the compiled kernel
//! cannot host is RECORDED as unlaunchable rather than skipped. Nothing here
//! selects a production configuration; it produces the table the audit reads.
//!
//! # The measurement protocol (normative, from the plan)
//!
//!   * [`SEG_WARMUP_ITERS`] warmups and [`SEG_TIMING_ITERS`] timed samples PER
//!     SIDE, alternating candidate/incumbent inside one loop — so a clock or
//!     thermal drift moves both sides together instead of landing on whichever was
//!     measured second.
//!   * The statistic is the MEDIAN RATIO with a 95% percentile bootstrap CI over
//!     resampled PAIRS ([`SEG_BOOTSTRAP_RESAMPLES`] resamples, seeded, so the
//!     interval is reproducible from the same samples).
//!   * **Inversion is `ci_high < 1.0`.** An interval straddling 1.0 means the
//!     deficit CLOSED; it does not mean it inverted, and
//!     [`RatioEstimate::inverts`] is the only place that judgement is made.
//!   * Nothing is poisoned or read back inside a timed loop. The parity ladder's
//!     per-launch poison + D2H sync is correctness hygiene and costs milliseconds
//!     per launch; a timing loop that paid it would be measuring the harness.
//!
//! # How a timed configuration is certified
//!
//! Every timed configuration is parity-checked first, and the check is a
//! DIFFERENT, small cell of the same shape:
//!
//!   1. a PARITY TWIN at [`SEG_PARITY_ROWS`] rows (not a multiple of 32, so the
//!      dead-lane clamp runs) is launched at exactly the shape about to be timed
//!      and compared per row against BOTH CPU oracles — `interpret_coeff_layer`
//!      and `interpret_lean_program` at this `K` — times the host mirror of the
//!      device's own eq;
//!   2. the TIMED cell then runs one preflight launch over poisoned
//!      contributions, and a bounded prefix of its output must be free of poison
//!      AND bit-identical to the cell's reference shape.
//!
//! Rung 1 is the value certificate; rung 2 is what makes it a statement about the
//! rows actually timed, since a full oracle at eight million rows is not
//! computable on the host. Both are required before a row's timing counts, and a
//! row records which of them it passed.
//!
//! # `--features bench`
//!
//! Gated exactly like [`report`](super::report) and [`seg_gpu_tests`](super::seg_gpu_tests):
//! a default `cargo test -p gpu_circuit_prover` compiles none of it. The GPU
//! drivers are additionally `#[ignore]`d.
//!
//! ```text
//! cargo +nightly-2026-02-10 test -p gpu_circuit_prover --features bench --release --no-run
//! .agents/bin/with_gpu_lock.sh <binary> --exact <test> --ignored --nocapture
//! ```

use std::ffi::c_void;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::execution::KernelFunction;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaFuncGetAttributes, CudaFuncAttributes};

use super::seg::{
    bwd_seg_acc_blocks_per_sm, bwd_seg_acc_dynamic_smem_bytes, bwd_seg_acc_entry_point,
    bwd_seg_blocks_per_sm, bwd_seg_entry_point, bwd_seg_epilogue_smem_bytes, launch_bwd_seg,
    launch_bwd_seg_acc, BwdSegAccPlacement, BwdSegEpilogue, BWD_SEG_ACC_RUNG_EPILOGUE,
};
use super::seg_desc::BWD_SEG_MAX_K;
use super::seg_lower::{
    lower_bwd_seg, BwdSegLaunchDesc, BwdSegLowerError, BwdSegSetup, CoeffMode, D2Policy,
    ListWorkStats, ProgramMode,
};
use crate::primitives::field::E4;
use crate::primitives::utils::WARP_SIZE;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::gkr::backward::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};
use crate::prover::ProverContext;
use crate::upstream::{BwdRegime, Field, FieldExtension};

// The INCUMBENT's `__constant__` coefficient symbol, declared here because this
// harness is the only thing in the segmented lineage that touches it: the paired
// A/B timing has to stage the incumbent's own bank before timing its launch. The
// segmented executor reads `ab_gkr_bwd_seg_coeff_bank` and nothing else.
era_cudart_sys::cuda_struct_and_stub! {
    static ab_gkr_flat_coefficients: [E4; FLAT_CONST_MAX];
}

// ── The protocol's constants ─────────────────────────────────────────────────

/// Untimed launches per side before the first sample. The plan's floor is five.
pub(super) const SEG_WARMUP_ITERS: usize = 5;
/// Timed samples PER SIDE. The plan's floor is thirty; thirty-two is that floor
/// with headroom, and an even count so the median averages two real samples
/// rather than resting on one.
pub(super) const SEG_TIMING_ITERS: usize = 32;
/// Bootstrap resamples behind every published interval.
pub(super) const SEG_BOOTSTRAP_RESAMPLES: usize = 10_000;
/// Seeded, so re-deriving the interval from the same samples gives the same
/// numbers. A CI that moves when nothing was measured again is not evidence.
pub(super) const SEG_BOOTSTRAP_SEED: u64 = 0x5E67_1EA1_0000_0009;
/// Two-sided 95%.
pub(super) const SEG_CI_ALPHA: f64 = 0.05;

/// Rows the parity twin of every timed cell evaluates.
///
/// Deliberately NOT a multiple of 32: the last tile is partial, so the dead-lane
/// clamp runs in every parity launch rather than in a special case.
pub(super) const SEG_PARITY_ROWS: usize = 200;

const _: () = {
    assert!(SEG_TIMING_ITERS >= 30);
    assert!(SEG_WARMUP_ITERS >= 5);
    assert!(SEG_PARITY_ROWS % 32 != 0);
};

/// Contribution rows compared for bit-identity on a TIMED cell.
///
/// A configuration that diverges diverges on essentially every row — the axes here
/// are reduction shape and list count, not data — so a bounded prefix of each half
/// is enough, and downloading two halves of eight million E4 values per cell is
/// not.
pub(super) const SEG_IDENTITY_SAMPLE_ROWS: usize = 1 << 13;

/// The certification window a cell of `rows` rows actually uses.
///
/// [`SEG_IDENTITY_SAMPLE_ROWS`], except that it never takes more than HALF the
/// cell. The head window is `[0, sample)` and the tail window is
/// `[rows - sample, rows)`, so a sample wider than half the cell would make the
/// two overlap — at which point the tail check is reading rows the head check
/// already covered and `SegCell::preflight`'s self-proving `head != tail`
/// assertion fails on a cell that is perfectly correct.
///
/// Above `2 * SEG_IDENTITY_SAMPLE_ROWS` rows this is the constant, so every cell
/// the Stage-A matrix and the parity ladder measure is unaffected. It exists for
/// the CORPUS SWEEP, whose heaviest coordinates fit only a few thousand rows
/// inside the per-cell backing budget: those are recorded as below the timing
/// floor, but they are still certified, and certifying them must not depend on
/// the floor.
pub(super) fn identity_sample_rows(rows: usize) -> usize {
    SEG_IDENTITY_SAMPLE_ROWS.min(rows / 2)
}

/// Everything this harness writes lands under `target/`, which is git-ignored on
/// purpose: these are machine measurements, not repository content.
pub(super) const SEG_OUTPUT_DIR: &str = "target/gkr/seg";
pub(super) const SEG_MATRIX_CSV: &str = "seg_stage_a_matrix.csv";
pub(super) const SEG_SUMMARY_MD: &str = "seg_spike_summary.md";

/// The NVTX range the `ncu` workflow captures.
///
/// `ncu --nvtx-include` matches the literal `Domain@Range` string, DOMAIN FIRST.
/// The reversed order matches nothing and `ncu` answers `No kernels were profiled`
/// instead of failing, which is how this plan produced a vacuous profiling run
/// once already. (`nsys --nvtx-capture` takes the opposite order.)
pub(super) const SEG_NVTX_DOMAIN: &str = "gpu_circuit_prover.tests";
pub(super) const SEG_NVTX_MESSAGE: &str = "test.gpu.bwd_seg.spike";
/// The incumbent's own range, so the two sides are selected by NVTX rather than by
/// a launch-skip count that drifts with the warmup constant.
pub(super) const SEG_NVTX_INCUMBENT_MESSAGE: &str = "test.gpu.bwd_seg.incumbent";

pub(super) fn seg_output_path(file: &str) -> PathBuf {
    PathBuf::from(SEG_OUTPUT_DIR).join(file)
}

/// Write `contents` through a process-unique temporary, so a reader never observes
/// a half-written table.
pub(super) fn publish(path: &Path, contents: &str) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("create {}: {error}", parent.display()));
    }
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("seg-report");
    let temporary = path.with_file_name(format!(".{name}.{}.tmp", std::process::id()));
    std::fs::write(&temporary, contents)
        .unwrap_or_else(|error| panic!("write {}: {error}", temporary.display()));
    std::fs::rename(&temporary, path)
        .unwrap_or_else(|error| panic!("publish {}: {error}", path.display()));
}

// ── Statistics ───────────────────────────────────────────────────────────────

/// A deterministic 64-bit generator, so a published interval is reproducible.
///
/// SplitMix64, written out rather than pulled in: the harness needs uniform
/// indices into a sample vector and nothing else, and a seeded bootstrap whose
/// generator is a dependency version is a CI that can move without a measurement.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A uniform index in `0..n`, by Lemire's multiply-shift. `n` must be nonzero.
    fn below(&mut self, n: usize) -> usize {
        ((u128::from(self.next_u64()) * (n as u128)) >> 64) as usize
    }
}

/// The median of an unsorted sample vector, by copy.
pub(super) fn median(samples: &[f64]) -> f64 {
    assert!(!samples.is_empty(), "a median needs at least one sample");
    let mut sorted = samples.to_vec();
    sorted.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite CUDA timing"));
    median_of_sorted(&sorted)
}

fn median_of_sorted(sorted: &[f64]) -> f64 {
    let middle = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        (sorted[middle - 1] + sorted[middle]) / 2.0
    } else {
        sorted[middle]
    }
}

/// The candidate/incumbent ratio with its interval, and the ONE place the plan's
/// inversion rule is evaluated.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct RatioEstimate {
    pub(super) median_ratio: f64,
    pub(super) ci_low: f64,
    pub(super) ci_high: f64,
}

impl RatioEstimate {
    /// The plan's rule, verbatim: the deficit is INVERTED only when the whole
    /// interval sits below one. An interval containing 1.0 means the two are
    /// indistinguishable — the deficit CLOSED — and closing is not inverting.
    pub(super) fn inverts(&self) -> bool {
        self.ci_high < 1.0
    }

    /// The complementary reading: the candidate is measurably SLOWER.
    pub(super) fn regresses(&self) -> bool {
        self.ci_low > 1.0
    }

    pub(super) fn verdict(&self) -> &'static str {
        if self.inverts() {
            "INVERTED"
        } else if self.regresses() {
            "still-behind"
        } else {
            "closed (CI spans 1.0)"
        }
    }
}

/// One interleaved measurement: the two sides' per-sample microseconds, paired by
/// index because sample `i` of each side was taken adjacent in time.
#[derive(Clone, Debug)]
pub(super) struct PairedSamples {
    pub(super) candidate_us: Vec<f64>,
    pub(super) incumbent_us: Vec<f64>,
}

impl PairedSamples {
    pub(super) fn candidate_median(&self) -> f64 {
        median(&self.candidate_us)
    }

    pub(super) fn incumbent_median(&self) -> f64 {
        median(&self.incumbent_us)
    }

    pub(super) fn candidate_min(&self) -> f64 {
        self.candidate_us.iter().copied().fold(f64::MAX, f64::min)
    }

    pub(super) fn incumbent_min(&self) -> f64 {
        self.incumbent_us.iter().copied().fold(f64::MAX, f64::min)
    }

    /// The median ratio and its percentile bootstrap interval, resampling PAIRS.
    ///
    /// Pairs rather than each side independently: the two sides share a clock, a
    /// thermal state and a memory state at every index, and resampling them apart
    /// would throw that pairing away and widen the interval with variance the
    /// design deliberately removed.
    pub(super) fn estimate(&self) -> RatioEstimate {
        assert_eq!(
            self.candidate_us.len(),
            self.incumbent_us.len(),
            "interleaved timing produces one sample per side per iteration"
        );
        let n = self.candidate_us.len();
        assert!(n >= 2, "a bootstrap needs at least two pairs");
        let point = self.candidate_median() / self.incumbent_median();

        let mut rng = SplitMix64(SEG_BOOTSTRAP_SEED);
        let mut ratios = Vec::with_capacity(SEG_BOOTSTRAP_RESAMPLES);
        let mut candidate = vec![0.0f64; n];
        let mut incumbent = vec![0.0f64; n];
        for _ in 0..SEG_BOOTSTRAP_RESAMPLES {
            for slot in 0..n {
                let index = rng.below(n);
                candidate[slot] = self.candidate_us[index];
                incumbent[slot] = self.incumbent_us[index];
            }
            candidate.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite sample"));
            incumbent.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite sample"));
            ratios.push(median_of_sorted(&candidate) / median_of_sorted(&incumbent));
        }
        ratios.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite ratio"));
        let low = percentile(&ratios, SEG_CI_ALPHA / 2.0);
        let high = percentile(&ratios, 1.0 - SEG_CI_ALPHA / 2.0);
        RatioEstimate {
            median_ratio: point,
            ci_low: low,
            ci_high: high,
        }
    }
}

/// The `q`-quantile of an ascending vector, by nearest rank.
fn percentile(sorted: &[f64], q: f64) -> f64 {
    assert!(!sorted.is_empty());
    let rank = (q * sorted.len() as f64).floor() as usize;
    sorted[rank.min(sorted.len() - 1)]
}

// ── Timing ───────────────────────────────────────────────────────────────────

/// Interleaved paired timing: warmups on both sides, then
/// [`SEG_TIMING_ITERS`] iterations of `candidate` then `incumbent`, each inside its
/// own event pair.
///
/// Neither closure may poison, download or synchronize: the loop's cost must be the
/// kernels' cost. Callers stage everything a launch reads BEFORE this is entered.
pub(super) fn time_paired(
    stream: &CudaStream,
    mut candidate: impl FnMut() -> CudaResult<()>,
    mut incumbent: impl FnMut() -> CudaResult<()>,
) -> CudaResult<PairedSamples> {
    for _ in 0..SEG_WARMUP_ITERS {
        candidate()?;
        incumbent()?;
    }
    stream.synchronize()?;

    let start = CudaEvent::create()?;
    let end = CudaEvent::create()?;
    let mut candidate_us = Vec::with_capacity(SEG_TIMING_ITERS);
    let mut incumbent_us = Vec::with_capacity(SEG_TIMING_ITERS);
    for _ in 0..SEG_TIMING_ITERS {
        start.record(stream)?;
        candidate()?;
        end.record(stream)?;
        stream.synchronize()?;
        candidate_us.push(f64::from(elapsed_time(&start, &end)?) * 1_000.0);

        start.record(stream)?;
        incumbent()?;
        end.record(stream)?;
        stream.synchronize()?;
        incumbent_us.push(f64::from(elapsed_time(&start, &end)?) * 1_000.0);
    }
    Ok(PairedSamples {
        candidate_us,
        incumbent_us,
    })
}

/// One side alone, same warmup and sample discipline. Used where the coordinate has
/// no incumbent launch to pair against — the matrix still records a wall time for
/// every cell.
pub(super) fn time_solo(
    stream: &CudaStream,
    mut launch: impl FnMut() -> CudaResult<()>,
) -> CudaResult<Vec<f64>> {
    for _ in 0..SEG_WARMUP_ITERS {
        launch()?;
    }
    stream.synchronize()?;
    let start = CudaEvent::create()?;
    let end = CudaEvent::create()?;
    let mut samples = Vec::with_capacity(SEG_TIMING_ITERS);
    for _ in 0..SEG_TIMING_ITERS {
        start.record(stream)?;
        launch()?;
        end.record(stream)?;
        stream.synchronize()?;
        samples.push(f64::from(elapsed_time(&start, &end)?) * 1_000.0);
    }
    Ok(samples)
}

// ── Kernel attributes: the spec's register and spill gate, per instantiation ──

/// What the loaded module says about one instantiation.
///
/// Self-contained rather than borrowed from the cell-era [`report`](super::report):
/// that module is retired with the cell executor, and this lineage's gate is a
/// different one — `max_threads_per_block` has to admit `32 * k`, not a fixed
/// 128-thread block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SegKernelAttributes {
    pub(super) registers: i32,
    /// `localSizeBytes`: the per-thread local frame, which is where a spill lands.
    /// The spec's hard gate is that it is ZERO.
    pub(super) local_size_bytes: usize,
    pub(super) static_smem_bytes: usize,
    pub(super) max_threads_per_block: i32,
}

impl SegKernelAttributes {
    fn of(kernel: *const c_void) -> Self {
        let mut attributes = std::mem::MaybeUninit::<CudaFuncAttributes>::zeroed();
        // SAFETY: `CudaFuncAttributes` is plain data and `kernel` is a valid
        // `__global__` entry point from `bwd_seg_entry_point`, which routes through
        // the launcher's own symbol table.
        unsafe { cudaFuncGetAttributes(attributes.as_mut_ptr(), kernel) }
            .wrap()
            .expect("cudaFuncGetAttributes for a segmented lean executor");
        // SAFETY: the call above initialized it.
        let attributes = unsafe { attributes.assume_init() };
        Self {
            registers: attributes.numRegs,
            local_size_bytes: attributes.localSizeBytes,
            static_smem_bytes: attributes.sharedSizeBytes,
            max_threads_per_block: attributes.maxThreadsPerBlock,
        }
    }

    /// The spec's spill gate. Asserted per instantiation against the LOADED module,
    /// never read off a build log.
    pub(super) fn assert_no_spills(&self, label: &str) {
        assert_eq!(
            self.local_size_bytes, 0,
            "{label}: a segmented executor must have zero local-memory spills, \
             cudaFuncGetAttributes reports {} bytes",
            self.local_size_bytes
        );
    }

    /// Whether the compiled image can host a `32 * k`-thread block at all.
    ///
    /// This is the SAME fact `bwd_seg_blocks_per_sm` answers zero for, from the
    /// other side: `__launch_bounds__` is unset by design, so a family needing more
    /// than `65536 / (32 * k)` registers per thread simply cannot run that block.
    pub(super) fn hosts(&self, k: u32) -> bool {
        self.max_threads_per_block >= (k * WARP_SIZE) as i32
    }
}

/// The attributes of the exact `(regime, program, loader, epilogue)` executor.
pub(super) fn seg_attributes(
    regime: BwdRegime,
    program: ProgramMode,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
) -> SegKernelAttributes {
    SegKernelAttributes::of(bwd_seg_entry_point(regime, program, coeff, epilogue))
}

/// The attributes of the exact executor a SHAPE names, register placement or
/// Stage-B rung. One entry point per shape, routed through the launcher's own
/// symbol tables in both cases.
pub(super) fn shape_attributes(regime: BwdRegime, shape: SegShape) -> SegKernelAttributes {
    match shape.acc {
        None => seg_attributes(regime, shape.program, shape.coeff, shape.epilogue),
        Some(placement) => SegKernelAttributes::of(bwd_seg_acc_entry_point(regime, placement)),
    }
}

/// A bare entry point as a [`KernelFunction`].
///
/// The macro-generated `…Function` wrappers hold their signature in a private tuple
/// field, so a kernel declared in another module cannot be wrapped from here. Both
/// queries this module makes of the incumbent — `cudaFuncGetAttributes` and the
/// occupancy API — need only the entry-point address, and `Signature = ()` makes
/// `KernelFunction::launch` uncallable, which is the point: nothing may launch
/// through this.
pub(super) struct RawKernel(pub(super) *const c_void);

impl KernelFunction for RawKernel {
    type Signature = ();

    fn as_ptr(&self) -> *const c_void {
        self.0
    }
}

/// The INCUMBENT `add_sub` layer-0 R0 entry point — the compact flat constant
/// evaluator the plan names as the A/B baseline.
pub(super) fn incumbent_r0_kernel() -> RawKernel {
    use crate::prover::gkr::backward::compact::ab_gkr_main_round0_flat_constant_compact_e4_kernel;
    RawKernel(ab_gkr_main_round0_flat_constant_compact_e4_kernel as *const c_void)
}

pub(super) fn incumbent_r0_attributes() -> SegKernelAttributes {
    SegKernelAttributes::of(incumbent_r0_kernel().as_ptr())
}

/// The incumbent's resident blocks per SM — PINNED from the profiler capture, not
/// queried, and this is the one number in the report whose provenance differs from
/// its neighbours.
///
/// The incumbent is compiled `__launch_bounds__(128, 8)` and
/// `cudaOccupancyMaxActiveBlocksPerMultiprocessor` returns that `minBlocks` HINT
/// (8, i.e. a 64-register cap) rather than what its 44 allocated registers permit
/// (10). The capture measured 83.333% THEORETICAL against 81.57% ACHIEVED, and
/// 81.57% is above the 66.67% ceiling 8 blocks would impose, so more than 8 were
/// resident. Our own executors set no `__launch_bounds__` at all, so nothing
/// contaminates the API for them and they are queried.
///
/// [`the_incumbent_occupancy_pin_still_holds`] asserts the premise and the reason,
/// so a recompile that changes the allocation invalidates the pin loudly.
pub(super) const PINNED_INCUMBENT_R0_BLOCKS_PER_SM: i32 = 10;
pub(super) const PINNED_INCUMBENT_R0_REGISTERS: i32 = 44;
pub(super) const INCUMBENT_R0_LAUNCH_BOUNDS_MIN_BLOCKS: i32 = 8;
pub(super) const INCUMBENT_R0_THREADS_PER_BLOCK: u32 = 128;

/// The incumbent launch sequence the ratio is against, named in every artifact so a
/// reader knows exactly what was compared.
pub(super) const INCUMBENT_R0_SEQUENCE: &str = "compact flat round-0 constant evaluator \
(ab_gkr_main_round0_flat_constant_compact_e4_kernel)";

/// Short form of [`INCUMBENT_R0_SEQUENCE`] for the ratio-baseline column.
pub(super) const INCUMBENT_R0_BASELINE_LABEL: &str = "incumbent-compact-r0";
/// The Stage-B ratio baseline: each rung's own register-placement twin, at the
/// same `K`, epilogue, loader, cell and rows.
pub(super) const STAGE_B_TWIN_BASELINE_LABEL: &str = "register-twin";

// ── Device facts ─────────────────────────────────────────────────────────────

/// The device constants every occupancy number is relative to.
#[derive(Clone, Copy, Debug)]
pub(super) struct SegDeviceFacts {
    pub(super) multiprocessors: u32,
    pub(super) max_threads_per_sm: i32,
    pub(super) max_registers_per_sm: i32,
    pub(super) max_shared_per_sm: i32,
}

impl SegDeviceFacts {
    pub(super) fn query() -> Self {
        use era_cudart::device::{device_get_attribute, get_device};
        use era_cudart_sys::CudaDeviceAttr;
        let device = get_device().expect("active CUDA device");
        let attribute = |which| device_get_attribute(which, device).expect("device attribute");
        Self {
            multiprocessors: attribute(CudaDeviceAttr::MultiProcessorCount) as u32,
            max_threads_per_sm: attribute(CudaDeviceAttr::MaxThreadsPerMultiProcessor),
            max_registers_per_sm: attribute(CudaDeviceAttr::MaxRegistersPerMultiprocessor),
            max_shared_per_sm: attribute(CudaDeviceAttr::MaxSharedMemoryPerMultiprocessor),
        }
    }

    /// Theoretical occupancy of `blocks` resident blocks of `32 * k` threads.
    pub(super) fn occupancy(&self, blocks: i32, k: u32) -> f64 {
        f64::from(blocks) * f64::from(k * WARP_SIZE) / f64::from(self.max_threads_per_sm)
    }
}

// ── The host mirror of the device's own eq ───────────────────────────────────

/// `gkr_compute_eq_inline`'s host twin, over the SAME factored state the launch
/// reads.
///
/// Downloaded rather than recomputed: the three slabs are built on the device by
/// the real `launch_build_eq_high_and_low_groups_from_point`, so a host
/// reimplementation of the BUILD would be a second oracle for a quantity that is
/// not under test. Only the per-row COMBINATION is mirrored here, and it is
/// mirrored expression for expression from `support/eq_inline.cuh:15-26`.
pub(super) struct HostEq {
    high: [Vec<E4>; 2],
    low: Vec<E4>,
    sizes: GkrEqSizes,
}

impl HostEq {
    pub(super) fn download(eq_low: *const E4, sizes: GkrEqSizes, context: &ProverContext) -> Self {
        use crate::prover::gkr::backward::get_eq_high_constant_device_ptr;
        let mut high_flat = vec![E4::ZERO; GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN];
        // SAFETY: `get_eq_high_constant_device_ptr` is the address of the
        // `ab_gkr_eq_high` symbol, whose declared extent is exactly this many E4
        // values; the slice is read-only and used for one copy.
        let high_device = unsafe {
            DeviceSlice::from_raw_parts(
                get_eq_high_constant_device_ptr() as *const E4,
                high_flat.len(),
            )
        };
        memory_copy_async(&mut high_flat[..], high_device, context.get_exec_stream())
            .expect("eq-high D2H");
        let mut low = vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN];
        // SAFETY: the caller supplies the live low-group table, whose length is the
        // group table length by construction.
        let low_device = unsafe { DeviceSlice::from_raw_parts(eq_low, low.len()) };
        memory_copy_async(&mut low[..], low_device, context.get_exec_stream()).expect("eq-low D2H");
        context
            .get_exec_stream()
            .synchronize()
            .expect("eq mirror sync");
        let (first, second) = high_flat.split_at(GKR_EQ_GROUP_TABLE_LEN);
        Self {
            high: [first.to_vec(), second.to_vec()],
            low,
            sizes,
        }
    }

    /// `eq(row)`, exactly as the kernel computes it.
    pub(super) fn at(&self, row: usize) -> E4 {
        let row = row as u32;
        let shift1 = self.sizes.low;
        let shift0 = self.sizes.low + self.sizes.high[1];
        let hi0 = ((row >> shift0) & ((1u32 << self.sizes.high[0]) - 1)) as usize;
        let hi1 = ((row >> shift1) & ((1u32 << self.sizes.high[1]) - 1)) as usize;
        let lo = (row & ((1u32 << self.sizes.low) - 1)) as usize;
        let mut acc = self.high[0][hi0];
        acc.mul_assign(&self.high[1][hi1]);
        acc.mul_assign(&self.low[lo]);
        acc
    }
}

// ── One matrix coordinate ────────────────────────────────────────────────────

/// The four axes a launch is specialized on, beyond the round its cell fixes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SegShape {
    pub(super) k: usize,
    pub(super) coeff: CoeffMode,
    pub(super) program: ProgramMode,
    pub(super) epilogue: BwdSegEpilogue,
    /// `None` is the fifteen release symbols' placement: both accumulators in
    /// registers. `Some` selects a Stage-B rung, which exists only on the Stage-A
    /// winner's epilogue and loader.
    pub(super) acc: Option<BwdSegAccPlacement>,
}

impl SegShape {
    /// A register-placement shape.
    pub(super) fn regs(
        k: usize,
        coeff: CoeffMode,
        program: ProgramMode,
        epilogue: BwdSegEpilogue,
    ) -> Self {
        Self {
            k,
            coeff,
            program,
            epilogue,
            acc: None,
        }
    }

    /// A Stage-B rung shape. The loader and epilogue are FIXED by what is
    /// compiled, so they are not parameters — asking for a rung on another
    /// epilogue would name a symbol that does not exist.
    pub(super) fn rung(k: usize, placement: BwdSegAccPlacement) -> Self {
        Self {
            k,
            coeff: CoeffMode::Constant,
            program: ProgramMode::Inline,
            epilogue: BWD_SEG_ACC_RUNG_EPILOGUE,
            acc: Some(placement),
        }
    }

    pub(super) fn acc_label(&self) -> &'static str {
        match self.acc {
            None => "registers",
            Some(placement) => placement.label(),
        }
    }

    pub(super) fn label(&self) -> String {
        format!(
            "K{} {} {} {} {}",
            self.k,
            coeff_label(self.coeff),
            program_label(self.program),
            epilogue_label(self.epilogue),
            self.acc_label(),
        )
    }
}

pub(super) fn epilogue_label(epilogue: BwdSegEpilogue) -> &'static str {
    match epilogue {
        BwdSegEpilogue::Staged => "staged",
        BwdSegEpilogue::Plane => "plane",
        BwdSegEpilogue::Wide => "wide",
    }
}

pub(super) fn coeff_label(coeff: CoeffMode) -> &'static str {
    match coeff {
        CoeffMode::Constant => "const",
        CoeffMode::DevPtr => "ptr",
    }
}

pub(super) fn program_label(program: ProgramMode) -> &'static str {
    match program {
        ProgramMode::Inline => "inline",
        ProgramMode::DevPtr => "devptr",
    }
}

pub(super) fn d2_label(d2: D2Policy) -> &'static str {
    match d2 {
        D2Policy::Inline => "inline",
        D2Policy::Materialize => "materialize",
    }
}

/// How a row's value was certified before its timing was allowed to count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegParity {
    /// Both CPU oracles on the parity twin, plus prefix identity on the timed cell.
    OraclesAndIdentity,
    /// Both CPU oracles on the parity twin; this row IS the timed cell's identity
    /// reference, so there is nothing yet to compare it against.
    OraclesAndReference,
    /// The cell could not be launched at all, so nothing was timed and nothing was
    /// certified.
    Unlaunchable,
}

impl SegParity {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::OraclesAndIdentity => "oracles+identity",
            Self::OraclesAndReference => "oracles+reference",
            Self::Unlaunchable => "unlaunchable",
        }
    }
}

/// One measured (or explicitly unmeasurable) matrix coordinate.
#[derive(Clone, Debug)]
pub(super) struct SegMatrixRow {
    pub(super) benchmark: String,
    pub(super) circuit: String,
    pub(super) layer: usize,
    pub(super) regime: BwdRegime,
    pub(super) round: u8,
    pub(super) rows: usize,
    /// Whether `rows` is the coordinate's intended row count or a memory-capped one.
    pub(super) saturated: bool,
    pub(super) shape: SegShape,
    pub(super) d2: D2Policy,
    /// Blocks per SM the occupancy API reports for this exact executor and geometry.
    /// ZERO means the compiled kernel cannot host the block — the cell is recorded,
    /// not skipped.
    pub(super) blocks_per_sm: i32,
    pub(super) theoretical_occupancy: f64,
    pub(super) attributes: SegKernelAttributes,
    pub(super) dynamic_smem_bytes: usize,
    pub(super) grid_blocks: u32,
    pub(super) waves: f64,
    /// The lowering's static per-list work spread: one means perfectly balanced.
    pub(super) max_over_mean_work: f64,
    pub(super) parity: SegParity,
    pub(super) candidate_median_us: f64,
    pub(super) candidate_min_us: f64,
    pub(super) incumbent_median_us: Option<f64>,
    pub(super) incumbent_min_us: Option<f64>,
    pub(super) ratio: Option<RatioEstimate>,
    /// WHAT the ratio is against, or `"-"` when the cell was timed solo.
    ///
    /// The ratio column carries two different comparisons — the R0 matrix pairs
    /// against the incumbent compact evaluator, Stage B pairs each rung against its
    /// own register-placement twin — and a reader cannot tell them apart from the
    /// number. Naming the baseline in the row is what keeps them distinguishable in
    /// the CSV and in every generated table.
    pub(super) baseline: &'static str,
}

impl SegMatrixRow {
    pub(super) fn launchable(&self) -> bool {
        self.blocks_per_sm > 0
    }

    /// Which timing protocol produced this row's numbers.
    ///
    /// `paired` is the plan's normative protocol: interleaved, one baseline sample
    /// between every two candidate samples, and a bootstrap CI over the pairs.
    /// `solo` is warmup-and-samples on one side only — a wall time with no
    /// interval, and NOT a number two rows of which may be divided to four
    /// decimals. Recorded per row so no table can quietly mix them.
    pub(super) fn protocol(&self) -> &'static str {
        if self.ratio.is_some() {
            "paired"
        } else {
            "solo"
        }
    }
}

pub(super) const SEG_CSV_HEADER: &str = "benchmark,circuit,layer,regime,round,rows,saturated,k,\
epilogue,coeff,program,acc_placement,d2_policy,launchable,blocks_per_sm,theoretical_occupancy_percent,registers,\
local_spill_bytes,static_smem_bytes,max_threads_per_block,dynamic_smem_bytes,grid_blocks,waves,\
max_over_mean_work,parity,protocol,ratio_baseline,candidate_median_us,candidate_min_us,\
baseline_median_us,baseline_min_us,median_ratio,ci_low,ci_high,verdict\n";

pub(super) fn render_matrix_csv(rows: &[SegMatrixRow]) -> String {
    let mut out = String::from(SEG_CSV_HEADER);
    for row in rows {
        let (ratio, low, high, verdict) = match row.ratio {
            Some(estimate) => (
                estimate.median_ratio,
                estimate.ci_low,
                estimate.ci_high,
                estimate.verdict(),
            ),
            None => (f64::NAN, f64::NAN, f64::NAN, "-"),
        };
        writeln!(
            out,
            "{},{},{},{:?},{},{},{},{},{},{},{},{},{},{},{},{:.2},{},{},{},{},{},{},{:.3},{:.4},\
             {},{},{},{:.3},{:.3},{:.3},{:.3},{:.6},{:.6},{:.6},{}",
            row.benchmark,
            row.circuit,
            row.layer,
            row.regime,
            row.round,
            row.rows,
            row.saturated,
            row.shape.k,
            epilogue_label(row.shape.epilogue),
            coeff_label(row.shape.coeff),
            program_label(row.shape.program),
            row.shape.acc_label(),
            d2_label(row.d2),
            row.launchable(),
            row.blocks_per_sm,
            row.theoretical_occupancy * 100.0,
            row.attributes.registers,
            row.attributes.local_size_bytes,
            row.attributes.static_smem_bytes,
            row.attributes.max_threads_per_block,
            row.dynamic_smem_bytes,
            row.grid_blocks,
            row.waves,
            row.max_over_mean_work,
            row.parity.label(),
            row.protocol(),
            row.baseline,
            row.candidate_median_us,
            row.candidate_min_us,
            row.incumbent_median_us.unwrap_or(f64::NAN),
            row.incumbent_min_us.unwrap_or(f64::NAN),
            ratio,
            low,
            high,
            verdict,
        )
        .expect("write String");
    }
    out
}

/// The production loader pair: the `__constant__` bank and the by-value program.
///
/// The other three cells of the loader grid are compiled valves the spike measures
/// and the audit reports; they are not what a production launch would use, so the
/// WINNER is chosen among production-loader rows only and the valve axis is
/// reported beside it rather than allowed to name the winner.
pub(super) fn is_production_loader(shape: &SegShape) -> bool {
    shape.coeff == CoeffMode::Constant
        && shape.program == ProgramMode::Inline
        && shape.acc.is_none()
}

/// How close to the fastest median a configuration must be to count as TIED with
/// it.
///
/// Not a fudge factor — a measured property of the thing being selected. At the
/// winning `K` this benchmark is DRAM-bandwidth bound: the epilogue differs only in
/// barrier count and shared-memory footprint, and at four warps per block the whole
/// reduction is a rounding error against the source traffic. The six loader ×
/// epilogue cells at `K = 4` land inside 0.31% of each other, five of them inside
/// 0.003%, while the `K` tiers around them are 1-2% and then 50% apart. Selecting
/// on the raw argmin therefore names an arbitrary member of the winning tier and
/// names a different one on the next run.
///
/// 0.1% of a 5.9 ms launch is ~6 us, comfortably above the CUDA event timer's tick
/// and far below any real shape effect.
pub(super) const SEG_SELECTION_TIE_FRACTION: f64 = 0.001;

/// The Stage-A winner: the fastest PRODUCTION-loader configuration, with the tie
/// band resolved in favour of the smallest `K` and then the smallest shared-memory
/// carveout.
///
/// Smallest `K` first because `K` is the axis that costs residency — a narrower
/// block leaves more blocks per SM and more room for the next benchmark's register
/// pressure — and smallest carveout second because two configurations that measure
/// the same should not both be carried forward.
pub(super) fn select_winner(rows: &[SegMatrixRow]) -> Option<&SegMatrixRow> {
    let production: Vec<&SegMatrixRow> = rows
        .iter()
        .filter(|row| row.launchable() && is_production_loader(&row.shape))
        .collect();
    let best = production
        .iter()
        .map(|row| row.candidate_median_us)
        .fold(f64::MAX, f64::min);
    if !best.is_finite() {
        return None;
    }
    let threshold = best * (1.0 + SEG_SELECTION_TIE_FRACTION);
    production
        .into_iter()
        .filter(|row| row.candidate_median_us <= threshold)
        .min_by_key(|row| (row.shape.k, row.dynamic_smem_bytes))
}

/// Every production-loader row inside the winner's tie band, so the audit can state
/// what the selection could NOT distinguish rather than implying it resolved.
pub(super) fn tie_band(rows: &[SegMatrixRow]) -> Vec<&SegMatrixRow> {
    let Some(winner) = select_winner(rows) else {
        return Vec::new();
    };
    let best = rows
        .iter()
        .filter(|row| row.launchable() && is_production_loader(&row.shape))
        .map(|row| row.candidate_median_us)
        .fold(f64::MAX, f64::min);
    let threshold = best * (1.0 + SEG_SELECTION_TIE_FRACTION);
    let _ = winner;
    rows.iter()
        .filter(|row| {
            row.launchable()
                && is_production_loader(&row.shape)
                && row.candidate_median_us <= threshold
        })
        .collect()
}

/// The fastest LAUNCHABLE row of a set, by candidate median.
pub(super) fn fastest(rows: &[SegMatrixRow]) -> Option<&SegMatrixRow> {
    rows.iter()
        .filter(|row| row.launchable())
        .min_by(|lhs, rhs| {
            lhs.candidate_median_us
                .partial_cmp(&rhs.candidate_median_us)
                .expect("finite median")
        })
}

/// Occupancy-probe the whole `1..=BWD_SEG_MAX_K` axis of one family.
///
/// ENUMERATED, not bisected. Bisection would answer "the largest launchable K"
/// only under an assumption the axis is monotone in `k`, and the register limit
/// interacts with the epilogue's shared-memory footprint, so monotonicity is
/// exactly what the probe should be measuring rather than assuming. Thirty-two
/// driver queries cost microseconds.
pub(super) fn seg_launchable_k_axis(
    regime: BwdRegime,
    program: ProgramMode,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
) -> Vec<(u32, i32)> {
    (1..=BWD_SEG_MAX_K as u32)
        .map(|k| {
            (
                k,
                bwd_seg_blocks_per_sm(regime, program, coeff, epilogue, k)
                    .expect("segmented occupancy query"),
            )
        })
        .collect()
}

/// Launch geometry facts a row records, derived from the same helpers the launcher
/// uses so a reported number and a launched one cannot disagree.
pub(super) fn seg_geometry_facts(
    regime: BwdRegime,
    shape: SegShape,
    rows: usize,
    device: &SegDeviceFacts,
) -> (i32, f64, usize, u32, f64) {
    let k = shape.k as u32;
    let (blocks_per_sm, smem) = match shape.acc {
        None => (
            bwd_seg_blocks_per_sm(regime, shape.program, shape.coeff, shape.epilogue, k)
                .expect("segmented occupancy query"),
            bwd_seg_epilogue_smem_bytes(shape.epilogue, k),
        ),
        Some(placement) => (
            bwd_seg_acc_blocks_per_sm(regime, placement, k).expect("rung occupancy query"),
            bwd_seg_acc_dynamic_smem_bytes(placement, k),
        ),
    };
    let grid = (rows.max(1) as u32).div_ceil(WARP_SIZE);
    let per_wave = (blocks_per_sm.max(1) as u32) * device.multiprocessors;
    (
        blocks_per_sm,
        device.occupancy(blocks_per_sm, k),
        smem,
        grid,
        f64::from(grid) / f64::from(per_wave),
    )
}

// ── Lowering and launching one shape ─────────────────────────────────────────

/// A lowered launch plus the device buffers whose pointers were patched into it.
///
/// The two allocations are held for RAII: the descriptor carries raw pointers into
/// them, so dropping this is what makes the launch's inputs dead.
pub(super) struct SegLaunchable {
    pub(super) setup: BwdSegSetup,
    _coefficients: Option<crate::primitives::context::DeviceAllocation<E4>>,
    _program: Option<crate::primitives::context::DeviceAllocation<u16>>,
    regime: BwdRegime,
    shape: SegShape,
}

impl SegLaunchable {
    /// Enqueue-only. Everything this reads was staged when the shape was prepared.
    pub(super) fn launch(&self, context: &ProverContext) -> CudaResult<()> {
        match self.shape.acc {
            None => launch_bwd_seg(
                &self.setup,
                self.regime,
                self.shape.coeff,
                self.shape.epilogue,
                context,
            ),
            Some(placement) => launch_bwd_seg_acc(&self.setup, self.regime, placement, context),
        }
    }
}

/// Upload `values` into a fresh top-placed device allocation.
pub(super) fn upload<T: Copy>(
    values: &[T],
    context: &ProverContext,
) -> crate::primitives::context::DeviceAllocation<T> {
    use crate::allocator::tracker::AllocationPlacement;
    let mut device = context
        .alloc(values.len().max(1), AllocationPlacement::Top)
        .expect("spike device allocation");
    if !values.is_empty() {
        memory_copy_async(
            &mut device[..values.len()],
            values,
            context.get_exec_stream(),
        )
        .expect("spike H2D");
    }
    device
}

/// Stage the fold challenges this round reads into the ONE challenge authority.
pub(super) fn stage_claim_point(claim_point: &[E4], context: &ProverContext) {
    use super::seg::bwd_seg_claim_point_device_ptr;
    if claim_point.is_empty() {
        return;
    }
    // SAFETY: the symbol holds `MAX_MAIN_LAYER_CLAIM_POINT_LEN` E4 values and
    // lowering rejects a claim point longer than the round it serves, which is
    // bounded well below that.
    let slab = unsafe {
        DeviceSlice::from_raw_parts_mut(bwd_seg_claim_point_device_ptr(), claim_point.len())
    };
    memory_copy_async(slab, claim_point, context.get_exec_stream()).expect("claim point H2D");
}

/// Stage the reserved-inclusive coefficient payload into THIS lineage's own
/// `__constant__` bank. Never `ab_gkr_flat_coefficients`: the two lineages share no
/// coefficient symbol, which is what lets both be staged in one process.
pub(super) fn stage_seg_bank(payload: &[E4], context: &ProverContext) {
    use super::seg::bwd_seg_coeff_bank_device_ptr;
    use super::seg_desc::BWD_SEG_CONST_BANK;
    assert!(
        payload.len() <= BWD_SEG_CONST_BANK,
        "the segmented coefficient payload must fit its own constant bank"
    );
    if payload.is_empty() {
        return;
    }
    // SAFETY: the symbol's declared extent is `BWD_SEG_CONST_BANK` E4 values and the
    // assertion above bounds the copy by it.
    let slab =
        unsafe { DeviceSlice::from_raw_parts_mut(bwd_seg_coeff_bank_device_ptr(), payload.len()) };
    memory_copy_async(slab, payload, context.get_exec_stream()).expect("segmented bank H2D");
}

/// Download `len` E4 values, synchronizing the stream.
pub(super) fn download_e4(ptr: *const E4, len: usize, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; len];
    // SAFETY: the caller supplies a live device span of at least `len` E4 values.
    let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
    memory_copy_async(&mut host[..], device, context.get_exec_stream()).expect("spike D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("spike D2H sync");
    host
}

/// Fill `2 * rows` contribution slots with a value no correct launch can produce.
pub(super) fn poison_contributions(
    ptr: *mut E4,
    rows: usize,
    value: E4,
    context: &ProverContext,
) -> CudaResult<()> {
    // SAFETY: every caller supplies a live device allocation of at least `2 * rows`
    // E4 values and serializes access on `exec_stream`.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(ptr, 2 * rows) };
    crate::ops::simple::set_by_val(value, slice, context.get_exec_stream())
}

/// Bytes of E4, as raw words, for exact comparison.
pub(super) fn e4_bits(value: E4) -> [u32; 4] {
    // SAFETY: E4 is the pinned four-u32 Rust/CUDA ABI field representation and this
    // is a read-only reinterpretation.
    unsafe { std::mem::transmute(value) }
}

#[track_caller]
pub(super) fn assert_e4(label: &str, got: E4, expected: E4) {
    assert_eq!(e4_bits(got), e4_bits(expected), "{label}");
}

// ── Summary publication ──────────────────────────────────────────────────────

/// Append one section to the spike summary, replacing an earlier run's section of
/// the same title rather than stacking duplicates.
pub(super) fn record_summary_section(title: &str, body: &str) {
    let path = seg_output_path(SEG_SUMMARY_MD);
    let mut existing = std::fs::read_to_string(&path).unwrap_or_default();
    if existing.is_empty() {
        existing.push_str("# Segmented lean VM spike summary\n");
    }
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

/// The per-benchmark table every section prints.
pub(super) fn render_matrix_table(rows: &[SegMatrixRow]) -> String {
    let mut body = String::from(
        "| K | epilogue | coeff | program | acc | d2 | regs | blocks/SM | occ % | smem B | \
         median (us) | ratio | 95% CI | verdict |\n\
         |---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for row in rows {
        if !row.launchable() {
            writeln!(
                body,
                "| {} | {} | {} | {} | {} | {} | {} | 0 | - | {} | UNLAUNCHABLE | - | - | - |",
                row.shape.k,
                epilogue_label(row.shape.epilogue),
                coeff_label(row.shape.coeff),
                program_label(row.shape.program),
                row.shape.acc_label(),
                d2_label(row.d2),
                row.attributes.registers,
                row.dynamic_smem_bytes,
            )
            .expect("write String");
            continue;
        }
        let (ratio, ci, verdict) = match row.ratio {
            Some(estimate) => (
                format!("{:.4}", estimate.median_ratio),
                format!("[{:.4}, {:.4}]", estimate.ci_low, estimate.ci_high),
                format!("{} vs {}", estimate.verdict(), row.baseline),
            ),
            // A solo cell has no baseline sampled beside it, so it gets no ratio and
            // no interval — printing either would invent a comparison the protocol
            // did not make.
            None => ("solo".to_owned(), "solo".to_owned(), "solo".to_owned()),
        };
        writeln!(
            body,
            "| {} | {} | {} | {} | {} | {} | {} | {} | {:.1} | {} | {:.3} | {ratio} | {ci} | \
             {verdict} |",
            row.shape.k,
            epilogue_label(row.shape.epilogue),
            coeff_label(row.shape.coeff),
            program_label(row.shape.program),
            row.shape.acc_label(),
            d2_label(row.d2),
            row.attributes.registers,
            row.blocks_per_sm,
            row.theoretical_occupancy * 100.0,
            row.dynamic_smem_bytes,
            row.candidate_median_us,
        )
        .expect("write String");
    }
    body
}

// ── Benchmark cells ──────────────────────────────────────────────────────────

use gkr_eval_isa::bwd::coeff::interp::{interpret_coeff_layer, interpret_lean_program};
use gkr_eval_isa::bwd::coeff::model::{CoeffLayer, CoefficientRecipeId};

use super::seg_compile::{
    seg_host_model, seg_round_binding, short_name, upload_round_storage, E4Deltas, SegBacking,
    SegCoordinate, SegHostModel, SegResolver, SegRoundStorage, SegScratch,
};
use crate::primitives::context::DeviceAllocation;
use crate::prover::gkr::backward::GkrEqSizes as EqSizes;

/// Device bytes ONE row of a `(coordinate, round, D2 policy)` cell costs.
///
/// Probed rather than derived: it builds the cell's host model at a single row and
/// reads the geometry back off it, so the delta assignment, the publish decision
/// and the element widths are `seg_host_model`'s own. A hand-written formula here
/// would be a second copy of that rule, and the two would diverge the first time
/// the delta policy changed.
pub(super) fn probe_bytes_per_row(coord: &SegCoordinate, round: u8, d2: D2Policy) -> usize {
    probe_geometry(coord, round, d2).bytes_per_row
}

/// The per-row device footprint AND the source width mix of one
/// `(coordinate, round, D2 policy)` cell, from ONE probe model.
///
/// The width mix is per SOURCE rather than per window: the closed-form `K` policy
/// reads it, and what costs a term an operand load is the source it names, not
/// how many windows the binding happens to group those sources into.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SegGeometryProbe {
    pub(super) bytes_per_row: usize,
    pub(super) windows: usize,
    pub(super) bf_sources: usize,
    pub(super) e4_sources: usize,
    pub(super) procedural_sources: usize,
}

pub(super) fn probe_geometry(coord: &SegCoordinate, round: u8, d2: D2Policy) -> SegGeometryProbe {
    let probe = seg_host_model(coord, round, 1, d2, E4Deltas::Supported);
    // The two contribution halves.
    let mut bytes = 2 * size_of::<E4>();
    for (index, window) in probe.windows.iter().enumerate() {
        let element = match &window.backing {
            SegBacking::Bf(_) => size_of::<u32>(),
            SegBacking::Ext(_) => size_of::<E4>(),
            // Synthesized from the row index: no matrix, no bytes.
            SegBacking::Procedural(_) => 0,
        };
        // At one row `column_len` IS `2 << delta`, i.e. elements per row per column.
        bytes += probe.columns[index] * window.column_len * element;
        if window.publishes {
            bytes += probe.columns[index] * 2 * size_of::<E4>();
        }
    }
    let mut mix = SegGeometryProbe {
        bytes_per_row: bytes,
        windows: probe.windows.len(),
        bf_sources: 0,
        e4_sources: 0,
        procedural_sources: 0,
    };
    for &(window, _) in &probe.slots {
        match probe.windows[window].backing {
            SegBacking::Bf(_) => mix.bf_sources += 1,
            SegBacking::Ext(_) => mix.e4_sources += 1,
            SegBacking::Procedural(_) => mix.procedural_sources += 1,
        }
    }
    mix
}

/// The row count a cell is measured at: `target`, halved until its synthetic
/// backings fit `budget`.
///
/// Returns the row count and whether it reached the target. A capped cell is
/// REPORTED as capped — a wall time at a quarter of the intended rows is a
/// different measurement, not the same one with noise.
pub(super) fn fit_rows(
    target: usize,
    per_row: usize,
    budget: usize,
    floor: usize,
) -> (usize, bool) {
    let mut rows = target;
    while rows > floor && rows.saturating_mul(per_row) > budget {
        rows /= 2;
    }
    (rows, rows >= target)
}

/// One `(coordinate, round, rows, D2 policy)` cell: the synthetic storage, the
/// publish scratch, and the contribution target every shape of it launches into.
pub(super) struct SegCell {
    pub(super) coord: Arc<SegCoordinate>,
    pub(super) layer: CoeffLayer,
    pub(super) c_init: Option<CoefficientRecipeId>,
    pub(super) model: SegHostModel,
    pub(super) storage: SegRoundStorage,
    pub(super) scratch: SegScratch,
    pub(super) claim_point: Vec<E4>,
    pub(super) rows: usize,
    pub(super) saturated: bool,
    pub(super) eq_low: *const E4,
    pub(super) eq_sizes: EqSizes,
    pub(super) contributions: *mut E4,
    /// Held only when this cell owns its contribution buffer. The R0 gate cell
    /// borrows the incumbent plan's accumulator instead, so that both lineages
    /// write the same bytes.
    _owned_contributions: Option<DeviceAllocation<E4>>,
}

impl SegCell {
    /// Build a cell, allocating its own contribution buffer.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build(
        coord: Arc<SegCoordinate>,
        round: u8,
        rows: usize,
        saturated: bool,
        d2: D2Policy,
        eq_low: *const E4,
        eq_sizes: EqSizes,
        context: &ProverContext,
    ) -> Self {
        let model = seg_host_model(&coord, round, rows, d2, E4Deltas::Supported);
        let storage = upload_round_storage(&model, context);
        let scratch = SegScratch::new(&[&model], context);
        let contributions = upload(&vec![E4::ZERO; 2 * rows], context);
        let pointer = contributions.as_ptr() as *mut E4;
        Self::finish(
            coord,
            model,
            storage,
            scratch,
            rows,
            saturated,
            eq_low,
            eq_sizes,
            pointer,
            Some(contributions),
        )
    }

    /// Build a cell that writes into a contribution buffer the CALLER owns — the
    /// incumbent plan's own accumulator, in the head-to-head.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_into(
        coord: Arc<SegCoordinate>,
        round: u8,
        rows: usize,
        saturated: bool,
        d2: D2Policy,
        eq_low: *const E4,
        eq_sizes: EqSizes,
        contributions: *mut E4,
        context: &ProverContext,
    ) -> Self {
        let model = seg_host_model(&coord, round, rows, d2, E4Deltas::Supported);
        let storage = upload_round_storage(&model, context);
        let scratch = SegScratch::new(&[&model], context);
        Self::finish(
            coord,
            model,
            storage,
            scratch,
            rows,
            saturated,
            eq_low,
            eq_sizes,
            contributions,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn finish(
        coord: Arc<SegCoordinate>,
        model: SegHostModel,
        storage: SegRoundStorage,
        scratch: SegScratch,
        rows: usize,
        saturated: bool,
        eq_low: *const E4,
        eq_sizes: EqSizes,
        contributions: *mut E4,
        owned: Option<DeviceAllocation<E4>>,
    ) -> Self {
        let layer = coord.layer.clone();
        // The layer's OWN seed. Every corpus continuation layer carries one, and a
        // binding that dropped it would leave the CPU oracle seeding `acc_c0` while
        // the descriptor seeded zero — a silent per-row offset rather than a
        // rejection.
        let c_init = layer.c_init;
        let claim_point = super::seg_compile::seg_claim_point(model.round);
        Self {
            coord,
            layer,
            c_init,
            model,
            storage,
            scratch,
            claim_point,
            rows,
            saturated,
            eq_low,
            eq_sizes,
            contributions,
            _owned_contributions: owned,
        }
    }

    pub(super) fn label(&self) -> String {
        format!(
            "{} L{} {:?} r{}",
            short_name(self.coord.circuit),
            self.coord.layer_index,
            self.coord.regime,
            self.model.round,
        )
    }

    /// Lower this cell at one shape, stage everything the launch reads, and patch
    /// the descriptor's runtime pointers.
    ///
    /// Staging happens HERE, once per shape, and never inside a timed loop.
    pub(super) fn prepare(&self, shape: SegShape, context: &ProverContext) -> SegLaunchable {
        let setup = self.try_lower(shape).unwrap_or_else(|error| {
            panic!("{}: {}: lower: {error:?}", self.label(), shape.label())
        });
        self.stage(setup, shape, context)
    }

    /// Lower this cell at one shape WITHOUT staging anything.
    ///
    /// Split out of [`Self::prepare`] for the corpus sweep, which walks
    /// coordinates the parity ladder never lowered: a coordinate host lowering
    /// REJECTS must be recorded with its rejection, not turned into a panic that
    /// takes the rest of the chunk with it. It is also how a cell that will never
    /// be timed still contributes its [`ListWorkStats`], which is a property of
    /// the lowering rather than of any launch.
    pub(super) fn try_lower(&self, shape: SegShape) -> Result<BwdSegSetup, BwdSegLowerError> {
        let binding = seg_round_binding(
            &self.model,
            &self.storage,
            &self.claim_point,
            &self.model.bank,
            self.c_init,
            self.eq_low,
            self.eq_sizes,
            self.contributions,
        );
        lower_bwd_seg(
            &self.coord.artifact,
            &binding,
            &self.scratch.resolved(),
            shape.k,
            self.model.d2,
            shape.program,
            shape.coeff,
        )
    }

    /// Upload everything a lowered shape reads and patch the descriptor's runtime
    /// pointers. Never called from inside a timed loop.
    fn stage(
        &self,
        mut setup: BwdSegSetup,
        shape: SegShape,
        context: &ProverContext,
    ) -> SegLaunchable {
        stage_claim_point(&setup.claim_point, context);
        let coefficients = match shape.coeff {
            CoeffMode::Constant => {
                stage_seg_bank(&setup.coefficients, context);
                None
            }
            CoeffMode::DevPtr => Some(upload(&setup.coefficients, context)),
        };
        let program =
            (shape.program == ProgramMode::DevPtr).then(|| upload(&setup.program_words, context));
        match &mut setup.desc {
            BwdSegLaunchDesc::Inline(desc) => {
                if let Some(bank) = &coefficients {
                    desc.coefficients = bank.as_ptr();
                }
            }
            BwdSegLaunchDesc::ProgPtr(desc) => {
                if let Some(bank) = &coefficients {
                    desc.coefficients = bank.as_ptr();
                }
                desc.program = program
                    .as_ref()
                    .expect("the progptr family uploads a stream")
                    .as_ptr();
            }
        }
        SegLaunchable {
            setup,
            _coefficients: coefficients,
            _program: program,
            regime: self.coord.regime,
            shape,
        }
    }

    /// The two CPU oracles for this cell, per row: `interpret_coeff_layer` and
    /// `interpret_lean_program` at `k`, asserted equal, then eq-weighted.
    ///
    /// Only ever called on a PARITY TWIN — it is `O(rows * terms)` on the host and
    /// its pair table is `O(sources * rows)` E4 values, neither of which is
    /// computable at the row counts the matrix times.
    pub(super) fn expected(&self, k: usize, eq: &HostEq) -> Vec<(E4, E4)> {
        let table = self.model.pair_table();
        let resolver = SegResolver {
            table: &table,
            rows: self.rows,
            bank: &self.model.bank,
        };
        let label = self.label();
        (0..self.rows)
            .map(|row| {
                let semantic = interpret_coeff_layer(&self.layer, row, &resolver)
                    .unwrap_or_else(|error| panic!("{label}: semantic row {row}: {error:?}"));
                let lean = interpret_lean_program(
                    &self.coord.artifact.program,
                    &self.layer,
                    row,
                    &resolver,
                    k,
                )
                .unwrap_or_else(|error| panic!("{label}: lean K{k} row {row}: {error:?}"));
                assert_e4(
                    &format!("{label}: semantic vs lean acc_c0 row {row}"),
                    lean.0,
                    semantic.0,
                );
                assert_e4(
                    &format!("{label}: semantic vs lean acc_c2 row {row}"),
                    lean.1,
                    semantic.1,
                );
                let weight = eq.at(row);
                let mut c0 = weight;
                c0.mul_assign(&semantic.0);
                let mut c2 = weight;
                c2.mul_assign(&semantic.1);
                (c0, c2)
            })
            .collect()
    }

    /// Launch one shape on the parity twin and compare every row against
    /// [`Self::expected`].
    pub(super) fn assert_oracles(&self, shape: SegShape, eq: &HostEq, context: &ProverContext) {
        let expected = self.expected(shape.k, eq);
        let launchable = self.prepare(shape, context);
        self.scratch.poison_write_parity(self.model.round, context);
        poison_contributions(
            self.contributions,
            self.rows,
            super::seg_compile::seg_ext(0xdead, 0, 0),
            context,
        )
        .expect("parity poison");
        launchable
            .launch(context)
            .unwrap_or_else(|error| panic!("{}: {}: {error:?}", self.label(), shape.label()));
        let got = download_e4(self.contributions, 2 * self.rows, context);
        let name = format!("{}: {}", self.label(), shape.label());
        for row in 0..self.rows {
            assert_e4(
                &format!("{name}: GPU eq*acc_c0 row {row}"),
                got[row],
                expected[row].0,
            );
            assert_e4(
                &format!("{name}: GPU eq*acc_c2 row {row}"),
                got[self.rows + row],
                expected[row].1,
            );
        }
    }

    /// One preflight launch over poisoned contributions; returns the bounded output
    /// prefix the timed cell's identity check compares.
    pub(super) fn preflight(
        &self,
        launchable: &SegLaunchable,
        shape: SegShape,
        context: &ProverContext,
    ) -> Vec<E4> {
        let poison = super::seg_compile::seg_ext(0xbeef, shape.k as u32, 0);
        self.scratch.poison_write_parity(self.model.round, context);
        poison_contributions(self.contributions, self.rows, poison, context)
            .expect("preflight poison");
        launchable
            .launch(context)
            .unwrap_or_else(|error| panic!("{}: {}: {error:?}", self.label(), shape.label()));
        let sample = identity_sample_rows(self.rows);
        // HEAD **and TAIL** of both halves. A prefix alone cannot see a short grid
        // or a truncated row count: those faults leave the last rows untouched, and
        // a kernel that evaluates fewer rows than it was asked for is FASTER, so a
        // prefix-only check would let a deflated wall time through certified.
        // Sampling `[rows - sample, rows)` of each half is what makes the far end of
        // the launch's own output an assertion.
        let tail = self.rows - sample;
        let mut out = download_e4(self.contributions, sample, context);
        // SAFETY: `contributions` spans `2 * rows` E4 values, so every offset below
        // is inside it: the second half starts `rows` values in, and `tail + sample`
        // is exactly `rows`.
        unsafe {
            out.extend(download_e4(
                self.contributions.add(self.rows),
                sample,
                context,
            ));
            out.extend(download_e4(self.contributions.add(tail), sample, context));
            out.extend(download_e4(
                self.contributions.add(self.rows + tail),
                sample,
                context,
            ));
        }
        // The tail check is only worth having if it reads DIFFERENT memory from the
        // head check, and a wrong offset would leave it silently reading the head
        // twice — at which point every downstream assertion still passes and the
        // guard is decoration. Contributions are `eq(row) * acc(row)` over
        // per-row-distinct pseudorandom sources, so head and tail cannot coincide;
        // asserting that they differ is what makes this measured rather than
        // assumed. (`tail > 0` for every cell of two rows or more: see
        // [`identity_sample_rows`], which halves the window rather than letting a
        // narrow cell's head and tail coincide.)
        assert!(
            tail > 0,
            "the timed cell must be wider than one sample window"
        );
        assert_ne!(
            e4_bits(out[0]),
            e4_bits(out[2 * sample]),
            "{}: {}: the tail sample read the same bytes as the head sample -- the \
             tail-inclusive certification is not reading the far end of the launch",
            self.label(),
            shape.label(),
        );
        // EVERY sampled slot, not merely one of them. `any` is satisfied by a single
        // changed value, so it passes a launch that wrote one tile and stopped; the
        // poison is a pseudorandom E4, so a correct contribution colliding with it
        // is a 2^-124 event and `all` costs nothing in false failures.
        for (slot, value) in out.iter().enumerate() {
            assert_ne!(
                e4_bits(*value),
                e4_bits(poison),
                "{}: {}: sampled contribution slot {slot} (of head+tail over both \
                 halves at {} rows) is still poison -- the launch did not cover it",
                self.label(),
                shape.label(),
                self.rows,
            );
        }
        out
    }
}

// ── The Stage-A matrix drivers ───────────────────────────────────────────────

use cs::gkr_compiler::dag_ir::BwdRegime as DagBwdRegime;

use super::seg_compile::{
    lean_coordinate, seg_coordinate_layers, ADD_SUB_LAYOUT, SEG_CORPUS_LAYOUTS, SEG_LAYOUTS,
};
use crate::prover::test_utils::make_test_context;

/// The `K` axis.
///
/// The plan's Stage A names `{4, 8, 16, 24, 32}`; `{1, 2}` extend it DOWNWARD,
/// added after the first pass found the winner at the bottom of the named set and
/// the wall time rising monotonically with `K`. They are also the two shapes only a
/// boundary reaches: `K = 1` bypasses shared memory and every barrier entirely (all
/// three epilogues collapse to the same code), and `K = 2` is the staged epilogue's
/// zero-trip loop. Extending the axis can only add information — nothing in the
/// matrix depends on the set being exactly the plan's five.
const STAGE_A_K: [usize; 7] = [1, 2, 4, 8, 16, 24, 32];
const STAGE_A_EPILOGUES: [BwdSegEpilogue; 3] = [
    BwdSegEpilogue::Staged,
    BwdSegEpilogue::Plane,
    BwdSegEpilogue::Wide,
];

/// Device bytes one benchmark cell may spend on synthetic backings. Rows halve
/// until the cell fits, and a capped cell is reported as unsaturated.
const SEG_BACKING_BUDGET_BYTES: usize = 32 << 30;
/// Never below this: a launch under it measures dispatch overhead.
const SEG_MIN_TIMED_ROWS: usize = 1 << 16;
/// The continuation matrix's own arena.
const SEG_CONT_ARENA_BYTES: usize = 64 << 30;

fn make_seg_spike_context(arena_bytes: usize) -> ProverContext {
    let block_log = crate::prover::ProverContextConfig::default().allocator_block_log_size;
    make_test_context((arena_bytes >> block_log).max(1), 64)
}

/// The `(program, coeff)` pairs the continuation family has compiled kernels for.
const CONT_LOADERS: [(ProgramMode, CoeffMode); 3] = [
    (ProgramMode::Inline, CoeffMode::Constant),
    (ProgramMode::Inline, CoeffMode::DevPtr),
    (ProgramMode::DevPtr, CoeffMode::Constant),
];

/// Build the real factored eq state every cell of a run shares.
///
/// The SAME `launch_build_eq_high_and_low_groups_from_point` the production round-0
/// path uses, at the production challenge count, so the per-row inline eq costs
/// what it costs in production — three loads and two multiplies, not the one load a
/// single-group state would give.
fn build_shared_eq(
    folding_steps: usize,
    context: &ProverContext,
) -> (DeviceAllocation<E4>, EqSizes) {
    use crate::prover::gkr::backward::{
        get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
        make_eq_sizes,
    };
    let remaining = folding_steps - 1;
    let sizes = make_eq_sizes(remaining);
    let point: Vec<E4> = (0..folding_steps)
        .map(|index| super::seg_compile::seg_ext(0x4100, index as u32, 0))
        .collect();
    let point_device = upload(&point, context);
    let mut eq_low = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], context);
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        point_device.as_ptr(),
        1,
        remaining,
        get_eq_high_constant_device_ptr(),
        eq_low.as_mut_ptr(),
        context,
    )
    .expect("build the real factored eq");
    context
        .get_exec_stream()
        .synchronize()
        .expect("eq build sync");
    drop(point_device);
    (eq_low, sizes)
}

/// The census the plan's `17..=31` question is answered by.
///
/// Enumerating the whole axis rather than bisecting it: see
/// [`seg_launchable_k_axis`]. Printed per family and published, because "the
/// continuation family caps at 16" was an artifact of a five-point probe with a
/// fifteen-value hole in it.
#[test]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_k_axis_census() {
    let _context = make_seg_spike_context(1 << 30);
    let device = SegDeviceFacts::query();
    let mut body = format!(
        "Device: {} SMs, {} threads/SM, {} registers/SM, {} B shared/SM.\n\n\
         Every `K` in `1..={BWD_SEG_MAX_K}` probed through `bwd_seg_blocks_per_sm`, \
         which answers ZERO for a geometry the compiled kernel cannot host. \
         ENUMERATED, not bisected.\n\n\
         | family | regs | largest launchable K | blocks/SM over the Stage-A K axis |\n\
         |---|---|---|---|\n",
        device.multiprocessors,
        device.max_threads_per_sm,
        device.max_registers_per_sm,
        device.max_shared_per_sm,
    );
    for (regime, program, coeff) in [
        (BwdRegime::R0, ProgramMode::Inline, CoeffMode::Constant),
        (BwdRegime::R0, ProgramMode::Inline, CoeffMode::DevPtr),
        (BwdRegime::Ext, ProgramMode::Inline, CoeffMode::Constant),
        (BwdRegime::Ext, ProgramMode::Inline, CoeffMode::DevPtr),
        (BwdRegime::Ext, ProgramMode::DevPtr, CoeffMode::Constant),
    ] {
        for epilogue in STAGE_A_EPILOGUES {
            let axis = seg_launchable_k_axis(regime, program, coeff, epilogue);
            let attributes = seg_attributes(regime, program, coeff, epilogue);
            attributes.assert_no_spills(&format!(
                "{regime:?}/{}/{}/{}",
                program_label(program),
                coeff_label(coeff),
                epilogue_label(epilogue)
            ));
            let largest = axis
                .iter()
                .filter(|(_, blocks)| *blocks > 0)
                .map(|(k, _)| *k)
                .max()
                .unwrap_or(0);
            let sampled: Vec<String> = STAGE_A_K
                .iter()
                .map(|k| {
                    axis.iter()
                        .find(|(probe, _)| *probe == *k as u32)
                        .map(|(_, blocks)| blocks.to_string())
                        .expect("the probed axis covers every Stage-A K")
                })
                .collect();
            // The occupancy API and the attribute query must agree about which
            // blocks the image can host; they are independent driver paths onto the
            // same fact, so a disagreement means one of them is answering about a
            // different kernel.
            for (k, blocks) in &axis {
                assert_eq!(
                    *blocks > 0,
                    attributes.hosts(*k),
                    "{regime:?}/{}/{}/{} at K={k}: the occupancy API and \
                     cudaFuncGetAttributes disagree about launchability",
                    program_label(program),
                    coeff_label(coeff),
                    epilogue_label(epilogue),
                );
            }
            eprintln!(
                "[seg-spike] {regime:?}/{}/{}/{}: regs={} largest launchable K={largest} \
                 blocks/SM at Stage-A K = [{}]",
                program_label(program),
                coeff_label(coeff),
                epilogue_label(epilogue),
                attributes.registers,
                sampled.join(", "),
            );
            writeln!(
                body,
                "| {regime:?} {} {} {} | {} | {largest} | {} |",
                program_label(program),
                coeff_label(coeff),
                epilogue_label(epilogue),
                attributes.registers,
                sampled.join(" / "),
            )
            .expect("write String");
        }
    }
    record_summary_section("K-axis launchability census (1..=32, enumerated)", &body);
}

/// The incumbent occupancy pin's premise and reason, asserted rather than
/// documented — the pin is the one published number here whose provenance is a
/// profiler capture rather than a live query.
#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn the_incumbent_occupancy_pin_still_holds() {
    let _context = make_test_context(16, 16);
    let device = SegDeviceFacts::query();
    let attributes = incumbent_r0_attributes();
    let queried = era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        &incumbent_r0_kernel(),
        INCUMBENT_R0_THREADS_PER_BLOCK as i32,
        0,
    )
    .expect("query incumbent round-0 occupancy");
    let occupancy = f64::from(PINNED_INCUMBENT_R0_BLOCKS_PER_SM)
        * f64::from(INCUMBENT_R0_THREADS_PER_BLOCK)
        / f64::from(device.max_threads_per_sm);
    eprintln!(
        "[seg-spike] incumbent: registers={} local={} B static_smem={} B \
         max_threads_per_block={} | API blocks={queried} | published blocks={} \
         occupancy={:.2}%",
        attributes.registers,
        attributes.local_size_bytes,
        attributes.static_smem_bytes,
        attributes.max_threads_per_block,
        PINNED_INCUMBENT_R0_BLOCKS_PER_SM,
        occupancy * 100.0,
    );
    assert_eq!(
        attributes.registers, PINNED_INCUMBENT_R0_REGISTERS,
        "the pin is derived from this allocation and must be re-derived if it moves"
    );
    assert_eq!(
        attributes.local_size_bytes, 0,
        "the incumbent must not spill"
    );
    assert_eq!(
        queried, INCUMBENT_R0_LAUNCH_BOUNDS_MIN_BLOCKS,
        "the occupancy API is expected to answer the `__launch_bounds__(128, 8)` \
         minBlocks hint; if it now answers {PINNED_INCUMBENT_R0_BLOCKS_PER_SM}, delete \
         the pin and query instead"
    );
    assert!(
        queried < PINNED_INCUMBENT_R0_BLOCKS_PER_SM,
        "the hint may only UNDERSTATE the achievable occupancy"
    );
    assert!(
        (occupancy - 0.8333).abs() < 0.001,
        "the capture's theoretical occupancy is 83.33%; got {:.2}%",
        occupancy * 100.0
    );
}

/// The profiled shape, overridable so a capture can re-target without a rebuild.
fn profile_shape() -> SegShape {
    let k = std::env::var("BWD_SEG_PROFILE_K")
        .ok()
        .map(|value| {
            value
                .trim()
                .parse::<usize>()
                .unwrap_or_else(|error| panic!("invalid BWD_SEG_PROFILE_K={value:?}: {error}"))
        })
        .unwrap_or(8);
    let epilogue = match std::env::var("BWD_SEG_PROFILE_EPILOGUE")
        .unwrap_or_else(|_| "plane".to_owned())
        .trim()
    {
        "staged" => BwdSegEpilogue::Staged,
        "plane" => BwdSegEpilogue::Plane,
        "wide" => BwdSegEpilogue::Wide,
        other => panic!("invalid BWD_SEG_PROFILE_EPILOGUE={other:?}"),
    };
    SegShape::regs(k, CoeffMode::Constant, ProgramMode::Inline, epilogue)
}

/// **THE GATE benchmark.** `add_sub` layer-0 R0, the whole Stage-A matrix, paired
/// against the REAL incumbent compact evaluator in one process, one context, one
/// row count, one eq state and one contribution buffer.
///
/// Shared with the incumbent, deliberately: the row count (taken from the real
/// plan), the same `eq_low` pointer and `GkrEqSizes` built by the real factored-eq
/// build kernel, the same contribution buffer with the same `2 * rows` half-stride,
/// and one release binary with no validation launch on either side.
///
/// **Not shared: the candidate's source windows read SYNTHETIC backings.** The
/// production backward source binder is a later task, so each bound window gets its
/// own device buffer whose field width, column count, column stride and fold
/// geometry are the compiler's real ones for this coordinate — but not its real
/// addresses. That makes the CACHE-HIT comparison a layout artifact; the read
/// VOLUME and access SHAPE are real, which is what the ratio rests on.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_add_sub_l0_r0_matrix() {
    let rows = run_r0_matrix(None);
    assert!(!rows.is_empty(), "the matrix must record every coordinate");
}

/// The profiler selector: ONE candidate launch and ONE incumbent launch, each
/// inside its own registered NVTX range, after the matrix has warmed and measured.
#[test]
#[ignore = "GPU profiling; run under `ncu` through with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_add_sub_l0_r0_profile() {
    let shape = profile_shape();
    let rows = run_r0_matrix(Some(shape));
    assert!(rows
        .iter()
        .any(|row| row.shape == shape && row.launchable()));
}

#[allow(clippy::too_many_lines)]
fn run_r0_matrix(profile: Option<SegShape>) -> Vec<SegMatrixRow> {
    use crate::prover::gkr::backward::compact;
    use crate::prover::gkr::backward::flat::CoefficientRecipe;
    use crate::prover::gkr::backward::{
        GpuGKRMainLayerDeferredChallengeSource, GpuGKRMainLayerSumcheckLayerPlan,
    };
    use crate::prover::tests::prepare_basic_unrolled_async_backward_fixture;

    // ── the real incumbent plan ──────────────────────────────────────────
    let fixture = prepare_basic_unrolled_async_backward_fixture(8);
    let context = fixture.context;
    let mut gpu_backward_state = fixture.gpu_backward_state;
    while let Some(plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .expect("prepare incumbent dimension-reducing layer")
    {
        drop(plan);
    }
    let mut main_state = gpu_backward_state.into_main_layer_backward_state(
        fixture.compiled_circuit,
        fixture.external_challenges.clone(),
        fixture.lookup_multiplicative_part,
        fixture.lookup_additive_part,
        false,
    );
    let mut plan: GpuGKRMainLayerSumcheckLayerPlan<E4> = loop {
        let Some(plan) = main_state
            .prepare_next_layer(fixture.batching_challenge, &context)
            .expect("prepare incumbent main layer")
        else {
            panic!("the incumbent fixture produced no add/sub layer 0")
        };
        if plan.layer_idx == 0 {
            break plan;
        }
        drop(plan);
    };
    assert!(
        plan.flat_use_constant,
        "add/sub R0 must use the constant-coefficient incumbent path"
    );

    let mut external_values = fixture
        .external_challenges
        .permutation_argument_linearization_challenges
        .to_vec();
    external_values.push(
        fixture
            .external_challenges
            .permutation_argument_additive_part,
    );
    let incumbent_bank: Vec<E4> = plan
        .flat_round0_template_compact
        .as_ref()
        .expect("incumbent round-0 descriptor")
        .recipes
        .iter()
        .map(|recipe: &CoefficientRecipe<E4>| {
            let immediate = if recipe.negate {
                recipe.immediate_recipe.negated()
            } else {
                recipe.immediate_recipe.clone()
            };
            let mut coefficient = fixture.batching_challenge.pow(recipe.batch_power);
            coefficient.mul_assign(&immediate.evaluate(&external_values));
            for group in &recipe.prefactors {
                let mut group_sum = E4::ZERO;
                for term in group {
                    let challenge = match term.source {
                        GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative => {
                            fixture.lookup_multiplicative_part
                        }
                        GpuGKRMainLayerDeferredChallengeSource::LookupAdditive => {
                            fixture.lookup_additive_part
                        }
                    };
                    let mut value = challenge.pow(term.power);
                    value.mul_assign_by_base(&term.coeff);
                    group_sum.add_assign(&value);
                }
                coefficient.mul_assign(&group_sum);
            }
            coefficient
        })
        .collect();

    let folding_steps = plan.folding_steps;
    let incumbent_rows = plan.trace_len >> 1;
    let (eq_low, eq_sizes) = build_shared_eq(folding_steps, &context);
    let host_eq = HostEq::download(eq_low.as_ptr(), eq_sizes, &context);
    let output_ptr = plan.round_scratch.accumulator.as_mut_ptr();
    let device = SegDeviceFacts::query();

    // ── the candidate's row count ────────────────────────────────────────
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, DagBwdRegime::R0);
    let per_row = probe_bytes_per_row(&coord, 0, D2Policy::Inline);
    let (rows, saturated) = fit_rows(
        incumbent_rows,
        per_row,
        SEG_BACKING_BUDGET_BYTES,
        SEG_MIN_TIMED_ROWS,
    );
    eprintln!(
        "[seg-spike] add/sub L0 R0: incumbent rows {incumbent_rows}, folding steps \
         {folding_steps}, eq_sizes {{low:{}, high:[{}, {}]}}, incumbent bank {} | candidate \
         {per_row} B/row -> {rows} rows ({:.2} GiB, saturated={saturated})",
        eq_sizes.low,
        eq_sizes.high[0],
        eq_sizes.high[1],
        incumbent_bank.len(),
        (rows * per_row) as f64 / (1u64 << 30) as f64,
    );

    // ── the incumbent's own preflight ────────────────────────────────────
    assert!(
        incumbent_bank.len() <= FLAT_CONST_MAX,
        "the incumbent add/sub round-0 bank must fit its constant symbol"
    );
    let staged: [E4; FLAT_CONST_MAX] =
        core::array::from_fn(|index| incumbent_bank.get(index).copied().unwrap_or(E4::ZERO));
    // SAFETY: this Rust stub names the exact CUDA `e4[FLAT_CONST_MAX]` coefficient
    // symbol; the copy is stream-ordered before every launch that reads it and is
    // always outside a timed span.
    unsafe {
        crate::primitives::utils::memcpy_to_symbol_async(
            &ab_gkr_flat_coefficients,
            &staged,
            context.get_exec_stream(),
        )
    }
    .expect("stage the incumbent round-0 bank");

    let incumbent_launch = |context: &ProverContext| {
        compact::launch_main_round0_constant::<E4>(
            &plan
                .flat_round0_template_compact
                .as_ref()
                .expect("incumbent round-0 descriptor")
                .static_desc,
            eq_low.as_ptr(),
            &eq_sizes,
            output_ptr,
            rows as u32,
            context,
        )
    };
    let preflight = super::seg_compile::seg_ext(0x00a1, 0, 0);
    poison_contributions(output_ptr, rows, preflight, &context)
        .expect("poison the incumbent preflight");
    incumbent_launch(&context).expect("incumbent correctness launch");
    let sample = SEG_IDENTITY_SAMPLE_ROWS.min(rows);
    let incumbent_output = download_e4(output_ptr, sample, &context);
    assert!(
        incumbent_output
            .iter()
            .any(|value| e4_bits(*value) != e4_bits(preflight)),
        "the incumbent round-0 launch left every sampled contribution poisoned"
    );

    // ── the candidate's parity twin and timed cell ───────────────────────
    let parity = SegCell::build(
        Arc::clone(&coord),
        0,
        SEG_PARITY_ROWS,
        true,
        D2Policy::Inline,
        eq_low.as_ptr(),
        eq_sizes,
        &context,
    );
    let timed = SegCell::build_into(
        Arc::clone(&coord),
        0,
        rows,
        saturated,
        D2Policy::Inline,
        eq_low.as_ptr(),
        eq_sizes,
        output_ptr,
        &context,
    );

    // A PROFILE run measures the one shape it is capturing and nothing else: under
    // `ncu` every launch outside the filter still costs interception, and a
    // forty-two cell matrix behind a one-kernel capture is a long wait for a number
    // the matrix run already published.
    let shapes: Vec<SegShape> = match profile {
        Some(shape) => vec![shape],
        None => {
            let mut all = Vec::with_capacity(STAGE_A_EPILOGUES.len() * 2 * STAGE_A_K.len());
            for epilogue in STAGE_A_EPILOGUES {
                for coeff in [CoeffMode::Constant, CoeffMode::DevPtr] {
                    for k in STAGE_A_K {
                        all.push(SegShape::regs(k, coeff, ProgramMode::Inline, epilogue));
                    }
                }
            }
            all
        }
    };
    let mut matrix = Vec::new();
    let mut reference: Option<Vec<E4>> = None;
    for shape in shapes {
        matrix.push(measure_shape(
            "add_sub L0 R0",
            &timed,
            &parity,
            shape,
            &host_eq,
            &device,
            &mut reference,
            Some((INCUMBENT_R0_BASELINE_LABEL, &incumbent_launch)),
            profile == Some(shape),
            &context,
        ));
    }

    let csv = seg_output_path(if profile.is_some() {
        "seg_r0_profile.csv"
    } else {
        SEG_MATRIX_CSV
    });
    publish(&csv, &render_matrix_csv(&matrix));
    let best = select_winner(&matrix).expect("at least one launchable R0 configuration");
    let band = tie_band(&matrix);
    let quickest = fastest(&matrix).expect("at least one launchable R0 configuration");
    let inverted: Vec<&SegMatrixRow> = matrix
        .iter()
        .filter(|row| row.ratio.is_some_and(|ratio| ratio.inverts()))
        .collect();
    let gate = best.ratio.expect("the gate row carries an incumbent");
    eprintln!(
        "[seg-spike] add/sub L0 R0 WINNER {} regs={} median={:.3}us ratio={:.4} \
         [{:.4}, {:.4}] {} | tie band {} rows | raw argmin over all loaders {} at \
         {:.3}us | {} of {} launchable configurations invert",
        best.shape.label(),
        best.attributes.registers,
        best.candidate_median_us,
        gate.median_ratio,
        gate.ci_low,
        gate.ci_high,
        gate.verdict(),
        band.len(),
        quickest.shape.label(),
        quickest.candidate_median_us,
        inverted.len(),
        matrix.iter().filter(|row| row.launchable()).count(),
    );
    record_summary_section(
        if profile.is_some() {
            "add/sub layer-0 R0 Nsight Compute capture"
        } else {
            "add/sub layer-0 R0 Stage-A matrix (THE GATE)"
        },
        &format!(
            "{}Incumbent: `{INCUMBENT_R0_SEQUENCE}`\n\n\
             Rows {rows} (candidate) against the incumbent at the same `acc_size`; the real \
             plan's row count is {incumbent_rows} (saturated={saturated}). \
             {SEG_WARMUP_ITERS} warmups and {SEG_TIMING_ITERS} timed samples PER SIDE, \
             interleaved. Ratio is candidate/incumbent; the interval is a \
             {SEG_BOOTSTRAP_RESAMPLES}-resample percentile bootstrap over PAIRS. \
             **Inversion is `ci_high < 1.0`.**\n\n\
             **Winner: `{}`, {} registers, {:.3} us, ratio {:.4} with 95% CI \
             [{:.4}, {:.4}] -- {}.** Chosen among PRODUCTION-loader rows \
             (`const` bank, by-value program) with the tie band resolved to the \
             smallest `K` and then the smallest carveout; {} production rows sit \
             inside that band, so the epilogue axis is NOT resolved at this `K`. \
             The raw argmin over every loader is `{}` at {:.3} us, {:.4}% away.\n\n\
             {} of {} launchable configurations invert.\n\n{}\n\nCSV: `{}`\n",
            if profile.is_some() {
                "**Do not quote this section's ratio.** It is written by the \
                 profiler-selector test, whose launches sit inside the capture range; \
                 when `ncu` is attached it serializes and replays them, which perturbs \
                 these medians. The \"Stage-A matrix\" section -- measured with nothing \
                 attached -- is the authority for the ratio.\n\n"
            } else {
                ""
            },
            best.shape.label(),
            best.attributes.registers,
            best.candidate_median_us,
            gate.median_ratio,
            gate.ci_low,
            gate.ci_high,
            gate.verdict(),
            band.len(),
            quickest.shape.label(),
            quickest.candidate_median_us,
            (best.candidate_median_us / quickest.candidate_median_us - 1.0) * 100.0,
            inverted.len(),
            matrix.iter().filter(|row| row.launchable()).count(),
            render_matrix_table(&matrix),
            csv.display(),
        ),
    );
    if profile.is_some() {
        record_summary_section(
            "Nsight Compute invocation",
            &format!(
                "`ncu --nvtx-include` takes `Domain@Range`, DOMAIN FIRST; the reversed \
                 form matches nothing and reports `No kernels were profiled` rather than \
                 failing.\n\nCandidate:\n\n```\n\
                 --nvtx --nvtx-include '{SEG_NVTX_DOMAIN}@{SEG_NVTX_MESSAGE}' \\\n\
                 --launch-count 1 -o target/profiling/ncu/seg_r0_candidate\n\
                 ```\n\nIncumbent (its own range, so the selection is NVTX rather than a \
                 launch-skip count that drifts with `SEG_WARMUP_ITERS`):\n\n```\n\
                 --nvtx --nvtx-include '{SEG_NVTX_DOMAIN}@{SEG_NVTX_INCUMBENT_MESSAGE}' \\\n\
                 --launch-count 1 -o target/profiling/ncu/seg_r0_incumbent\n```\n"
            ),
        );
    }

    drop(timed);
    drop(parity);
    drop(eq_low);
    drop(plan);
    drop(main_state);
    matrix
}

/// Probe, certify and time ONE matrix coordinate.
///
/// The order is load-bearing: launchability first (a cell that cannot run is
/// recorded, never skipped), then both CPU oracles on the parity twin, then the
/// timed cell's preflight and identity check, and only then the timing loop.
#[allow(clippy::too_many_arguments)]
fn measure_shape(
    benchmark: &str,
    timed: &SegCell,
    parity: &SegCell,
    shape: SegShape,
    eq: &HostEq,
    device: &SegDeviceFacts,
    reference: &mut Option<Vec<E4>>,
    // `baseline`: what this shape is PAIRED against, and the label naming it.
    // `None` falls back to solo timing, which the row records as such.
    baseline: Option<(&'static str, &dyn Fn(&ProverContext) -> CudaResult<()>)>,
    profile: bool,
    context: &ProverContext,
) -> SegMatrixRow {
    let regime = timed.coord.regime;
    let attributes = shape_attributes(regime, shape);
    attributes.assert_no_spills(&format!("{benchmark} {}", shape.label()));
    let (blocks_per_sm, occupancy, smem, grid, waves) =
        seg_geometry_facts(regime, shape, timed.rows, device);

    let mut row = SegMatrixRow {
        benchmark: benchmark.to_owned(),
        circuit: timed.coord.circuit.to_owned(),
        layer: timed.coord.layer_index,
        regime,
        round: timed.model.round,
        rows: timed.rows,
        saturated: timed.saturated,
        shape,
        d2: timed.model.d2,
        blocks_per_sm,
        theoretical_occupancy: occupancy,
        attributes,
        dynamic_smem_bytes: smem,
        grid_blocks: grid,
        waves,
        max_over_mean_work: 0.0,
        parity: SegParity::Unlaunchable,
        candidate_median_us: 0.0,
        candidate_min_us: 0.0,
        incumbent_median_us: None,
        incumbent_min_us: None,
        ratio: None,
        baseline: baseline.map_or("-", |(label, _)| label),
    };
    if blocks_per_sm == 0 {
        eprintln!(
            "[seg-spike] {benchmark} {}: UNLAUNCHABLE (regs {}, max_threads_per_block {})",
            shape.label(),
            attributes.registers,
            attributes.max_threads_per_block,
        );
        return row;
    }

    // Rung 1: both CPU oracles, at this exact shape, on the small twin.
    parity.assert_oracles(shape, eq, context);

    // Rung 2: the timed cell's own preflight and prefix identity.
    let launchable = timed.prepare(shape, context);
    row.max_over_mean_work = launchable.setup.work.max_over_mean;
    let prefix = timed.preflight(&launchable, shape, context);
    match reference {
        None => {
            row.parity = SegParity::OraclesAndReference;
            *reference = Some(prefix);
        }
        Some(expected) => {
            assert_eq!(
                prefix.len(),
                expected.len(),
                "{benchmark} {}: identity sample length",
                shape.label()
            );
            for (slot, (got, want)) in prefix.iter().zip(expected.iter()).enumerate() {
                assert_e4(
                    &format!(
                        "{benchmark} {}: contribution slot {slot} must be bit-identical to the \
                         cell's reference configuration -- K and the epilogue are pure \
                         performance axes",
                        shape.label()
                    ),
                    *got,
                    *want,
                );
            }
            row.parity = SegParity::OraclesAndIdentity;
        }
    }

    // Rung 3: the timing loop. Nothing is poisoned, downloaded or synchronized
    // inside it beyond the event pair each sample needs.
    let stream = context.get_exec_stream();
    match baseline {
        Some((label, baseline)) => {
            let paired = time_paired(stream, || launchable.launch(context), || baseline(context))
                .expect("interleaved paired timing");
            let estimate = paired.estimate();
            eprintln!(
                "[seg-spike] {benchmark} {}: candidate {:.3}us vs {label} {:.3}us -> \
                 {:.4} [{:.4}, {:.4}] {}",
                shape.label(),
                paired.candidate_median(),
                paired.incumbent_median(),
                estimate.median_ratio,
                estimate.ci_low,
                estimate.ci_high,
                estimate.verdict(),
            );
            row.candidate_median_us = paired.candidate_median();
            row.candidate_min_us = paired.candidate_min();
            row.incumbent_median_us = Some(paired.incumbent_median());
            row.incumbent_min_us = Some(paired.incumbent_min());
            row.ratio = Some(estimate);
        }
        None => {
            let samples =
                time_solo(stream, || launchable.launch(context)).expect("candidate timing");
            row.candidate_median_us = median(&samples);
            row.candidate_min_us = samples.iter().copied().fold(f64::MAX, f64::min);
            eprintln!(
                "[seg-spike] {benchmark} {}: candidate {:.3}us SOLO (blocks/SM \
                 {blocks_per_sm}, occ {:.1}%, regs {})",
                shape.label(),
                row.candidate_median_us,
                occupancy * 100.0,
                attributes.registers,
            );
        }
    }

    // The profiler's launches: ONE per side, after every warmup and every timed
    // sample, and the only things inside the registered ranges.
    if profile {
        context.get_exec_stream().synchronize().expect("settle");
        {
            let _range =
                crate::primitives::nvtx::scoped_range(Some(SEG_NVTX_DOMAIN), SEG_NVTX_MESSAGE);
            launchable.launch(context).expect("profiled candidate");
            context
                .get_exec_stream()
                .synchronize()
                .expect("profiled candidate completion");
        }
        if let Some((_, baseline)) = baseline {
            let _range = crate::primitives::nvtx::scoped_range(
                Some(SEG_NVTX_DOMAIN),
                SEG_NVTX_INCUMBENT_MESSAGE,
            );
            baseline(context).expect("profiled baseline");
            context
                .get_exec_stream()
                .synchronize()
                .expect("profiled incumbent completion");
        }
    }
    row
}

/// The continuation half of Stage A: `add_sub` layer-0 at D1 and D2, over the whole
/// `(K, epilogue, loader, program source, D2 policy)` grid.
///
/// Candidate-only. The incumbent's round-1 and round-2 unified evaluators need a
/// real folded state and the plan's PRIVATE `flat_round{1,2}_size_check()`
/// resolution to be launched safely, so no honest pairing exists here without
/// running the real sumcheck forward — see the audit. The matrix's own purpose at
/// these rounds is the `(epilogue, K)` winner, the D2-policy A/B and the
/// continuation `K` ceiling, and all three are candidate-internal comparisons.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_add_sub_l0_cont_matrix() {
    let context = make_seg_spike_context(SEG_CONT_ARENA_BYTES);
    let device = SegDeviceFacts::query();
    let (eq_low, eq_sizes) = build_shared_eq(24, &context);
    let host_eq = HostEq::download(eq_low.as_ptr(), eq_sizes, &context);
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, DagBwdRegime::Ext);

    let mut matrix = Vec::new();
    for (round, d2) in [
        (1u8, D2Policy::Inline),
        (2u8, D2Policy::Inline),
        (2u8, D2Policy::Materialize),
    ] {
        let per_row = probe_bytes_per_row(&coord, round, d2);
        // The real sumcheck halves rows per round; the target mirrors that so the
        // per-round wall times are comparable to a production progression.
        let target = (1usize << 23) >> usize::from(round);
        let (rows, saturated) = fit_rows(
            target,
            per_row,
            SEG_BACKING_BUDGET_BYTES,
            SEG_MIN_TIMED_ROWS,
        );
        let benchmark = format!("add_sub L0 D{round} {}", d2_label(d2));
        eprintln!(
            "[seg-spike] {benchmark}: {per_row} B/row -> {rows} rows ({:.2} GiB, \
             saturated={saturated}, target {target})",
            (rows * per_row) as f64 / (1u64 << 30) as f64,
        );
        let parity = SegCell::build(
            Arc::clone(&coord),
            round,
            SEG_PARITY_ROWS,
            true,
            d2,
            eq_low.as_ptr(),
            eq_sizes,
            &context,
        );
        let timed = SegCell::build(
            Arc::clone(&coord),
            round,
            rows,
            saturated,
            d2,
            eq_low.as_ptr(),
            eq_sizes,
            &context,
        );
        let mut reference: Option<Vec<E4>> = None;
        for epilogue in STAGE_A_EPILOGUES {
            for (program, coeff) in CONT_LOADERS {
                for k in STAGE_A_K {
                    let shape = SegShape::regs(k, coeff, program, epilogue);
                    matrix.push(measure_shape(
                        &benchmark,
                        &timed,
                        &parity,
                        shape,
                        &host_eq,
                        &device,
                        &mut reference,
                        None,
                        false,
                        &context,
                    ));
                }
            }
        }
        drop(timed);
        drop(parity);
    }

    let csv = seg_output_path("seg_stage_a_cont_matrix.csv");
    publish(&csv, &render_matrix_csv(&matrix));
    let ceiling = matrix
        .iter()
        .filter(|row| row.launchable())
        .map(|row| row.shape.k)
        .max()
        .unwrap_or(0);
    // PER BENCHMARK: the three cells run at different row counts and different
    // policies, so a winner picked across them would be comparing a D1 launch at
    // four million rows with a D2 launch at two million.
    let mut winners = String::new();
    for benchmark in [
        "add_sub L0 D1 inline",
        "add_sub L0 D2 inline",
        "add_sub L0 D2 materialize",
    ] {
        let cell: Vec<SegMatrixRow> = matrix
            .iter()
            .filter(|row| row.benchmark == benchmark)
            .cloned()
            .collect();
        let Some(best) = select_winner(&cell) else {
            continue;
        };
        eprintln!(
            "[seg-spike] {benchmark} WINNER {} regs={} at {:.3}us ({} blocks/SM, occ \
             {:.1}%, {} rows)",
            best.shape.label(),
            best.attributes.registers,
            best.candidate_median_us,
            best.blocks_per_sm,
            best.theoretical_occupancy * 100.0,
            best.rows,
        );
        writeln!(
            winners,
            "| {benchmark} | {} | {} | {} | {:.1}% | {} | {:.3} |",
            best.shape.label(),
            best.attributes.registers,
            best.blocks_per_sm,
            best.theoretical_occupancy * 100.0,
            best.rows,
            best.candidate_median_us,
        )
        .expect("write String");
    }
    record_summary_section(
        "add/sub layer-0 D1/D2 Stage-A matrix (candidate-only)",
        &format!(
            "Candidate-only: the incumbent round-1/round-2 unified evaluators need a real \
             folded state and the plan's private size-check resolution, so no honest \
             pairing exists here without running the real sumcheck forward.\n\n\
             Largest launchable Stage-A `K` over the whole continuation grid: \
             **{ceiling}**.\n\n\
             Winner per cell (production loader, tie band resolved):\n\n\
             | benchmark | winner | regs | blocks/SM | occupancy | rows | median (us) |\n\
             |---|---|---|---|---|---|---|\n{winners}\n{}\n\nCSV: `{}`\n",
            render_matrix_table(&matrix),
            csv.display(),
        ),
    );
    drop(eq_low);
}

/// **Stage B: the AccPlacement ladder**, measured on the Stage-A winner.
///
/// Design section 6 offers three placements for a loop that lands above the
/// 40-register target, and the task's condition for building rungs (b) and (c) is
/// that the winner records more than 40 registers. On this device the GATE
/// benchmark's winner does NOT — the R0 `plane` executor is exactly 40 — but the
/// nine CONTINUATION symbols are 68-76, so the ladder is measured where the
/// register count is actually the binding occupancy limiter as well as on the R0
/// winner, which gives the rungs a same-family reference point.
///
/// Both rungs are parity-checked against BOTH CPU oracles on a Task-8-shaped
/// ladder cell before either is timed, and both are timed against their own
/// register-placement twin — same `K`, same epilogue, same loader, same rows — so
/// the only difference between the two sides of every pair is where the
/// accumulator lives.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_stage_b_acc_ladder() {
    let context = make_seg_spike_context(SEG_CONT_ARENA_BYTES);
    let device = SegDeviceFacts::query();
    let (eq_low, eq_sizes) = build_shared_eq(24, &context);
    let host_eq = HostEq::download(eq_low.as_ptr(), eq_sizes, &context);

    // The register DELTA is the ladder's headline, and it is a property of the
    // compiled image rather than of any launch, so it is read first and reported
    // even if a rung turns out to be slower.
    let mut ladder = String::from(
        "| family | placement | regs | delta vs registers | local | max threads |\n\
         |---|---|---|---|---|---|\n",
    );
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        let base = seg_attributes(
            regime,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BWD_SEG_ACC_RUNG_EPILOGUE,
        );
        base.assert_no_spills(&format!("{regime:?} plane registers"));
        writeln!(
            ladder,
            "| {regime:?} | registers | {} | - | {} | {} |",
            base.registers, base.local_size_bytes, base.max_threads_per_block
        )
        .expect("write String");
        for placement in [
            BwdSegAccPlacement::AccC2Smem,
            BwdSegAccPlacement::AccBothSmem,
        ] {
            let rung = SegKernelAttributes::of(bwd_seg_acc_entry_point(regime, placement));
            rung.assert_no_spills(&format!("{regime:?} plane {}", placement.label()));
            eprintln!(
                "[seg-spike] Stage B {regime:?} {}: regs {} (registers placement {}, delta \
                 {:+}), local {} B, max_threads_per_block {}",
                placement.label(),
                rung.registers,
                base.registers,
                rung.registers - base.registers,
                rung.local_size_bytes,
                rung.max_threads_per_block,
            );
            writeln!(
                ladder,
                "| {regime:?} | {} | {} | {:+} | {} | {} |",
                placement.label(),
                rung.registers,
                rung.registers - base.registers,
                rung.local_size_bytes,
                rung.max_threads_per_block,
            )
            .expect("write String");
        }
    }

    // The two benchmark cells: the R0 winner's coordinate, and the continuation
    // cell whose registers are the reason the ladder exists at all.
    let mut matrix = Vec::new();
    let cells: [(&str, &'static str, DagBwdRegime, u8, D2Policy, usize); 2] = [
        (
            "add_sub L0 R0",
            ADD_SUB_LAYOUT,
            DagBwdRegime::R0,
            0,
            D2Policy::Inline,
            1 << 23,
        ),
        (
            "add_sub L0 D2 materialize",
            ADD_SUB_LAYOUT,
            DagBwdRegime::Ext,
            2,
            D2Policy::Materialize,
            1 << 21,
        ),
    ];
    for (benchmark, layout, regime, round, d2, target) in cells {
        let coord = lean_coordinate(layout, 0, regime);
        let per_row = probe_bytes_per_row(&coord, round, d2);
        let (rows, saturated) = fit_rows(
            target,
            per_row,
            SEG_BACKING_BUDGET_BYTES,
            SEG_MIN_TIMED_ROWS,
        );
        eprintln!(
            "[seg-spike] Stage B {benchmark}: {per_row} B/row -> {rows} rows \
             (saturated={saturated})"
        );
        let parity = SegCell::build(
            Arc::clone(&coord),
            round,
            SEG_PARITY_ROWS,
            true,
            d2,
            eq_low.as_ptr(),
            eq_sizes,
            &context,
        );
        let timed = SegCell::build(
            Arc::clone(&coord),
            round,
            rows,
            saturated,
            d2,
            eq_low.as_ptr(),
            eq_sizes,
            &context,
        );
        let mut reference: Option<Vec<E4>> = None;
        for k in [4usize, 8] {
            // The register placement FIRST at each `K`, for two reasons: it is the
            // identity reference every rung of that `K` is compared against (so a
            // rung that computed something else fails against the placement it is
            // supposed to be equivalent to, not against an arbitrary earlier row),
            // and it is the BASELINE the rungs are then paired against.
            let twin_shape = SegShape::regs(
                k,
                CoeffMode::Constant,
                ProgramMode::Inline,
                BWD_SEG_ACC_RUNG_EPILOGUE,
            );
            matrix.push(measure_shape(
                benchmark,
                &timed,
                &parity,
                twin_shape,
                &host_eq,
                &device,
                &mut reference,
                None,
                false,
                &context,
            ));
            // A live twin to pair against. Rung-vs-twin is exactly a pairable
            // comparison — same cell, same rows, same buffer — so it gets the
            // NORMATIVE protocol rather than a quotient of two separately-timed
            // medians, which would carry a fixed-direction drift bias (the twin is
            // always measured first) and no interval at all.
            let twin = timed.prepare(twin_shape, &context);
            for placement in [
                BwdSegAccPlacement::AccC2Smem,
                BwdSegAccPlacement::AccBothSmem,
            ] {
                matrix.push(measure_shape(
                    benchmark,
                    &timed,
                    &parity,
                    SegShape::rung(k, placement),
                    &host_eq,
                    &device,
                    &mut reference,
                    Some((STAGE_B_TWIN_BASELINE_LABEL, &|ctx: &ProverContext| {
                        twin.launch(ctx)
                    })),
                    false,
                    &context,
                ));
            }
        }
        drop(timed);
        drop(parity);
    }

    let csv = seg_output_path("seg_stage_b_acc_ladder.csv");
    publish(&csv, &render_matrix_csv(&matrix));
    // Per (benchmark, K): the rung against its own register twin, as the paired
    // estimate the row already carries. NOT a quotient of two medians — that is
    // the thing this fix removed.
    let mut pairs = String::from(
        "| benchmark | K | placement | protocol | regs | blocks/SM | occ % | median (us) | \
         rung / twin | 95% CI | verdict |\n|---|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for row in &matrix {
        let (ratio, ci, verdict) = match row.ratio {
            Some(estimate) => (
                format!("{:.4}", estimate.median_ratio),
                format!("[{:.4}, {:.4}]", estimate.ci_low, estimate.ci_high),
                // Against the twin, "INVERTED" means the RUNG is faster. Spelled
                // out because the same word means something else in the gate table.
                match (estimate.inverts(), estimate.regresses()) {
                    (true, _) => "rung faster",
                    (_, true) => "rung slower",
                    _ => "indistinguishable",
                }
                .to_owned(),
            ),
            None => ("baseline".to_owned(), "-".to_owned(), "-".to_owned()),
        };
        writeln!(
            pairs,
            "| {} | {} | {} | {} | {} | {} | {:.1} | {:.3} | {ratio} | {ci} | {verdict} |",
            row.benchmark,
            row.shape.k,
            row.shape.acc_label(),
            row.protocol(),
            row.attributes.registers,
            row.blocks_per_sm,
            row.theoretical_occupancy * 100.0,
            row.candidate_median_us,
        )
        .expect("write String");
    }
    eprintln!("[seg-spike] Stage B ladder\n{ladder}\n{pairs}");
    record_summary_section(
        "Stage B: the AccPlacement ladder",
        &format!(
            "Rungs compiled ON the Stage-A winner's epilogue and loader (`plane`, \
             `const`) and nowhere else. Registers, spills and `maxThreadsPerBlock` are \
             `cudaFuncGetAttributes` on the loaded module; every timed rung was \
             parity-checked against BOTH CPU oracles at {SEG_PARITY_ROWS} rows first and \
             is bit-identical to its register-placement twin (head AND tail of both \
             contribution halves).\n\n\
             Register ladder:\n\n{ladder}\n\
             Wall time: each rung is INTERLEAVED against its own register-placement \
             twin under the normative protocol ({SEG_WARMUP_ITERS} warmups and \
             {SEG_TIMING_ITERS} samples per side, alternating), so every ratio below \
             carries a bootstrap CI and no fixed-direction drift bias. The twin rows \
             are the baseline and are timed solo.\n\n{pairs}\n\
             CSV: `{}`\n",
            csv.display(),
        ),
    );
    drop(eq_low);
}

/// The monster geometry: `keccak_special5` layer 0, whose live-source footprint is
/// what the spec's "L2-targeted, DRAM fallback expected" sizing is about.
///
/// Measured, not assumed. This driver produces the wall times and the launch
/// geometry; the L2 sector hit rate and the DRAM read/write bytes come from the
/// `ncu` pass over the same shape, because no runtime API reports them.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_keccak_l0_monster() {
    let context = make_seg_spike_context(SEG_CONT_ARENA_BYTES);
    let device = SegDeviceFacts::query();
    let (eq_low, eq_sizes) = build_shared_eq(24, &context);
    let host_eq = HostEq::download(eq_low.as_ptr(), eq_sizes, &context);
    let coord = lean_coordinate(SEG_LAYOUTS[3], 0, DagBwdRegime::R0);
    let per_row = probe_bytes_per_row(&coord, 0, D2Policy::Inline);
    let (rows, saturated) = fit_rows(
        1 << 20,
        per_row,
        SEG_BACKING_BUDGET_BYTES,
        SEG_MIN_TIMED_ROWS,
    );
    eprintln!(
        "[seg-spike] keccak_special5 L0 R0 monster: {} windows, {per_row} B/row -> {rows} \
         rows ({:.2} GiB, saturated={saturated})",
        coord.artifact.binding.windows.len(),
        (rows * per_row) as f64 / (1u64 << 30) as f64,
    );

    let parity = SegCell::build(
        Arc::clone(&coord),
        0,
        SEG_PARITY_ROWS,
        true,
        D2Policy::Inline,
        eq_low.as_ptr(),
        eq_sizes,
        &context,
    );
    let timed = SegCell::build(
        Arc::clone(&coord),
        0,
        rows,
        saturated,
        D2Policy::Inline,
        eq_low.as_ptr(),
        eq_sizes,
        &context,
    );

    let mut matrix = Vec::new();
    let mut reference: Option<Vec<E4>> = None;
    let profiled = profile_shape();
    for epilogue in STAGE_A_EPILOGUES {
        for k in STAGE_A_K {
            let shape = SegShape::regs(k, CoeffMode::Constant, ProgramMode::Inline, epilogue);
            matrix.push(measure_shape(
                "keccak_special5 L0 R0 monster",
                &timed,
                &parity,
                shape,
                &host_eq,
                &device,
                &mut reference,
                None,
                shape == profiled,
                &context,
            ));
        }
    }

    let csv = seg_output_path("seg_stage_a_monster.csv");
    publish(&csv, &render_matrix_csv(&matrix));
    let best = select_winner(&matrix).expect("at least one launchable monster configuration");
    let at_32: Vec<&SegMatrixRow> = matrix
        .iter()
        .filter(|row| row.shape.k == 32 && row.launchable())
        .collect();
    eprintln!(
        "[seg-spike] monster winner: {} at {:.3}us; K=32 cells resident at {} block(s)/SM",
        best.shape.label(),
        best.candidate_median_us,
        at_32.first().map_or(0, |row| row.blocks_per_sm),
    );
    record_summary_section(
        "keccak_special5 layer-0 monster geometry",
        &format!(
            "{} bound windows, {per_row} B per row of synthetic backing, {rows} rows \
             (saturated={saturated}). The spec sizes this class as L2-targeted with DRAM \
             fallback expected; the sector hit rate and DRAM bytes are the `ncu` pass's, \
             not this driver's.\n\n{}\n\nCSV: `{}`\n",
            coord.artifact.binding.windows.len(),
            render_matrix_table(&matrix),
            csv.display(),
        ),
    );
    drop(timed);
    drop(parity);
    drop(eq_low);
}

// ── Task 10: the full-corpus sweep and the closed-form `K` policy ────────────
//
// Stage A answered "which configuration wins on ONE coordinate". This answers
// "what does a launcher choose, at setup, for ANY coordinate" — which is a
// different question and needs the whole corpus rather than the four circuits the
// parity ladder runs.
//
// Three properties are deliberate, and each of them is a lesson from Stage A:
//
//   * `K` is the ONLY free axis. Epilogue, coefficient loader and program source
//     are pinned to the Task-9 winner, because at the winning `K` those three
//     axes were measured to be INSIDE the selection tie band — sweeping them
//     again over 12 circuits would multiply the run by six and resolve nothing.
//   * every non-baseline `K` is PAIRED against the same cell's `K = 4` twin.
//     A `K`-vs-`K` comparison on one cell is a genuine A/B (same rows, same
//     buffer, same context), so it gets the normative protocol and an interval.
//     Stage B's review found that dividing two solo medians carries a
//     fixed-direction drift bias of ~0.3% and no interval at all; the loss table
//     below is built entirely out of paired estimates for exactly that reason.
//   * a coordinate that cannot be measured is RECORDED with the reason. There are
//     four of those (see [`SegCorpusStatus`]) and the sweep's coverage line prints
//     all of them, because a corpus sweep that quietly measured 60% of the corpus
//     would look identical to one that measured all of it.

/// The `K` axis the corpus sweep ranks: the plan's set, unextended.
///
/// Stage A extended its own axis DOWN to `{1, 2}` after the gate coordinate's
/// winner landed at the bottom of the named set. That is not repeated here and
/// the omission is a measurement, not an oversight: `K = 1` ran 4% behind the
/// incumbent on the gate coordinate (50% occupancy, no cross-warp amortization)
/// and `K = 2` lost to `K = 4` on every Stage-A cell it was launchable in.
pub(super) const SEG_CORPUS_K: [usize; 5] = [4, 8, 16, 24, 32];

/// The member of [`SEG_CORPUS_K`] every other `K` of a coordinate is paired
/// against: the Task-9 winner, so a corpus ratio reads directly as "against the
/// configuration the gate was won at".
pub(super) const SEG_CORPUS_BASELINE_K: usize = SEG_CORPUS_K[0];
pub(super) const SEG_CORPUS_BASELINE_LABEL: &str = "K4-same-cell";

/// Rows a corpus cell aims for.
///
/// Chosen so the grid stays deep at EVERY `K` of the axis rather than so the cell
/// is large: at `K = 4` the R0 family is resident 12 blocks deep on 188 SMs, so
/// 2^20 rows is 2^15 blocks over a 2,256-block wave — about 14 waves — and at
/// `K = 32` it is 166. Task 9 measured the gate coordinate at 116 waves and noted
/// that tail effects are negligible there; 14 is the shallowest point of this
/// sweep and every row records its own `waves` so a reader can see it.
const SEG_CORPUS_TARGET_ROWS: usize = 1 << 20;

/// Device bytes ONE corpus cell may spend on its synthetic backings and publish
/// scratch together.
///
/// This is the sweep's real budget and it is a HOST-time budget, not a device one:
/// the backings are generated on the CPU one field element at a time, so a cell is
/// paid for twice — once to synthesize it and once to upload it. 2 GiB per cell
/// keeps the whole 12-circuit corpus inside a locked afternoon; raising it makes
/// the heavy continuation coordinates measurable at more rows and makes the sweep
/// several hours long. The consequence is recorded per coordinate rather than
/// smoothed: a cell that cannot reach [`SEG_MIN_TIMED_ROWS`] inside this budget is
/// flagged [`SegCorpusStatus::BelowFloor`] and excluded from the policy fit.
const SEG_CORPUS_DEFAULT_BUDGET_BYTES: usize = 2 << 30;

/// The budget this invocation runs under: [`SEG_CORPUS_DEFAULT_BUDGET_BYTES`], or
/// `BWD_SEG_CORPUS_BUDGET_GIB`.
///
/// It exists to break a CONFOUND, and that is the only reason it is a knob. Under
/// one fixed budget the row count is a deterministic function of the coordinate's
/// per-row footprint, so grid depth and coordinate weight move together and no
/// amount of corpus can separate them: every deep-grid coordinate is light because
/// only a light coordinate fits 2^20 rows. Re-running the heavy circuits at a
/// larger budget puts a HEAVY coordinate at a DEEP grid, which is the missing
/// quadrant. Every row records the rows it was measured at, so the two passes
/// merge into one table rather than overwriting each other.
fn corpus_budget_bytes() -> usize {
    match std::env::var("BWD_SEG_CORPUS_BUDGET_GIB") {
        Err(_) => SEG_CORPUS_DEFAULT_BUDGET_BYTES,
        Ok(value) => {
            let gib: usize = value.trim().parse().unwrap_or_else(|error| {
                panic!("invalid BWD_SEG_CORPUS_BUDGET_GIB={value:?}: {error}")
            });
            assert!(gib > 0, "the corpus budget must admit at least one cell");
            gib << 30
        }
    }
}

/// The row LADDER every coordinate is measured on: the fitted row count, and the
/// same coordinate a quarter and a sixteenth as deep.
///
/// The second half of the confound fix. Sweeping one row count per coordinate
/// measures `best_k` as a function of the coordinate, and the coordinate alone
/// fixes the grid depth — so "does depth matter, or does weight?" is unanswerable
/// from it. Re-measuring the SAME coordinate at three depths answers it within the
/// coordinate, where weight is held constant by construction.
///
/// Divisors rather than absolute row counts, because the fitted row count already
/// differs per coordinate; rungs that would fall under [`SEG_MIN_TIMED_ROWS`] are
/// dropped rather than measured below the floor, since the ladder exists to vary
/// depth and a below-floor rung varies the protocol as well.
const SEG_CORPUS_ROW_STEPS: [usize; 3] = [1, 4, 16];

/// Rows below which a corpus cell is not launched at all: at four blocks it is
/// measuring dispatch, and the certification windows have nothing to sample.
const SEG_CORPUS_MIN_ROWS: usize = 1 << 10;

const _: () = {
    assert!(SEG_CORPUS_MIN_ROWS >= 2 * 32);
    assert!(SEG_CORPUS_TARGET_ROWS > SEG_MIN_TIMED_ROWS);
    assert!(SEG_CORPUS_K[0] == 4);
    assert!(SEG_CORPUS_ROW_STEPS[0] == 1);
};

/// The round classes a coordinate is swept at.
///
/// `R0` is the round-zero regime (no fold). The continuation regime is swept at
/// D1, D2 and D3, and D2 is swept TWICE — the two `D2Policy` values are the same
/// round with different source classes for every base-field window at catch-up
/// two, and Task 9 saw them 35% apart on a single coordinate. That single
/// coordinate is why the policy is decided here and not there.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum SegRoundClass {
    R0,
    D1,
    D2Inline,
    D2Materialize,
    D3,
}

pub(super) const SEG_ROUND_CLASSES: [SegRoundClass; 5] = [
    SegRoundClass::R0,
    SegRoundClass::D1,
    SegRoundClass::D2Inline,
    SegRoundClass::D2Materialize,
    SegRoundClass::D3,
];

impl SegRoundClass {
    pub(super) fn regime(self) -> BwdRegime {
        match self {
            Self::R0 => BwdRegime::R0,
            _ => BwdRegime::Ext,
        }
    }

    pub(super) fn round(self) -> u8 {
        match self {
            Self::R0 => 0,
            Self::D1 => 1,
            Self::D2Inline | Self::D2Materialize => 2,
            Self::D3 => 3,
        }
    }

    pub(super) fn d2(self) -> D2Policy {
        match self {
            Self::D2Materialize => D2Policy::Materialize,
            _ => D2Policy::Inline,
        }
    }

    /// Whether this class is one of the two the `D2Policy` A/B is decided on.
    pub(super) fn is_d2_class(self) -> bool {
        matches!(self, Self::D2Inline | Self::D2Materialize)
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::R0 => "R0",
            Self::D1 => "D1",
            Self::D2Inline => "D2-inline",
            Self::D2Materialize => "D2-materialize",
            Self::D3 => "D3",
        }
    }

    pub(super) fn parse(label: &str) -> Option<Self> {
        SEG_ROUND_CLASSES
            .into_iter()
            .find(|class| class.label() == label)
    }
}

/// Why a coordinate at one `K` carries no wall time — or that it does.
///
/// Five outcomes, and the sweep's coverage line prints the count of each. The
/// point of enumerating them is that they are NOT interchangeable: an
/// unlaunchable cell is a property of the compiled kernel, a below-floor cell is
/// a property of this harness's memory budget, and a lower-rejected cell is a
/// property of the coordinate itself and the only one of the three that would be
/// a finding about the VM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegCorpusStatus {
    /// Timed at or above [`SEG_MIN_TIMED_ROWS`], certified, counts for the policy.
    Timed,
    /// Timed and certified, but at fewer rows than the timing floor because the
    /// cell's per-row footprint would not fit [`corpus_budget_bytes`]. The
    /// number is real; it is a different measurement from the ones beside it, so
    /// it is excluded from the policy fit and reported separately.
    BelowFloor,
    /// Not even [`SEG_CORPUS_MIN_ROWS`] rows fit the budget. Nothing was launched.
    OverBudget,
    /// The compiled kernel cannot host a `32 * k`-thread block for this family.
    Unlaunchable,
    /// HOST LOWERING rejected the shape. Recorded rather than panicked: the corpus
    /// reaches coordinates the parity ladder's four circuits never lowered.
    LowerRejected,
}

impl SegCorpusStatus {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Timed => "timed",
            Self::BelowFloor => "below-floor",
            Self::OverBudget => "over-budget",
            Self::Unlaunchable => "unlaunchable",
            Self::LowerRejected => "lower-rejected",
        }
    }

    pub(super) fn parse(label: &str) -> Option<Self> {
        [
            Self::Timed,
            Self::BelowFloor,
            Self::OverBudget,
            Self::Unlaunchable,
            Self::LowerRejected,
        ]
        .into_iter()
        .find(|status| status.label() == label)
    }

    /// Whether a row with this status carries a wall time at all.
    pub(super) fn measured(self) -> bool {
        matches!(self, Self::Timed | Self::BelowFloor)
    }
}

/// The production shape: the Task-9 winner's epilogue, loader and program source,
/// with `K` the only free axis.
pub(super) fn corpus_shape(k: usize) -> SegShape {
    SegShape::regs(
        k,
        CoeffMode::Constant,
        ProgramMode::Inline,
        BwdSegEpilogue::Plane,
    )
}

/// The `K`-independent facts of one corpus coordinate.
///
/// Everything the closed-form policy is ALLOWED to read lives here, and nothing
/// else does: the policy has to be evaluable at setup, before any launch, so it
/// may not depend on a measured median. `total_static_work` is the lowering's own
/// per-list work model summed back over the lists, which is where the "width mix"
/// of spec §12 actually enters — a BF-inline-d2 operand costs 10 and an E4-direct
/// one costs 0, so the sum already carries the mix that a raw term count does not.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct SegCoordFacts {
    pub(super) circuit: String,
    pub(super) layer: usize,
    pub(super) class: SegRoundClass,
    pub(super) terms: usize,
    pub(super) sources: usize,
    pub(super) windows: usize,
    pub(super) bf_sources: usize,
    pub(super) e4_sources: usize,
    pub(super) procedural_sources: usize,
    pub(super) total_static_work: u64,
    pub(super) bytes_per_row: usize,
    pub(super) rows: usize,
}

impl SegCoordFacts {
    /// One MEASUREMENT POINT, i.e. one group of `K` rows.
    ///
    /// The row count is part of the key, not an attribute of the coordinate: the
    /// same coordinate is deliberately measured at several depths (see
    /// [`SEG_CORPUS_ROW_STEPS`]), each of which has its own best `K`, and a key
    /// without it would silently merge three measurements into one.
    pub(super) fn key(&self) -> (String, usize, SegRoundClass, usize) {
        (self.circuit.clone(), self.layer, self.class, self.rows)
    }

    /// The coordinate the point belongs to, without the depth.
    pub(super) fn coordinate(&self) -> (String, usize, SegRoundClass) {
        (self.circuit.clone(), self.layer, self.class)
    }

    pub(super) fn label(&self) -> String {
        format!(
            "{} L{} {} @{}",
            self.circuit,
            self.layer,
            self.class.label(),
            self.rows
        )
    }

    /// The launch grid: one 32-row tile per block, at every `K`.
    pub(super) fn grid_blocks(&self) -> u32 {
        (self.rows.max(1) as u32).div_ceil(WARP_SIZE)
    }
}

/// One corpus coordinate at one `K`.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct SegCorpusRow {
    pub(super) facts: SegCoordFacts,
    pub(super) k: usize,
    pub(super) status: SegCorpusStatus,
    pub(super) blocks_per_sm: i32,
    pub(super) theoretical_occupancy: f64,
    pub(super) registers: i32,
    pub(super) dynamic_smem_bytes: usize,
    pub(super) waves: f64,
    /// The lowering's static per-list spread at THIS `K`; one is perfect balance.
    pub(super) max_over_mean_work: f64,
    pub(super) parity: SegParity,
    /// **Two protocols share this column.** On the `K = 4` baseline row it is a
    /// SOLO median; on every other `K` it is the candidate median of an
    /// INTERLEAVED pair. The two are not interchangeable — 23 of 792 points
    /// disagree by more than 10% between the solo and the interleaved reading of
    /// the same baseline, worst 1.795x — so anything that divides medians ACROSS
    /// rows must first put both sides on one protocol (see
    /// [`interleaved_baseline_median`]). Ratios are unaffected: they are measured
    /// inside the pair.
    pub(super) median_us: Option<f64>,
    pub(super) min_us: Option<f64>,
    /// The PAIRED baseline's own median, as measured inside the same interleaved
    /// loop. `None` on the baseline row and on every untimed row — and on every
    /// row of a schema-v1 chunk, which did not carry the column.
    pub(super) baseline_median_us: Option<f64>,
    /// Against the same cell's `K = 4` twin. `None` on the baseline row itself
    /// (which is timed solo, and says so) and on every untimed row.
    pub(super) ratio_vs_baseline: Option<RatioEstimate>,
}

impl SegCorpusRow {
    /// A row for a coordinate that produced no launch.
    pub(super) fn untimed(facts: SegCoordFacts, k: usize, status: SegCorpusStatus) -> Self {
        Self {
            facts,
            k,
            status,
            blocks_per_sm: 0,
            theoretical_occupancy: 0.0,
            registers: 0,
            dynamic_smem_bytes: 0,
            waves: 0.0,
            max_over_mean_work: 0.0,
            parity: SegParity::Unlaunchable,
            median_us: None,
            min_us: None,
            baseline_median_us: None,
            ratio_vs_baseline: None,
        }
    }

    pub(super) fn protocol(&self) -> &'static str {
        if !self.status.measured() {
            "-"
        } else if self.ratio_vs_baseline.is_some() {
            "paired"
        } else {
            "solo"
        }
    }
}

/// The filename prefix `load_corpus_tables` globs for. Every sweep chunk carries
/// it; nothing else under [`SEG_OUTPUT_DIR`] may.
pub(super) const SEG_CORPUS_CHUNK_PREFIX: &str = "seg_corpus_";
/// The policy pass's own table. Deliberately OUTSIDE the chunk prefix.
pub(super) const SEG_POLICY_CSV: &str = "seg_k_policy.csv";

/// The chunk table's columns.
///
/// **Schema v2.** v1 was this without `baseline_median_us`, and the reader accepts
/// both — see [`parse_corpus_csv`]. The column was added because the row already
/// computed the paired baseline's median and then threw it away, which left
/// `median_us` carrying two different protocols in one column (a solo median on the
/// `K = 4` baseline row, an interleaved candidate median on every other row) with
/// no way to recover the missing half. The `K` policy never saw it — it reads
/// paired ratios only — but the D2 verdict consumes raw medians, and a reader
/// cannot tell the two apart from the number.
pub(super) const SEG_CORPUS_CSV_HEADER: &str = "circuit,layer,class,regime,round,d2_policy,terms,\
sources,windows,bf_sources,e4_sources,procedural_sources,total_static_work,bytes_per_row,rows,\
grid_blocks,k,status,blocks_per_sm,theoretical_occupancy_percent,registers,dynamic_smem_bytes,\
waves,max_over_mean_work,parity,protocol,median_us,min_us,baseline_median_us,ratio_vs_k4,ci_low,\
ci_high\n";

/// The one column schema v1 lacks. Absent from an on-disk v1 chunk, and its
/// absence is not an error: the sweeps that produced this workspace's tables ran
/// before it existed, and regenerating 12 locked chunk runs to add a column that
/// no conclusion depends on would be a worse trade than reading both schemas.
pub(super) const SEG_CORPUS_V2_COLUMN: &str = "baseline_median_us";

fn optional(value: Option<f64>) -> String {
    value.map_or_else(|| "-".to_owned(), |value| format!("{value:.3}"))
}

fn parse_optional(field: &str) -> Option<f64> {
    (field != "-").then(|| field.parse().expect("a finite CSV measurement"))
}

pub(super) fn render_corpus_csv(rows: &[SegCorpusRow]) -> String {
    let mut out = String::from(SEG_CORPUS_CSV_HEADER);
    for row in rows {
        let (ratio, low, high) = match row.ratio_vs_baseline {
            Some(estimate) => (
                format!("{:.6}", estimate.median_ratio),
                format!("{:.6}", estimate.ci_low),
                format!("{:.6}", estimate.ci_high),
            ),
            None => ("-".to_owned(), "-".to_owned(), "-".to_owned()),
        };
        writeln!(
            out,
            "{},{},{},{:?},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.4},{},{},{:.4},{:.6},\
             {},{},{},{},{},{ratio},{low},{high}",
            row.facts.circuit,
            row.facts.layer,
            row.facts.class.label(),
            row.facts.class.regime(),
            row.facts.class.round(),
            d2_label(row.facts.class.d2()),
            row.facts.terms,
            row.facts.sources,
            row.facts.windows,
            row.facts.bf_sources,
            row.facts.e4_sources,
            row.facts.procedural_sources,
            row.facts.total_static_work,
            row.facts.bytes_per_row,
            row.facts.rows,
            row.facts.grid_blocks(),
            row.k,
            row.status.label(),
            row.blocks_per_sm,
            row.theoretical_occupancy * 100.0,
            row.registers,
            row.dynamic_smem_bytes,
            row.waves,
            row.max_over_mean_work,
            row.parity.label(),
            row.protocol(),
            optional(row.median_us),
            optional(row.min_us),
            optional(row.baseline_median_us),
        )
        .expect("write String");
    }
    out
}

/// Read a corpus CSV back, schema v1 or v2.
///
/// The sweep is CHUNKED — twelve circuits is far more than one locked run should
/// hold — so the policy is derived in a separate pass over every chunk's table
/// rather than inside the process that measured one of them. That makes the
/// round-trip load-bearing.
///
/// Fields are resolved BY COLUMN NAME, not by position. The earlier positional
/// reader made the schema unextendable: adding a column meant either shifting
/// every index in lockstep (and re-running twelve locked GPU chunks to reissue the
/// on-disk tables) or shipping a silently misaligned parse. Name resolution means
/// a v1 chunk — everything this workspace measured — stays readable while new runs
/// carry [`SEG_CORPUS_V2_COLUMN`]. Every other column is still REQUIRED, so a
/// dropped or renamed one is a loud failure rather than a default.
pub(super) fn parse_corpus_csv(text: &str) -> Vec<SegCorpusRow> {
    let mut lines = text.lines();
    let header = lines.next().expect("a corpus CSV has a header");
    let names: Vec<&str> = header.split(',').map(str::trim).collect();
    let index = |column: &str| -> Option<usize> { names.iter().position(|name| *name == column) };
    for column in SEG_CORPUS_CSV_HEADER.trim_end().split(',') {
        assert!(
            index(column).is_some() || column == SEG_CORPUS_V2_COLUMN,
            "the corpus CSV is missing the required column {column:?}; header was {header:?}"
        );
    }
    let at = |column: &'static str| -> usize { index(column).expect("a required column") };
    let (circuit, layer, class) = (at("circuit"), at("layer"), at("class"));
    let (terms, sources, windows) = (at("terms"), at("sources"), at("windows"));
    let (bf, e4, proc) = (at("bf_sources"), at("e4_sources"), at("procedural_sources"));
    let (work, bpr, rows) = (at("total_static_work"), at("bytes_per_row"), at("rows"));
    let (k, status, blocks) = (at("k"), at("status"), at("blocks_per_sm"));
    let (occupancy, registers, smem) = (
        at("theoretical_occupancy_percent"),
        at("registers"),
        at("dynamic_smem_bytes"),
    );
    let (waves, spread, parity) = (at("waves"), at("max_over_mean_work"), at("parity"));
    let (median, min) = (at("median_us"), at("min_us"));
    let baseline = index(SEG_CORPUS_V2_COLUMN);
    let (ratio_at, low_at, high_at) = (at("ratio_vs_k4"), at("ci_low"), at("ci_high"));
    lines
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let field: Vec<&str> = line.split(',').collect();
            assert_eq!(field.len(), names.len(), "corpus CSV row: {line}");
            let facts = SegCoordFacts {
                circuit: field[circuit].to_owned(),
                layer: field[layer].parse().expect("layer"),
                class: SegRoundClass::parse(field[class]).expect("round class"),
                terms: field[terms].parse().expect("terms"),
                sources: field[sources].parse().expect("sources"),
                windows: field[windows].parse().expect("windows"),
                bf_sources: field[bf].parse().expect("bf sources"),
                e4_sources: field[e4].parse().expect("e4 sources"),
                procedural_sources: field[proc].parse().expect("procedural sources"),
                total_static_work: field[work].parse().expect("static work"),
                bytes_per_row: field[bpr].parse().expect("bytes per row"),
                rows: field[rows].parse().expect("rows"),
            };
            let ratio = parse_optional(field[ratio_at]).map(|median_ratio| RatioEstimate {
                median_ratio,
                ci_low: parse_optional(field[low_at]).expect("a ratio carries an interval"),
                ci_high: parse_optional(field[high_at]).expect("a ratio carries an interval"),
            });
            SegCorpusRow {
                facts,
                k: field[k].parse().expect("k"),
                status: SegCorpusStatus::parse(field[status]).expect("status"),
                blocks_per_sm: field[blocks].parse().expect("blocks/SM"),
                theoretical_occupancy: field[occupancy].parse::<f64>().expect("occupancy") / 100.0,
                registers: field[registers].parse().expect("registers"),
                dynamic_smem_bytes: field[smem].parse().expect("smem"),
                waves: field[waves].parse().expect("waves"),
                max_over_mean_work: field[spread].parse().expect("max/mean"),
                parity: match field[parity] {
                    "oracles+identity" => SegParity::OraclesAndIdentity,
                    "oracles+reference" => SegParity::OraclesAndReference,
                    "unlaunchable" => SegParity::Unlaunchable,
                    other => panic!("unknown parity label {other:?}"),
                },
                median_us: parse_optional(field[median]),
                min_us: parse_optional(field[min]),
                baseline_median_us: baseline.and_then(|at| parse_optional(field[at])),
                ratio_vs_baseline: ratio,
            }
        })
        .collect()
}

// ── The closed-form `K` policy (spec §12) ────────────────────────────────────

/// Below this per-row source footprint a coordinate takes the NARROW block.
///
/// 1,280 B/row is exactly 40 KiB per 32-row tile. **This is the scan optimum
/// ROUNDED, not the scan optimum.** [`fit_policy_thresholds`] over the corpus
/// returns 1,248 B/row, which scores 78 points over threshold at mean +0.6478%
/// against this constant's 83 at +0.6784%. The rounding is deliberate — a whole
/// tile size is a number a reader can hold and a launcher can justify, and the
/// difference is five points out of 782, inside the leave-one-circuit-out spread
/// ([`loco_validation`]) — but it IS a difference and the audit states it.
///
/// The neighbourhood is broad but not flat: 1,216–1,472 B/row all score 81–84.
pub(super) const SEG_POLICY_NARROW_BYTES_PER_ROW: usize = 1_280;

/// Above this per-row source footprint a coordinate takes the WIDEST block its
/// family can host. 18,432 B/row is exactly 576 KiB per tile.
///
/// Same story: the scan optimum is 19,200 B/row, and it is a THREE-POINT SPIKE
/// rather than a plateau — the neighbouring candidates score worse. Rounding down
/// to a whole tile size trades those three points for a constant that is not
/// balanced on a spike in one dataset.
pub(super) const SEG_POLICY_WIDE_BYTES_PER_ROW: usize = 18_432;

const _: () = assert!(SEG_POLICY_NARROW_BYTES_PER_ROW < SEG_POLICY_WIDE_BYTES_PER_ROW);

/// The closed form (spec §12), and what the corpus says its arguments are.
///
/// Spec §12 expected `k = f(sources, rows, width mix)`. The corpus says **`k` is a
/// function of the per-row source footprint alone**, and the two other candidates
/// were tested and dropped rather than assumed away:
///
///   * **rows do not enter.** The first pass measured one row count per coordinate
///     and produced a convincing "deeper grid wants a narrower block" rule — which
///     was an ARTIFACT: under one memory budget the row count is a deterministic
///     function of the footprint, so depth and weight moved together. Re-measuring
///     every coordinate at three depths, and the heavy circuits again at a six-times
///     larger budget, separates them: a LIGHT coordinate still wants `K = 4` at the
///     shallowest grid swept, and a HEAVY one still wants a wide block at the
///     deepest. Grid depth as a single feature scores no better than the constant
///     `K = 4`.
///   * **static work does not add.** `ListWorkStats`'s per-list work, the term
///     count and the source count were each fitted as the step feature; all three
///     score measurably worse than the footprint, and adding a work term on top of
///     the footprint moves nothing.
///
/// `bytes_per_row` is [`probe_geometry`]'s, i.e. the round's own window geometry:
/// `sum over windows of columns * (2 << delta) * width`, plus two E4 per published
/// column. That is exactly "sources and width mix" as one number, and a launcher can
/// compute it at setup from the binding it is about to lower.
///
/// `ceiling` is the largest `K` the compiled family can host — a register fact, not
/// a choice: 32 for R0, 24 for the continuation families (Task 9's enumeration).
///
/// The result is always a member of [`SEG_CORPUS_K`] at or below `ceiling`, and
/// never `K = 16`: on the continuation family `K = 16` and `K = 24` are both one
/// block per SM, so 16 is strictly dominated (33% occupancy against 50%), and on R0
/// no band of the corpus preferred it by enough to earn one. It is deliberately not
/// interpolated either — `K` is a block geometry, and a launcher choosing `K = 11`
/// would be choosing a shape nothing was measured at.
pub(super) fn seg_policy_k(bytes_per_row: usize, ceiling: usize) -> usize {
    seg_policy_k_with(
        bytes_per_row,
        ceiling,
        SEG_POLICY_NARROW_BYTES_PER_ROW,
        SEG_POLICY_WIDE_BYTES_PER_ROW,
    )
}

/// [`seg_policy_k`] with the two thresholds supplied rather than committed.
///
/// The fit and the leave-one-circuit-out validation both need to evaluate the
/// policy at thresholds that are NOT the committed ones; sharing this function is
/// what stops the validation from silently scoring a differently-shaped rule.
pub(super) fn seg_policy_k_with(
    bytes_per_row: usize,
    ceiling: usize,
    narrow: usize,
    wide: usize,
) -> usize {
    let want = if bytes_per_row < narrow {
        4
    } else if bytes_per_row < wide {
        8
    } else {
        24
    };
    // `want` is at least the axis minimum and so is `ceiling`, so the filter is
    // never empty; the `unwrap_or` is a total function, not a guess.
    let cap = want.min(ceiling);
    SEG_CORPUS_K
        .into_iter()
        .filter(|k| *k <= cap)
        .max()
        .unwrap_or(SEG_CORPUS_K[0])
}

/// One coordinate's verdict: what measured best, what the formula picks, and what
/// the difference costs.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct SegPolicyVerdict {
    pub(super) facts: SegCoordFacts,
    pub(super) ceiling: usize,
    pub(super) best_k: usize,
    pub(super) policy_k: usize,
    /// `median(policy_k) / median(best_k) - 1`, as a fraction.
    ///
    /// A QUOTIENT OF TWO PAIRED ESTIMATES against the same `K = 4` twin, measured
    /// in the same cell of the same run — not a quotient of two solo medians. The
    /// shared baseline is what makes it legitimate; it also means the loss inherits
    /// both estimates' intervals, so a loss under a few tenths of a percent is not
    /// resolved and the table says so.
    pub(super) loss: f64,
    /// `max_over_mean` at the policy's `K`, for the skew comparison.
    pub(super) max_over_mean_at_policy: f64,
    pub(super) best_ratio: Option<RatioEstimate>,
    pub(super) policy_ratio: Option<RatioEstimate>,
}

/// A coordinate's ranking key: its ratio against the shared `K = 4` twin, or 1.0
/// for the baseline row itself.
///
/// The ratio, never the raw median: two rows of one coordinate were measured at
/// the same rows in the same cell, but only the paired estimate removes the drift
/// between the moments they were measured at.
fn corpus_score(row: &SegCorpusRow, below_floor_counts: bool) -> Option<f64> {
    let usable = match row.status {
        SegCorpusStatus::Timed => true,
        SegCorpusStatus::BelowFloor => below_floor_counts,
        _ => false,
    };
    if !usable {
        return None;
    }
    match row.ratio_vs_baseline {
        Some(estimate) => Some(estimate.median_ratio),
        None => (row.k == SEG_CORPUS_BASELINE_K).then_some(1.0),
    }
}

/// The measured best `K` of one coordinate, with the same tie discipline the
/// Stage-A winner uses: inside [`SEG_SELECTION_TIE_FRACTION`] of the fastest,
/// prefer the SMALLEST `K` — it is the axis that costs residency.
pub(super) fn corpus_best_k(group: &[SegCorpusRow], below_floor_counts: bool) -> Option<usize> {
    let best = group
        .iter()
        .filter_map(|row| corpus_score(row, below_floor_counts))
        .fold(f64::MAX, f64::min);
    if !best.is_finite() {
        return None;
    }
    let threshold = best * (1.0 + SEG_SELECTION_TIE_FRACTION);
    group
        .iter()
        .filter(|row| corpus_score(row, below_floor_counts).is_some_and(|score| score <= threshold))
        .map(|row| row.k)
        .min()
}

/// Group a sweep's rows by coordinate and judge the formula against each.
///
/// `below_floor_counts` is the one knob: the POLICY FIT reads only coordinates
/// that reached the timing floor, and the audit's coverage section reads both, so
/// a reader can see whether the below-floor coordinates would have moved it.
pub(super) fn evaluate_policy(
    rows: &[SegCorpusRow],
    below_floor_counts: bool,
) -> Vec<SegPolicyVerdict> {
    evaluate_policy_with(
        rows,
        below_floor_counts,
        SEG_POLICY_NARROW_BYTES_PER_ROW,
        SEG_POLICY_WIDE_BYTES_PER_ROW,
    )
}

/// [`evaluate_policy`] at supplied thresholds — the fit's and the validation's
/// scoring function, and the committed policy's, so all three agree by
/// construction.
pub(super) fn evaluate_policy_with(
    rows: &[SegCorpusRow],
    below_floor_counts: bool,
    narrow: usize,
    wide: usize,
) -> Vec<SegPolicyVerdict> {
    let mut keys: Vec<(String, usize, SegRoundClass, usize)> = Vec::new();
    for row in rows {
        if !keys.contains(&row.facts.key()) {
            keys.push(row.facts.key());
        }
    }
    keys.sort();
    let mut out = Vec::new();
    for key in keys {
        let group: Vec<SegCorpusRow> = rows
            .iter()
            .filter(|row| row.facts.key() == key)
            .cloned()
            .collect();
        let Some(best_k) = corpus_best_k(&group, below_floor_counts) else {
            continue;
        };
        let facts = group[0].facts.clone();
        // The ceiling is READ OFF THE SWEEP, not assumed: a row is unlaunchable
        // exactly when the compiled family cannot host its block, so the largest
        // launchable `K` in the group IS the family's ceiling at this coordinate.
        let ceiling = group
            .iter()
            .filter(|row| row.status != SegCorpusStatus::Unlaunchable)
            .map(|row| row.k)
            .max()
            .unwrap_or(SEG_CORPUS_BASELINE_K);
        let policy_k = seg_policy_k_with(facts.bytes_per_row, ceiling, narrow, wide);
        let score = |k: usize| {
            group
                .iter()
                .find(|row| row.k == k)
                .and_then(|row| corpus_score(row, below_floor_counts))
        };
        let best_score = score(best_k).expect("the best K is a scored row");
        // A policy that names a `K` this coordinate could not measure is a loss of
        // the whole comparison, not a small one: report it as such rather than
        // silently falling back to the best.
        let loss = match score(policy_k) {
            Some(policy_score) => policy_score / best_score - 1.0,
            None => f64::INFINITY,
        };
        let ratio_of = |k: usize| {
            group
                .iter()
                .find(|row| row.k == k)
                .and_then(|row| row.ratio_vs_baseline)
        };
        out.push(SegPolicyVerdict {
            max_over_mean_at_policy: group
                .iter()
                .find(|row| row.k == policy_k)
                .map_or(0.0, |row| row.max_over_mean_work),
            facts,
            ceiling,
            best_k,
            policy_k,
            loss,
            best_ratio: ratio_of(best_k),
            policy_ratio: ratio_of(policy_k),
        });
    }
    out
}

/// The plan's threshold: a coordinate the formula loses more than this on is
/// tabulated individually.
pub(super) const SEG_POLICY_LOSS_THRESHOLD: f64 = 0.02;

/// How a set of verdicts scores: `(over threshold, mean loss, exact hits)`.
///
/// The objective the fit minimizes, lexicographically in that order — count first
/// because the plan's criterion is stated as a count, mean second to break its
/// many ties.
pub(super) fn policy_score(verdicts: &[SegPolicyVerdict]) -> (usize, f64, usize) {
    let finite: Vec<f64> = verdicts
        .iter()
        .map(|verdict| verdict.loss)
        .filter(|loss| loss.is_finite())
        .collect();
    (
        verdicts
            .iter()
            .filter(|verdict| !(verdict.loss <= SEG_POLICY_LOSS_THRESHOLD))
            .count(),
        finite.iter().sum::<f64>() / finite.len().max(1) as f64,
        verdicts
            .iter()
            .filter(|verdict| verdict.policy_k == verdict.best_k)
            .count(),
    )
}

/// One measurement point reduced to what a threshold search needs.
///
/// The fit evaluates ~15,000 threshold pairs per fold and twelve folds; doing that
/// through [`evaluate_policy_with`] would re-group 782 rows by key inside every
/// evaluation, which is quadratic and turns a seconds-long reduction into an
/// hour-long one. This is the same computation hoisted out of the loop: grouping,
/// best-`K` selection and the ceiling are properties of the DATA, and only the
/// `K` the thresholds name changes between candidates.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct SegPolicyPoint {
    pub(super) circuit: String,
    pub(super) bytes_per_row: usize,
    pub(super) ceiling: usize,
    pub(super) best_k: usize,
    /// The paired score of every scored `K`, and the best `K`'s score, so a loss is
    /// one lookup and one divide.
    pub(super) scores: Vec<(usize, f64)>,
    pub(super) best_score: f64,
}

impl SegPolicyPoint {
    /// The loss of choosing `k`: infinite if this point never measured it.
    pub(super) fn loss(&self, k: usize) -> f64 {
        self.scores
            .iter()
            .find(|(candidate, _)| *candidate == k)
            .map_or(f64::INFINITY, |(_, score)| score / self.best_score - 1.0)
    }
}

/// Reduce rows to the compact points the fit and the validation score.
pub(super) fn policy_points(
    rows: &[SegCorpusRow],
    below_floor_counts: bool,
) -> Vec<SegPolicyPoint> {
    let mut keys: Vec<(String, usize, SegRoundClass, usize)> =
        rows.iter().map(|row| row.facts.key()).collect();
    keys.sort();
    keys.dedup();
    let mut out = Vec::with_capacity(keys.len());
    for key in keys {
        let group: Vec<&SegCorpusRow> = rows.iter().filter(|row| row.facts.key() == key).collect();
        let scores: Vec<(usize, f64)> = group
            .iter()
            .filter_map(|row| corpus_score(row, below_floor_counts).map(|score| (row.k, score)))
            .collect();
        if scores.is_empty() {
            continue;
        }
        let best = scores
            .iter()
            .map(|(_, score)| *score)
            .fold(f64::MAX, f64::min);
        let threshold = best * (1.0 + SEG_SELECTION_TIE_FRACTION);
        let best_k = scores
            .iter()
            .filter(|(_, score)| *score <= threshold)
            .map(|(k, _)| *k)
            .min()
            .expect("a nonempty score set has a minimum");
        let best_score = scores
            .iter()
            .find(|(k, _)| *k == best_k)
            .map(|(_, score)| *score)
            .expect("the best K is a scored row");
        out.push(SegPolicyPoint {
            circuit: group[0].facts.circuit.clone(),
            bytes_per_row: group[0].facts.bytes_per_row,
            ceiling: group
                .iter()
                .filter(|row| row.status != SegCorpusStatus::Unlaunchable)
                .map(|row| row.k)
                .max()
                .unwrap_or(SEG_CORPUS_BASELINE_K),
            best_k,
            scores,
            best_score,
        });
    }
    out
}

/// Score a threshold pair over compact points: `(over threshold, mean loss)`.
pub(super) fn score_points(points: &[SegPolicyPoint], narrow: usize, wide: usize) -> (usize, f64) {
    let mut over = 0;
    let mut sum = 0.0;
    let mut finite = 0usize;
    for point in points {
        let loss = point.loss(seg_policy_k_with(
            point.bytes_per_row,
            point.ceiling,
            narrow,
            wide,
        ));
        if !(loss <= SEG_POLICY_LOSS_THRESHOLD) {
            over += 1;
        }
        if loss.is_finite() {
            sum += loss;
            finite += 1;
        }
    }
    (over, sum / finite.max(1) as f64)
}

/// Fit both thresholds to `rows` by exhaustive search.
///
/// The candidate set is the OBSERVED `bytes_per_row` values, not an arbitrary
/// grid: a threshold only matters where it separates two coordinates, so every
/// distinct footprint is a candidate and nothing between two of them can score
/// differently. That makes this an exact argmin over the rule's whole parameter
/// space, which is what lets [`loco_validation`] refit honestly per fold.
///
/// ~177 distinct footprints over the corpus, so ~15k threshold pairs; over the
/// compact points of [`policy_points`] the whole twelve-fold validation is a few
/// seconds of CPU on the published tables.
pub(super) fn fit_policy_thresholds(rows: &[SegCorpusRow]) -> (usize, usize) {
    fit_over_points(&policy_points(rows, false))
}

/// [`fit_policy_thresholds`] over points already reduced.
pub(super) fn fit_over_points(points: &[SegPolicyPoint]) -> (usize, usize) {
    let mut candidates: Vec<usize> = points.iter().map(|point| point.bytes_per_row).collect();
    candidates.sort_unstable();
    candidates.dedup();
    let mut best: Option<((usize, u64), (usize, usize))> = None;
    for (position, narrow) in candidates.iter().copied().enumerate() {
        for wide in candidates[position + 1..].iter().copied() {
            let (over, mean) = score_points(points, narrow, wide);
            // The mean is compared as sortable bits so the objective is a total
            // order and the argmin cannot depend on float comparison order.
            let key = ((over, (mean * 1e12) as u64), (narrow, wide));
            if best.as_ref().is_none_or(|current| key.0 < current.0) {
                best = Some(key);
            }
        }
    }
    best.map(|(_, thresholds)| thresholds)
        .expect("a corpus with at least two distinct footprints")
}

/// One fold of [`loco_validation`].
#[derive(Clone, Debug, PartialEq)]
pub(super) struct SegLocoFold {
    pub(super) held_out: String,
    pub(super) narrow: usize,
    pub(super) wide: usize,
    pub(super) points: usize,
    /// Points whose loss is finite, i.e. the denominator of `mean_loss`. Carried
    /// separately so [`loco_summary`] can pool exactly instead of weighting a mean
    /// over finite losses by a count that includes infinite ones.
    pub(super) finite: usize,
    pub(super) mean_loss: f64,
    pub(super) over_threshold: usize,
}

/// Leave-one-CIRCUIT-out validation of the fitted thresholds.
///
/// The thresholds are two degrees of freedom fitted on the same 782 points they
/// were then scored against, and the first version of this audit defended that
/// with "the optimum is broad" plus one out-of-sample point — a defence that was
/// **wrong on its own terms** (see the K-policy section: that point disagrees with
/// the policy). This is the defence that actually holds: refit BOTH thresholds on
/// eleven circuits, score the twelfth, and repeat.
///
/// Leave-one-CIRCUIT-out rather than leave-one-point-out because the points are
/// not independent — 782 points are 285 coordinates measured at up to four depths,
/// and a held-out point whose own coordinate stayed in the training set is not
/// held out in any useful sense. Circuits are the coarsest grouping the corpus
/// offers and the only one that removes a whole family of related coordinates.
pub(super) fn loco_validation(rows: &[SegCorpusRow]) -> Vec<SegLocoFold> {
    let mut circuits: Vec<String> = rows.iter().map(|row| row.facts.circuit.clone()).collect();
    circuits.sort();
    circuits.dedup();
    circuits
        .into_iter()
        .map(|held_out| {
            let train: Vec<SegCorpusRow> = rows
                .iter()
                .filter(|row| row.facts.circuit != held_out)
                .cloned()
                .collect();
            let test: Vec<SegCorpusRow> = rows
                .iter()
                .filter(|row| row.facts.circuit == held_out)
                .cloned()
                .collect();
            let (narrow, wide) = fit_over_points(&policy_points(&train, false));
            let held = policy_points(&test, false);
            let (over, mean) = score_points(&held, narrow, wide);
            let finite = held
                .iter()
                .filter(|point| {
                    point
                        .loss(seg_policy_k_with(
                            point.bytes_per_row,
                            point.ceiling,
                            narrow,
                            wide,
                        ))
                        .is_finite()
                })
                .count();
            SegLocoFold {
                held_out,
                narrow,
                wide,
                points: held.len(),
                finite,
                mean_loss: mean,
                over_threshold: over,
            }
        })
        .collect()
}

/// What the static per-list work model says about measured `K` scaling.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct SegCriticalPathFit {
    pub(super) pairs: usize,
    pub(super) pearson: f64,
    pub(super) spearman: f64,
    pub(super) predicted_median: f64,
    pub(super) measured_median: f64,
}

/// Correlate the static critical-path prediction with the measured `K` ratio.
///
/// The static model says a block finishes when its slowest list does, so its
/// per-`K` prediction is `(max_over_mean(K) / K) / (max_over_mean(4) / 4)` — the
/// busiest list's work at `K`, relative to the busiest list's work at the baseline.
/// The measurement is the paired ratio the same row carries.
///
/// Committed rather than computed once in a scratch script: the audit's skew
/// section quotes these four numbers, and a number in an audit that cannot be
/// regenerated from the published tables is an assertion, not a measurement.
pub(super) fn static_critical_path_correlation(rows: &[SegCorpusRow]) -> SegCriticalPathFit {
    let mut groups: Vec<(String, usize, SegRoundClass, usize)> =
        rows.iter().map(|row| row.facts.key()).collect();
    groups.sort();
    groups.dedup();
    let mut predicted = Vec::new();
    let mut measured = Vec::new();
    for key in groups {
        let group: Vec<&SegCorpusRow> = rows.iter().filter(|row| row.facts.key() == key).collect();
        let Some(base) = group
            .iter()
            .find(|row| row.k == SEG_CORPUS_BASELINE_K && row.status.measured())
        else {
            continue;
        };
        if base.max_over_mean_work <= 0.0 {
            continue;
        }
        let reference = base.max_over_mean_work / SEG_CORPUS_BASELINE_K as f64;
        for row in &group {
            let (Some(ratio), true) = (row.ratio_vs_baseline, row.status.measured()) else {
                continue;
            };
            if row.max_over_mean_work <= 0.0 {
                continue;
            }
            predicted.push((row.max_over_mean_work / row.k as f64) / reference);
            measured.push(ratio.median_ratio);
        }
    }
    SegCriticalPathFit {
        pairs: predicted.len(),
        pearson: pearson(&predicted, &measured),
        spearman: spearman(&predicted, &measured),
        predicted_median: if predicted.is_empty() {
            f64::NAN
        } else {
            median(&predicted)
        },
        measured_median: if measured.is_empty() {
            f64::NAN
        } else {
            median(&measured)
        },
    }
}

/// Pearson's product-moment correlation. `NaN` for fewer than two points or a
/// degenerate side.
pub(super) fn pearson(lhs: &[f64], rhs: &[f64]) -> f64 {
    assert_eq!(lhs.len(), rhs.len());
    let n = lhs.len();
    if n < 2 {
        return f64::NAN;
    }
    let mean = |values: &[f64]| values.iter().sum::<f64>() / n as f64;
    let (mean_lhs, mean_rhs) = (mean(lhs), mean(rhs));
    let mut covariance = 0.0;
    let mut variance_lhs = 0.0;
    let mut variance_rhs = 0.0;
    for (left, right) in lhs.iter().zip(rhs.iter()) {
        covariance += (left - mean_lhs) * (right - mean_rhs);
        variance_lhs += (left - mean_lhs).powi(2);
        variance_rhs += (right - mean_rhs).powi(2);
    }
    covariance / (variance_lhs.sqrt() * variance_rhs.sqrt())
}

/// Spearman's rank correlation, by Pearson over ordinal ranks.
///
/// Ties take their ordinal position rather than a mid-rank. Over 2,544 pairs of
/// continuous timings, ties are rare enough that the difference is far below the
/// third decimal this is quoted to; the simplification is stated rather than left
/// for a reader to discover.
pub(super) fn spearman(lhs: &[f64], rhs: &[f64]) -> f64 {
    fn ranks(values: &[f64]) -> Vec<f64> {
        let mut order: Vec<usize> = (0..values.len()).collect();
        order.sort_by(|left, right| {
            values[*left]
                .partial_cmp(&values[*right])
                .expect("finite sample")
        });
        let mut out = vec![0.0; values.len()];
        for (rank, index) in order.into_iter().enumerate() {
            out[index] = rank as f64;
        }
        out
    }
    pearson(&ranks(lhs), &ranks(rhs))
}

/// The pooled leave-one-circuit-out figures: `(points, mean loss, over threshold)`.
///
/// Pooled over folds by POINT, not averaged over folds, so a twelve-point circuit
/// does not weigh the same as a 168-point one.
pub(super) fn loco_summary(folds: &[SegLocoFold]) -> (usize, f64, usize) {
    let points: usize = folds.iter().map(|fold| fold.points).sum();
    let finite: usize = folds.iter().map(|fold| fold.finite).sum();
    let weighted: f64 = folds
        .iter()
        .map(|fold| fold.mean_loss * fold.finite as f64)
        .sum();
    (
        points,
        weighted / finite.max(1) as f64,
        folds.iter().map(|fold| fold.over_threshold).sum(),
    )
}

// ── The sweep driver ─────────────────────────────────────────────────────────

/// The largest launchable `K` of each regime's production family, probed once.
#[derive(Clone, Copy, Debug)]
pub(super) struct SegKCeilings {
    pub(super) r0: usize,
    pub(super) ext: usize,
}

impl SegKCeilings {
    fn probe() -> Self {
        let largest = |regime| {
            seg_launchable_k_axis(
                regime,
                ProgramMode::Inline,
                CoeffMode::Constant,
                BwdSegEpilogue::Plane,
            )
            .into_iter()
            .filter(|(_, blocks)| *blocks > 0)
            .map(|(k, _)| k as usize)
            .max()
            .expect("a production family hosts at least one K")
        };
        Self {
            r0: largest(BwdRegime::R0),
            ext: largest(BwdRegime::Ext),
        }
    }

    fn of(&self, regime: BwdRegime) -> usize {
        match regime {
            BwdRegime::R0 => self.r0,
            _ => self.ext,
        }
    }
}

/// The circuits this invocation sweeps.
///
/// The whole corpus in one locked run would be a single very long section, so the
/// driver takes a chunk: `BWD_SEG_CORPUS_CIRCUITS=keccak_special5,blake2_g_function`
/// (short names, comma-separated) or `all`. Each chunk publishes its own CSV and
/// the policy pass reads every chunk's, so chunking changes only how the run is
/// scheduled, never what it covers.
fn corpus_chunk() -> Vec<&'static str> {
    let requested = std::env::var("BWD_SEG_CORPUS_CIRCUITS").unwrap_or_else(|_| "all".to_owned());
    if requested.trim() == "all" {
        return SEG_CORPUS_LAYOUTS.to_vec();
    }
    requested
        .split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(|name| {
            SEG_CORPUS_LAYOUTS
                .into_iter()
                .find(|layout| short_name(layout) == name || *layout == name)
                .unwrap_or_else(|| {
                    panic!(
                        "BWD_SEG_CORPUS_CIRCUITS names {name:?}, which is not a corpus layout; \
                         the corpus is {:?}",
                        SEG_CORPUS_LAYOUTS.map(short_name)
                    )
                })
        })
        .collect()
}

fn corpus_csv_name(chunk: &[&'static str], budget: usize, profiled: bool) -> String {
    // A PROFILED run is not a chunk. `ncu` serializes and replays the launches it
    // intercepts, so every median in that process is perturbed; publishing it under
    // the chunk prefix would silently merge profiler timings into the corpus table
    // (and, because the same coordinate is then present twice, would show up as a
    // 250% "run-to-run band"). Learned the hard way.
    if profiled {
        return "seg_profiled_corpus_run.csv".to_owned();
    }
    let circuits = if chunk.len() == SEG_CORPUS_LAYOUTS.len() {
        "all".to_owned()
    } else {
        chunk
            .iter()
            .map(|layout| short_name(layout))
            .collect::<Vec<_>>()
            .join("+")
    };
    // The budget rides in the NAME, so a deep re-run of the heavy circuits lands
    // beside the default-budget table instead of overwriting it. The two together
    // are what separate grid depth from coordinate weight.
    if budget == SEG_CORPUS_DEFAULT_BUDGET_BYTES {
        format!("seg_corpus_{circuits}.csv")
    } else {
        format!("seg_corpus_{circuits}_{}gib.csv", budget >> 30)
    }
}

/// The ONE `(circuit, layer, class, K)` this invocation wraps in the profiler's
/// NVTX range, from `BWD_SEG_CORPUS_PROFILE=<circuit>:<layer>:<class>:<K>`.
///
/// The corpus sweep's own answer to the plan's skew question is a wall-time
/// comparison against the static work model, which is a proxy. This is how the
/// direct observable is reached: warps of one block join at the epilogue, so a
/// warp that finishes its list early waits there, and `ncu`'s barrier stall is
/// warp-completion skew measured rather than modelled. One shape per capture,
/// selected the same way [`profile_shape`] selects the Stage-A one.
fn corpus_profile_target() -> Option<(String, usize, SegRoundClass, usize)> {
    let spec = std::env::var("BWD_SEG_CORPUS_PROFILE").ok()?;
    let field: Vec<&str> = spec.split(':').map(str::trim).collect();
    assert_eq!(
        field.len(),
        4,
        "BWD_SEG_CORPUS_PROFILE must be <circuit>:<layer>:<class>:<K>, got {spec:?}"
    );
    let class = SegRoundClass::parse(field[2]).unwrap_or_else(|| {
        panic!(
            "BWD_SEG_CORPUS_PROFILE names class {:?}; the classes are {:?}",
            field[2],
            SEG_ROUND_CLASSES.map(SegRoundClass::label)
        )
    });
    let k: usize = field[3].parse().expect("BWD_SEG_CORPUS_PROFILE K");
    assert!(
        SEG_CORPUS_K.contains(&k),
        "BWD_SEG_CORPUS_PROFILE names K{k}, which is not on the axis {SEG_CORPUS_K:?}"
    );
    Some((
        field[0].to_owned(),
        field[1].parse().expect("layer"),
        class,
        k,
    ))
}

/// **The corpus sweep.** Every coordinate of the requested circuits, at every
/// round class, over [`SEG_CORPUS_K`], certified before every timing.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_corpus_sweep() {
    let chunk = corpus_chunk();
    let budget = corpus_budget_bytes();
    let profile = corpus_profile_target();
    let context = make_seg_spike_context(SEG_CONT_ARENA_BYTES);
    let device = SegDeviceFacts::query();
    let ceilings = SegKCeilings::probe();
    let (eq_low, eq_sizes) = build_shared_eq(24, &context);
    let host_eq = HostEq::download(eq_low.as_ptr(), eq_sizes, &context);
    eprintln!(
        "[seg-corpus] chunk {:?}; K axis {SEG_CORPUS_K:?}; ceilings R0={} Ext={}; target {} rows \
         within {} GiB per cell",
        chunk.iter().map(|c| short_name(c)).collect::<Vec<_>>(),
        ceilings.r0,
        ceilings.ext,
        SEG_CORPUS_TARGET_ROWS,
        budget >> 30,
    );

    let mut rows = Vec::new();
    for circuit in &chunk {
        let layers = seg_coordinate_layers(circuit);
        eprintln!(
            "[seg-corpus] {}: {} layers with backward roots",
            short_name(circuit),
            layers.len()
        );
        for layer in layers {
            for class in SEG_ROUND_CLASSES {
                rows.extend(measure_corpus_cell(
                    circuit,
                    layer,
                    class,
                    profile.as_ref(),
                    &host_eq,
                    eq_low.as_ptr(),
                    eq_sizes,
                    &device,
                    &context,
                ));
            }
        }
    }

    let csv = seg_output_path(&corpus_csv_name(&chunk, budget, profile.is_some()));
    publish(&csv, &render_corpus_csv(&rows));
    let count = |status| rows.iter().filter(|row| row.status == status).count();
    let coordinates = distinct_count(rows.iter().map(|row| row.facts.coordinate()));
    let points = distinct_count(rows.iter().map(|row| row.facts.key()));
    eprintln!(
        "[seg-corpus] {coordinates} coordinates over {points} depth points, {} cells: \
         timed {}, below-floor {}, over-budget {}, unlaunchable {}, lower-rejected {} -> {}",
        rows.len(),
        count(SegCorpusStatus::Timed),
        count(SegCorpusStatus::BelowFloor),
        count(SegCorpusStatus::OverBudget),
        count(SegCorpusStatus::Unlaunchable),
        count(SegCorpusStatus::LowerRejected),
        csv.display(),
    );
    assert!(!rows.is_empty(), "the sweep must record every coordinate");
    // Every launchable cell is certified; the certification itself panics on a
    // mismatch, so this asserts that the accounting agrees with what ran rather
    // than re-checking the values.
    for row in &rows {
        assert_eq!(
            row.status.measured(),
            row.parity != SegParity::Unlaunchable,
            "{} K{}: a measured cell must carry a certificate",
            row.facts.label(),
            row.k
        );
        // The family ceiling was probed ONCE up front and every cell probes its own
        // geometry again inside `measure_shape`; the two are independent paths onto
        // the same register limit and must not disagree. (Host lowering never
        // rejects on `K` inside the axis, so an above-ceiling row can only be
        // unlaunchable.)
        if row.status == SegCorpusStatus::OverBudget {
            continue;
        }
        assert_eq!(
            row.k > ceilings.of(row.facts.class.regime()),
            row.status == SegCorpusStatus::Unlaunchable,
            "{} K{}: the per-family ceiling probe and the per-cell occupancy probe \
             disagree (ceiling R0={} Ext={})",
            row.facts.label(),
            row.k,
            ceilings.r0,
            ceilings.ext,
        );
    }
    drop(eq_low);
}

/// Sweep ONE `(circuit, layer, round class)` coordinate: the whole `K` axis at
/// every rung of the row ladder.
#[allow(clippy::too_many_arguments)]
fn measure_corpus_cell(
    circuit: &'static str,
    layer: usize,
    class: SegRoundClass,
    profile: Option<&(String, usize, SegRoundClass, usize)>,
    eq: &HostEq,
    eq_low: *const E4,
    eq_sizes: EqSizes,
    device: &SegDeviceFacts,
    context: &ProverContext,
) -> Vec<SegCorpusRow> {
    let regime = class.regime();
    let coord = lean_coordinate(circuit, layer, regime);
    let round = class.round();
    let d2 = class.d2();
    let budget = corpus_budget_bytes();
    let probe = probe_geometry(&coord, round, d2);
    let (top_rows, _) = fit_rows(
        SEG_CORPUS_TARGET_ROWS,
        probe.bytes_per_row,
        budget,
        SEG_CORPUS_MIN_ROWS,
    );
    let facts_at = |rows: usize| SegCoordFacts {
        circuit: short_name(circuit).to_owned(),
        layer,
        class,
        terms: coord.layer.terms.len(),
        sources: coord.layer.sources.len(),
        windows: probe.windows,
        bf_sources: probe.bf_sources,
        e4_sources: probe.e4_sources,
        procedural_sources: probe.procedural_sources,
        total_static_work: 0,
        bytes_per_row: probe.bytes_per_row,
        rows,
    };

    if top_rows.saturating_mul(probe.bytes_per_row) > budget {
        let facts = facts_at(top_rows);
        eprintln!(
            "[seg-corpus] {}: OVER BUDGET -- {} B/row needs {:.1} GiB at the \
             {top_rows}-row minimum",
            facts.label(),
            probe.bytes_per_row,
            (top_rows * probe.bytes_per_row) as f64 / (1u64 << 30) as f64,
        );
        return SEG_CORPUS_K
            .into_iter()
            .map(|k| SegCorpusRow::untimed(facts.clone(), k, SegCorpusStatus::OverBudget))
            .collect();
    }

    // One parity twin for the whole ladder: it is a property of the
    // `(coordinate, round, policy)`, not of the row count, and rebuilding it per
    // rung would triple the oracle cost for an identical certificate.
    let parity = SegCell::build(
        Arc::clone(&coord),
        round,
        SEG_PARITY_ROWS,
        true,
        d2,
        eq_low,
        eq_sizes,
        context,
    );

    let mut out = Vec::with_capacity(SEG_CORPUS_K.len() * SEG_CORPUS_ROW_STEPS.len());
    for step in SEG_CORPUS_ROW_STEPS {
        let rows = top_rows / step;
        // A rung under the timing floor is DROPPED rather than measured: the ladder
        // varies grid depth, and a below-floor rung would vary the protocol with it.
        // The TOP rung is always kept, even below the floor — that is the
        // coordinate's only measurement, and it is recorded as below-floor.
        if step != 1 && rows < SEG_MIN_TIMED_ROWS {
            continue;
        }
        // Only the TOP rung is ever profiled: a capture is one launch, and the
        // rung a reader means by "this coordinate" is the one it was fitted at.
        let profile_k = profile.and_then(|(c, l, cl, k)| {
            (step == 1 && *c == short_name(circuit) && *l == layer && *cl == class).then_some(*k)
        });
        out.extend(measure_corpus_rung(
            &coord,
            facts_at(rows),
            round,
            d2,
            rows,
            profile_k,
            eq,
            eq_low,
            eq_sizes,
            device,
            &parity,
            context,
        ));
    }
    drop(parity);
    out
}

/// One rung of the ladder: a `(coordinate, round, policy, rows)` cell over the
/// whole `K` axis, paired against its own `K = 4` twin.
#[allow(clippy::too_many_arguments)]
fn measure_corpus_rung(
    coord: &Arc<SegCoordinate>,
    mut facts: SegCoordFacts,
    round: u8,
    d2: D2Policy,
    rows: usize,
    profile_k: Option<usize>,
    eq: &HostEq,
    eq_low: *const E4,
    eq_sizes: EqSizes,
    device: &SegDeviceFacts,
    parity: &SegCell,
    context: &ProverContext,
) -> Vec<SegCorpusRow> {
    let below_floor = rows < SEG_MIN_TIMED_ROWS;
    let timed = SegCell::build(
        Arc::clone(coord),
        round,
        rows,
        !below_floor,
        d2,
        eq_low,
        eq_sizes,
        context,
    );

    // Lower every `K` BEFORE launching anything. The work model is a property of
    // the lowering, so this is also how an unlaunchable or rejected cell still
    // contributes its `max_over_mean`.
    let lowered: Vec<Result<ListWorkStats, BwdSegLowerError>> = SEG_CORPUS_K
        .into_iter()
        .map(|k| timed.try_lower(corpus_shape(k)).map(|setup| setup.work))
        .collect();
    facts.total_static_work = SEG_CORPUS_K
        .into_iter()
        .zip(lowered.iter())
        .find_map(|(k, work)| {
            work.as_ref()
                .ok()
                .map(|w| (w.mean_work * k as f64).round() as u64)
        })
        .unwrap_or(0);
    eprintln!(
        "[seg-corpus] {}: {} terms, {} sources ({} bf / {} e4 / {} proc), {} windows, work {}, \
         {} B/row -> {rows} rows ({:.2} GiB, below_floor={below_floor})",
        facts.label(),
        facts.terms,
        facts.sources,
        facts.bf_sources,
        facts.e4_sources,
        facts.procedural_sources,
        facts.windows,
        facts.total_static_work,
        facts.bytes_per_row,
        (rows * facts.bytes_per_row) as f64 / (1u64 << 30) as f64,
    );

    let benchmark = facts.label();
    let mut reference: Option<Vec<E4>> = None;
    let mut out: Vec<SegCorpusRow> = Vec::with_capacity(SEG_CORPUS_K.len());

    // The baseline `K` first, for the two reasons Stage B established: it is the
    // identity reference every other `K` must reproduce bit for bit, and it is the
    // twin they are paired against.
    let baseline_shape = corpus_shape(SEG_CORPUS_BASELINE_K);
    let twin = match &lowered[0] {
        Err(error) => {
            eprintln!(
                "[seg-corpus] {benchmark} K{SEG_CORPUS_BASELINE_K}: LOWER REJECTED {error:?}"
            );
            out.push(SegCorpusRow::untimed(
                facts.clone(),
                SEG_CORPUS_BASELINE_K,
                SegCorpusStatus::LowerRejected,
            ));
            None
        }
        Ok(work) => {
            let row = measure_shape(
                &benchmark,
                &timed,
                parity,
                baseline_shape,
                eq,
                device,
                &mut reference,
                None,
                profile_k == Some(SEG_CORPUS_BASELINE_K),
                context,
            );
            let launchable = row.launchable();
            out.push(corpus_row(facts.clone(), *work, &row, below_floor));
            launchable.then(|| timed.prepare(baseline_shape, context))
        }
    };

    for (index, k) in SEG_CORPUS_K.into_iter().enumerate().skip(1) {
        let work = match &lowered[index] {
            Err(error) => {
                eprintln!("[seg-corpus] {benchmark} K{k}: LOWER REJECTED {error:?}");
                out.push(SegCorpusRow::untimed(
                    facts.clone(),
                    k,
                    SegCorpusStatus::LowerRejected,
                ));
                continue;
            }
            Ok(work) => *work,
        };
        let shape = corpus_shape(k);
        let row = match &twin {
            Some(twin) => measure_shape(
                &benchmark,
                &timed,
                parity,
                shape,
                eq,
                device,
                &mut reference,
                Some((SEG_CORPUS_BASELINE_LABEL, &|ctx: &ProverContext| {
                    twin.launch(ctx)
                })),
                profile_k == Some(k),
                context,
            ),
            None => measure_shape(
                &benchmark,
                &timed,
                parity,
                shape,
                eq,
                device,
                &mut reference,
                None,
                profile_k == Some(k),
                context,
            ),
        };
        out.push(corpus_row(facts.clone(), work, &row, below_floor));
    }

    drop(twin);
    drop(timed);
    out
}

/// Fold one measured [`SegMatrixRow`] and the coordinate's facts into a corpus row.
fn corpus_row(
    facts: SegCoordFacts,
    work: ListWorkStats,
    row: &SegMatrixRow,
    below_floor: bool,
) -> SegCorpusRow {
    let status = if !row.launchable() {
        SegCorpusStatus::Unlaunchable
    } else if below_floor {
        SegCorpusStatus::BelowFloor
    } else {
        SegCorpusStatus::Timed
    };
    SegCorpusRow {
        facts,
        k: row.shape.k,
        status,
        blocks_per_sm: row.blocks_per_sm,
        theoretical_occupancy: row.theoretical_occupancy,
        registers: row.attributes.registers,
        dynamic_smem_bytes: row.dynamic_smem_bytes,
        waves: row.waves,
        max_over_mean_work: work.max_over_mean,
        parity: row.parity,
        median_us: status.measured().then_some(row.candidate_median_us),
        min_us: status.measured().then_some(row.candidate_min_us),
        baseline_median_us: status
            .measured()
            .then_some(row.incumbent_median_us)
            .flatten(),
        ratio_vs_baseline: status.measured().then_some(row.ratio).flatten(),
    }
}

// ── The policy pass ──────────────────────────────────────────────────────────

/// Every corpus chunk this workspace has measured, in one table.
///
/// Reads the published CSVs rather than re-measuring: the sweep is chunked across
/// locked runs, so the policy must be derivable from their union without a GPU.
pub(super) fn load_corpus_tables() -> (Vec<SegCorpusRow>, SegCorpusRepeats) {
    let directory = PathBuf::from(SEG_OUTPUT_DIR);
    let mut files: Vec<PathBuf> = std::fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.starts_with(SEG_CORPUS_CHUNK_PREFIX) && name.ends_with(".csv")
                })
        })
        .collect();
    files.sort();
    let mut rows = Vec::new();
    for file in &files {
        let text = std::fs::read_to_string(file)
            .unwrap_or_else(|error| panic!("read {}: {error}", file.display()));
        rows.extend(parse_corpus_csv(&text));
    }
    // Two chunks CAN cover the same measurement point — a re-run at a larger
    // budget re-measures every coordinate the budget did not move, and a
    // deliberate repeat of one chunk is how the run-to-run band is measured at all.
    // So a repeat is folded rather than rejected: the FIRST reading is kept (chunk
    // files are read in sorted order, so which one that is, is deterministic) and
    // every later reading of the same point contributes its relative disagreement
    // to the band. Silently averaging them would hide exactly the quantity the
    // solo-protocol discipline requires to be reported.
    let mut kept: Vec<SegCorpusRow> = Vec::with_capacity(rows.len());
    let mut band: Vec<f64> = Vec::new();
    for row in rows {
        let point = (row.facts.key(), row.k);
        match kept
            .iter()
            .find(|other| (other.facts.key(), other.k) == point)
        {
            None => kept.push(row),
            Some(first) => {
                if let (Some(a), Some(b)) = (first.median_us, row.median_us) {
                    band.push((b - a).abs() / a);
                }
            }
        }
    }
    assert_corpus_coverage(&kept, &files);
    (kept, SegCorpusRepeats { band, files })
}

/// Layers with backward roots across [`SEG_CORPUS_LAYOUTS`] — the Task-4 census
/// freeze, restated here so the coverage assertion has something to compare to
/// without lowering twelve DAGs.
pub(super) const SEG_CORPUS_LAYER_COUNT: usize = 57;
/// `(coordinate, round class)` cells the corpus has: 57 layers x 5 classes.
pub(super) const SEG_CORPUS_CLASS_CELL_COUNT: usize =
    SEG_CORPUS_LAYER_COUNT * SEG_ROUND_CLASSES.len();

/// The union of the chunk tables must BE the corpus.
///
/// Without this the policy is a function of which files happen to be on disk. A
/// chunk that was never run, or one deleted to resolve a stale-data problem,
/// silently narrows the corpus and moves both thresholds — and the reduction would
/// publish the narrowed result with the same confident headline. Asserted before
/// anything is published rather than reported afterwards, because the failure mode
/// is a plausible-looking number, not a crash.
pub(super) fn assert_corpus_coverage(rows: &[SegCorpusRow], files: &[PathBuf]) {
    let named = |paths: &[PathBuf]| {
        paths
            .iter()
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    let mut circuits: Vec<&str> = rows.iter().map(|row| row.facts.circuit.as_str()).collect();
    circuits.sort_unstable();
    circuits.dedup();
    let mut expected: Vec<&str> = SEG_CORPUS_LAYOUTS.iter().copied().map(short_name).collect();
    expected.sort_unstable();
    assert_eq!(
        circuits,
        expected,
        "the chunk tables under {SEG_OUTPUT_DIR} do not cover the corpus; found {} of {}          circuits across [{}] -- re-run the missing chunk instead of publishing a policy          fitted on part of the corpus",
        circuits.len(),
        expected.len(),
        named(files),
    );
    let layers = distinct_count(rows.iter().map(|row| (&row.facts.circuit, row.facts.layer)));
    assert_eq!(
        layers, SEG_CORPUS_LAYER_COUNT,
        "the chunk tables cover {layers} layers; the corpus has {SEG_CORPUS_LAYER_COUNT}"
    );
    let cells = distinct_count(rows.iter().map(|row| row.facts.coordinate()));
    assert_eq!(
        cells, SEG_CORPUS_CLASS_CELL_COUNT,
        "the chunk tables cover {cells} (coordinate, round class) cells; the corpus has          {SEG_CORPUS_CLASS_CELL_COUNT}"
    );
}

/// The `K = 4` twin's median AS MEASURED INSIDE THE PAIRED LOOP, reconstructed
/// from the group's paired rows.
///
/// This is the protocol-consistent anchor. `median_us` on the `K = 4` row is a
/// SOLO median — measured on its own, before any interleaving — while every other
/// row's `median_us` is the candidate half of an interleaved pair. Dividing one by
/// the other silently crosses protocols, and on this corpus that is not
/// hypothetical: 23 of 792 points disagree by more than 10% between the two
/// readings of the same baseline (19 of them R0, which is swept first in each
/// chunk and therefore pays a cold-clock cost on its solo baseline), worst
/// **1.795x** on `blake2_g_function` L0 R0.
///
/// Reconstructed as the median over paired rows of `candidate_median / ratio`,
/// because schema v1 chunks did not record the baseline's own median. On a v2
/// chunk [`SegCorpusRow::baseline_median_us`] carries it directly and the two
/// agree; the reconstruction is used regardless so a mixed-schema workspace
/// reduces one way.
pub(super) fn interleaved_baseline_median(group: &[SegCorpusRow]) -> Option<f64> {
    let mut samples: Vec<f64> = group
        .iter()
        .filter_map(|row| {
            let ratio = row.ratio_vs_baseline?.median_ratio;
            let median = row.median_us?;
            (ratio > 0.0).then_some(median / ratio)
        })
        .collect();
    if samples.is_empty() {
        return None;
    }
    samples.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite median"));
    Some(median_of_sorted(&samples))
}

/// What the repeated measurement points in a loaded table say about run-to-run
/// spread — the band every SOLO median in this sweep has to be read against.
pub(super) struct SegCorpusRepeats {
    pub(super) band: Vec<f64>,
    pub(super) files: Vec<PathBuf>,
}

impl SegCorpusRepeats {
    /// `(repeats, median, p90, worst)` of the relative disagreement, as fractions.
    pub(super) fn summary(&self) -> (usize, f64, f64, f64) {
        if self.band.is_empty() {
            return (0, f64::NAN, f64::NAN, f64::NAN);
        }
        let mut sorted = self.band.clone();
        sorted.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite band"));
        (
            sorted.len(),
            median_of_sorted(&sorted),
            percentile(&sorted, 0.9),
            *sorted.last().expect("nonempty"),
        )
    }
}

/// How many distinct values an iterator yields.
fn distinct_count<T: Ord>(items: impl Iterator<Item = T>) -> usize {
    let mut all: Vec<T> = items.collect();
    all.sort();
    all.dedup();
    all.len()
}

/// The per-round-class summary the audit's corpus table is.
fn render_class_summary(rows: &[SegCorpusRow]) -> String {
    let mut body = String::from(
        "| round class | coordinates | depth points | timed | below floor | over budget | \
         unlaunchable cells | lower-rejected cells | best K (mode) |\n\
         |---|---|---|---|---|---|---|---|---|\n",
    );
    for class in SEG_ROUND_CLASSES {
        let group: Vec<SegCorpusRow> = rows
            .iter()
            .filter(|row| row.facts.class == class)
            .cloned()
            .collect();
        if group.is_empty() {
            continue;
        }
        let coordinates = distinct_count(group.iter().map(|row| row.facts.coordinate()));
        let points = distinct_count(group.iter().map(|row| row.facts.key()));
        let count = |status| group.iter().filter(|row| row.status == status).count();
        let verdicts = evaluate_policy(&group, false);
        let mut modes: Vec<(usize, usize)> = SEG_CORPUS_K
            .into_iter()
            .map(|k| (verdicts.iter().filter(|v| v.best_k == k).count(), k))
            .collect();
        modes.sort_by(|lhs, rhs| rhs.cmp(lhs));
        writeln!(
            body,
            "| {} | {coordinates} | {points} | {} | {} | {} | {} | {} | K{} ({} of {}) |",
            class.label(),
            count(SegCorpusStatus::Timed),
            count(SegCorpusStatus::BelowFloor),
            count(SegCorpusStatus::OverBudget),
            count(SegCorpusStatus::Unlaunchable),
            count(SegCorpusStatus::LowerRejected),
            modes[0].1,
            modes[0].0,
            verdicts.len(),
        )
        .expect("write String");
    }
    body
}

/// The loss table: every coordinate the closed form gives up more than
/// [`SEG_POLICY_LOSS_THRESHOLD`] on.
fn render_loss_table(verdicts: &[SegPolicyVerdict]) -> String {
    let mut body = String::from(
        "| coordinate | terms | sources (bf/e4/proc) | static work | rows | ceiling | best K | \
         policy K | loss |\n|---|---|---|---|---|---|---|---|---|\n",
    );
    for verdict in verdicts {
        writeln!(
            body,
            "| {} | {} | {} ({}/{}/{}) | {} | {} | {} | K{} | K{} | {} |",
            verdict.facts.label(),
            verdict.facts.terms,
            verdict.facts.sources,
            verdict.facts.bf_sources,
            verdict.facts.e4_sources,
            verdict.facts.procedural_sources,
            verdict.facts.total_static_work,
            verdict.facts.rows,
            verdict.ceiling,
            verdict.best_k,
            verdict.policy_k,
            if verdict.loss.is_finite() {
                format!("{:+.2}%", verdict.loss * 100.0)
            } else {
                "policy K not measurable here".to_owned()
            },
        )
        .expect("write String");
    }
    body
}

/// **The K policy pass.** Reads every published corpus chunk, derives the best `K`
/// per coordinate, scores the closed form against it and publishes both tables.
///
/// No GPU: the sweep already did the measuring, and a policy that could only be
/// re-derived on the machine that measured it would be unreviewable.
#[test]
#[ignore = "reads the corpus sweep's published CSVs; run bwd_seg_corpus_sweep first"]
fn bwd_seg_corpus_k_policy() {
    let (rows, repeats) = load_corpus_tables();
    let files = &repeats.files;
    assert!(
        !rows.is_empty(),
        "no corpus chunk under {SEG_OUTPUT_DIR}; run bwd_seg_corpus_sweep first"
    );
    let verdicts = evaluate_policy(&rows, false);
    let with_below_floor = evaluate_policy(&rows, true);
    let over: Vec<SegPolicyVerdict> = verdicts
        .iter()
        .filter(|verdict| !(verdict.loss <= SEG_POLICY_LOSS_THRESHOLD))
        .cloned()
        .collect();
    let exact = verdicts
        .iter()
        .filter(|verdict| verdict.policy_k == verdict.best_k)
        .count();
    let losses: Vec<f64> = verdicts
        .iter()
        .map(|verdict| verdict.loss)
        .filter(|loss| loss.is_finite())
        .collect();
    let worst = losses.iter().copied().fold(0.0f64, f64::max);
    let (repeated, band_median, band_p90, band_worst) = repeats.summary();
    eprintln!(
        "[seg-corpus] policy over {} coordinates ({} chunk files, {repeated} repeated \
         points: median {:.3}%, p90 {:.3}%, worst {:.3}%): exact {exact}, \
         mean loss {:+.3}%, worst {:+.2}%, over {:.0}% threshold {} | with below-floor \
         coordinates included {} coordinates",
        verdicts.len(),
        files.len(),
        band_median * 100.0,
        band_p90 * 100.0,
        band_worst * 100.0,
        losses.iter().sum::<f64>() / losses.len().max(1) as f64 * 100.0,
        worst * 100.0,
        SEG_POLICY_LOSS_THRESHOLD * 100.0,
        over.len(),
        with_below_floor.len(),
    );

    // The skew comparison the plan asks for: the static per-list work model
    // against the coordinates where more warps stopped paying. Reported, never
    // asserted — a correlation is evidence for a follow-up lever, not a gate.
    let skew: Vec<(f64, f64)> = verdicts
        .iter()
        .filter(|verdict| verdict.loss.is_finite() && verdict.max_over_mean_at_policy > 0.0)
        .map(|verdict| (verdict.max_over_mean_at_policy, verdict.loss))
        .collect();
    let mean_skew = skew.iter().map(|(spread, _)| spread).sum::<f64>() / skew.len().max(1) as f64;
    let worst_skew = skew
        .iter()
        .map(|(spread, _)| *spread)
        .fold(0.0f64, f64::max);
    let critical_path = static_critical_path_correlation(&rows);

    // Leave-one-CIRCUIT-out: refit BOTH thresholds on eleven circuits, score the
    // twelfth. This is the committed derivation of the out-of-sample number; the
    // audit quotes it beside the in-sample one and does not defend the fit any
    // other way.
    let folds = loco_validation(&rows);
    let (loco_points, loco_mean, loco_over) = loco_summary(&folds);
    let points = policy_points(&rows, false);
    let scan_optimum = fit_over_points(&points);
    let (fit_over, fit_mean) = score_points(&points, scan_optimum.0, scan_optimum.1);
    let agreeing = folds
        .iter()
        .filter(|fold| (fold.narrow, fold.wide) == scan_optimum)
        .count();
    let dissenting: String = {
        let listed: Vec<String> = folds
            .iter()
            .filter(|fold| (fold.narrow, fold.wide) != scan_optimum)
            .map(|fold| format!("{} -> ({}, {})", fold.held_out, fold.narrow, fold.wide))
            .collect();
        if listed.is_empty() {
            "none".to_owned()
        } else {
            listed.join("; ")
        }
    };
    eprintln!(
        "[seg-corpus] LOCO over {} folds: {loco_points} points, mean loss {:+.3}%          (in-sample {:+.3}%), {loco_over} over threshold (in-sample {}); full-corpus scan          optimum ({}, {}) reproduced by {agreeing} of {} folds [{dissenting}]; \
         committed ({}, {})",
        folds.len(),
        loco_mean * 100.0,
        losses.iter().sum::<f64>() / losses.len().max(1) as f64 * 100.0,
        over.len(),
        scan_optimum.0,
        scan_optimum.1,
        folds.len(),
        SEG_POLICY_NARROW_BYTES_PER_ROW,
        SEG_POLICY_WIDE_BYTES_PER_ROW,
    );
    eprintln!(
        "[seg-corpus] static critical-path model vs measured K scaling over {} pairs:          Pearson {:.3}, Spearman {:.3}; model predicts median {:.3}x where the          measurement shows {:.3}x",
        critical_path.pairs,
        critical_path.pearson,
        critical_path.spearman,
        critical_path.predicted_median,
        critical_path.measured_median,
    );

    // NOT `seg_corpus_*`: that prefix is the chunk glob `load_corpus_tables` reads,
    // and a policy table left in it would be parsed as a chunk on the next run --
    // which the header assertion would turn into a panic on a perfectly good
    // workspace.
    let csv = seg_output_path(SEG_POLICY_CSV);
    let mut table = String::from(
        "circuit,layer,class,terms,sources,bf_sources,e4_sources,procedural_sources,\
         total_static_work,rows,grid_blocks,ceiling,best_k,policy_k,loss_fraction,\
         max_over_mean_at_policy\n",
    );
    for verdict in &verdicts {
        writeln!(
            table,
            "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.6},{:.6}",
            verdict.facts.circuit,
            verdict.facts.layer,
            verdict.facts.class.label(),
            verdict.facts.terms,
            verdict.facts.sources,
            verdict.facts.bf_sources,
            verdict.facts.e4_sources,
            verdict.facts.procedural_sources,
            verdict.facts.total_static_work,
            verdict.facts.rows,
            verdict.facts.grid_blocks(),
            verdict.ceiling,
            verdict.best_k,
            verdict.policy_k,
            verdict.loss,
            verdict.max_over_mean_at_policy,
        )
        .expect("write String");
    }
    publish(&csv, &table);

    record_summary_section(
        "Corpus sweep: coverage by round class",
        &format!(
            "Chunks read: {}.\n\nEvery cell counted below was launch-probed before it was \
             timed and certified against BOTH CPU oracles at {SEG_PARITY_ROWS} rows plus \
             head-and-tail identity on the timed cell. `K` is the only free axis \
             ({SEG_CORPUS_K:?}); epilogue `plane`, loader `const`, program by-value -- the \
             Task-9 winner.\n\n{}\n",
            files
                .iter()
                .map(|file| format!("`{}`", file.display()))
                .collect::<Vec<_>>()
                .join(", "),
            render_class_summary(&rows),
        ),
    );
    record_summary_section(
        "Corpus sweep: the closed-form K policy",
        &format!(
            "`seg_policy_k(bytes_per_row, ceiling)`: `K = 4` below \
             {SEG_POLICY_NARROW_BYTES_PER_ROW} B/row, `K = 8` below \
             {SEG_POLICY_WIDE_BYTES_PER_ROW} B/row, otherwise the widest `K` the \
             family hosts -- clamped to the family ceiling (32 on R0, 24 on \
             continuation). The committed thresholds are the full-corpus scan \
             optimum ({}, {}) ROUNDED to whole 32-row tile sizes (40 KiB, 576 KiB); \
             the optimum itself scores {} over threshold at {:+.4}%.\n\n\
             **Leave-one-circuit-out**: refit both thresholds on 11 circuits, score \
             the 12th, x12 -> {loco_points} points, mean loss **{:+.3}%** against \
             {:+.3}% in-sample, **{loco_over}** over threshold against {}. The scan \
             optimum is reproduced by **{agreeing} of {}** folds ({dissenting}). The \
             points are NOT \
             independent (782 points are 285 coordinates at up to four depths, and \
             three 12 GiB circuits supply 323 of them), which is why the fold is the \
             circuit and not the point.\n\n\
             **`best_k` is an argmin over noisy candidates**, so every loss below is \
             slightly OVER-estimated wherever two `K` are within the band: the \
             winner absorbs the favourable noise and the policy pays for it.\n\n\
             Scored over **{} measurement points that reached the timing floor**: it \
             names the measured best `K` on **{exact}** of them, mean loss **{:+.3}%**, \
             worst **{:+.2}%**, and **{}** point(s) lose more than \
             {:.0}%.\n\nStatic per-list spread (`ListWorkStats.max_over_mean`) at the \
             policy's `K`: mean **{mean_skew:.3}**, worst **{worst_skew:.3}** over {} \
             points.\n\n**Run-to-run band, measured**: {repeated} points were measured \
             twice; their medians disagree by {:.3}% (median), {:.3}% (p90), {:.3}% \
             (worst). No loss below that band is resolved.\n\n\
             **Static critical-path model vs measured `K` scaling** over {} pairs: \
             Pearson **{:.3}**, Spearman **{:.3}**; the model predicts a median \
             **{:.3}x** where the measurement shows **{:.3}x**.\n\n\
             Points over the threshold:\n\n{}\n\nCSV: `{}`\n",
            scan_optimum.0,
            scan_optimum.1,
            fit_over,
            fit_mean * 100.0,
            loco_mean * 100.0,
            losses.iter().sum::<f64>() / losses.len().max(1) as f64 * 100.0,
            over.len(),
            folds.len(),
            verdicts.len(),
            losses.iter().sum::<f64>() / losses.len().max(1) as f64 * 100.0,
            worst * 100.0,
            over.len(),
            SEG_POLICY_LOSS_THRESHOLD * 100.0,
            skew.len(),
            band_median * 100.0,
            band_p90 * 100.0,
            band_worst * 100.0,
            critical_path.pairs,
            critical_path.pearson,
            critical_path.spearman,
            critical_path.predicted_median,
            critical_path.measured_median,
            if over.is_empty() {
                "None.\n".to_owned()
            } else {
                render_loss_table(&over)
            },
            csv.display(),
        ),
    );
}

/// **The `D2Policy` verdict.** `Inline` against `Materialize` at every D2-class
/// coordinate the sweep timed, at each one's own best `K`.
///
/// Task 9 saw `Materialize` 35% ahead on ONE coordinate and explicitly refused to
/// make it policy on that evidence. This is the evidence.
#[test]
#[ignore = "reads the corpus sweep's published CSVs; run bwd_seg_corpus_sweep first"]
fn bwd_seg_corpus_d2_policy() {
    let (rows, repeats) = load_corpus_tables();
    let (repeated, band_median, band_p90, band_worst) = repeats.summary();
    let d2: Vec<SegCorpusRow> = rows
        .iter()
        .filter(|row| row.facts.class.is_d2_class())
        .cloned()
        .collect();
    assert!(!d2.is_empty(), "the sweep must cover the D2 classes");

    // Pair the two policies point by point: same circuit, same layer, same ROW
    // COUNT, and each side at ITS OWN best `K`, since the policy changes the source
    // classes and could move the best `K` with them.
    //
    // Equal rows is not a nicety. The two policies have different per-row
    // footprints (`Materialize` publishes what `Inline` refolds), so the budget
    // fits them at different depths, and a quotient taken across two depths would
    // be measuring the row count.
    let mut points: Vec<(String, usize, usize)> = d2
        .iter()
        .map(|row| (row.facts.circuit.clone(), row.facts.layer, row.facts.rows))
        .collect();
    points.sort();
    points.dedup();

    let mut body = String::from(
        "| coordinate | rows | inline best K | inline (us) | materialize best K | \
         materialize (us) | materialize / inline (anchored) | as-recorded |\n\
         |---|---|---|---|---|---|---|---|\n",
    );
    let mut wins = 0usize;
    let mut losses = 0usize;
    let mut ratios: Vec<f64> = Vec::new();
    let mut recorded: Vec<f64> = Vec::new();
    let mut recorded_wins = 0usize;
    let mut mixed = 0usize;
    let mut unresolved = 0usize;
    for (circuit, layer, rows) in &points {
        // Two readings of each side, so the protocol asymmetry is visible rather
        // than absorbed. `as-recorded` divides the winning row's `median_us`
        // directly, which crosses protocols whenever one side's best `K` is the
        // solo baseline and the other's is not. `anchored` puts BOTH sides on the
        // interleaved protocol first: the twin's in-loop median times the winning
        // `K`'s paired ratio.
        let side = |class: SegRoundClass| -> Option<(usize, f64, f64)> {
            let group: Vec<SegCorpusRow> = d2
                .iter()
                .filter(|row| {
                    row.facts.circuit == *circuit
                        && row.facts.layer == *layer
                        && row.facts.rows == *rows
                        && row.facts.class == class
                })
                .cloned()
                .collect();
            let best = corpus_best_k(&group, true)?;
            let row = group.iter().find(|row| row.k == best)?;
            let ratio = row.ratio_vs_baseline.map_or_else(
                || (best == SEG_CORPUS_BASELINE_K).then_some(1.0),
                |estimate| Some(estimate.median_ratio),
            )?;
            Some((
                best,
                interleaved_baseline_median(&group)? * ratio,
                row.median_us?,
            ))
        };
        let (Some(inline), Some(materialize)) = (
            side(SegRoundClass::D2Inline),
            side(SegRoundClass::D2Materialize),
        ) else {
            unresolved += 1;
            continue;
        };
        if (inline.0 == SEG_CORPUS_BASELINE_K) != (materialize.0 == SEG_CORPUS_BASELINE_K) {
            mixed += 1;
        }
        // The two policies are DIFFERENT cells (different backings, different
        // scratch), so this is still a quotient of two SOLO-anchored medians and is
        // quoted with no interval. The verdict rests on the sign and on effects far
        // outside the run-to-run band, not on the third digit.
        let ratio = materialize.1 / inline.1;
        ratios.push(ratio);
        recorded.push(materialize.2 / inline.2);
        recorded_wins += usize::from(materialize.2 / inline.2 < 1.0);
        if ratio < 1.0 {
            wins += 1;
        } else {
            losses += 1;
        }
        writeln!(
            body,
            "| {circuit} L{layer} D2 | {rows} | K{} | {:.1} | K{} | {:.1} | {ratio:.4} | \
             {:.4} |",
            inline.0,
            inline.1,
            materialize.0,
            materialize.1,
            materialize.2 / inline.2,
        )
        .expect("write String");
    }
    recorded.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite ratio"));
    let recorded_median = if recorded.is_empty() {
        f64::NAN
    } else {
        median_of_sorted(&recorded)
    };
    ratios.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite ratio"));
    let median_ratio = if ratios.is_empty() {
        f64::NAN
    } else {
        median_of_sorted(&ratios)
    };
    eprintln!(
        "[seg-corpus] D2 policy over {} paired points (anchored): materialize faster on \
         {wins}, slower on {losses}, median materialize/inline {median_ratio:.4} | \
         as-recorded: faster on {recorded_wins}, median {recorded_median:.4} | {mixed} \
         pair(s) mix protocols, {unresolved} unresolved",
        ratios.len(),
    );
    record_summary_section(
        "Corpus sweep: the D2Policy verdict",
        &format!(
            "Each side at its own best `K`, at the SAME row count. **SOLO medians on two \
             different cells** -- the two policies allocate different backings and \
             different publish scratch, so no paired protocol exists between them and the \
             quotient is quoted with no interval. The measured run-to-run band on repeated \
             points of this sweep is {:.3}% (median) / {:.3}% (p90) / {:.3}% (worst) over \
             {} repeats, which is what a quotient near 1.0 has to be read against.\n\n\
             **Protocol asymmetry, disclosed.** The corpus table\'s `median_us` column \
             carries a SOLO median on each cell\'s `K = 4` row and an INTERLEAVED \
             candidate median on every other `K`. **{mixed} of {} pairs here divide across \
             those two protocols** because one side\'s best `K` is the baseline and the \
             other\'s is not. Both readings are therefore given: `anchored` rebuilds each \
             side from the twin\'s in-loop median times the winning `K`\'s paired ratio, so \
             both sides are on the interleaved protocol; `as-recorded` divides the raw \
             column. **The verdict is the same under both** -- anchored: faster on \
             **{wins}**, slower on **{losses}**, median **{median_ratio:.4}**; \
             as-recorded: faster on **{recorded_wins}**, median \
             **{recorded_median:.4}**. {unresolved} point(s) had no comparable \
             pair.\n\n{body}\n",
            band_median * 100.0,
            band_p90 * 100.0,
            band_worst * 100.0,
            repeated,
            ratios.len(),
        ),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_sample_discipline_meets_the_protocol_floors() {
        assert!(SEG_WARMUP_ITERS >= 5, "the plan's warmup floor is five");
        assert!(SEG_TIMING_ITERS >= 30, "the plan's sample floor is thirty");
        assert!((SEG_CI_ALPHA - 0.05).abs() < f64::EPSILON, "95% two-sided");
    }

    #[test]
    fn the_median_is_the_sorted_middle_and_averages_an_even_pair() {
        assert_eq!(median(&[4.0, 1.0, 3.0, 2.0, 5.0]), 3.0);
        assert_eq!(median(&[4.0, 1.0, 3.0, 2.0]), 2.5);
    }

    fn samples(candidate: &[f64], incumbent: &[f64]) -> PairedSamples {
        PairedSamples {
            candidate_us: candidate.to_vec(),
            incumbent_us: incumbent.to_vec(),
        }
    }

    /// The rule the whole gate rests on: an interval that STRADDLES one is a closed
    /// deficit, not an inverted one. The three cases are asserted separately
    /// because conflating the middle one with inversion is precisely the error the
    /// plan spells the rule out to prevent.
    #[test]
    fn inversion_requires_the_whole_interval_below_one() {
        let inverted = RatioEstimate {
            median_ratio: 0.90,
            ci_low: 0.88,
            ci_high: 0.93,
        };
        assert!(inverted.inverts() && !inverted.regresses());
        assert_eq!(inverted.verdict(), "INVERTED");

        let closed = RatioEstimate {
            median_ratio: 0.99,
            ci_low: 0.96,
            ci_high: 1.02,
        };
        assert!(!closed.inverts(), "a CI containing 1.0 has not inverted");
        assert!(!closed.regresses());
        assert_eq!(closed.verdict(), "closed (CI spans 1.0)");

        let behind = RatioEstimate {
            median_ratio: 1.17,
            ci_low: 1.15,
            ci_high: 1.19,
        };
        assert!(!behind.inverts() && behind.regresses());
        assert_eq!(behind.verdict(), "still-behind");

        // The exact boundary: a CI whose upper bound IS one does not invert.
        let boundary = RatioEstimate {
            median_ratio: 0.97,
            ci_low: 0.94,
            ci_high: 1.0,
        };
        assert!(!boundary.inverts());
    }

    /// A clean 10% win over well-separated samples must produce an interval that is
    /// entirely below one, and a pure tie must produce one that contains it.
    #[test]
    fn the_bootstrap_separates_a_real_win_from_a_tie() {
        let win = samples(
            &(0..32)
                .map(|i| 90.0 + f64::from(i % 4) * 0.1)
                .collect::<Vec<_>>(),
            &(0..32)
                .map(|i| 100.0 + f64::from(i % 4) * 0.1)
                .collect::<Vec<_>>(),
        )
        .estimate();
        assert!((win.median_ratio - 0.9).abs() < 0.01, "{win:?}");
        assert!(win.inverts(), "a clean 10% win must invert: {win:?}");

        let tie = samples(
            &(0..32)
                .map(|i| 100.0 + f64::from(i % 8) - 4.0)
                .collect::<Vec<_>>(),
            &(0..32)
                .map(|i| 100.0 + f64::from((i + 4) % 8) - 4.0)
                .collect::<Vec<_>>(),
        )
        .estimate();
        assert!(
            !tie.inverts(),
            "identical distributions must not invert: {tie:?}"
        );
        assert!(tie.ci_low <= 1.0 && tie.ci_high >= 1.0, "{tie:?}");
    }

    /// The interval is a function of the samples alone, not of when it was computed.
    #[test]
    fn the_bootstrap_is_reproducible() {
        let set = samples(
            &(0..32).map(|i| 100.0 + f64::from(i)).collect::<Vec<_>>(),
            &(0..32).map(|i| 95.0 + f64::from(i)).collect::<Vec<_>>(),
        );
        assert_eq!(set.estimate(), set.estimate());
    }

    #[test]
    fn a_row_that_cannot_launch_is_recorded_rather_than_dropped() {
        let row = row_fixture(32, 0, None);
        assert!(!row.launchable());
        let csv = render_matrix_csv(&[row]);
        assert!(csv.contains("false,0,"), "{csv}");
        assert!(csv.contains("unlaunchable"), "{csv}");
        assert!(render_matrix_table(&[row_fixture(32, 0, None)]).contains("UNLAUNCHABLE"));
    }

    #[test]
    fn the_csv_names_every_required_column() {
        let row = row_fixture(
            8,
            6,
            Some(RatioEstimate {
                median_ratio: 0.91,
                ci_low: 0.90,
                ci_high: 0.92,
            }),
        );
        let csv = render_matrix_csv(&[row]);
        for column in [
            "registers",
            "local_spill_bytes",
            "blocks_per_sm",
            "theoretical_occupancy_percent",
            "dynamic_smem_bytes",
            "candidate_median_us",
            "baseline_median_us",
            "baseline_min_us",
            "protocol",
            "ratio_baseline",
            "median_ratio",
            "ci_low",
            "ci_high",
            "verdict",
            "parity",
            "saturated",
        ] {
            assert!(csv.contains(column), "missing column {column}");
        }
        assert!(csv.contains("INVERTED"), "{csv}");
        // A paired row says so and names what it was paired against; a solo row
        // says THAT, and carries no ratio to be divided by anything.
        assert!(csv.contains("paired,incumbent"), "{csv}");
        let solo = render_matrix_csv(&[row_fixture(4, 6, None)]);
        assert!(solo.contains("solo,-,"), "{solo}");
        assert!(render_matrix_table(&[row_fixture(4, 6, None)]).contains("| solo | solo | solo |"));
    }

    /// The winner is chosen among PRODUCTION-loader rows, resolves its tie band to
    /// the smallest `K` and then the smallest carveout, and is therefore stable
    /// under the sub-timer-resolution noise that separates the tied cells.
    #[test]
    fn the_winner_resolves_the_tie_band_and_ignores_the_valve_loaders() {
        let make = |k: usize, epilogue, coeff, smem, median| {
            let mut row = row_fixture(k, 6, None);
            row.shape.epilogue = epilogue;
            row.shape.coeff = coeff;
            row.dynamic_smem_bytes = smem;
            row.candidate_median_us = median;
            row
        };
        // Three production rows within 0.03% of each other and one 0.3% behind,
        // plus a valve row that is the raw argmin of the whole set.
        let rows = vec![
            make(
                4,
                BwdSegEpilogue::Staged,
                CoeffMode::Constant,
                1_024,
                5_889.4,
            ),
            make(
                4,
                BwdSegEpilogue::Plane,
                CoeffMode::Constant,
                1_536,
                5_871.4,
            ),
            make(4, BwdSegEpilogue::Wide, CoeffMode::Constant, 3_072, 5_871.3),
            make(
                8,
                BwdSegEpilogue::Plane,
                CoeffMode::Constant,
                3_584,
                5_959.5,
            ),
            make(4, BwdSegEpilogue::Wide, CoeffMode::DevPtr, 3_072, 5_100.0),
        ];
        let winner = select_winner(&rows).expect("a production winner");
        assert_eq!(
            winner.shape.coeff,
            CoeffMode::Constant,
            "a valve never wins"
        );
        assert_eq!(winner.shape.k, 4);
        assert_eq!(
            winner.shape.epilogue,
            BwdSegEpilogue::Plane,
            "the tie band resolves to the smaller carveout, not the raw argmin"
        );
        // The 0.3% row is outside the 0.1% band; the 8-warp row is far outside.
        let band = tie_band(&rows);
        assert_eq!(band.len(), 2, "{band:?}");
        assert!(band.iter().all(|row| row.shape.k == 4));
        // The raw argmin over every loader is still the valve row, and the two
        // helpers must disagree here — that disagreement is what the summary
        // reports.
        assert_eq!(
            fastest(&rows).expect("a fastest row").shape.coeff,
            CoeffMode::DevPtr
        );
    }

    #[test]
    fn the_fastest_row_ignores_unlaunchable_cells() {
        let mut slow = row_fixture(4, 6, None);
        slow.candidate_median_us = 900.0;
        let mut quick = row_fixture(8, 6, None);
        quick.candidate_median_us = 100.0;
        // Unlaunchable rows carry a zero median; they must never win.
        let dead = row_fixture(32, 0, None);
        let rows = vec![slow, dead, quick];
        assert_eq!(fastest(&rows).expect("a launchable row").shape.k, 8);
    }

    fn row_fixture(k: usize, blocks: i32, ratio: Option<RatioEstimate>) -> SegMatrixRow {
        SegMatrixRow {
            benchmark: "add_sub L0 R0".to_owned(),
            circuit: "add_sub_lui_auipc_mop_layout_gkr.json".to_owned(),
            layer: 0,
            regime: BwdRegime::R0,
            round: 0,
            rows: 8_388_608,
            saturated: true,
            shape: SegShape::regs(
                k,
                CoeffMode::Constant,
                ProgramMode::Inline,
                BwdSegEpilogue::Plane,
            ),
            d2: D2Policy::Inline,
            blocks_per_sm: blocks,
            theoretical_occupancy: if blocks > 0 { 1.0 } else { 0.0 },
            attributes: SegKernelAttributes {
                registers: 40,
                local_size_bytes: 0,
                static_smem_bytes: 0,
                max_threads_per_block: 1_024,
            },
            dynamic_smem_bytes: 3_584,
            grid_blocks: 262_144,
            waves: 1.5,
            max_over_mean_work: 1.02,
            parity: if blocks > 0 {
                SegParity::OraclesAndReference
            } else {
                SegParity::Unlaunchable
            },
            candidate_median_us: if blocks > 0 { 5_000.0 } else { 0.0 },
            candidate_min_us: if blocks > 0 { 4_990.0 } else { 0.0 },
            incumbent_median_us: ratio.map(|_| 6_101.5),
            incumbent_min_us: ratio.map(|_| 6_098.9),
            ratio,
            baseline: if ratio.is_some() { "incumbent" } else { "-" },
        }
    }

    /// A spill gate that passes on a clean kernel and fails on one spilled byte.
    #[test]
    fn the_spill_gate_is_zero_tolerance() {
        let clean = SegKernelAttributes {
            registers: 40,
            local_size_bytes: 0,
            static_smem_bytes: 0,
            max_threads_per_block: 1_024,
        };
        clean.assert_no_spills("clean");
        assert!(clean.hosts(32) && clean.hosts(4));
        let narrow = SegKernelAttributes {
            max_threads_per_block: 512,
            ..clean
        };
        assert!(!narrow.hosts(32), "512 threads cannot host a K=32 block");
        assert!(narrow.hosts(16));
    }

    #[test]
    #[should_panic(expected = "zero local-memory spills")]
    fn one_spilled_byte_fails_the_gate() {
        SegKernelAttributes {
            registers: 40,
            local_size_bytes: 8,
            static_smem_bytes: 0,
            max_threads_per_block: 1_024,
        }
        .assert_no_spills("spilling");
    }

    /// Row fitting halves until the budget admits the cell, and reports the cap.
    #[test]
    fn row_fitting_halves_and_reports_the_cap() {
        assert_eq!(fit_rows(1 << 20, 1_000, 1 << 40, 1 << 10), (1 << 20, true));
        let (rows, saturated) = fit_rows(1 << 20, 1_000, 1 << 29, 1 << 10);
        assert!(!saturated);
        assert!(rows < 1 << 20 && rows * 1_000 <= 1 << 29);
        // The floor wins over the budget: a cell too big even at the floor is
        // measured at the floor and reported unsaturated, never at zero rows.
        assert_eq!(fit_rows(1 << 20, usize::MAX / 2, 1, 1 << 10).0, 1 << 10);
    }

    // ── Task 10: the corpus sweep and the K policy ───────────────────────────

    /// The certification window never eats the whole cell.
    ///
    /// This is what lets a below-floor corpus coordinate still be certified: the
    /// head and tail windows have to name different rows, and at the constant they
    /// would overlap for anything under two sample widths.
    #[test]
    fn the_certification_window_leaves_a_tail_on_a_narrow_cell() {
        assert_eq!(identity_sample_rows(1 << 20), SEG_IDENTITY_SAMPLE_ROWS);
        assert_eq!(
            identity_sample_rows(2 * SEG_IDENTITY_SAMPLE_ROWS),
            SEG_IDENTITY_SAMPLE_ROWS
        );
        for rows in [2usize, 3, 64, 1_000, SEG_CORPUS_MIN_ROWS, 12_345] {
            let sample = identity_sample_rows(rows);
            assert!(sample >= 1, "{rows} rows must sample something");
            assert!(
                rows - sample > 0,
                "{rows} rows must leave a tail the head does not cover"
            );
        }
    }

    fn corpus_facts(class: SegRoundClass, work: u64, rows: usize) -> SegCoordFacts {
        SegCoordFacts {
            circuit: "add_sub_lui_auipc_mop".to_owned(),
            layer: 0,
            class,
            terms: 128,
            sources: 64,
            windows: 3,
            bf_sources: 40,
            e4_sources: 20,
            procedural_sources: 4,
            total_static_work: work,
            bytes_per_row: 1_824,
            rows,
        }
    }

    fn corpus_fixture(k: usize, status: SegCorpusStatus, ratio: Option<f64>) -> SegCorpusRow {
        SegCorpusRow {
            facts: corpus_facts(SegRoundClass::R0, 1_024, 1 << 20),
            k,
            status,
            blocks_per_sm: 12,
            theoretical_occupancy: 1.0,
            registers: 40,
            dynamic_smem_bytes: 1_536,
            waves: 14.5,
            max_over_mean_work: 1.02,
            parity: match status {
                SegCorpusStatus::Timed | SegCorpusStatus::BelowFloor => {
                    SegParity::OraclesAndIdentity
                }
                _ => SegParity::Unlaunchable,
            },
            median_us: status.measured().then_some(1_000.0),
            min_us: status.measured().then_some(999.0),
            baseline_median_us: ratio.map(|_| 1_000.0),
            ratio_vs_baseline: ratio.map(|median_ratio| RatioEstimate {
                median_ratio,
                ci_low: median_ratio - 0.001,
                ci_high: median_ratio + 0.001,
            }),
        }
    }

    /// The chunked sweep only works if the table survives the round trip.
    #[test]
    fn a_corpus_table_round_trips_through_its_csv() {
        let rows = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            corpus_fixture(8, SegCorpusStatus::Timed, Some(0.97)),
            corpus_fixture(24, SegCorpusStatus::BelowFloor, Some(1.31)),
            corpus_fixture(32, SegCorpusStatus::Unlaunchable, None),
            SegCorpusRow::untimed(
                corpus_facts(SegRoundClass::D2Materialize, 4_096, 1 << 14),
                16,
                SegCorpusStatus::OverBudget,
            ),
            SegCorpusRow::untimed(
                corpus_facts(SegRoundClass::D3, 0, 1 << 13),
                4,
                SegCorpusStatus::LowerRejected,
            ),
        ];
        let csv = render_corpus_csv(&rows);
        let back = parse_corpus_csv(&csv);
        assert_eq!(back.len(), rows.len());
        for (got, want) in back.iter().zip(rows.iter()) {
            assert_eq!(got.facts, want.facts);
            assert_eq!(got.k, want.k);
            assert_eq!(got.status, want.status);
            assert_eq!(got.parity, want.parity);
            assert_eq!(got.median_us, want.median_us);
            assert_eq!(got.protocol(), want.protocol());
            assert_eq!(
                got.ratio_vs_baseline.map(|estimate| estimate.median_ratio),
                want.ratio_vs_baseline.map(|estimate| estimate.median_ratio)
            );
        }
    }

    /// An untimed row must not print a number a reader could average.
    #[test]
    fn an_untimed_corpus_row_prints_no_wall_time() {
        let csv = render_corpus_csv(&[SegCorpusRow::untimed(
            corpus_facts(SegRoundClass::D1, 0, 1 << 15),
            32,
            SegCorpusStatus::Unlaunchable,
        )]);
        let row = csv.lines().nth(1).expect("one data row");
        assert!(row.contains(",unlaunchable,"), "{row}");
        assert!(row.ends_with(",-,-,-,-,-"), "{row}");
    }

    /// The parse must not silently accept a table whose columns moved.
    #[test]
    #[should_panic(expected = "missing the required column")]
    fn a_shifted_corpus_header_is_rejected() {
        parse_corpus_csv("circuit,layer,class\nadd_sub,0,R0\n");
    }

    /// A schema-v1 chunk — everything measured before `baseline_median_us` existed
    /// — must still read, and must read the SAME values.
    ///
    /// Positional parsing made this impossible: adding one column would have meant
    /// re-running twelve locked GPU chunks. Name resolution is what keeps the
    /// on-disk record valid across the schema change.
    #[test]
    fn a_schema_v1_chunk_still_reads_and_agrees_with_v2() {
        let rows = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            corpus_fixture(8, SegCorpusStatus::Timed, Some(0.97)),
        ];
        let v2 = render_corpus_csv(&rows);
        // Strip the v2 column from the header and from every row to make a v1 table.
        let strip = |line: &str, at: usize| {
            let mut field: Vec<&str> = line.split(',').collect();
            field.remove(at);
            field.join(",")
        };
        let at = SEG_CORPUS_CSV_HEADER
            .trim_end()
            .split(',')
            .position(|name| name == SEG_CORPUS_V2_COLUMN)
            .expect("the v2 column is in the v2 header");
        let v1: String = v2
            .lines()
            .map(|line| format!("{}\n", strip(line, at)))
            .collect();
        assert!(!v1.contains(SEG_CORPUS_V2_COLUMN));
        let from_v1 = parse_corpus_csv(&v1);
        let from_v2 = parse_corpus_csv(&v2);
        assert_eq!(from_v1.len(), from_v2.len());
        for (old, new) in from_v1.iter().zip(from_v2.iter()) {
            assert_eq!(old.facts, new.facts);
            assert_eq!(old.median_us, new.median_us);
            assert_eq!(old.ratio_vs_baseline, new.ratio_vs_baseline);
            assert_eq!(
                old.baseline_median_us, None,
                "a v1 chunk cannot carry the baseline median"
            );
        }
        assert!(from_v2[1].baseline_median_us.is_some());
    }

    /// A missing chunk must fail loudly rather than narrow the corpus.
    #[test]
    #[should_panic(expected = "do not cover the corpus")]
    fn a_missing_chunk_fails_the_coverage_assertion() {
        assert_corpus_coverage(&[corpus_fixture(4, SegCorpusStatus::Timed, None)], &[]);
    }

    /// Best-`K` reads the PAIRED ratios, prefers the smallest `K` inside the tie
    /// band, and never names a `K` that was not timed.
    #[test]
    fn best_k_uses_the_paired_ratios_and_resolves_the_tie_band() {
        let group = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            // Inside the 0.1% band of the K=8 minimum, so the smaller K wins.
            corpus_fixture(8, SegCorpusStatus::Timed, Some(0.9000)),
            corpus_fixture(16, SegCorpusStatus::Timed, Some(0.9005)),
            corpus_fixture(24, SegCorpusStatus::Timed, Some(1.4000)),
            corpus_fixture(32, SegCorpusStatus::Unlaunchable, None),
        ];
        assert_eq!(corpus_best_k(&group, false), Some(8));

        // The baseline row alone still scores: it IS the 1.0 of its own axis.
        let only_baseline = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            corpus_fixture(8, SegCorpusStatus::Unlaunchable, None),
        ];
        assert_eq!(corpus_best_k(&only_baseline, false), Some(4));

        // A coordinate that never reached the timing floor contributes nothing to
        // the fit, and everything to the inclusive view.
        let below: Vec<SegCorpusRow> = group
            .iter()
            .map(|row| SegCorpusRow {
                status: match row.status {
                    SegCorpusStatus::Timed => SegCorpusStatus::BelowFloor,
                    other => other,
                },
                ..row.clone()
            })
            .collect();
        assert_eq!(corpus_best_k(&below, false), None);
        assert_eq!(corpus_best_k(&below, true), Some(8));
    }

    /// The closed form stays inside the axis and inside the family's ceiling.
    #[test]
    fn the_policy_never_leaves_the_axis_or_the_ceiling() {
        for bytes in [0usize, 1, 1_279, 1_280, 18_431, 18_432, 1 << 20, usize::MAX] {
            for ceiling in [4usize, 8, 16, 24, 28, 32] {
                let k = seg_policy_k(bytes, ceiling);
                assert!(
                    SEG_CORPUS_K.contains(&k),
                    "policy named K{k}, which is not on the axis"
                );
                assert!(
                    k <= ceiling,
                    "policy named K{k} above the ceiling {ceiling}"
                );
            }
        }
        // A ceiling below the whole axis still yields the axis minimum rather than
        // nothing: every compiled family hosts K=4.
        assert_eq!(seg_policy_k(usize::MAX, 4), 4);
        // The continuation ceiling is 24, so the widest band lands there and never
        // on the R0-only K=32.
        assert_eq!(seg_policy_k(usize::MAX, 24), 24);
        assert_eq!(seg_policy_k(usize::MAX, 32), 24, "K=32 is never selected");
    }

    /// The closed form is monotone in its one argument, and its two thresholds are
    /// where the documentation says they are.
    #[test]
    fn the_policy_is_monotone_in_the_per_row_footprint() {
        let mut previous = 0;
        for bytes in [0usize, 512, 1_279, 1_280, 4_096, 18_431, 18_432, 1 << 20] {
            let k = seg_policy_k(bytes, 32);
            assert!(
                k >= previous,
                "{bytes} B/row lowered the policy from K{previous} to K{k}"
            );
            previous = k;
        }
        assert_eq!(seg_policy_k(SEG_POLICY_NARROW_BYTES_PER_ROW - 1, 32), 4);
        assert_eq!(seg_policy_k(SEG_POLICY_NARROW_BYTES_PER_ROW, 32), 8);
        assert_eq!(seg_policy_k(SEG_POLICY_WIDE_BYTES_PER_ROW - 1, 32), 8);
        assert_eq!(seg_policy_k(SEG_POLICY_WIDE_BYTES_PER_ROW, 32), 24);
    }

    /// **The Task-9 gate coordinate, pinned as a DISAGREEMENT.**
    ///
    /// `add_sub` L0 R0 is 1,824 B/row, so the policy answers `K = 8`. The gate was
    /// won at `K = 4`, and at the gate's own row count (8,388,608 — four times
    /// deeper than anything the corpus sweep reached) `K = 8` measured **1.27%
    /// slower** (5,948.2 us against 5,873.4 us, `seg_stage_a_matrix.csv`). This is
    /// the policy's only out-of-sample point and **it is a loss, not a
    /// validation** — an earlier draft of the audit claimed the opposite by
    /// asserting the policy returns 4 here without evaluating it.
    ///
    /// Pinned exactly rather than as `4 | 8` so the disagreement cannot be
    /// re-absorbed by a threshold change without someone reading this comment. It
    /// is also a live instance of the audit's own footprint-vs-traffic caveat: the
    /// gate coordinate ALLOCATES 1,824 B/row but MOVES 1,004.3 B/row, and 1,004.3
    /// is on the `K = 4` side of the narrow threshold.
    #[test]
    fn the_gate_coordinate_is_the_policys_known_out_of_sample_disagreement() {
        assert_eq!(seg_policy_k(1_824, 32), 8);
        // The measured traffic, had the policy been keyed on traffic instead of
        // footprint, would have landed on the K the gate was actually won at.
        assert_eq!(seg_policy_k(1_004, 32), 4);
    }

    /// The fit is an exact argmin over its own candidate set, and the committed
    /// constants are a ROUNDING of it rather than the argmin itself.
    #[test]
    fn the_committed_thresholds_are_a_rounding_of_the_fitted_optimum() {
        // Three synthetic coordinates whose best K is a clean step in footprint, so
        // the argmin is checkable by hand.
        let rows = policy_fixture();
        let points = policy_points(&rows, false);
        assert_eq!(points.len(), 3, "one point per synthetic coordinate");
        let (narrow, wide) = fit_over_points(&points);
        assert!(narrow < wide, "the fit must return an ordered pair");
        let fitted = score_points(&points, narrow, wide);
        for candidate in [(600usize, 5_000usize), (2_000, 30_000), (100, 200)] {
            let other = score_points(&points, candidate.0, candidate.1);
            assert!(
                fitted <= other,
                "the fit is not the argmin: {candidate:?} scores {other:?} against {fitted:?}"
            );
        }
        // The fit finds the step the fixture was built from: every point on its own
        // best K, so nothing is over threshold.
        assert_eq!(fitted.0, 0, "the synthetic step is perfectly separable");
        // The compact scoring and the verdict path must agree.
        let verdicts = evaluate_policy_with(&rows, false, narrow, wide);
        assert_eq!(policy_score(&verdicts).0, fitted.0);
        assert!((policy_score(&verdicts).1 - fitted.1).abs() < 1e-12);
    }

    /// Leave-one-circuit-out holds out a whole circuit and refits.
    #[test]
    fn leave_one_circuit_out_refits_per_fold_and_pools_by_point() {
        let mut rows = policy_fixture();
        for row in &mut rows {
            row.facts.circuit = format!("circuit_{}", row.facts.bytes_per_row);
        }
        let folds = loco_validation(&rows);
        assert_eq!(folds.len(), 3, "one fold per circuit");
        let mut held: Vec<&str> = folds.iter().map(|fold| fold.held_out.as_str()).collect();
        held.sort_unstable();
        held.dedup();
        assert_eq!(held.len(), 3, "every circuit is held out exactly once");
        for fold in &folds {
            assert_eq!(fold.points, 1, "each synthetic circuit holds one point");
            // The fold's thresholds must be the argmin on the COMPLEMENT, i.e. the
            // held-out circuit may not have voted on the rule it is scored by.
            let train: Vec<SegCorpusRow> = rows
                .iter()
                .filter(|row| row.facts.circuit != fold.held_out)
                .cloned()
                .collect();
            assert_eq!(
                fit_policy_thresholds(&train),
                (fold.narrow, fold.wide),
                "fold {} was scored by thresholds that are not its training argmin",
                fold.held_out
            );
        }
        let (points, mean, over) = loco_summary(&folds);
        assert_eq!(points, 3);
        assert!(mean.is_finite());
        assert!(over <= points);
    }

    /// Pearson and Spearman on inputs whose answers are known.
    #[test]
    fn the_correlations_are_the_textbook_ones() {
        let rising = [1.0, 2.0, 3.0, 4.0, 5.0];
        let doubled = [2.0, 4.0, 6.0, 8.0, 10.0];
        assert!((pearson(&rising, &doubled) - 1.0).abs() < 1e-12);
        assert!((spearman(&rising, &doubled) - 1.0).abs() < 1e-12);
        let falling = [5.0, 4.0, 3.0, 2.0, 1.0];
        assert!((pearson(&rising, &falling) + 1.0).abs() < 1e-12);
        assert!((spearman(&rising, &falling) + 1.0).abs() < 1e-12);
        // Monotone but not linear: Spearman sees the order, Pearson does not.
        let convex = [1.0, 4.0, 9.0, 16.0, 25.0];
        assert!((spearman(&rising, &convex) - 1.0).abs() < 1e-12);
        assert!(pearson(&rising, &convex) < 1.0);
        assert!(
            pearson(&[1.0], &[1.0]).is_nan(),
            "one point is no correlation"
        );
    }

    /// The anchor puts a solo baseline and a paired candidate on one protocol.
    #[test]
    fn the_interleaved_anchor_ignores_the_solo_baseline_median() {
        let mut group = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            corpus_fixture(8, SegCorpusStatus::Timed, Some(0.5)),
            corpus_fixture(16, SegCorpusStatus::Timed, Some(0.25)),
        ];
        // The paired rows say the twin ran at 2,000 us in-loop; the baseline row's
        // SOLO median says 1,000. The anchor must believe the paired rows.
        group[1].median_us = Some(1_000.0);
        group[2].median_us = Some(500.0);
        assert_eq!(interleaved_baseline_median(&group), Some(2_000.0));
        // With no paired row there is nothing to reconstruct from.
        assert_eq!(
            interleaved_baseline_median(&group[..1]),
            None,
            "a solo-only group has no interleaved reading"
        );
    }

    /// Three synthetic coordinates: a light one that wants K4, a mid one that wants
    /// K8 and a heavy one that wants K24.
    fn policy_fixture() -> Vec<SegCorpusRow> {
        let mut rows = Vec::new();
        for (bytes, best) in [(512usize, 4usize), (4_096, 8), (40_960, 24)] {
            for k in SEG_CORPUS_K {
                let ratio = if k == best { Some(0.5) } else { Some(1.5) };
                let mut row = corpus_fixture(
                    k,
                    SegCorpusStatus::Timed,
                    (k != SEG_CORPUS_BASELINE_K).then(|| ratio.expect("set")),
                );
                row.facts.bytes_per_row = bytes;
                row.facts.circuit = format!("c{bytes}");
                if best == SEG_CORPUS_BASELINE_K && k != SEG_CORPUS_BASELINE_K {
                    row.ratio_vs_baseline = Some(RatioEstimate {
                        median_ratio: 1.5,
                        ci_low: 1.4,
                        ci_high: 1.6,
                    });
                }
                rows.push(row);
            }
        }
        rows
    }

    /// A policy that names a `K` the coordinate could not run is an INFINITE loss,
    /// not a quietly-substituted best.
    #[test]
    fn a_policy_k_that_was_never_measured_is_reported_as_a_total_loss() {
        let mut group = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            corpus_fixture(8, SegCorpusStatus::Timed, Some(0.95)),
        ];
        // The remaining axis members were never measured at all.
        let verdicts = evaluate_policy(&group, false);
        assert_eq!(verdicts.len(), 1);
        assert_eq!(verdicts[0].best_k, 8);
        assert_eq!(verdicts[0].ceiling, 8, "the ceiling is read off the sweep");
        assert!(verdicts[0].loss.is_finite());

        // Now make the group's best K unlaunchable and leave a slower one behind:
        // the loss must be the real quotient, not zero.
        group.push(corpus_fixture(16, SegCorpusStatus::Timed, Some(1.10)));
        let verdicts = evaluate_policy(&group, false);
        assert_eq!(verdicts[0].best_k, 8);
        assert_eq!(verdicts[0].ceiling, 16);
        let policy = verdicts[0].policy_k;
        let expected = match policy {
            4 => 1.0 / 0.95 - 1.0,
            8 => 0.0,
            16 => 1.10 / 0.95 - 1.0,
            other => panic!("unexpected policy K{other}"),
        };
        assert!(
            (verdicts[0].loss - expected).abs() < 1e-12,
            "loss {} for policy K{policy}",
            verdicts[0].loss
        );
    }

    /// The policy table must not land inside the glob that reads sweep chunks.
    ///
    /// It did, once: the policy pass wrote `seg_corpus_k_policy.csv`, which the
    /// next run's loader would have picked up as a chunk and rejected on the header
    /// assertion — a self-inflicted panic on an otherwise healthy workspace.
    #[test]
    fn the_policy_table_is_not_mistaken_for_a_sweep_chunk() {
        assert!(!SEG_POLICY_CSV.starts_with(SEG_CORPUS_CHUNK_PREFIX));
        assert!(SEG_MATRIX_CSV.starts_with("seg_stage_a"));
        assert!(!SEG_MATRIX_CSV.starts_with(SEG_CORPUS_CHUNK_PREFIX));
        assert!(
            corpus_csv_name(&SEG_CORPUS_LAYOUTS, SEG_CORPUS_DEFAULT_BUDGET_BYTES, false)
                .starts_with(SEG_CORPUS_CHUNK_PREFIX)
        );
        assert!(corpus_csv_name(&[ADD_SUB_LAYOUT], 12 << 30, false)
            .starts_with(SEG_CORPUS_CHUNK_PREFIX));
        // A deep re-run must not overwrite the default-budget chunk.
        assert_ne!(
            corpus_csv_name(&[ADD_SUB_LAYOUT], SEG_CORPUS_DEFAULT_BUDGET_BYTES, false),
            corpus_csv_name(&[ADD_SUB_LAYOUT], 12 << 30, false)
        );
        // A PROFILED run never lands in the chunk glob: its medians are the
        // profiler's, not the sweep's.
        assert!(
            !corpus_csv_name(&[ADD_SUB_LAYOUT], SEG_CORPUS_DEFAULT_BUDGET_BYTES, true)
                .starts_with(SEG_CORPUS_CHUNK_PREFIX)
        );
    }

    /// The round classes are the axis the sweep and the audit both read.
    #[test]
    fn the_round_classes_agree_on_regime_round_and_policy() {
        assert_eq!(SegRoundClass::R0.regime(), BwdRegime::R0);
        assert_eq!(SegRoundClass::R0.round(), 0);
        for class in SEG_ROUND_CLASSES.into_iter().skip(1) {
            assert_eq!(class.regime(), BwdRegime::Ext, "{}", class.label());
        }
        assert_eq!(SegRoundClass::D2Inline.round(), 2);
        assert_eq!(SegRoundClass::D2Materialize.round(), 2);
        assert_eq!(SegRoundClass::D2Inline.d2(), D2Policy::Inline);
        assert_eq!(SegRoundClass::D2Materialize.d2(), D2Policy::Materialize);
        assert!(SegRoundClass::D2Inline.is_d2_class());
        assert!(SegRoundClass::D2Materialize.is_d2_class());
        assert!(!SegRoundClass::D3.is_d2_class());
        for class in SEG_ROUND_CLASSES {
            assert_eq!(SegRoundClass::parse(class.label()), Some(class));
        }
        for status in [
            SegCorpusStatus::Timed,
            SegCorpusStatus::BelowFloor,
            SegCorpusStatus::OverBudget,
            SegCorpusStatus::Unlaunchable,
            SegCorpusStatus::LowerRejected,
        ] {
            assert_eq!(SegCorpusStatus::parse(status.label()), Some(status));
        }
    }
}
