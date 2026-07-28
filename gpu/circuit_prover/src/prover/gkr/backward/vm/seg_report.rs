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
    lower_bwd_seg, BwdSegLaunchDesc, BwdSegSetup, CoeffMode, D2Policy, ProgramMode,
};
use crate::primitives::field::E4;
use crate::primitives::utils::WARP_SIZE;
use crate::prover::gkr::backward::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};
use crate::prover::ProverContext;
use crate::upstream::{BwdRegime, Field, FieldExtension};

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
    bytes
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
        let mut setup = lower_bwd_seg(
            &self.coord.artifact,
            &binding,
            &self.scratch.resolved(),
            shape.k,
            self.model.d2,
            shape.program,
            shape.coeff,
        )
        .unwrap_or_else(|error| panic!("{}: {}: lower: {error:?}", self.label(), shape.label()));

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
        let sample = SEG_IDENTITY_SAMPLE_ROWS.min(self.rows);
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
        // assumed. (`tail > 0` always: `SEG_MIN_TIMED_ROWS` is eight times
        // `SEG_IDENTITY_SAMPLE_ROWS`.)
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

use super::seg_compile::{lean_coordinate, ADD_SUB_LAYOUT, SEG_LAYOUTS};
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
        incumbent_bank.len() <= crate::prover::gkr::backward::flat::FLAT_CONST_MAX,
        "the incumbent add/sub round-0 bank must fit its constant symbol"
    );
    let staged: [E4; crate::prover::gkr::backward::flat::FLAT_CONST_MAX] =
        core::array::from_fn(|index| incumbent_bank.get(index).copied().unwrap_or(E4::ZERO));
    // SAFETY: this Rust stub names the exact CUDA `e4[FLAT_CONST_MAX]` coefficient
    // symbol; the copy is stream-ordered before every launch that reads it and is
    // always outside a timed span.
    unsafe {
        crate::primitives::utils::memcpy_to_symbol_async(
            &super::ab_gkr_flat_coefficients,
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
}
