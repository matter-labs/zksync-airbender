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
//!   * The PAIRED path is BALANCED TWO-PAIR BLOCKS (spec §6(a)):
//!     [`SEG_WARMUP_SUPERBLOCKS`] whole warmup superblocks, then
//!     [`SEG_TIMED_BLOCKS`] timed blocks of four samples each — `ABBA` or `BAAB`,
//!     so every block holds one candidate-first and one incumbent-first pair and
//!     the arm order is not a constant of the experiment. A clock or thermal drift
//!     still moves both sides together, and an ORDER effect is now identifiable
//!     instead of being absorbed into the ratio.
//!   * The statistic is the MEDIAN BLOCK RATIO with a 95% percentile bootstrap CI
//!     whose resample unit is the BLOCK, stratified jointly on `(orientation,
//!     incoming transition class)` ([`SEG_BOOTSTRAP_RESAMPLES`] resamples, seeded,
//!     so the interval is reproducible from the same samples).
//!   * The ONE interaction statistic is the order contrast
//!     ([`SegBlockedSamples::order_interaction`]), and it is a HARD GATE: a cell
//!     whose whole CI does not lie inside ±[`SEG_ORDER_EQUIVALENCE_PCT`]% has NO
//!     pooled ratio at all — [`SegRatio`] makes that unrepresentable rather than a
//!     label three consumers could forget to read.
//!   * **Inversion is `ci_high < 1.0`.** An interval straddling 1.0 means the
//!     deficit CLOSED; it does not mean it inverted, and
//!     [`RatioEstimate::inverts`] is the only place that judgement is made.
//!   * Every timed sample is RETAINED (spec §6(c)): [`record_raw_samples`] writes
//!     one row per sample, with its block, orientation, incoming class, boundary
//!     source, order id and the run's full identity, into the run-unique directory
//!     the launcher reserved. [`time_paired`] and [`PairedSamples::estimate`]
//!     survive only for the solo/ladder paths that have no incumbent arm.
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
//! Gated exactly like [`seg_gpu_tests`](super::seg_gpu_tests): a default
//! `cargo test -p gpu_circuit_prover` compiles none of it. The GPU drivers are
//! additionally `#[ignore]`d.
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

// `seg_report.rs` CONSUMES the carveout vocabulary Task 3 defines in `seg.rs`; the
// names are added to this one import block. Nothing is redefined here — one
// definition, one file.
use super::seg::{
    bwd_seg_acc_blocks_per_sm, bwd_seg_acc_dynamic_smem_bytes, bwd_seg_acc_entry_point,
    bwd_seg_blocks_per_sm, bwd_seg_carveout_pct_for_bucket, bwd_seg_entry_point,
    bwd_seg_epilogue_smem_bytes, bwd_seg_register_bound_blocks_per_sm, launch_bwd_seg,
    launch_bwd_seg_acc, launch_bwd_seg_build_fold_weights, BwdSegAccPlacement, BwdSegEpilogue,
    CarveoutMode, CarveoutPlan, CarveoutShape, BWD_SEG_ACC_RUNG_EPILOGUE,
    BWD_SEG_SMEM_BUCKETS_BYTES, SEG_REFERENCE_CLOCK_BUCKET_BYTES,
};
use super::seg_desc::BWD_SEG_MAX_K;
use super::seg_lower::{
    bwd_seg_floor_backing_census, bwd_seg_traffic_floor, lower_bwd_seg, BwdSegLaunchDesc,
    BwdSegLowerError, BwdSegSetup, BwdSegTrafficFloor, CoeffMode, D2Policy, ListWorkStats,
    ProgramMode,
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

// ── The physical schedule (spec §6(a) step 1) ────────────────────────────────

/// Timed two-pair BLOCKS per cell: `SEG_TIMING_ITERS` pairs, four samples each.
pub(super) const SEG_TIMED_BLOCKS: usize = SEG_TIMING_ITERS / 2;
/// Warmup superblocks. A whole number of superblocks, so the timed region never
/// begins mid-orientation, and at least [`SEG_WARMUP_ITERS`] pairs per side: two
/// superblocks are 8 pairs against that floor of 5. The LAST one must be of the
/// type that leads the timed sequence — that is what supplies the leading
/// boundary and brings it INSIDE the census.
pub(super) const SEG_WARMUP_SUPERBLOCKS: usize = 2;
const _: () = assert!(SEG_WARMUP_SUPERBLOCKS * 4 >= SEG_WARMUP_ITERS);
const _: () = assert!(
    SEG_TIMED_BLOCKS == 16,
    "the 3/5/3/5 census is exact at 16 blocks"
);
/// Predeclared equivalence bound on the order contrast, in percent (spec §6(a)
/// step 5), from results §2.3's 42-cell same-cell p90 of 0.28%, rounded up. It
/// CANNOT see II-1's predicted ~0.1% reconfiguration term — a passing gate is not
/// evidence the flap is absent, only that no measurable order coupling is
/// present. Removing the mechanism is §7.2.1's primary column's job.
pub(super) const SEG_ORDER_EQUIVALENCE_PCT: f64 = 0.30;
/// Discovery shortlist band (spec §6(b) stage 1). NOT
/// [`SEG_SELECTION_TIE_FRACTION`]: 0.1% is an order of magnitude below the
/// measured repeat noise, so a 0.1% cut can exclude the true winner on one run's
/// noise and the freeze would make that permanent and invisible. From the
/// corpus-wide repeated-point spread (0.932% p90 over 620 points), rounded up.
pub(super) const SEG_DISCOVERY_SHORTLIST_FRACTION: f64 = 0.010;
/// Cross-process tie band for the §4.5 pin decision, and the same number as the
/// repeated-level reproduction threshold: the 0.932% p90 is the finest
/// distinction three processes support.
pub(super) const SEG_PIN_TIE_FRACTION: f64 = 0.0093;
/// The predeclared confirmation process count, and the ONE predeclared escalation
/// count. Nothing else is admissible — "adding a fourth process ad hoc" is
/// exactly what §6(b) forbids.
pub(super) const SEG_CONFIRM_PROCESSES: usize = 3;
pub(super) const SEG_ESCALATION_PROCESSES: usize = 5;
/// The recorded schedule seed. It chooses only which of the two exactly balanced
/// mirrors runs; both have the same census.
pub(super) const SEG_SCHEDULE_SEED: u64 = 0x5E67_1EA1_0000_000A;

/// Which arm a sample times. `A` is the candidate, `B` the incumbent — the
/// lettering spec §6(a)'s transition census uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegArm {
    A,
    B,
}

/// A two-pair block's arm order. Both orientations hold one candidate-first pair
/// and one incumbent-first pair, so every block is internally balanced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegBlockOrientation {
    /// `A, B, B, A` — starts A, ends A.
    Abba,
    /// `B, A, A, B` — starts B, ends B.
    Baab,
}

impl SegBlockOrientation {
    pub(super) fn arms(self) -> [SegArm; 4] {
        match self {
            Self::Abba => [SegArm::A, SegArm::B, SegArm::B, SegArm::A],
            Self::Baab => [SegArm::B, SegArm::A, SegArm::A, SegArm::B],
        }
    }

    fn first(self) -> SegArm {
        self.arms()[0]
    }

    fn last(self) -> SegArm {
        self.arms()[3]
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Abba => "ABBA",
            Self::Baab => "BAAB",
        }
    }
}

/// A superblock TYPE. Superblocks are a PHYSICAL SCHEDULING CONSTRUCT ONLY — they
/// exist to make the transition census balance, and are never an inference unit
/// (spec §6(a) step 3, and the round-6 adjudication in §2.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegSuperblockType {
    /// `ABBA` then `BAAB`: starts A, ends B.
    X,
    /// `BAAB` then `ABBA`: starts B, ends A.
    Y,
}

impl SegSuperblockType {
    fn blocks(self) -> [SegBlockOrientation; 2] {
        match self {
            Self::X => [SegBlockOrientation::Abba, SegBlockOrientation::Baab],
            Self::Y => [SegBlockOrientation::Baab, SegBlockOrientation::Abba],
        }
    }

    fn other(self) -> Self {
        match self {
            Self::X => Self::Y,
            Self::Y => Self::X,
        }
    }
}

/// The incoming-transition class of a block or a sample: the arm that ran last
/// before it, paired with its own arm. Exactly four values, and it is NOT the
/// same fact as [`SegBoundarySource`] — the warmup-supplied boundary has a real
/// direction, and which one it is swaps with the mirror, so folding "warmup" into
/// this enum would destroy the census the stratification depends on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) enum SegTransitionClass {
    SelfA,
    SelfB,
    AToB,
    BToA,
}

impl SegTransitionClass {
    pub(super) fn of(previous: SegArm, next: SegArm) -> Self {
        match (previous, next) {
            (SegArm::A, SegArm::A) => Self::SelfA,
            (SegArm::B, SegArm::B) => Self::SelfB,
            (SegArm::A, SegArm::B) => Self::AToB,
            (SegArm::B, SegArm::A) => Self::BToA,
        }
    }

    pub(super) fn label(self) -> &'static str {
        match self {
            Self::SelfA => "self-A",
            Self::SelfB => "self-B",
            Self::AToB => "A->B",
            Self::BToA => "B->A",
        }
    }

    fn parse(text: &str) -> Self {
        match text {
            "self-A" => Self::SelfA,
            "self-B" => Self::SelfB,
            "A->B" => Self::AToB,
            "B->A" => Self::BToA,
            other => panic!("transition class {other:?}"),
        }
    }
}

/// Where a block's incoming boundary came from. Emitted separately from the class
/// so the 15-internal-plus-1 accounting can be re-verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegBoundarySource {
    Internal,
    WarmupSupplied,
}

impl SegBoundarySource {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Internal => "internal",
            Self::WarmupSupplied => "warmup_supplied",
        }
    }
}

/// One planned block: its orientation, its superblock, and the incoming boundary
/// it will receive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SegPlannedBlock {
    pub(super) block_id: usize,
    pub(super) superblock_id: usize,
    pub(super) orientation: SegBlockOrientation,
    pub(super) incoming: SegTransitionClass,
    pub(super) boundary_source: SegBoundarySource,
}

/// The cell's plan: warmup superblock types, timed superblock types, and the 16
/// planned blocks with their boundary census.
#[derive(Clone, Debug)]
pub(super) struct SegSchedule {
    pub(super) seed: u64,
    pub(super) warmup: Vec<SegSuperblockType>,
    pub(super) timed: Vec<SegSuperblockType>,
    pub(super) blocks: Vec<SegPlannedBlock>,
}

/// The base superblock sequence (spec §6(a) step 1).
///
/// Of the 256 length-8 arrangements, **30 balance all four transition
/// categories** once the warmup supplies the leading boundary. This is the one
/// closest to strict alternation (a single adjacent repeat), which also minimizes
/// same-orientation runs. Strict alternation itself FAILS at n = 8: it balances
/// self directions only when n is odd (n=7 -> 3/3, n=8 -> 4/3, n=9 -> 4/4), and
/// `SEG_TIMING_ITERS = 32` gives exactly 8 superblocks.
const SEG_SUPERBLOCK_SEQUENCE: [SegSuperblockType; 8] = {
    use SegSuperblockType::{X, Y};
    [X, Y, X, Y, Y, X, Y, X]
};

/// Build the cell's schedule. The seed chooses only the mirror; both mirrors are
/// exactly balanced (superblock-level self 3/3 and cross 1/1; block-level joint
/// census 3/5/3/5; sample-level 11/11/21/21 over 64 transitions), so this is
/// reproducibility, not randomization of the balance.
pub(super) fn seg_schedule(seed: u64) -> SegSchedule {
    let mirror = SplitMix64(seed).below(2) == 1;
    let timed: Vec<SegSuperblockType> = SEG_SUPERBLOCK_SEQUENCE
        .iter()
        .map(|kind| if mirror { kind.other() } else { *kind })
        .collect();
    let lead = timed[0];
    // The last warmup superblock MUST be of the leading timed type: that is what
    // supplies the leading boundary and brings it inside the census. The
    // preceding warmup superblocks alternate away from it so the warmup itself is
    // not a run of one type.
    let mut warmup = Vec::with_capacity(SEG_WARMUP_SUPERBLOCKS);
    for slot in 0..SEG_WARMUP_SUPERBLOCKS {
        let from_end = SEG_WARMUP_SUPERBLOCKS - 1 - slot;
        warmup.push(if from_end % 2 == 0 {
            lead
        } else {
            lead.other()
        });
    }

    let orientations: Vec<(usize, SegBlockOrientation)> = timed
        .iter()
        .enumerate()
        .flat_map(|(sb, kind)| kind.blocks().into_iter().map(move |o| (sb, o)))
        .collect();
    // The warmup's final sample is the last arm of its final superblock's final
    // block, so the leading boundary is data with a real direction.
    let mut previous = warmup
        .last()
        .expect("at least one warmup superblock")
        .blocks()[1]
        .last();
    let mut blocks = Vec::with_capacity(orientations.len());
    for (block_id, (superblock_id, orientation)) in orientations.into_iter().enumerate() {
        blocks.push(SegPlannedBlock {
            block_id,
            superblock_id,
            orientation,
            incoming: SegTransitionClass::of(previous, orientation.first()),
            boundary_source: if block_id == 0 {
                SegBoundarySource::WarmupSupplied
            } else {
                SegBoundarySource::Internal
            },
        });
        previous = orientation.last();
    }
    assert_eq!(blocks.len(), SEG_TIMED_BLOCKS, "16 two-pair blocks");
    SegSchedule {
        seed,
        warmup,
        timed,
        blocks,
    }
}

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
/// a half-written table, and MIRROR it into the reservation.
///
/// [`SEG_OUTPUT_DIR`] is a FIXED path, so the last process to publish overwrites
/// every earlier one's table and a campaign of nine processes would keep exactly one
/// of them. With a reservation active the same bytes are therefore written a second
/// time into `$BWD_SEG_RUN_DIR`, beside the raw samples they summarize, where no
/// later process can overwrite them; the fixed path stays the LATEST-VIEW copy.
/// Every published artifact inherits this because every publisher goes through here.
pub(super) fn publish(path: &Path, contents: &str) {
    publish_at(path, contents);
    let Some(dir) = std::env::var_os("BWD_SEG_RUN_DIR") else {
        return;
    };
    let dir = PathBuf::from(dir);
    // Only a RESERVED directory is mirrored into. `seg_env` claims it with `mkdir`;
    // creating it here would defeat the reservation exactly as it would in
    // `record_raw_samples`.
    if !dir.is_dir() {
        return;
    }
    let name = path
        .file_name()
        .expect("a published artifact has a file name");
    let mirror = dir.join(name);
    if mirror != path {
        publish_at(&mirror, contents);
    }
}

fn publish_at(path: &Path, contents: &str) {
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
    /// **LEGACY IID PROTOCOL — not admissible for a headline; the paired path is
    /// [`SegBlockedSamples::estimate_stratified`].** It resamples adjacent pairs
    /// independently, which has no orientation balance to preserve because
    /// [`time_paired`] produced none.
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
/// **LEGACY IID PROTOCOL — not admissible for a headline; the paired path is
/// [`time_paired_blocked`].** Kept for the solo/ladder callers that have no
/// incumbent arm to balance against: its fixed candidate-then-incumbent order gives
/// every candidate sample an `A->B` predecessor and every incumbent sample a `B->A`
/// one, so an order effect is not identifiable from its samples at all.
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

/// One timed block's four samples, with everything the analyses need to be
/// reproduced after the fact.
#[derive(Clone, Copy, Debug)]
pub(super) struct SegBlockSample {
    pub(super) plan: SegPlannedBlock,
    /// The first timed sample index of this block, so an order effect tied to
    /// elapsed time stays visible in the raw data.
    pub(super) first_order_id: usize,
    /// The block's two candidate samples, in the order they ran.
    pub(super) candidate_us: [f64; 2],
    /// The block's two incumbent samples, in the order they ran.
    pub(super) incumbent_us: [f64; 2],
}

impl SegBlockSample {
    /// `cand_mean / inc_mean` (spec §6(a) step 4). Means over the block's two
    /// samples per arm, so the block is internally orientation-balanced.
    pub(super) fn ratio(&self) -> f64 {
        let cand = (self.candidate_us[0] + self.candidate_us[1]) / 2.0;
        let inc = (self.incumbent_us[0] + self.incumbent_us[1]) / 2.0;
        cand / inc
    }

    pub(super) fn candidate_mean(&self) -> f64 {
        (self.candidate_us[0] + self.candidate_us[1]) / 2.0
    }

    pub(super) fn incumbent_mean(&self) -> f64 {
        (self.incumbent_us[0] + self.incumbent_us[1]) / 2.0
    }
}

/// Every timed block of one cell, plus the schedule that produced them.
#[derive(Clone, Debug)]
pub(super) struct SegBlockedSamples {
    pub(super) schedule: SegSchedule,
    pub(super) blocks: Vec<SegBlockSample>,
}

/// Seeded balanced two-pair blocks (spec §6(a) steps 1-2).
///
/// Neither closure may poison, download or synchronize: the loop's cost must be
/// the kernels' cost. Callers stage everything a launch reads, and apply the
/// pair's `CarveoutPlan`, BEFORE this is entered.
pub(super) fn time_paired_blocked(
    stream: &CudaStream,
    mut candidate: impl FnMut() -> CudaResult<()>,
    mut incumbent: impl FnMut() -> CudaResult<()>,
    schedule: &SegSchedule,
) -> CudaResult<SegBlockedSamples> {
    let mut run = |arm: SegArm| -> CudaResult<()> {
        match arm {
            SegArm::A => candidate(),
            SegArm::B => incumbent(),
        }
    };
    // Warmups are complete superblocks, and the last one has the required type.
    for kind in &schedule.warmup {
        for orientation in kind.blocks() {
            for arm in orientation.arms() {
                run(arm)?;
            }
        }
    }
    stream.synchronize()?;

    let start = CudaEvent::create()?;
    let end = CudaEvent::create()?;
    let mut blocks = Vec::with_capacity(schedule.blocks.len());
    let mut order_id = 0usize;
    for plan in &schedule.blocks {
        let first_order_id = order_id;
        let mut candidate_us = Vec::with_capacity(2);
        let mut incumbent_us = Vec::with_capacity(2);
        for arm in plan.orientation.arms() {
            start.record(stream)?;
            run(arm)?;
            end.record(stream)?;
            stream.synchronize()?;
            let micros = f64::from(elapsed_time(&start, &end)?) * 1_000.0;
            match arm {
                SegArm::A => candidate_us.push(micros),
                SegArm::B => incumbent_us.push(micros),
            }
            order_id += 1;
        }
        blocks.push(SegBlockSample {
            plan: *plan,
            first_order_id,
            candidate_us: [candidate_us[0], candidate_us[1]],
            incumbent_us: [incumbent_us[0], incumbent_us[1]],
        });
    }
    Ok(SegBlockedSamples {
        schedule: schedule.clone(),
        blocks,
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

// ── The joint-stratified block bootstrap (spec §6(a) steps 3-6) ───────────────

/// The four joint strata (spec §6(a) step 3). An `ABBA` block starts with a
/// candidate sample, so its incoming class is `self-A` or `B->A`; a `BAAB` block
/// symmetrically admits only `self-B` or `A->B`. Hence exactly four non-empty
/// cells, and the resample preserves BOTH the 8/8 orientation balance and the
/// 3/5/3/5 boundary composition in every replicate by construction.
pub(super) const SEG_JOINT_STRATA: [(SegBlockOrientation, SegTransitionClass); 4] = [
    (SegBlockOrientation::Abba, SegTransitionClass::SelfA),
    (SegBlockOrientation::Abba, SegTransitionClass::BToA),
    (SegBlockOrientation::Baab, SegTransitionClass::SelfB),
    (SegBlockOrientation::Baab, SegTransitionClass::AToB),
];

/// The order interaction (spec §6(a) step 5) — the ONE interaction statistic.
#[derive(Clone, Copy, Debug)]
pub(super) struct SegOrderInteraction {
    pub(super) delta_order_pct: f64,
    pub(super) ci_low_pct: f64,
    pub(super) ci_high_pct: f64,
}

impl SegOrderInteraction {
    /// The HARD validity gate: the ENTIRE CI must lie within the predeclared
    /// bound, which is what an equivalence test requires. Not the point estimate,
    /// and not "the interval overlaps the bound".
    pub(super) fn passes(&self) -> bool {
        self.ci_low_pct >= -SEG_ORDER_EQUIVALENCE_PCT
            && self.ci_high_pct <= SEG_ORDER_EQUIVALENCE_PCT
    }
}

impl SegBlockedSamples {
    pub(super) fn block_ratios(&self) -> Vec<f64> {
        self.blocks.iter().map(SegBlockSample::ratio).collect()
    }

    /// Observed joint-stratum membership, as block indices per stratum.
    fn strata(&self) -> [Vec<usize>; 4] {
        let mut out: [Vec<usize>; 4] = Default::default();
        for (slot, (orientation, class)) in SEG_JOINT_STRATA.iter().enumerate() {
            for (index, block) in self.blocks.iter().enumerate() {
                if block.plan.orientation == *orientation && block.plan.incoming == *class {
                    out[slot].push(index);
                }
            }
        }
        out
    }

    /// The observed census, for the property tests and the emitted metadata.
    pub(super) fn stratum_census(&self) -> [usize; 4] {
        let s = self.strata();
        [s[0].len(), s[1].len(), s[2].len(), s[3].len()]
    }

    /// The point estimate: the MEDIAN BLOCK RATIO over the 16 observed blocks.
    pub(super) fn point_ratio(&self) -> f64 {
        median(&self.block_ratios())
    }

    /// One replicate's block indices, as `(stratum slot, block index)` pairs:
    /// resampled with replacement WITHIN each stratum at its observed size.
    /// Factored out so a test can assert the COMPOSITION of a replicate rather
    /// than only of the observed set.
    fn resample_indices(rng: &mut SplitMix64, strata: &[Vec<usize>; 4]) -> Vec<(usize, usize)> {
        let mut out = Vec::with_capacity(SEG_TIMED_BLOCKS);
        for (slot, indices) in strata.iter().enumerate() {
            for _ in 0..indices.len() {
                out.push((slot, indices[rng.below(indices.len())]));
            }
        }
        out
    }

    /// The per-replicate stratum counts, for the composition property test.
    pub(super) fn replicate_stratum_counts(&self, replicates: usize) -> Vec<[usize; 4]> {
        let strata = self.strata();
        let mut rng = SplitMix64(SEG_BOOTSTRAP_SEED);
        (0..replicates)
            .map(|_| {
                let mut counts = [0usize; 4];
                for (slot, _) in Self::resample_indices(&mut rng, &strata) {
                    counts[slot] += 1;
                }
                counts
            })
            .collect()
    }

    /// `(pooled median, ABBA median, BAAB median)` per replicate.
    fn replicates(&self) -> Vec<(f64, f64, f64)> {
        let strata = self.strata();
        let ratios = self.block_ratios();
        let mut rng = SplitMix64(SEG_BOOTSTRAP_SEED);
        let mut out = Vec::with_capacity(SEG_BOOTSTRAP_RESAMPLES);
        for _ in 0..SEG_BOOTSTRAP_RESAMPLES {
            let mut all = Vec::with_capacity(SEG_TIMED_BLOCKS);
            let mut abba = Vec::new();
            let mut baab = Vec::new();
            for (slot, index) in Self::resample_indices(&mut rng, &strata) {
                let ratio = ratios[index];
                all.push(ratio);
                if SEG_JOINT_STRATA[slot].0 == SegBlockOrientation::Abba {
                    abba.push(ratio);
                } else {
                    baab.push(ratio);
                }
            }
            out.push((median(&all), median(&abba), median(&baab)));
        }
        out
    }

    /// The percentile interval on the median block ratio, from the
    /// joint-stratified replicates. Replaces [`PairedSamples::estimate`]'s IID
    /// resampling of adjacent pairs, which would destroy the orientation balance
    /// the design just paid for.
    pub(super) fn estimate_stratified(&self) -> RatioEstimate {
        let mut pooled: Vec<f64> = self.replicates().iter().map(|(all, _, _)| *all).collect();
        pooled.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite ratio"));
        RatioEstimate {
            median_ratio: self.point_ratio(),
            ci_low: percentile(&pooled, SEG_CI_ALPHA / 2.0),
            ci_high: percentile(&pooled, 1.0 - SEG_CI_ALPHA / 2.0),
        }
    }

    /// `Delta_order = 100 * (median(ratio | ABBA) / median(ratio | BAAB) - 1)`,
    /// with its CI from the SAME joint-stratified replicates, so the contrast
    /// costs nothing extra. The four strata are aggregated back up by orientation
    /// (`ABBA` = 3 + 5, `BAAB` = 3 + 5). This is the ONLY interaction statistic.
    pub(super) fn order_interaction(&self) -> SegOrderInteraction {
        let ratios = self.block_ratios();
        let by = |want: SegBlockOrientation| -> Vec<f64> {
            self.blocks
                .iter()
                .enumerate()
                .filter(|(_, block)| block.plan.orientation == want)
                .map(|(index, _)| ratios[index])
                .collect()
        };
        let point = 100.0
            * (median(&by(SegBlockOrientation::Abba)) / median(&by(SegBlockOrientation::Baab))
                - 1.0);
        let mut deltas: Vec<f64> = self
            .replicates()
            .iter()
            .map(|(_, abba, baab)| 100.0 * (abba / baab - 1.0))
            .collect();
        deltas.sort_by(|lhs, rhs| lhs.partial_cmp(rhs).expect("finite delta"));
        SegOrderInteraction {
            delta_order_pct: point,
            ci_low_pct: percentile(&deltas, SEG_CI_ALPHA / 2.0),
            ci_high_pct: percentile(&deltas, 1.0 - SEG_CI_ALPHA / 2.0),
        }
    }

    /// The four order-conditional medians §7.2.1's secondary column reports.
    pub(super) fn order_conditional_medians(&self) -> [f64; 4] {
        let pick = |want: SegBlockOrientation, arm: SegArm| -> f64 {
            let values: Vec<f64> = self
                .blocks
                .iter()
                .filter(|block| block.plan.orientation == want)
                .map(|block| match arm {
                    SegArm::A => block.candidate_mean(),
                    SegArm::B => block.incumbent_mean(),
                })
                .collect();
            median(&values)
        };
        [
            pick(SegBlockOrientation::Abba, SegArm::A),
            pick(SegBlockOrientation::Abba, SegArm::B),
            pick(SegBlockOrientation::Baab, SegArm::A),
            pick(SegBlockOrientation::Baab, SegArm::B),
        ]
    }
}

/// A paired cell's ratio WITH its order-gate verdict fused in, so a
/// materially order-coupled cell has no selectable ratio at all.
///
/// §6(a) step 6 is an absolute: "If any part of the CI falls outside, do not pool
/// and do not assert the headline." Expressing that as a label would leave three
/// consumers — `select_winner`, the §6(b) confirmation and the §4.5 pin
/// aggregation — each free to forget it. Here the only way to obtain a ratio for
/// any decision is [`Self::selectable`], which yields `None` for `OrderInvalid`.
#[derive(Clone, Copy, Debug)]
pub(super) enum SegRatio {
    /// Solo-timed: no incumbent arm, so no ratio exists.
    Solo,
    /// Paired, and the whole `Delta_order` CI lies inside +/-0.30%.
    Valid {
        estimate: RatioEstimate,
        order: SegOrderInteraction,
        /// `[ABBA candidate, ABBA incumbent, BAAB candidate, BAAB incumbent]`, in
        /// microseconds. Carried on the VALID variant too, because §7.2.1's
        /// secondary column is required to report "its four order-conditional
        /// medians" and that column's cells normally PASS the gate — a field that
        /// existed only on `OrderInvalid` would leave the requirement homeless.
        conditional_medians: [f64; 4],
    },
    /// Paired, but the order gate FAILED.
    ///
    /// **It carries NO `RatioEstimate`.** §6(a) step 6 says "do not POOL and do not
    /// assert the headline", and a pooled median block ratio is precisely the pooled
    /// quantity the gate forbids — storing one would leave a publishable number one
    /// field access away, which is how a label-based gate leaks. What is published
    /// instead is DIAGNOSTIC: the order contrast that failed, and the four
    /// order-conditional medians that show the coupling. A reader can see the effect
    /// and cannot quote a ratio.
    OrderInvalid {
        order: SegOrderInteraction,
        /// `[ABBA candidate, ABBA incumbent, BAAB candidate, BAAB incumbent]`, in
        /// microseconds — the shape of the coupling, not a ratio.
        conditional_medians: [f64; 4],
    },
}

impl SegRatio {
    /// Build from a completed paired cell. The estimate is COMPUTED but DISCARDED
    /// when the gate fails, so no pooled number survives into the invalid variant.
    pub(super) fn of(samples: &SegBlockedSamples) -> Self {
        let order = samples.order_interaction();
        if order.passes() {
            Self::Valid {
                estimate: samples.estimate_stratified(),
                order,
                conditional_medians: samples.order_conditional_medians(),
            }
        } else {
            Self::OrderInvalid {
                order,
                conditional_medians: samples.order_conditional_medians(),
            }
        }
    }

    /// The ONLY accessor any decision may use.
    pub(super) fn selectable(&self) -> Option<(RatioEstimate, SegOrderInteraction)> {
        match self {
            Self::Valid {
                estimate, order, ..
            } => Some((*estimate, *order)),
            _ => None,
        }
    }

    /// The pooled estimate, for CSV and table rendering. `None` for an
    /// order-coupled cell, because none exists — the ratio columns render `-`.
    pub(super) fn reported_estimate(&self) -> Option<RatioEstimate> {
        match self {
            Self::Valid { estimate, .. } => Some(*estimate),
            _ => None,
        }
    }

    /// The order diagnostics, which exist for EVERY paired cell and are always
    /// emitted — that is how an order-coupled cell is visible without being
    /// quotable.
    pub(super) fn order(&self) -> Option<SegOrderInteraction> {
        match self {
            Self::Solo => None,
            Self::Valid { order, .. } | Self::OrderInvalid { order, .. } => Some(*order),
        }
    }

    /// Available for EVERY paired cell, valid or not.
    pub(super) fn conditional_medians(&self) -> Option<[f64; 4]> {
        match self {
            Self::Solo => None,
            Self::Valid {
                conditional_medians,
                ..
            }
            | Self::OrderInvalid {
                conditional_medians,
                ..
            } => Some(*conditional_medians),
        }
    }

    pub(super) fn verdict(&self) -> &'static str {
        match self {
            Self::Solo => "-",
            Self::OrderInvalid { .. } => "ORDER-COUPLED",
            Self::Valid { estimate, .. } => estimate.verdict(),
        }
    }
}

// ── The decision rule (spec §6(b)) ───────────────────────────────────────────

/// The verdict on a frozen shape (spec §6(b)).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegConfirmOutcome {
    Inverted,
    NotInverted,
    Unresolved,
}

impl SegConfirmOutcome {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Inverted => "INVERTED",
            Self::NotInverted => "NOT INVERTED",
            Self::Unresolved => "UNRESOLVED",
        }
    }
}

/// What §6(b) requires a confirmed cell to report — as an ENUM, so an unresolved
/// cell cannot carry pooled headline numbers.
///
/// A struct with `median_ratio` / `min_ratio` / `max_ratio` plus an `outcome` label
/// computes and stores the pooled summary and *then* marks it unresolved, leaving a
/// publishable number one field access away. §6(a) step 6 says "do not POOL and do
/// not assert the headline" — so the unresolved variant simply has no such fields.
#[derive(Clone, Debug)]
pub(super) enum SegConfirmSummary {
    /// All processes' order gates passed AND their intervals agree in direction.
    /// The ONLY variant with pooled numbers.
    Resolved {
        /// `true` = INVERTED, `false` = NOT INVERTED. Both require unanimity.
        inverted: bool,
        process_ratios: Vec<f64>,
        median_ratio: f64,
        min_ratio: f64,
        max_ratio: f64,
        intervals: Vec<RatioEstimate>,
        order: Vec<SegOrderInteraction>,
        conditional_medians: Vec<[f64; 4]>,
    },
    /// No pooled number exists, and none is computed. Diagnostics only.
    Unresolved {
        reason: String,
        /// Per process: `Some` where that process's order gate passed, `None` where
        /// it did not. Deliberately NOT reduced to a median.
        per_process: Vec<Option<RatioEstimate>>,
        order: Vec<SegOrderInteraction>,
        conditional_medians: Vec<[f64; 4]>,
    },
}

impl SegConfirmSummary {
    pub(super) fn outcome(&self) -> SegConfirmOutcome {
        match self {
            Self::Resolved { inverted: true, .. } => SegConfirmOutcome::Inverted,
            Self::Resolved {
                inverted: false, ..
            } => SegConfirmOutcome::NotInverted,
            Self::Unresolved { .. } => SegConfirmOutcome::Unresolved,
        }
    }
}

/// **The predeclared decision rule (spec §6(b)), verbatim:**
///
/// > *For a frozen shape, let each of the three confirmation processes contribute
/// > one stratified-bootstrap interval (§6(a) step 4) and one order-interaction
/// > verdict (§6(a) step 6). The shape is classified into exactly one of three
/// > outcomes:*
/// >
/// > - ***INVERTED** — all three intervals lie **strictly below 1.0** and all
/// >   three interaction gates pass. Report inverted; quote the median of the
/// >   three point ratios with the across-process min and max.*
/// > - ***NOT INVERTED** — all three intervals lie **strictly above 1.0** and all
/// >   three interaction gates pass. Report not inverted, with the same
/// >   three-number summary.*
/// > - ***UNRESOLVED** — every other case: any interval straddling 1.0, any
/// >   mixture of directions across the three, or any failed interaction gate.
/// >   Report UNRESOLVED.*
/// >
/// > *An UNRESOLVED outcome is never silently coerced into either verdict — not
/// > by majority, not by mean, not by discarding the odd run, and not by adding a
/// > fourth process ad hoc. It triggers the predeclared escalation: **either** run
/// > a predeclared larger process count (five, decided before looking further)
/// > **or** investigate the disagreement as a defect, and record which was chosen
/// > and why. Selection stability — whether discovery's argmin reappears as the
/// > best shape in each confirmation process — is recorded separately and never
/// > substituted for this rule.*
///
/// NOT INVERTED requires the SAME unanimity as INVERTED, so a genuinely ambiguous
/// cell cannot be reported as a clean negative.
pub(super) fn classify_confirmation(
    runs: &[(RatioEstimate, SegOrderInteraction)],
) -> SegConfirmOutcome {
    // EXACTLY the predeclared counts. Four processes is the ad-hoc addition the
    // rule forbids, so it is rejected here rather than tolerated.
    assert!(
        runs.len() == SEG_CONFIRM_PROCESSES || runs.len() == SEG_ESCALATION_PROCESSES,
        "the rule admits exactly {SEG_CONFIRM_PROCESSES} processes, or the \
         predeclared escalation to {SEG_ESCALATION_PROCESSES}; got {}",
        runs.len()
    );
    if runs.iter().any(|(_, order)| !order.passes()) {
        return SegConfirmOutcome::Unresolved;
    }
    if runs.iter().all(|(estimate, _)| estimate.ci_high < 1.0) {
        SegConfirmOutcome::Inverted
    } else if runs.iter().all(|(estimate, _)| estimate.ci_low > 1.0) {
        SegConfirmOutcome::NotInverted
    } else {
        SegConfirmOutcome::Unresolved
    }
}

pub(super) fn summarize_confirmation(processes: &[SegBlockedSamples]) -> SegConfirmSummary {
    // Every process contributes its ratio through `SegRatio`, so an order-coupled
    // process yields `None` and NOTHING pools it.
    let ratios: Vec<SegRatio> = processes.iter().map(SegRatio::of).collect();
    let order: Vec<SegOrderInteraction> =
        ratios.iter().map(|r| r.order().expect("paired")).collect();
    let conditional_medians: Vec<[f64; 4]> = ratios
        .iter()
        .map(|r| r.conditional_medians().expect("paired"))
        .collect();
    let per_process: Vec<Option<RatioEstimate>> =
        ratios.iter().map(|r| r.reported_estimate()).collect();
    assert!(
        processes.len() == SEG_CONFIRM_PROCESSES || processes.len() == SEG_ESCALATION_PROCESSES,
        "the rule admits exactly {SEG_CONFIRM_PROCESSES} processes, or the \
         predeclared escalation to {SEG_ESCALATION_PROCESSES}; got {}",
        processes.len()
    );
    // Any failed gate, or any missing interval, is UNRESOLVED — and the pooled
    // fields are never computed on that path.
    if per_process.iter().any(Option::is_none) {
        let failed: Vec<usize> = per_process
            .iter()
            .enumerate()
            .filter(|(_, e)| e.is_none())
            .map(|(i, _)| i)
            .collect();
        return SegConfirmSummary::Unresolved {
            reason: format!("order gate failed in process(es) {failed:?}"),
            per_process,
            order,
            conditional_medians,
        };
    }
    let intervals: Vec<RatioEstimate> = per_process.iter().map(|e| e.expect("checked")).collect();
    let inverted = intervals.iter().all(|e| e.ci_high < 1.0);
    let not_inverted = intervals.iter().all(|e| e.ci_low > 1.0);
    if !inverted && !not_inverted {
        return SegConfirmSummary::Unresolved {
            reason: "intervals straddle 1.0 or disagree in direction".to_owned(),
            per_process,
            order,
            conditional_medians,
        };
    }
    let process_ratios: Vec<f64> = intervals.iter().map(|e| e.median_ratio).collect();
    SegConfirmSummary::Resolved {
        inverted,
        median_ratio: median(&process_ratios),
        min_ratio: process_ratios.iter().copied().fold(f64::MAX, f64::min),
        max_ratio: process_ratios.iter().copied().fold(f64::MIN, f64::max),
        process_ratios,
        intervals,
        order,
        conditional_medians,
    }
}

// ── Run identity and raw-sample emission (spec §6(c)) ────────────────────────

/// Everything that identifies the bytes a number came from. A resolved path plus
/// a byte size does NOT identify the bytes that were timed, because changing
/// `AB_GKR_SEG_CONT_MAXNREG` reruns the build script without creating a distinct
/// Cargo unit hash or output directory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SegRunMeta {
    pub(super) run_id: String,
    pub(super) commit: String,
    pub(super) feature_set: String,
    /// The STAGE this process is (`natural-r0-primary-2`, `40-3`,
    /// `natural-repeat-1`). Distinct from `pin_level`, which is the compiled
    /// qualifier: conflating them made a row's compiled pin unrecoverable.
    pub(super) run_label: String,
    /// The COMPILED qualifier the artifact carries: `natural`, `48`, `40`, `56`,
    /// `control`, or `unrecorded`.
    pub(super) pin_level: String,
    pub(super) archive_sha256: String,
    /// The TEST BINARY's hash. The harness is source too, so a row that names only
    /// its archive cannot prove which runner produced it.
    pub(super) test_binary_sha256: String,
    pub(super) toolkit: String,
    pub(super) device: String,
    pub(super) seed: u64,
}

impl SegRunMeta {
    /// From the campaign's environment.
    ///
    /// **A RESERVATION IS REQUIRED for any paired cell** — chosen over "unique
    /// non-publishable storage for unrecorded runs" because every caller of
    /// `measure_shape`'s paired branch is a campaign cell, and a raw file nobody can
    /// trace to an artifact is a number §7.3 criterion 4c forbids publishing. So
    /// refusing to run is more honest than writing an untraceable file, and the cost
    /// is one `seg_env` call in each block that reaches a paired cell.
    ///
    /// `BWD_SEG_REQUIRE_PROVENANCE=1` additionally makes the metadata fields fatal
    /// rather than `unrecorded`. Since `seg_env` sets it and `seg_env` is also what
    /// reserves the run directory, in practice **every** run that reaches a paired
    /// cell is fully identified — the `unrecorded` defaults survive only for a
    /// non-paired caller (nothing in this pass) and must never appear in a published
    /// row. Resolving this also PRINTS the run identity once, so a log is
    /// self-identifying and a reader never has to match a log to a run directory by
    /// timestamp.
    ///
    /// **There is no ad-hoc unrecorded run of a paired cell.** `record_raw_samples`
    /// requires the reserved directory `seg_env` creates, so a paired cell without
    /// `seg_env` PANICS rather than producing untraceable rows — that is the
    /// mandatory-reservation policy, chosen deliberately (see the doc above). The
    /// `unrecorded` defaults below therefore describe only a hypothetical non-paired
    /// caller; nothing in this pass is one, and such a value must never appear in a
    /// published row.
    pub(super) fn from_env() -> Self {
        let required = std::env::var_os("BWD_SEG_REQUIRE_PROVENANCE").is_some();
        // NOTE: `run_label` and `pin_level` are separate variables on purpose; see
        // the field docs. `seg_env <run_label> <pin_level>` sets both.
        let get = |key: &str, fallback: &str| -> String {
            match std::env::var(key) {
                Ok(value) => value,
                Err(_) if !required => fallback.to_owned(),
                Err(_) => panic!(
                    "{key} must be set under BWD_SEG_REQUIRE_PROVENANCE=1: every \
                     published number is identified by its artifact (§7.3 4c)"
                ),
            }
        };
        Self {
            run_id: get("BWD_SEG_RUN_ID", "unrecorded"),
            commit: get("BWD_SEG_RUN_COMMIT", "unrecorded"),
            feature_set: get("BWD_SEG_RUN_FEATURES", "unrecorded"),
            run_label: get("BWD_SEG_RUN_LABEL", "unrecorded"),
            pin_level: get("BWD_SEG_RUN_PIN_LEVEL", "unrecorded"),
            archive_sha256: get("BWD_SEG_RUN_ARCHIVE_SHA256", "unrecorded"),
            test_binary_sha256: get("BWD_SEG_RUN_TEST_BINARY_SHA256", "unrecorded"),
            toolkit: get("BWD_SEG_RUN_TOOLKIT", "unrecorded"),
            device: get("BWD_SEG_RUN_DEVICE", "unrecorded"),
            seed: SEG_SCHEDULE_SEED,
        }
    }

    /// One process, one meta. Read on every paired cell, so it is resolved once —
    /// and announced once, into the run's own log.
    pub(super) fn current() -> &'static Self {
        static META: std::sync::OnceLock<SegRunMeta> = std::sync::OnceLock::new();
        META.get_or_init(|| {
            let meta = Self::from_env();
            eprintln!(
                "[seg-run] run_id={} run_label={} pin_level={} archive_sha256={} \
                 test_binary_sha256={} commit={} dir={}",
                meta.run_id,
                meta.run_label,
                meta.pin_level,
                meta.archive_sha256,
                meta.test_binary_sha256,
                meta.commit,
                seg_run_dir(&meta).display(),
            );
            meta
        })
    }

    fn fields(&self) -> [&str; 9] {
        [
            &self.run_id,
            &self.commit,
            &self.feature_set,
            &self.run_label,
            &self.pin_level,
            &self.archive_sha256,
            &self.test_binary_sha256,
            &self.toolkit,
            &self.device,
        ]
    }
}

pub(super) const SEG_RAW_SAMPLES_TSV: &str = "seg_raw_samples.tsv";
pub(super) const SEG_FROZEN_CELLS_TSV: &str = "seg_frozen_cells.tsv";

/// TAB-separated, because a metadata field may contain a comma (a device name, a
/// toolkit string) and unquoted comma splitting would silently shift every later
/// column. Tabs are asserted absent on write.
pub(super) const SEG_RAW_TSV_HEADER: &str = "run_id\tcommit\tfeature_set\trun_label\t\
pin_level\tarchive_sha256\ttest_binary_sha256\ttoolkit\tdevice\tseed\tcell\tblock_id\t\
superblock_id\torientation\tincoming_class\tboundary_source\tfirst_order_id\torder_id\t\
arm\tsample_us\n";

/// A UNIQUE directory per process invocation, so repeats accumulate instead of
/// overwriting. A median-of-three must never be reconstructed by hand from
/// overwritten summaries.
pub(super) fn seg_run_dir(meta: &SegRunMeta) -> PathBuf {
    // The harness does NOT invent this path: the launcher RESERVES it with `mkdir`
    // (an atomic claim; a read-then-write counter is not one) and passes it in.
    // Deriving it here too would be a second source of truth that could disagree.
    let _ = meta;
    PathBuf::from(
        std::env::var("BWD_SEG_RUN_DIR")
            .unwrap_or_else(|_| panic!("BWD_SEG_RUN_DIR must name the reserved run directory")),
    )
}

/// One row per SAMPLE. Floats are written with `{:?}`, which is Rust's
/// shortest-round-trip form: `{:.3}` would lose the low bits and make the
/// round-trip test's own tolerance unmeetable.
pub(super) fn render_raw_samples_tsv(
    meta: &SegRunMeta,
    cell: &str,
    samples: &SegBlockedSamples,
) -> String {
    for field in meta.fields() {
        assert!(
            !field.contains('\t'),
            "a TSV metadata field may not contain a tab"
        );
    }
    assert!(!cell.contains('\t'), "a cell label may not contain a tab");
    let mut out = String::from(SEG_RAW_TSV_HEADER);
    let [run_id, commit, features, label, pin, sha, bin_sha, toolkit, device] = meta.fields();
    for block in &samples.blocks {
        let mut candidate = 0usize;
        let mut incumbent = 0usize;
        for (slot, arm) in block.plan.orientation.arms().into_iter().enumerate() {
            // `arm_label`, not `label`: `label` is the run label above.
            let (arm_label, micros) = match arm {
                SegArm::A => {
                    candidate += 1;
                    ("candidate", block.candidate_us[candidate - 1])
                }
                SegArm::B => {
                    incumbent += 1;
                    ("incumbent", block.incumbent_us[incumbent - 1])
                }
            };
            writeln!(
                out,
                "{run_id}\t{commit}\t{features}\t{label}\t{pin}\t{sha}\t{bin_sha}\t\
                 {toolkit}\t{device}\t{:#x}\t{cell}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t\
                 {arm_label}\t{micros:?}",
                meta.seed,
                block.plan.block_id,
                block.plan.superblock_id,
                block.plan.orientation.label(),
                block.plan.incoming.label(),
                block.plan.boundary_source.label(),
                block.first_order_id,
                block.first_order_id + slot,
            )
            .expect("write String");
        }
    }
    out
}

/// CLAIM `path` as one this process has begun writing. Returns **`true` on the FIRST
/// claim** and `false` on every later one — `HashSet::insert` reports "newly inserted",
/// so the name is a claim, not a question. The caller's `let fresh = …` therefore reads
/// correctly: `fresh` is true exactly once per path.
///
/// Per-path, so a process that writes several runs' samples gives each file its own
/// header; the first write to a path is still the one that must find no existing file.
fn seg_raw_writer_started(path: &Path) -> bool {
    static STARTED: std::sync::OnceLock<std::sync::Mutex<std::collections::HashSet<PathBuf>>> =
        std::sync::OnceLock::new();
    STARTED
        .get_or_init(Default::default)
        .lock()
        .expect("the raw-writer start set is not poisoned")
        .insert(path.to_path_buf())
}

/// Append one cell's raw samples into the run's own directory. APPEND, never
/// truncate: one process writes many cells and no cell may overwrite another.
pub(super) fn record_raw_samples(meta: &SegRunMeta, cell: &str, samples: &SegBlockedSamples) {
    // `seg_run_dir` reads the reservation, which the launcher created with `mkdir`.
    // It must already exist: creating it here would defeat the reservation's whole
    // purpose (an unclaimed directory two processes could share).
    let path = seg_run_dir(meta).join(SEG_RAW_SAMPLES_TSV);
    let parent = path.parent().expect("run dir has a parent");
    assert!(
        parent.is_dir(),
        "{} was not reserved: call `seg_env <run_label> <pin_level>` before any \
         paired cell (a paired number without a traceable artifact cannot be \
         published — §7.3 4c)",
        parent.display()
    );
    // One process owns its reserved directory, so the FIRST write must create the
    // file: appending to a pre-existing one would silently merge two processes'
    // samples into a single "run" and the median-of-three would be a median of two.
    // **Start state is keyed PER RESERVED PATH, not per process.** A process-global
    // `OnceLock` makes only the FIRST call in the process write `SEG_RAW_TSV_HEADER`;
    // every later call — including the first call for a DIFFERENT run directory —
    // appends a headerless body, and `parse_raw_samples_tsv` then panics on header
    // drift. That breaks any process that legitimately writes more than one run's
    // samples (the driven test writes three) and makes the writer order-dependent on
    // whatever else ran first.
    let fresh = seg_raw_writer_started(&path);
    if fresh {
        assert!(
            !path.exists(),
            "{} already exists: that run directory was not exclusively reserved, so \
             its samples would be merged with another run's",
            path.display()
        );
    }
    let text = render_raw_samples_tsv(meta, cell, samples);
    let body = if fresh {
        text
    } else {
        text[SEG_RAW_TSV_HEADER.len()..].to_owned()
    };
    {
        use std::io::Write as _;
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap_or_else(|error| panic!("open {}: {error}", path.display()));
        file.write_all(body.as_bytes())
            .unwrap_or_else(|error| panic!("append {}: {error}", path.display()));
    }
}

/// Rebuild `(meta, per-cell blocks)` from an emitted raw-sample TSV. The
/// round-trip is what makes the schema a record rather than a print.
pub(super) fn parse_raw_samples_tsv(text: &str) -> (SegRunMeta, Vec<(String, SegBlockSample)>) {
    let mut lines = text.lines();
    let header = lines.next().expect("a raw-sample TSV has a header");
    assert_eq!(
        format!("{header}\n"),
        SEG_RAW_TSV_HEADER,
        "raw-sample schema drift"
    );
    let mut meta: Option<SegRunMeta> = None;
    // `[Option<f64>; 4]` indexed by SCHEDULED SLOT, not two push-vectors.
    let mut open: Vec<(String, SegPlannedBlock, usize, [Option<f64>; 4])> = Vec::new();
    for line in lines.filter(|line| !line.trim().is_empty()) {
        let f: Vec<&str> = line.split('\t').collect();
        assert_eq!(f.len(), 20, "raw-sample row arity: {line}");
        // EVERY row's identity is validated, not just the first: a file that mixed
        // two runs would otherwise parse as one, and the median-of-three would be a
        // median over the wrong population.
        let row_meta = SegRunMeta {
            run_id: f[0].to_owned(),
            commit: f[1].to_owned(),
            feature_set: f[2].to_owned(),
            run_label: f[3].to_owned(),
            pin_level: f[4].to_owned(),
            archive_sha256: f[5].to_owned(),
            test_binary_sha256: f[6].to_owned(),
            toolkit: f[7].to_owned(),
            device: f[8].to_owned(),
            seed: u64::from_str_radix(f[9].trim_start_matches("0x"), 16).expect("seed"),
        };
        match &meta {
            None => meta = Some(row_meta),
            Some(first) => assert_eq!(
                *first, row_meta,
                "raw-sample file mixes runs: row identity differs from the first row"
            ),
        }
        let plan = SegPlannedBlock {
            block_id: f[11].parse().expect("block_id"),
            superblock_id: f[12].parse().expect("superblock_id"),
            orientation: match f[13] {
                "ABBA" => SegBlockOrientation::Abba,
                "BAAB" => SegBlockOrientation::Baab,
                other => panic!("orientation {other:?}"),
            },
            incoming: SegTransitionClass::parse(f[14]),
            boundary_source: match f[15] {
                "internal" => SegBoundarySource::Internal,
                "warmup_supplied" => SegBoundarySource::WarmupSupplied,
                other => panic!("boundary source {other:?}"),
            },
        };
        let cell = f[10].to_owned();
        let first_order_id: usize = f[16].parse().expect("first_order_id");
        let order_id: usize = f[17].parse().expect("order_id");
        let arm = f[18];
        let micros: f64 = f[19].parse().expect("sample_us");
        // **The row must agree with the SCHEDULE, not merely with itself.** Rebuild the
        // plan from the seed and check this row's block against it: an emitted plan is
        // data, and data that disagrees with its own declared seed is corruption.
        let schedule = seg_schedule(meta.as_ref().expect("meta set above").seed);
        let scheduled = &schedule.blocks[plan.block_id];
        assert_eq!(
            (
                plan.superblock_id,
                plan.orientation,
                plan.incoming,
                plan.boundary_source
            ),
            (
                scheduled.superblock_id,
                scheduled.orientation,
                scheduled.incoming,
                scheduled.boundary_source
            ),
            "block {} disagrees with seg_schedule(seed)",
            plan.block_id
        );
        assert_eq!(
            first_order_id,
            plan.block_id * 4,
            "block {}'s first_order_id must be 4 x block_id",
            plan.block_id
        );
        // The arm and its position are both determined by the orientation, so an
        // out-of-order or mislabelled sample cannot slip through.
        let slot = order_id
            .checked_sub(first_order_id)
            .filter(|slot| *slot < 4)
            .unwrap_or_else(|| panic!("order_id {order_id} outside block {}", plan.block_id));
        let expected_arm = match plan.orientation.arms()[slot] {
            SegArm::A => "candidate",
            SegArm::B => "incumbent",
        };
        assert_eq!(
            arm, expected_arm,
            "block {} slot {slot} must be {expected_arm}",
            plan.block_id
        );
        let index = open
            .iter()
            .position(|(c, p, _, _)| *c == cell && p.block_id == plan.block_id)
            .unwrap_or_else(|| {
                open.push((cell.clone(), plan, first_order_id, [None; 4]));
                open.len() - 1
            });
        // A later row for an already-open block must carry the SAME plan: grouping on
        // `(cell, block_id)` alone would let orientation, incoming class, boundary
        // source or first_order_id drift silently between a block's four rows.
        assert_eq!(
            (open[index].1, open[index].2),
            (plan, first_order_id),
            "block {} rows disagree on their plan",
            plan.block_id
        );
        // **Store BY SCHEDULED SLOT.** Pushing by arm and checking "2 and 2" at the end
        // accepts order ids `0,0,1,1`: two candidate rows at slot 0 and two incumbent
        // rows at slot 1 would fill both vectors to length two and pass. A slot-indexed
        // array rejects the duplicate on sight and the completeness check below rejects
        // a missing one.
        assert!(
            open[index].3[slot].is_none(),
            "block {} slot {slot} appears twice",
            plan.block_id
        );
        open[index].3[slot] = Some(micros);
        // The arm was already validated against the schedule above; nothing else to
        // dispatch on, because the SLOT determines which array position this is.
        let _ = arm;
    }
    let out = open
        .into_iter()
        .map(|(cell, plan, first_order_id, slots)| {
            // ALL FOUR slots present — a missing one is as fatal as a duplicate.
            let filled: Vec<f64> = slots
                .iter()
                .enumerate()
                .map(|(slot, value)| {
                    value
                        .unwrap_or_else(|| panic!("block {} slot {slot} is missing", plan.block_id))
                })
                .collect();
            // Reconstruct the two arrays BY SCHEDULE, not by encounter order, so the
            // sample order in the file cannot silently reorder a block.
            let mut cand = Vec::with_capacity(2);
            let mut inc = Vec::with_capacity(2);
            for (slot, arm) in plan.orientation.arms().into_iter().enumerate() {
                match arm {
                    SegArm::A => cand.push(filled[slot]),
                    SegArm::B => inc.push(filled[slot]),
                }
            }
            (
                cell,
                SegBlockSample {
                    plan,
                    first_order_id,
                    candidate_us: [cand[0], cand[1]],
                    incumbent_us: [inc[0], inc[1]],
                },
            )
        })
        .collect();
    (meta.expect("at least one raw-sample row"), out)
}

/// Read ONE run directory: parse its raw samples, and index its blocks by cell.
///
/// **The single place raw evidence becomes typed.** Both `aggregate_confirmation_runs`
/// and Task 7's `aggregate_arm` go through it, so the two cannot drift into divergent
/// parsing or divergent provenance rules — which is the whole reason this is a refactor
/// rather than a second implementation.
fn read_run(
    dir: &Path,
) -> (
    SegRunMeta,
    std::collections::BTreeMap<String, Vec<SegBlockSample>>,
) {
    let path = dir.join(SEG_RAW_SAMPLES_TSV);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let (meta, rows) = parse_raw_samples_tsv(&text);
    let mut by_cell: std::collections::BTreeMap<String, Vec<SegBlockSample>> = Default::default();
    for (cell, block) in rows {
        by_cell.entry(cell).or_default().push(block);
    }
    // The per-cell completeness assertion lives HERE, so both callers get it and
    // neither can forget it. Blocks are sorted by `block_id` so a caller never depends
    // on file order.
    for (cell, blocks) in &mut by_cell {
        blocks.sort_by_key(|b| b.plan.block_id);
        assert_eq!(
            blocks.len(),
            SEG_TIMED_BLOCKS,
            "{}: cell {cell} contributes {} blocks, expected {SEG_TIMED_BLOCKS}",
            path.display(),
            blocks.len()
        );
        let ids: Vec<usize> = blocks.iter().map(|b| b.plan.block_id).collect();
        assert!(
            ids.iter().copied().eq(0..SEG_TIMED_BLOCKS),
            "{}: cell {cell} block ids are {ids:?}, expected 0..{SEG_TIMED_BLOCKS}",
            path.display()
        );
    }
    (meta, by_cell)
}

/// The identity a set of runs must SHARE, validated and returned.
///
/// Constant: archive, test binary, commit, compiled pin, feature set, toolkit, device,
/// seed. Distinct: run id, pairwise. Extracted so one rule serves every caller.
fn shared_identity(ids: &[SegRunMeta]) -> SegRunMeta {
    let first = ids.first().expect("at least one run").clone();
    for other in &ids[1..] {
        for (field, a, b) in [
            ("ARCHIVE", &other.archive_sha256, &first.archive_sha256),
            (
                "TEST BINARY",
                &other.test_binary_sha256,
                &first.test_binary_sha256,
            ),
            ("COMMIT", &other.commit, &first.commit),
            ("COMPILED PIN", &other.pin_level, &first.pin_level),
            ("FEATURE SET", &other.feature_set, &first.feature_set),
            ("TOOLKIT", &other.toolkit, &first.toolkit),
            ("DEVICE", &other.device, &first.device),
        ] {
            assert_eq!(a, b, "runs differ in {field}");
        }
        assert_eq!(other.seed, first.seed, "runs differ in SEED");
    }
    for i in 0..ids.len() {
        for j in (i + 1)..ids.len() {
            assert_ne!(
                ids[i].run_id, ids[j].run_id,
                "runs {i} and {j} share a run id"
            );
        }
    }
    first
}

/// Median-of-three across the frozen confirmation runs, applying the predeclared
/// rule mechanically. Retires the manual reconstruction §9 flagged.
///
/// §6(b)'s three-process confirmation for ONE cell. Goes through [`read_run`] and
/// [`shared_identity`], so it and Task 7's `aggregate_arm` share one parsing and one
/// provenance rule.
pub(super) fn aggregate_confirmation_runs(dirs: &[PathBuf], cell: &str) -> SegConfirmSummary {
    // ONE parser and ONE provenance rule, shared with `aggregate_arm`. This function
    // previously carried its own `read_to_string` + `parse_raw_samples_tsv` + a
    // duplicated eight-field provenance loop; the two copies could drift, and a plan
    // that CLAIMED a single rule while shipping two is worse than one that admits the
    // duplication. `read_run` and `shared_identity` are now the only implementations.
    let mut unique: Vec<&PathBuf> = dirs.iter().collect();
    unique.sort();
    unique.dedup();
    assert_eq!(
        unique.len(),
        dirs.len(),
        "the confirmation run directories must be distinct: {dirs:?}"
    );
    assert!(
        dirs.len() == SEG_CONFIRM_PROCESSES || dirs.len() == SEG_ESCALATION_PROCESSES,
        "the rule admits exactly {SEG_CONFIRM_PROCESSES} processes, or the predeclared \
         escalation to {SEG_ESCALATION_PROCESSES}; got {}",
        dirs.len()
    );
    let runs: Vec<(SegRunMeta, _)> = dirs.iter().map(|dir| read_run(dir)).collect();
    // Validated and DISCARDED here on purpose: this function's caller wants the
    // verdict, and Task 7's `aggregate_arm` is the entry point that RETURNS the
    // identity for callers (the δ3 attribution) that must bind a payload to an arm.
    let _identity = shared_identity(&runs.iter().map(|(m, _)| m.clone()).collect::<Vec<_>>());
    let processes: Vec<SegBlockedSamples> = runs
        .iter()
        .map(|(meta, by_cell)| {
            let blocks = by_cell
                .get(cell)
                .unwrap_or_else(|| panic!("a run has no blocks for cell {cell}"));
            SegBlockedSamples {
                schedule: seg_schedule(meta.seed),
                blocks: blocks.clone(),
            }
        })
        .collect();
    summarize_confirmation(&processes)
}

// ── The freeze (spec §6(b) stage 2) ──────────────────────────────────────────

/// One frozen decision cell (spec §6(b) stage 2). Written once, BEFORE any level
/// is timed, and read back by the confirmation runs — which time ONLY these.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SegFrozenCell {
    pub(super) label: String,
    pub(super) circuit: String,
    pub(super) layer: usize,
    pub(super) class: SegRoundClass,
    pub(super) k: usize,
    pub(super) epilogue: String,
    pub(super) coeff: String,
    pub(super) program: String,
}

const SEG_FROZEN_TSV_HEADER: &str = "label\tcircuit\tlayer\tclass\tk\tepilogue\tcoeff\tprogram\n";

/// One probed shape. `bwd_seg_freeze_r0_headline` intersects discovery's shortlist
/// with this set, and `write_frozen_cells` asserts every surviving row is a member.
pub(super) struct SegProbedTuple {
    pub(super) epilogue: &'static str,
    pub(super) k: usize,
    pub(super) coeff: &'static str,
    pub(super) program: &'static str,
}

/// The FORCED carveout modes — the ones whose whole purpose is that both arms realize one
/// partition, and therefore the only ones a convergence probe can be about. `off` is the
/// driver-default control, where divergence is the expected outcome, and `as-configured`
/// gives the two arms deliberately different preferences.
/// Whether a mode KEY (see [`CarveoutMode::mode_key`]) names a configuration that forces
/// both arms toward one partition, and can therefore be the subject of a convergence probe.
///
/// Keyed on the FULL configuration, bucket included: `fixed-bucket:65536` and
/// `fixed-bucket:102400` are different probes with measured-opposite verdicts, so a bare
/// `fixed-bucket` is refused as ambiguous rather than accepted as either.
pub(super) fn is_forced_mode_key(key: &str) -> bool {
    if key == CarveoutMode::CommonBucket.label() {
        return true;
    }
    key.strip_prefix("fixed-bucket:")
        .and_then(|bytes| bytes.parse::<usize>().ok())
        .is_some_and(|bytes| BWD_SEG_SMEM_BUCKETS_BYTES.contains(&bytes))
}

/// **One MEASURED forced-mode convergence probe** — a `pair_gate.py` verdict, parsed
/// rather than assumed.
pub(super) struct SegProbeVerdict {
    pub(super) epilogue: String,
    pub(super) k: usize,
    pub(super) coeff: String,
    pub(super) program: String,
    /// The forced configuration KEY the probe ran in — bucket included, so a verdict is
    /// bound to the partition it was actually measured at. Must satisfy
    /// [`is_forced_mode_key`].
    pub(super) mode: String,
    /// `true` iff both arms realized the SAME `launch__shared_mem_config_size`.
    pub(super) converged: bool,
}

/// What `write_frozen_cells` is given about the probe, for the campaign it is writing.
///
/// **This exists because membership in [`SEG_R0_PROBED_TUPLES`] records that a probe was
/// TAKEN, never that it SUCCEEDED** — and the two came apart the first time the probe was
/// really run. `plane K4 const inline` is a probed tuple, its `common-bucket` probe
/// realized 65,536 B against 32,768 B, `pair_gate.py` printed `PROTOCOL FAILURE`, and the
/// membership assertion below would still have blessed the freeze. The precondition was
/// being guarded by an operator reading a log.
pub(super) enum SegProbeEvidence {
    /// The campaign carries no forced-bucket precondition. `pin-decision` and
    /// `d3-attribution` hardcode their bucket and assert the realized field in their own
    /// runners, so there is no shortlist-vs-probe gap to close.
    NotRequired,
    /// Every probe verdict available, from `BWD_SEG_PROBE_VERDICTS`, plus the ONE forced
    /// configuration this freeze is being written FOR.
    ///
    /// The `mode_key` is not decoration: a converged verdict is evidence about the partition
    /// it was measured at and about no other. Measured on this device — `fixed-bucket:65536`
    /// DIVERGED at the R0 headline cell while `fixed-bucket:102400` CONVERGED — so a freeze
    /// written for one must not be licensed by the other's verdict.
    Measured {
        mode_key: String,
        verdicts: Vec<SegProbeVerdict>,
    },
    /// **The freeze will be consumed ONLY by a convergence-independent column** — §7.1.0's
    /// `off` control, where the driver chooses per kernel and divergence is the expected
    /// outcome and the DATA. Demanding a converged forced probe there would gate a column
    /// on a property it does not claim.
    ///
    /// This exists because the freeze is written ONCE and consumed by every column, so at
    /// write time the writer cannot infer which column will read it: applying the primary
    /// column's precondition to every cell made the production-configuration column
    /// unconfirmable whenever the forced probes failed — which is exactly the case the
    /// record needs. The reason travels into the freeze artifact, so an off-only freeze can
    /// never be mistaken for a forced-converged one.
    ///
    /// It does NOT weaken the forced path: `Measured` still requires a converged verdict
    /// per cell, and a freeze written this way announces itself in its own header.
    ConvergenceIndependent { why: String },
}

impl SegProbeEvidence {
    /// The tag written into the freeze header. Every variant has one, so the artifact always
    /// states which precondition it was written under rather than leaving it inferred.
    fn label(&self) -> String {
        match self {
            Self::NotRequired => {
                "not-required (campaign carries no forced-bucket precondition)".to_owned()
            }
            Self::Measured { mode_key, verdicts } => {
                format!(
                    "forced-converged at {mode_key} (pair_gate.py, {} verdict(s))",
                    verdicts.len()
                )
            }
            Self::ConvergenceIndependent { why } => {
                format!("convergence-independent — NOT VALID FOR A FORCED COLUMN: {why}")
            }
        }
    }

    /// The verdicts, or a panic naming what the campaign needs. Deliberately not
    /// `Option`: a missing file must not be able to read as "nothing to check".
    fn require_measured(&self, campaign: &str) -> Option<(&str, &[SegProbeVerdict])> {
        match self {
            Self::Measured { mode_key, verdicts } => Some((mode_key, verdicts)),
            // The convergence question does not apply; the caller skips the predicate and
            // the header records why.
            Self::ConvergenceIndependent { .. } => None,
            Self::NotRequired => panic!(
                "the {campaign} freeze needs MEASURED probe verdicts: pass \
                 SegProbeEvidence::Measured (the runner reads BWD_SEG_PROBE_VERDICTS, \
                 written from pair_gate.py's own output), or \
                 SegProbeEvidence::ConvergenceIndependent for an off-column-only freeze. \
                 Probe membership alone records that a probe RAN, not that it CONVERGED \
                 (§9 item 2)."
            ),
        }
    }
}

/// Parse `BWD_SEG_PROBE_VERDICTS`: TAB-separated
/// `epilogue<TAB>k<TAB>coeff<TAB>program<TAB>mode<TAB>verdict`, `#` comments skipped,
/// `verdict` exactly `CONVERGED` or `DIVERGED`.
///
/// An unknown verdict token is REJECTED rather than treated as non-convergence: a typo
/// that silently means "diverged" would block a sound freeze, and a typo that silently
/// meant "converged" would pass an unsound one. Neither is a reading this file may admit.
pub(super) fn parse_probe_verdicts(text: &str) -> Vec<SegProbeVerdict> {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let field: Vec<&str> = line.split('\t').map(str::trim).collect();
            assert_eq!(
                field.len(),
                6,
                "a probe verdict is <epilogue>\\t<k>\\t<coeff>\\t<program>\\t<mode>\\t\
                 <CONVERGED|DIVERGED>; got {line:?}"
            );
            assert!(
                is_forced_mode_key(field[4]),
                "a convergence probe is only meaningful for a configuration that FORCES one \
                 partition, named by its FULL key (`common-bucket` or \
                 `fixed-bucket:<documented-bytes>`); {:?} names {:?}",
                line,
                field[4]
            );
            let converged = match field[5] {
                "CONVERGED" => true,
                "DIVERGED" => false,
                other => panic!(
                    "a probe verdict is CONVERGED or DIVERGED, never {other:?} \
                     (line {line:?})"
                ),
            };
            SegProbeVerdict {
                epilogue: field[0].to_owned(),
                k: field[1]
                    .parse()
                    .unwrap_or_else(|error| panic!("probe verdict K in {line:?}: {error}")),
                coeff: field[2].to_owned(),
                program: field[3].to_owned(),
                mode: field[4].to_owned(),
                converged,
            }
        })
        .collect()
}

/// **The shapes §7.1.0's `common-bucket` captures actually cover** (Task 9 step 1):
/// `plane`, `const`, inline, at `K in {4, 24}`. `K = 4` is results §2.3's measured
/// winner and `K = 24` is the one-block regime, so the pair spans both occupancy
/// regimes the R0 winner has ever occupied.
///
/// The CLASS and the coordinate are checked separately in `write_frozen_cells`: this
/// table is the shape axis only.
pub(super) const ADD_SUB_LAYOUT_SHORT: &str = "add_sub_lui_auipc_mop";
pub(super) const SEG_R0_PROBED_TUPLES: [SegProbedTuple; 2] = [
    SegProbedTuple {
        epilogue: "plane",
        k: 4,
        coeff: "const",
        program: "inline",
    },
    SegProbedTuple {
        epilogue: "plane",
        k: 24,
        coeff: "const",
        program: "inline",
    },
];

/// Write the freeze, with the seed and the rule alongside it.
///
/// The freeze's IDENTITY is a `sha256sum` of this file taken in the shell and
/// compared across discovery and every confirmation process — not a digest
/// computed here. `gpu_circuit_prover` has no one-shot hasher (`blake2s_u32` is a
/// low-level state machine and `sha2` is not a dependency — both verified), and
/// the repo rule forbids dependency churn, so the identity check lives where a
/// hasher already exists.
pub(super) fn write_frozen_cells(
    path: &Path,
    campaign: &str,
    cells: &[SegFrozenCell],
    seed: u64,
    // An EXPLICIT parameter, not an env read inside this function: the CPU tests that
    // drive the r0-headline path run in one process alongside every other test, and a
    // process-global variable would make them race each other.
    probes: &SegProbeEvidence,
) {
    assert!(!cells.is_empty(), "a freeze with no cells freezes nothing");
    // The campaign tag is a GATE, not a comment: the two campaigns have different
    // rules, and a runner handed the other campaign's freeze would silently time the
    // wrong cells under the wrong statistic.
    // THREE campaigns, each refusing the others' freezes: the R0 headline, the pin
    // decision, and the δ3 attribution. The δ3 set is scored by its OWN rule
    // (`summarize_d3_attribution`), not the pin rule, so sharing a tag with
    // `pin-decision` would let each runner silently accept the other's cells.
    assert!(
        matches!(campaign, "r0-headline" | "pin-decision" | "d3-attribution"),
        "unknown campaign {campaign:?}"
    );
    // **The probed-tuple predicate, ENFORCED here rather than described.** §9 item 2's
    // precondition is established only on the shapes the NCU probe covered, so a
    // freeze naming anything else would carry an unestablished precondition into the
    // acceptance gate.
    if campaign == "r0-headline" {
        for cell in cells {
            // The CLASS is part of the identity. Without it a D1 continuation cell
            // with the same epilogue/K/loader passes the guard — and the probe
            // established the precondition on an R0 launch, on a different data path.
            assert_eq!(
                cell.class,
                SegRoundClass::R0,
                "the R0 headline freeze may only name R0 cells; {} is {:?}",
                cell.label,
                cell.class
            );
            assert_eq!(
                (cell.circuit.as_str(), cell.layer),
                (ADD_SUB_LAYOUT_SHORT, 0),
                "the R0 headline is add_sub layer 0 (`bwd_seg_add_sub_l0_r0_matrix`); \
                 {} names {} layer {}",
                cell.label,
                cell.circuit,
                cell.layer
            );
            assert!(
                SEG_R0_PROBED_TUPLES.iter().any(|probed| {
                    probed.epilogue == cell.epilogue
                        && probed.k == cell.k
                        && probed.coeff == cell.coeff
                        && probed.program == cell.program
                }),
                "the R0 freeze names an UNPROBED tuple ({} K{} {} {}): the forced-bucket \
                 precondition was not established for it. Either extend the probe set and \
                 re-probe, or drop the shape — never freeze an unprobed tuple (§9 item 2).",
                cell.epilogue,
                cell.k,
                cell.coeff,
                cell.program
            );
            // **AND the probe must have SUCCEEDED.** Membership above says a capture was
            // taken; this says the two arms actually landed on one partition. Both are
            // required and neither implies the other — measured: `plane K4 const inline`
            // is a member whose `common-bucket` probe DIVERGED (65,536 B vs 32,768 B).
            //
            // SKIPPED, and only, for `ConvergenceIndependent`: the `off` column does not
            // claim equal partitions, so gating it on one would gate a column on a property
            // it does not assert. The header records that this freeze took that path.
            let Some((mode_key, verdicts)) = probes.require_measured(campaign) else {
                continue;
            };
            assert!(
                is_forced_mode_key(mode_key),
                "a freeze can only claim forced-convergence for a configuration that FORCES \
                 one partition; {mode_key:?} does not (and a bare `fixed-bucket` is ambiguous \
                 between buckets whose verdicts differ)"
            );
            // MATCHED ON THE TUPLE **AND** THE CONFIGURATION KEY. A verdict measured at a
            // different bucket is evidence about that bucket only: `fixed-bucket:65536`
            // DIVERGED here where `fixed-bucket:102400` CONVERGED, so accepting either for
            // the other would reinstate exactly the false-precondition F-9.3 closed.
            let matching: Vec<&SegProbeVerdict> = verdicts
                .iter()
                .filter(|verdict| {
                    verdict.epilogue == cell.epilogue
                        && verdict.k == cell.k
                        && verdict.coeff == cell.coeff
                        && verdict.program == cell.program
                        && verdict.mode == mode_key
                })
                .collect();
            assert!(
                !matching.is_empty(),
                "no probe verdict for the frozen tuple ({} K{} {} {}) AT {mode_key}: {} \
                 verdict(s) were supplied and none names this shape at this configuration, so \
                 its forced-bucket precondition is unestablished (§9 item 2, F-9.3)",
                cell.epilogue,
                cell.k,
                cell.coeff,
                cell.program,
                verdicts.len(),
            );
            assert!(
                matching.iter().any(|verdict| verdict.converged),
                "the R0 freeze names ({} K{} {} {}), whose probe at {mode_key} DIVERGED ({}). \
                 The arms did not realize one partition, so \
                 §7.2.1's primary column has no acceptance gate for this cell: change the \
                 forced mode to one that converges, or drop the shape. Never freeze a \
                 tuple whose probe FAILED — membership records that a probe RAN (F-9.3).",
                cell.epilogue,
                cell.k,
                cell.coeff,
                cell.program,
                matching
                    .iter()
                    .map(|verdict| verdict.mode.as_str())
                    .collect::<Vec<&str>>()
                    .join(", "),
            );
        }
    }
    // The probe-evidence tag is a FIELD of the artifact, not a note: an off-column-only
    // freeze and a forced-converged one are the same eight columns, and a later reader
    // (or a later task lifting the file) has no other way to tell them apart. It is written
    // for every campaign so its absence can never be read as "the safe kind".
    let mut out = format!(
        "# campaign = {campaign}\n# seed = {seed:#x}\n\
         # probe_evidence = {}\n\
         # rule = r0-headline: spec §6(b) stage 3 | pin-decision: spec §4.5 \
         cross-level | d3-attribution: spec §4.5 loop form, two arms at one pin\n",
        probes.label(),
    );
    out.push_str(SEG_FROZEN_TSV_HEADER);
    for cell in cells {
        writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            cell.label,
            cell.circuit,
            cell.layer,
            cell.class.label(),
            cell.k,
            cell.epilogue,
            cell.coeff,
            cell.program,
        )
        .expect("write String");
    }
    publish(path, &out);
}

/// Read a freeze and REJECT one belonging to the other campaign.
/// **A CONVERGENCE-INDEPENDENT FREEZE MAY NOT BE TIMED IN A FORCED CONFIGURATION.**
///
/// Such a freeze was written for §7.1.0's `off` control, whose cells were never required to
/// converge — so timing them under `common-bucket` or a fixed bucket would produce a
/// forced-column number resting on a precondition nobody established. The freeze declares
/// itself and the process knows its own mode, so the mismatch is checkable at consume time
/// rather than left to whoever reads the artifacts later.
///
/// Separated from the environment so its test does not mutate a process-global variable that
/// every other test in the binary shares.
pub(super) fn assert_freeze_matches_column(evidence: &str, mode: CarveoutMode, path: &str) {
    assert!(
        !(evidence.starts_with("convergence-independent") && mode.forces_one_partition()),
        "{path} is a CONVERGENCE-INDEPENDENT freeze (off-column only) but this process runs \
         BWD_SEG_CARVEOUT={} ({}), which forces one partition. Its cells carry no \
         forced-convergence evidence, so a number timed here would have no acceptance gate \
         behind it. Either run the off column, or write a freeze with measured verdicts for \
         this configuration.",
        mode.mode_key(),
        mode.label(),
    );
    // **A forced-converged freeze is consumable ONLY at its own `mode_key`** (ruling R8).
    //
    // The write side already keys each verdict on the configuration it was measured at, but
    // that binding was not re-checked on consume — so a freeze licensed at
    // `fixed-bucket:102400` was consumable in a `fixed-bucket:65536` process, and this
    // device measured those two disagreeing at the R0 headline cell (102,400 CONVERGED,
    // 65,536 DIVERGED). Keying on the label alone let each stand for the other, which is
    // exactly the license `CarveoutMode::mode_key` exists to close; closing it at write time
    // only was half the fix.
    //
    // **The reverse direction stays ALLOWED, deliberately.** A freeze carrying converged
    // evidence may be consumed under `off` or `as-configured`: those columns claim no
    // equal-partition property, so the evidence is simply unused — not contradicted. Only a
    // process that FORCES a partition is making a claim the evidence has to back.
    if let Some(measured_at) = evidence
        .strip_prefix("forced-converged at ")
        .and_then(|rest| rest.split_whitespace().next())
    {
        assert!(
            !mode.forces_one_partition() || measured_at == mode.mode_key(),
            "{path} carries FORCED-CONVERGED evidence measured at {measured_at:?}, but this \
             process forces {:?}. A convergence verdict is evidence about the partition it \
             was measured at and about no other — on this device `fixed-bucket:65536` \
             DIVERGED at the R0 headline cell where `fixed-bucket:102400` CONVERGED, so \
             accepting a mismatched key would let one stand for the other. Run at \
             {measured_at:?}, or write a freeze with verdicts for {:?}.",
            mode.mode_key(),
            mode.mode_key(),
        );
    }
}

/// The freeze's `# probe_evidence` field, or a PANIC. Never an `Option`: see the call site in
/// [`read_frozen_cells`] for why a missing field must not be tolerable.
pub(super) fn frozen_probe_evidence(text: &str, path: &Path) -> String {
    text.lines()
        .find_map(|line| line.strip_prefix("# probe_evidence = "))
        .map(|evidence| evidence.trim().to_owned())
        .unwrap_or_else(|| {
            panic!(
                "{}: no `# probe_evidence` field. A freeze must state the precondition it was \
                 written under — forced-converged at a named configuration, \
                 convergence-independent (off-column only), or not-required — because an \
                 off-column-only freeze and a forced-converged one are otherwise the same \
                 eight columns and a consumer cannot tell them apart.",
                path.display()
            )
        })
}

pub(super) fn read_frozen_cells(path: &Path, campaign: &str) -> Vec<SegFrozenCell> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("the freeze must exist before confirmation: {error}"));
    let declared = text
        .lines()
        .find_map(|line| line.strip_prefix("# campaign = "))
        .unwrap_or_else(|| panic!("{}: no campaign tag", path.display()));
    assert_eq!(
        declared.trim(),
        campaign,
        "{}: this is the {declared:?} freeze; {campaign:?} refuses it. The two \
         campaigns have different cell sets AND different rules (spec §4.5: using \
         §6(b)'s rule for the pin decision is a category error).",
        path.display()
    );
    // **The probe-evidence field is MANDATORY on read, at parity with the campaign tag.**
    // A best-effort echo was not enough: a freeze with no field looked exactly like a
    // forced-converged one to every consumer, so the absence of the strongest claim read as
    // the safest. Every freeze this code writes carries it, so a missing field means either a
    // hand-written artifact or one from before the field existed — neither may be timed.
    frozen_probe_evidence(&text, path);
    let mut cells = Vec::new();
    let mut saw_header = false;
    for line in text.lines() {
        if line.starts_with('#') {
            continue;
        }
        if !saw_header {
            assert_eq!(
                format!("{line}\n"),
                SEG_FROZEN_TSV_HEADER,
                "freeze schema drift"
            );
            saw_header = true;
            continue;
        }
        if line.trim().is_empty() {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        assert_eq!(f.len(), 8, "freeze row arity: {line}");
        cells.push(SegFrozenCell {
            label: f[0].to_owned(),
            circuit: f[1].to_owned(),
            layer: f[2].parse().expect("layer"),
            class: SegRoundClass::parse(f[3])
                .unwrap_or_else(|| panic!("freeze names class {:?}", f[3])),
            k: f[4].parse().expect("k"),
            epilogue: f[5].to_owned(),
            coeff: f[6].to_owned(),
            program: f[7].to_owned(),
        });
    }
    assert!(!cells.is_empty(), "the freeze file names no cells");
    cells
}

/// The launch shape a frozen cell names.
///
/// The three axis labels round-trip through the same functions that WROTE them
/// ([`epilogue_label`], [`coeff_label`], [`program_label`]), so a freeze naming an axis
/// value this harness cannot build fails here rather than silently selecting a
/// neighbouring shape. `acc` is `None`: every frozen cell is a release-symbol shape.
pub(super) fn frozen_cell_shape(cell: &SegFrozenCell) -> SegShape {
    let epilogue = [
        BwdSegEpilogue::Staged,
        BwdSegEpilogue::Plane,
        BwdSegEpilogue::Wide,
    ]
    .into_iter()
    .find(|epilogue| epilogue_label(*epilogue) == cell.epilogue)
    .unwrap_or_else(|| panic!("a freeze names epilogue {:?}", cell.epilogue));
    let coeff = [CoeffMode::Constant, CoeffMode::DevPtr]
        .into_iter()
        .find(|coeff| coeff_label(*coeff) == cell.coeff)
        .unwrap_or_else(|| panic!("a freeze names coefficient loader {:?}", cell.coeff));
    let program = [ProgramMode::Inline, ProgramMode::DevPtr]
        .into_iter()
        .find(|program| program_label(*program) == cell.program)
        .unwrap_or_else(|| panic!("a freeze names program source {:?}", cell.program));
    SegShape::regs(cell.k, coeff, program, epilogue)
}

/// The confirmation runs' cell filter: `BWD_SEG_FROZEN_CELLS=<path>` selects the
/// freeze, and a run with that variable set may time NOTHING else. Absent, the
/// caller is in discovery and times its own exploration set.
pub(super) fn frozen_cell_filter(campaign: &str) -> Option<Vec<SegFrozenCell>> {
    let path = std::env::var("BWD_SEG_FROZEN_CELLS").ok()?;
    let cells = read_frozen_cells(Path::new(&path), campaign);
    // Echo the path so the shell can `sha256sum` exactly the file this process
    // read and compare it against the one discovery wrote.
    eprintln!("[seg-freeze] consumed {} ({} cells)", path, cells.len());
    // The PROBE EVIDENCE the freeze was written under — echoed so every confirmation and
    // every aggregation logs which precondition its cells actually carry, and then GATED
    // against the configuration this process is actually running.
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("re-read the freeze {path}: {error}"));
    let evidence = frozen_probe_evidence(&text, Path::new(&path));
    eprintln!("[seg-freeze] probe_evidence = {evidence}");
    assert_freeze_matches_column(&evidence, carveout_mode(), &path);
    Some(cells)
}

// ── §4.5's pin decision set (predeclared, level-independent) ──────────────────

/// What a cell is FOR in the pin decision. The two roles are scored differently
/// and must never be pooled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegPinRole {
    /// Contributes to the level aggregate. Continuation shapes only — the swept
    /// symbols are the only ones the pin touches.
    Decision,
    /// §4.5 mechanism 3's cross-build anchor. R0 is PIN-INVARIANT (not on the sweep
    /// axis; its `plane`/`wide` symbols are permanently pinned at 40), so its
    /// movement across levels is build and session noise MEASURED. It runs in every
    /// process and is **excluded from every aggregate**: including it would dilute
    /// the very effect the aggregate is about.
    DriftControl,
}

impl SegPinRole {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Decision => "decision",
            Self::DriftControl => "drift-control",
        }
    }
}

/// One predeclared decision cell.
#[derive(Clone, Copy, Debug)]
pub(super) struct SegPinCell {
    pub(super) label: &'static str,
    pub(super) role: SegPinRole,
    pub(super) class: SegRoundClass,
    pub(super) k: usize,
}

/// **§4.5's δ3 ATTRIBUTION cell set** — a different question from the pin decision,
/// so a different set. The pin decision asks "which ceiling is fastest" over cells
/// chosen to span the K axis; the attribution asks "does the roll form explain the
/// δ3/K24 penalty", so it is exactly the δ3-BEARING shapes results §2.6 shows moving:
/// the D3 and D2-materialize classes at K = 16, 24 and 32. Running the pin set here
/// would time four cells that carry no δ3 at all.
pub(super) const SEG_D3_ATTRIBUTION_CELLS: [SegPinCell; 7] = [
    SegPinCell {
        label: "d3-attr-d3-k16",
        role: SegPinRole::Decision,
        class: SegRoundClass::D3,
        k: 16,
    },
    SegPinCell {
        label: "d3-attr-d3-k24",
        role: SegPinRole::Decision,
        class: SegRoundClass::D3,
        k: 24,
    },
    SegPinCell {
        label: "d3-attr-d3-k32",
        role: SegPinRole::Decision,
        class: SegRoundClass::D3,
        k: 32,
    },
    SegPinCell {
        label: "d3-attr-d2m-k16",
        role: SegPinRole::Decision,
        class: SegRoundClass::D2Materialize,
        k: 16,
    },
    SegPinCell {
        label: "d3-attr-d2m-k24",
        role: SegPinRole::Decision,
        class: SegRoundClass::D2Materialize,
        k: 24,
    },
    SegPinCell {
        label: "d3-attr-d2m-k32",
        role: SegPinRole::Decision,
        class: SegRoundClass::D2Materialize,
        k: 32,
    },
    SegPinCell {
        label: "r0-drift-k4",
        role: SegPinRole::DriftControl,
        class: SegRoundClass::R0,
        k: 4,
    },
];

/// **The frozen decision set.** Continuation classes on the production loader pair
/// (`const` inline `plane`, which is what [`SegShape::regs`] builds below) at the `K`
/// values results §2.6 shows moving, plus the R0 drift control.
///
/// Predeclared HERE, in source, rather than discovered: §4.5 fixes the cell set
/// before any level is timed, and a discovered set would differ per level and make
/// the levels incomparable. Changing this array is a spec-level decision, not a
/// tuning knob — the integration test below pins its shape.
pub(super) const SEG_PIN_DECISION_CELLS: [SegPinCell; 7] = [
    SegPinCell {
        label: "cont-d1-k4",
        role: SegPinRole::Decision,
        class: SegRoundClass::D1,
        k: 4,
    },
    SegPinCell {
        label: "cont-d1-k8",
        role: SegPinRole::Decision,
        class: SegRoundClass::D1,
        k: 8,
    },
    SegPinCell {
        label: "cont-d2i-k8",
        role: SegPinRole::Decision,
        class: SegRoundClass::D2Inline,
        k: 8,
    },
    SegPinCell {
        label: "cont-d2i-k16",
        role: SegPinRole::Decision,
        class: SegRoundClass::D2Inline,
        k: 16,
    },
    SegPinCell {
        label: "cont-d3-k16",
        role: SegPinRole::Decision,
        class: SegRoundClass::D3,
        k: 16,
    },
    SegPinCell {
        label: "cont-d3-k24",
        role: SegPinRole::Decision,
        class: SegRoundClass::D3,
        k: 24,
    },
    SegPinCell {
        label: "r0-drift-k4",
        role: SegPinRole::DriftControl,
        class: SegRoundClass::R0,
        k: 4,
    },
];

const _: () = {
    // Exactly one drift control, and at least four decision cells — an aggregate
    // over fewer would be a median of too little.
    let mut controls = 0;
    let mut decisions = 0;
    let mut i = 0;
    while i < SEG_PIN_DECISION_CELLS.len() {
        match SEG_PIN_DECISION_CELLS[i].role {
            SegPinRole::DriftControl => controls += 1,
            SegPinRole::Decision => decisions += 1,
        }
        i += 1;
    }
    assert!(controls == 1, "exactly one drift control");
    assert!(
        decisions >= 4,
        "the aggregate needs at least four decision cells"
    );
};

const _: () = {
    let mut controls = 0;
    let mut decisions = 0;
    let mut i = 0;
    while i < SEG_D3_ATTRIBUTION_CELLS.len() {
        match SEG_D3_ATTRIBUTION_CELLS[i].role {
            SegPinRole::DriftControl => controls += 1,
            SegPinRole::Decision => decisions += 1,
        }
        i += 1;
    }
    assert!(controls == 1, "exactly one drift control");
    assert!(
        decisions >= 4,
        "the attribution needs at least four δ3-bearing cells"
    );
};

/// One cell's per-level estimate in the pin decision.
#[derive(Clone, Debug)]
pub(super) struct SegPinCellSummary {
    pub(super) label: String,
    pub(super) role: SegPinRole,
    /// The median across this level's three processes of the median block ratio.
    /// `None` when ANY of the three processes' rows was order-invalid — an
    /// order-coupled cell is never pooled (§6(a) step 6).
    pub(super) estimate: Option<f64>,
    /// Per process, in run order. `None` marks a process whose order gate failed;
    /// [`summarize_pin_decision`] treats ANY `None` as UNRESOLVED rather than
    /// averaging the survivors.
    pub(super) process_ratios: Vec<Option<f64>>,
}

/// The pin decision's result — an ENUM, for the same reason [`SegConfirmSummary`] is:
/// an unresolved decision must not carry an aggregate, a tie set or a winner. A
/// struct with those fields plus an `outcome` label computes a **shrunken** aggregate
/// from whatever cells survived and then marks it unresolved, leaving a publishable
/// ranking one field access away.
#[derive(Clone, Debug)]
pub(super) enum SegPinSummary {
    Resolved {
        winner: String,
        /// Per level, per cell — ALWAYS reported, never only the aggregate.
        cells: Vec<(String, Vec<SegPinCellSummary>)>,
        /// Per DECISION level, the median across decision cells.
        aggregates: Vec<(String, f64)>,
        tie_set: Vec<String>,
        drift: Vec<(String, f64)>,
        drift_spread_pct: f64,
        reproduction_gap_pct: f64,
        /// The PREDECLARED-INELIGIBLE levels and their reasons
        /// ([`SEG_PIN_REFUSED_LEVELS`]), carried on the summary so no consumer can render a
        /// level table that silently omits them. A refused level is a per-level OUTCOME.
        refused: Vec<(String, String)>,
    },
    Unresolved {
        reason: String,
        /// The per-cell table still appears — it is the evidence.
        cells: Vec<(String, Vec<SegPinCellSummary>)>,
        drift: Vec<(String, f64)>,
        /// **No `aggregates`, no `tie_set`, no `winner`.** Nothing pooled exists.
        per_level_usable: Vec<(String, usize, usize)>,
        /// Carried on BOTH variants — see [`SEG_PIN_REFUSED_LEVELS`].
        refused: Vec<(String, String)>,
    },
}

/// **Levels the §4.5 decision SCORES.** Ruling R8, predeclared before any timing.
///
/// `40` is deliberately absent; see [`SEG_PIN_REFUSED_LEVELS`].
pub(super) const SEG_PIN_DECISION_LEVELS: [&str; 2] = ["natural", "48"];

/// **Levels PREDECLARED INELIGIBLE, with the measured reason each carries.**
///
/// This exists because §4.2's eligibility clause and §4.5's level-set assertion used to
/// contradict each other: the rule's doc said *"a level that spilled is ineligible — the
/// caller must not pass one"* while its `DECISION_LEVELS` array made `40` **mandatory**, so
/// no input satisfied both and the decision was unreachable rather than unresolved. Ruling
/// R8 reconciles them here: the ineligible level is named in source, with its reason, and
/// it enters the record as a per-level OUTCOME rather than as a missing row.
///
/// **The refusal is a MEASURED fact, not a policy.** `measure_shape` calls
/// [`SegKernelAttributes::assert_no_spills`] before it will launch anything, and at a
/// 40-register ceiling the swept continuation executor reports
/// `cudaFuncGetAttributes.localSizeBytes = 16` — so every one of the six decision cells
/// (all `cont_const_epi_plane`) aborts pre-launch, and only the R0 drift control
/// (`localSizeBytes = 0`) would survive. A level that can supply the control and no
/// decision cell cannot be scored.
///
/// **Which spill number is authoritative, since the two disagree at exactly this level.**
/// `cuobjdump --dump-resource-usage` reports `LOCAL=0, STACK=16` for that symbol, while the
/// runtime reports `localSizeBytes = 16`. **Launch eligibility keys on the RUNTIME
/// attribute** — it is what the launch actually pays and what `assert_no_spills` reads. The
/// `cuobjdump` STACK/LOCAL table stays the per-symbol BUILD-gate record and is recorded
/// beside it; it is not the eligibility predicate. Both are kept because they answer
/// different questions.
pub(super) const SEG_PIN_REFUSED_LEVELS: [(&str, &str); 1] =
    [("40", "REFUSED (outcome-B spill: localSizeBytes=16)")];

impl SegPinSummary {
    /// One machine-readable token, UNDERSCORED like the R0 verdicts so no outcome is
    /// a substring of another.
    pub(super) fn outcome(&self) -> &'static str {
        match self {
            Self::Resolved { .. } => "RESOLVED",
            Self::Unresolved { .. } => "UNRESOLVED",
        }
    }
}

/// **§4.5's rule, applied mechanically. This is NOT §6(b)'s rule.**
///
/// Preconditions, all asserted rather than assumed:
///   * the level set is EXACTLY [`SEG_PIN_DECISION_LEVELS`] (`{natural, 48}`) for the
///     decision, with `natural-repeat` MANDATORY and used ONLY as the reproduction gate,
///     and every level in [`SEG_PIN_REFUSED_LEVELS`] **absent**;
///   * every level contributed exactly [`SEG_CONFIRM_PROCESSES`] processes;
///   * the drift control ran at every level.
///
/// **Why the set is `{natural, 48}` and not `{natural, 48, 40}` (rulings R4 + R8).** An
/// earlier form made `40` mandatory *and* documented that a spilled level must not be
/// passed — a contradiction no input could satisfy, which made the decision UNREACHABLE
/// rather than unresolved. `40` is now refused with its measured reason
/// ([`SEG_PIN_REFUSED_LEVELS`]: `cudaFuncGetAttributes.localSizeBytes = 16` on every
/// decision cell's executor) and is REPORTED as a per-level outcome. Passing it is a
/// caller error and panics, so an ineligible level can never be silently dropped into the
/// aggregate either.
///
/// **The tie-break consequence, PREDECLARED by R8 before any level was timed:** with `40`
/// out, `48` is the lowest ELIGIBLE ceiling, so a `natural`-vs-`48` tie resolves to **48**.
/// That is the same rule as before (lowest ceiling in the tie set), applied to the eligible
/// set; it is written down here rather than discovered from an outcome.
///
/// Rules:
///   * **Aggregate = median over DECISION cells** of the per-cell level estimates.
///     The drift control is excluded — it is pin-invariant by construction, so
///     including it would dilute the effect being measured.
///   * **Any order-invalid cell at any level ⇒ UNRESOLVED.** Not "drop the cell":
///     the cell set is predeclared, so silently shrinking it changes the estimator
///     after the fact.
///   * **Tie set** = every level within [`SEG_PIN_TIE_FRACTION`] of the BEST
///     aggregate (defined against the best, so transitive by construction).
///   * **Winner** = lowest register ceiling in the tie set. Over the ELIGIBLE set that is
///     `48 < natural/56`; the full ordering is `40 < 48 < natural/56`, but `40` cannot
///     enter a tie set (see [`SEG_PIN_REFUSED_LEVELS`]).
///   * **Mechanism 3 gate:** if the best-to-second-best margin is smaller than the
///     drift control's own cross-level spread, the pin delta is **NOT resolved**.
///   * **Mechanism 4 gate:** if `natural-repeat` differs from `natural` by more than
///     [`SEG_PIN_TIE_FRACTION`], **UNRESOLVED**.
///   * A level that spilled is ineligible (§4.2). It is named in
///     [`SEG_PIN_REFUSED_LEVELS`], REFUSED if passed, and REPORTED as a per-level
///     outcome — so the ineligibility is visible without being mandatory, which is the
///     contradiction R8 removed.
pub(super) fn summarize_pin_decision(
    per_level: &[(String, Vec<SegPinCellSummary>)],
) -> SegPinSummary {
    const DECISION_LEVELS: [&str; SEG_PIN_DECISION_LEVELS.len()] = SEG_PIN_DECISION_LEVELS;
    const REPEAT_LEVEL: &str = "natural-repeat";
    let refused: Vec<(String, String)> = SEG_PIN_REFUSED_LEVELS
        .iter()
        .map(|(level, why)| ((*level).to_owned(), (*why).to_owned()))
        .collect();
    // The set is EXACT and the repeat is MANDATORY. An optional repeat would let
    // mechanism 4 be skipped by omission, and a missing decision level would let the
    // aggregate be computed over a shrunken ladder — both fail-open holes.
    let levels: Vec<&str> = per_level.iter().map(|(l, _)| l.as_str()).collect();
    // A PREDECLARED-INELIGIBLE level is REFUSED, never silently dropped. Dropping it
    // would let a caller hand in a spilled level's numbers and get a decision back that
    // looks like it scored three levels; panicking makes the ineligibility visible at the
    // one place that could otherwise launder it.
    for (level, why) in SEG_PIN_REFUSED_LEVELS {
        assert!(
            !levels.contains(&level),
            "level {level} is PREDECLARED INELIGIBLE — {why} — so it may not be scored \
             (rulings R4 + R8). It is reported as a per-level outcome instead; remove it \
             from the dirs spec. Got levels {levels:?}"
        );
    }
    let mut expected: Vec<&str> = DECISION_LEVELS.to_vec();
    expected.push(REPEAT_LEVEL);
    for want in &expected {
        assert_eq!(
            levels.iter().filter(|l| *l == want).count(),
            1,
            "the pin decision needs EXACTLY ONE {want} (mechanism 4's repeat is \
             mandatory, not optional); got levels {levels:?}"
        );
    }
    assert_eq!(
        levels.len(),
        expected.len(),
        "unexpected levels {levels:?}: the set is exactly {expected:?}"
    );
    let mut reasons: Vec<String> = Vec::new();
    let mut aggregates = Vec::new();
    let mut drift = Vec::new();
    let mut per_level_usable: Vec<(String, usize, usize)> = Vec::new();
    for (level, cells) in per_level {
        // **The cell set is EXACT, per level.** The set is predeclared, so a level
        // that contributed fewer cells did not measure the same thing — and letting
        // the aggregate be a median over "whatever arrived" is how a decision set
        // silently shrinks.
        assert_eq!(
            cells.len(),
            SEG_PIN_DECISION_CELLS.len(),
            "{level}: {} cells, expected exactly {}",
            cells.len(),
            SEG_PIN_DECISION_CELLS.len()
        );
        for expected in &SEG_PIN_DECISION_CELLS {
            let matching: Vec<&SegPinCellSummary> =
                cells.iter().filter(|c| c.label == expected.label).collect();
            assert_eq!(
                matching.len(),
                1,
                "{level}: expected EXACTLY ONE cell labelled {}, found {}",
                expected.label,
                matching.len()
            );
            assert_eq!(
                matching[0].role, expected.role,
                "{level} {}: role drifted from the predeclared set",
                expected.label
            );
        }
        for cell in cells {
            assert_eq!(
                cell.process_ratios.len(),
                SEG_CONFIRM_PROCESSES,
                "{level} {}: expected {SEG_CONFIRM_PROCESSES} processes",
                cell.label
            );
            // Every PROCESS must have contributed a usable ratio, not just the cell
            // overall: a cell whose median came from two of three processes is a
            // different estimator from the one predeclared.
            if cell.process_ratios.iter().any(Option::is_none) {
                reasons.push(format!(
                    "{level} {}: {} of {SEG_CONFIRM_PROCESSES} processes are \
                     order-invalid",
                    cell.label,
                    cell.process_ratios.iter().filter(|r| r.is_none()).count()
                ));
            }
            if cell.estimate.is_none() {
                reasons.push(format!("{level} {} has no usable estimate", cell.label));
            }
        }
        let decision_total = cells
            .iter()
            .filter(|c| c.role == SegPinRole::Decision)
            .count();
        let usable = cells
            .iter()
            .filter(|c| c.role == SegPinRole::Decision && c.estimate.is_some())
            .count();
        per_level_usable.push((level.clone(), usable, decision_total));
        if usable != decision_total {
            reasons.push(format!(
                "{level}: only {usable} of {decision_total} decision cells are \
                 usable — the aggregate is NOT computed over a shrunken set"
            ));
        }
        if cells
            .iter()
            .find(|c| c.role == SegPinRole::DriftControl)
            .and_then(|c| c.estimate)
            .is_none()
        {
            reasons.push(format!("{level}: the drift control has no usable estimate"));
        }
    }
    // ── EVERYTHING above is validation. Nothing is aggregated, no median is taken,
    //    and the structured Unresolved returns HERE — before any arithmetic that
    //    could be computed over an incomplete set. An earlier draft recorded reasons
    //    and then computed medians anyway, and its `assert_eq!(drift.len(), 3)`
    //    PANICKED on the very input it was meant to classify. ────────────────────
    if !reasons.is_empty() {
        return SegPinSummary::Unresolved {
            reason: reasons.join("; "),
            cells: per_level.to_vec(),
            drift,
            per_level_usable,
            refused,
        };
    }
    // From here every value is present by construction: the validation above proved
    // that every decision cell and every drift control at every level has an
    // estimate, so no `filter_map` can silently shrink anything.
    for (level, cells) in per_level {
        let control = cells
            .iter()
            .find(|c| c.role == SegPinRole::DriftControl)
            .and_then(|c| c.estimate)
            .expect("validated above");
        // Mechanism 3's spread is over the SCORED DECISION LEVELS only
        // (`SEG_PIN_DECISION_LEVELS`; two since R8, not three). The repeat is a rebuild of
        // `natural`, so folding it in would inflate the spread and make the margin gate
        // trivially passable. **Measured caveat on what the repeat can show:** this
        // toolchain's CUDA build is deterministic, so the repeat reproduced the archive
        // BYTE-IDENTICALLY — mechanism 4 therefore measures session drift, not rebuild
        // variance, and the exclusion here is about not diluting the spread rather than
        // about excluding rebuild noise that does not exist.
        if DECISION_LEVELS.contains(&level.as_str()) {
            drift.push((level.clone(), control));
            let decision: Vec<f64> = cells
                .iter()
                .filter(|c| c.role == SegPinRole::Decision)
                .map(|c| c.estimate.expect("validated above"))
                .collect();
            aggregates.push((level.clone(), median(&decision)));
        }
    }
    // Mechanism 4: the repeat compares ONLY to natural, and only as a gate.
    // `None` only when the level is absent (which the exact-set assertion already
    // ruled out) or when a decision cell lacks an estimate (a validated reason
    // above), so this never medians an empty slice.
    let value_of = |name: &str| -> Option<f64> {
        let (_, cells) = per_level.iter().find(|(l, _)| l == name)?;
        let decision: Vec<Option<f64>> = cells
            .iter()
            .filter(|c| c.role == SegPinRole::Decision)
            .map(|c| c.estimate)
            .collect();
        if decision.is_empty() || decision.iter().any(Option::is_none) {
            return None;
        }
        Some(median(
            &decision
                .into_iter()
                .map(|e| e.expect("checked"))
                .collect::<Vec<f64>>(),
        ))
    };
    // The repeat compares ONLY to natural, and only as the reproduction gate — it
    // never enters an aggregate, a tie set or the drift spread. Both operands are
    // complete by the validation above, so `value_of` cannot median an empty slice.
    let reproduction_gap_pct = {
        let a = value_of("natural").expect("validated above");
        let b = value_of(REPEAT_LEVEL).expect("validated above");
        (b / a - 1.0).abs() * 100.0
    };
    if reproduction_gap_pct > SEG_PIN_TIE_FRACTION * 100.0 {
        return SegPinSummary::Unresolved {
            reason: format!(
                "natural did not reproduce on rebuild: {reproduction_gap_pct:.3}% > {:.2}%",
                SEG_PIN_TIE_FRACTION * 100.0
            ),
            cells: per_level.to_vec(),
            drift,
            per_level_usable,
            refused,
        };
    }
    // Mechanism 3: the pin margin must exceed the control's own cross-level spread.
    // Complete by construction: the loop above pushes exactly one control per
    // decision level, and the validation proved each has an estimate.
    let drift_values: Vec<f64> = drift.iter().map(|(_, v)| *v).collect();
    debug_assert_eq!(drift_values.len(), DECISION_LEVELS.len());
    let drift_spread_pct = if drift_values.len() >= 2 {
        let lo = drift_values.iter().copied().fold(f64::MAX, f64::min);
        let hi = drift_values.iter().copied().fold(f64::MIN, f64::max);
        (hi / lo - 1.0) * 100.0
    } else {
        0.0
    };
    let mut ranked = aggregates.clone();
    ranked.sort_by(|a, b| a.1.partial_cmp(&b.1).expect("finite aggregate"));
    let best = ranked
        .first()
        .map(|(_, v)| *v)
        .expect("three decision levels");
    if ranked.len() >= 2 {
        let margin = (ranked[1].1 / best - 1.0) * 100.0;
        if margin < drift_spread_pct {
            return SegPinSummary::Unresolved {
                reason: format!(
                    "pin margin {margin:.3}% is below the drift control's own \
                     cross-level spread {drift_spread_pct:.3}%"
                ),
                cells: per_level.to_vec(),
                drift,
                per_level_usable,
                refused,
            };
        }
    }
    let tie_set: Vec<String> = aggregates
        .iter()
        .filter(|(_, v)| *v <= best * (1.0 + SEG_PIN_TIE_FRACTION))
        .map(|(l, _)| l.clone())
        .collect();
    // Lowest register ceiling within the tie set: 40 < 48 < natural/56. NOT "prefers
    // the level that pins a ceiling" — §4.3 ships a 56 pin when natural wins, so
    // every level ends up pinned and that tie-break is vacuous.
    // `"40"` is DEAD BY ELIGIBILITY, and is kept deliberately rather than deleted: `40` can
    // never reach a tie set while it is in `SEG_PIN_REFUSED_LEVELS`, but if F2 ever makes the
    // level launchable, a missing arm would silently score it as `56` and the tie-break would
    // prefer `48` over a genuinely lower ceiling. A dead arm is cheaper than that latent bug.
    let ceiling = |level: &str| match level {
        "40" => 40u32,
        "48" => 48,
        _ => 56,
    };
    let winner = tie_set
        .iter()
        .min_by_key(|level| ceiling(level))
        .expect("a non-empty tie set")
        .clone();
    SegPinSummary::Resolved {
        winner,
        cells: per_level.to_vec(),
        aggregates,
        tie_set,
        drift,
        drift_spread_pct,
        reproduction_gap_pct,
        refused,
    }
}

/// The δ3 loop-form attribution (§4.5's fourth build), scored on its own terms.
///
/// **This is neither §6(b)'s inversion rule nor §4.5's cross-level rule.** It asks
/// one question — *does unrolling the δ3 arm change the δ3-bearing cells' time?* — so
/// it is a two-arm, per-cell comparison at ONE pin, and it deliberately does not
/// aggregate across cells: the whole point is which cells move.
#[derive(Clone, Debug)]
pub(super) enum SegD3Attribution {
    /// Every cell scored on both arms with a passing order gate.
    Scored {
        /// Per cell: `(label, rolled, unrolled, unrolled / rolled)`.
        cells: Vec<(String, f64, f64, f64)>,
        /// The drift control's own two values, reported and never pooled with the
        /// decision cells.
        drift: (f64, f64),
    },
    Unresolved {
        reason: String,
        /// Per cell, per arm: `None` where that arm was order-invalid.
        cells: Vec<(String, Option<f64>, Option<f64>)>,
    },
}

/// `rolled` and `unrolled` are each that arm's THREE processes for the same cell.
pub(super) fn summarize_d3_attribution(
    rolled: &[(String, Vec<SegPinCellSummary>)],
    unrolled: &[(String, Vec<SegPinCellSummary>)],
) -> SegD3Attribution {
    let mut reasons: Vec<String> = Vec::new();
    // EXACT membership on both arms, against the attribution set — not the pin set.
    for (label, cells) in rolled.iter().chain(unrolled.iter()) {
        assert_eq!(
            cells.len(),
            SEG_D3_ATTRIBUTION_CELLS.len(),
            "{label}: {} cells, expected exactly {}",
            cells.len(),
            SEG_D3_ATTRIBUTION_CELLS.len()
        );
        for expected in &SEG_D3_ATTRIBUTION_CELLS {
            let matching: Vec<&SegPinCellSummary> =
                cells.iter().filter(|c| c.label == expected.label).collect();
            assert_eq!(
                matching.len(),
                1,
                "{label}: {} appears {} times",
                expected.label,
                matching.len()
            );
            assert_eq!(
                matching[0].role, expected.role,
                "{label} {}: role drifted",
                expected.label
            );
            assert_eq!(
                matching[0].process_ratios.len(),
                SEG_CONFIRM_PROCESSES,
                "{label} {}: expected {SEG_CONFIRM_PROCESSES} processes",
                expected.label
            );
            if matching[0].process_ratios.iter().any(Option::is_none)
                || matching[0].estimate.is_none()
            {
                reasons.push(format!("{label} {} is order-invalid", expected.label));
            }
        }
    }
    assert_eq!(rolled.len(), 1, "exactly one rolled arm");
    assert_eq!(unrolled.len(), 1, "exactly one unrolled arm");
    let pick = |arm: &[(String, Vec<SegPinCellSummary>)], label: &str| {
        arm[0]
            .1
            .iter()
            .find(|c| c.label == label)
            .expect("membership asserted")
            .estimate
    };
    let per_cell: Vec<(String, Option<f64>, Option<f64>)> = SEG_D3_ATTRIBUTION_CELLS
        .iter()
        .map(|c| {
            (
                c.label.to_owned(),
                pick(rolled, c.label),
                pick(unrolled, c.label),
            )
        })
        .collect();
    if !reasons.is_empty() {
        return SegD3Attribution::Unresolved {
            reason: reasons.join("; "),
            cells: per_cell,
        };
    }
    let control = SEG_D3_ATTRIBUTION_CELLS
        .iter()
        .find(|c| c.role == SegPinRole::DriftControl)
        .expect("one control");
    SegD3Attribution::Scored {
        cells: per_cell
            .iter()
            .filter(|(label, _, _)| label != control.label)
            .map(|(label, r, u)| {
                let (r, u) = (r.expect("validated"), u.expect("validated"));
                (label.clone(), r, u, u / r)
            })
            .collect(),
        drift: (
            pick(rolled, control.label).expect("validated"),
            pick(unrolled, control.label).expect("validated"),
        ),
    }
}

/// Split `BWD_SEG_CONFIRM_DIRS` into the (rolled, unrolled) arms by EXACT KEY.
///
/// The unrolled arm is keyed exactly `d3unroll`; the rolled arm is keyed exactly the
/// winning level, which must equal the compiled `pin_level` its own runs recorded.
/// Anything else — two keys the same, three keys, a rolled key that is not the winner,
/// a rolled arm whose runs were compiled at a different pin — is a caller error and is
/// refused here rather than silently inverting the attribution.
pub(super) fn split_d3_arms(spec: &str, winner: &str) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let mut groups: Vec<(String, Vec<PathBuf>)> = Vec::new();
    for group in spec.split(';').filter(|g| !g.trim().is_empty()) {
        let (key, dirs) = group
            .split_once('=')
            .unwrap_or_else(|| panic!("BWD_SEG_CONFIRM_DIRS group {group:?} is not <key>=<dirs>"));
        groups.push((key.to_owned(), dirs.split(':').map(PathBuf::from).collect()));
    }
    assert_eq!(
        groups.len(),
        2,
        "the attribution has exactly two arms; got {}",
        groups.len()
    );
    let unrolled_count = groups.iter().filter(|(k, _)| k == "d3unroll").count();
    assert_eq!(
        unrolled_count, 1,
        "exactly one arm must be keyed `d3unroll`"
    );
    let rolled_count = groups.iter().filter(|(k, _)| k == winner).count();
    assert_eq!(
        rolled_count, 1,
        "exactly one arm must be keyed with the winning level {winner:?}"
    );
    assert_ne!(winner, "d3unroll", "the winner cannot be the unrolled arm");
    let unrolled = groups
        .iter()
        .find(|(k, _)| k == "d3unroll")
        .expect("checked")
        .1
        .clone();
    let rolled = groups
        .iter()
        .find(|(k, _)| k == winner)
        .expect("checked")
        .1
        .clone();
    (rolled, unrolled)
}

/// One arm's aggregated evidence: its per-cell summaries AND the one validated
/// identity every run in it shares.
///
/// [`aggregate_confirmation_runs`] returns only a [`SegConfirmSummary`], which is why
/// the identity checks below need their own entry point: an aggregator that discards
/// the provenance it validated cannot then bind a payload to an arm.
pub(super) struct SegArmEvidence {
    pub(super) cells: Vec<SegPinCellSummary>,
    /// **EVERY run's identity, in `dirs` order — not one representative.**
    /// [`shared_identity`] proves the CONSTANT fields equal, but `run_label` and
    /// `run_id` differ per run by design, so reducing to a representative loses
    /// exactly the field the arm binding needs. The accepted counterexample: rolled
    /// run 1 labelled `d3attr-rolled-1` while runs 2 and 3 are labelled
    /// `d3attr-d3unroll-*`, all with the rolled expected hashes, the right pin and
    /// distinct ids — a representative check passes it.
    pub(super) identities: Vec<SegRunMeta>,
    pub(super) dirs: Vec<PathBuf>,
}

impl SegArmEvidence {
    /// The fields [`shared_identity`] proved constant across the arm's runs. Never use
    /// it for `run_label` or `run_id`, which are per-run.
    pub(super) fn constant(&self) -> &SegRunMeta {
        self.identities
            .first()
            .expect("an arm has at least one run")
    }
}

/// Read one arm's run directories and build per-cell summaries over `cells`, returning
/// the shared identity alongside them.
///
/// Per cell, per process: build the process's [`SegBlockedSamples`] from its blocks for
/// that cell and take [`SegRatio::of`]. `process_ratios[i]` is `Some(median block
/// ratio)` where that process's order gate PASSED and `None` where it failed — the gate
/// lives in the type, so this cannot accidentally pool an invalid process. The cell's
/// `estimate` is the median across processes, and `None` if ANY process is `None`: a
/// cell whose median came from two of three processes is a different estimator from the
/// one predeclared.
pub(super) fn aggregate_arm(dirs: &[PathBuf], cells: &[SegPinCell]) -> SegArmEvidence {
    let mut unique: Vec<&PathBuf> = dirs.iter().collect();
    unique.sort();
    unique.dedup();
    assert_eq!(
        unique.len(),
        dirs.len(),
        "an arm's run directories must be distinct: {dirs:?}"
    );
    assert_eq!(
        dirs.len(),
        SEG_CONFIRM_PROCESSES,
        "an arm has exactly {SEG_CONFIRM_PROCESSES} processes; got {}",
        dirs.len()
    );
    let runs: Vec<(SegRunMeta, _)> = dirs.iter().map(|dir| read_run(dir)).collect();
    // Validates the constant fields; the per-run fields are checked by the caller's
    // arm binding, which is the only place that knows what each run SHOULD be.
    shared_identity(&runs.iter().map(|(m, _)| m.clone()).collect::<Vec<_>>());
    // EXACT per-run cell membership: a missing cell already fails below, and an EXTRA
    // one must fail too — a run carrying cells the set does not name was produced by a
    // different freeze, so it is not this arm's evidence.
    let wanted: std::collections::BTreeSet<&str> = cells.iter().map(|c| c.label).collect();
    for (dir, (_, by_cell)) in dirs.iter().zip(runs.iter()) {
        let present: std::collections::BTreeSet<&str> =
            by_cell.keys().map(String::as_str).collect();
        assert_eq!(
            present,
            wanted,
            "{}: raw cells {present:?} are not exactly the requested set {wanted:?}",
            dir.display()
        );
    }
    let summaries = cells
        .iter()
        .map(|cell| {
            let process_ratios: Vec<Option<f64>> = runs
                .iter()
                .map(|(meta, by_cell)| {
                    let blocks = by_cell
                        .get(cell.label)
                        .unwrap_or_else(|| panic!("a run has no blocks for cell {}", cell.label));
                    let samples = SegBlockedSamples {
                        schedule: seg_schedule(meta.seed),
                        blocks: blocks.clone(),
                    };
                    SegRatio::of(&samples)
                        .selectable()
                        .map(|(estimate, _)| estimate.median_ratio)
                })
                .collect();
            let estimate = if process_ratios.iter().all(Option::is_some) {
                Some(median(
                    &process_ratios
                        .iter()
                        .map(|r| r.expect("checked"))
                        .collect::<Vec<f64>>(),
                ))
            } else {
                None
            };
            SegPinCellSummary {
                label: cell.label.to_owned(),
                role: cell.role,
                estimate,
                process_ratios,
            }
        })
        .collect();
    SegArmEvidence {
        cells: summaries,
        identities: runs.iter().map(|(m, _)| m.clone()).collect(),
        dirs: dirs.to_vec(),
    }
}

/// What the shell tells the aggregator each arm MUST be. Derived independently of
/// `BWD_SEG_CONFIRM_DIRS` — from the gated provenance files — so a swapped payload
/// cannot satisfy it.
pub(super) struct SegExpectedArm {
    pub(super) run_label_prefix: &'static str,
    pub(super) archive_sha256: String,
    pub(super) test_binary_sha256: String,
}

/// Bind each payload to its EXPECTED arm, then check the cross-arm invariants.
pub(super) fn assert_d3_arm_identities(
    winner: &str,
    rolled: &SegArmEvidence,
    unrolled: &SegArmEvidence,
    expect_rolled: &SegExpectedArm,
    expect_unrolled: &SegExpectedArm,
) {
    // (1) PAYLOAD BINDING. Each arm's actual artifact must be the one the shell read
    // out of THAT arm's gated provenance file. This is asymmetric, so a swap fails:
    // the rolled payload would carry the unrolled archive and test-binary hashes.
    for (what, arm, want) in [
        ("rolled", rolled, expect_rolled),
        ("unrolled", unrolled, expect_unrolled),
    ] {
        let got = arm.constant();
        assert_eq!(
            got.archive_sha256, want.archive_sha256,
            "the {what} arm's runs name archive {} but the gated {what} build is {} — \
             the two arms' payloads are swapped or the wrong dirs were passed",
            got.archive_sha256, want.archive_sha256
        );
        assert_eq!(
            got.test_binary_sha256, want.test_binary_sha256,
            "the {what} arm's runs name test binary {} but the gated {what} build is {}",
            got.test_binary_sha256, want.test_binary_sha256
        );
        // (2) A SECOND, INDEPENDENT binding: the run label the launcher stamped, checked
        // on EVERY run against its EXACT expected value. A prefix check on one
        // representative is not enough — see `SegArmEvidence::identities`.
        assert_eq!(
            arm.identities.len(),
            SEG_CONFIRM_PROCESSES,
            "the {what} arm has {} runs, expected {SEG_CONFIRM_PROCESSES}",
            arm.identities.len()
        );
        for (index, id) in arm.identities.iter().enumerate() {
            let expected = format!("{}{}", want.run_label_prefix, index + 1);
            assert_eq!(
                id.run_label,
                expected,
                "the {what} arm's run {} is labelled {:?}, expected {expected:?} — the \
                 launcher stamps `<prefix><1..3>`, so a mislabelled or swapped run \
                 shows up here even when every constant field agrees",
                index + 1,
                id.run_label
            );
        }
    }
    // (3) Constant across the arms — they differ ONLY in the loop form.
    let (r, u) = (rolled.constant(), unrolled.constant());
    for (field, a, b) in [
        ("commit", &r.commit, &u.commit),
        ("pin_level", &r.pin_level, &u.pin_level),
        ("feature_set", &r.feature_set, &u.feature_set),
        ("toolkit", &r.toolkit, &u.toolkit),
        ("device", &r.device, &u.device),
    ] {
        assert_eq!(a, b, "the two attribution arms differ in {field}");
    }
    assert_eq!(r.seed, u.seed, "the arms differ in SEED");
    // (4) The rolled arm's COMPILED pin must be the INDEPENDENTLY derived winner — not
    // merely its dict key, which the caller chose.
    assert_eq!(
        r.pin_level, winner,
        "the rolled arm was compiled at {}, not at the winning pin {winner}",
        r.pin_level
    );
    // (5) Two DIFFERENT builds, in the archive AND in the executable actually run. An
    // identical archive means the unroll define never reached nvcc; an identical test
    // binary means one measurement reported twice, whatever the archives say.
    assert_ne!(
        r.archive_sha256, u.archive_sha256,
        "both arms name the same ARCHIVE: AB_GKR_SEG_D3_UNROLL did not reach nvcc"
    );
    assert_ne!(
        r.test_binary_sha256, u.test_binary_sha256,
        "both arms name the same TEST BINARY: the executable actually run is identical"
    );
}

/// Serialize one predeclared cell set as a freeze, under its own campaign tag.
///
/// A *serialisation* of a constant, not a selection — which is what makes both
/// non-R0 cell sets level-independent by construction. The frozen row's coordinate
/// is add_sub layer 0 in the SHORT form [`ADD_SUB_LAYOUT_SHORT`], which is the form
/// every freeze predicate compares against.
fn write_predeclared_freeze(campaign: &str, cells: &[SegPinCell]) {
    let path = std::env::var("BWD_SEG_FROZEN_CELLS_OUT")
        .expect("BWD_SEG_FROZEN_CELLS_OUT must name the freeze to write");
    let frozen: Vec<SegFrozenCell> = cells
        .iter()
        .map(|cell| SegFrozenCell {
            label: cell.label.to_owned(),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: cell.class,
            k: cell.k,
            epilogue: epilogue_label(BwdSegEpilogue::Plane).to_owned(),
            coeff: coeff_label(CoeffMode::Constant).to_owned(),
            program: program_label(ProgramMode::Inline).to_owned(),
        })
        .collect();
    // `write_predeclared_freeze` serves `pin-decision` and `d3-attribution` only; both
    // hardcode `FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES)` and assert the realized
    // field in their own runners, so there is no probe-vs-shortlist gap to close here.
    // `write_frozen_cells` panics if this is ever pointed at `r0-headline`.
    write_frozen_cells(
        Path::new(&path),
        campaign,
        &frozen,
        SEG_SCHEDULE_SEED,
        &SegProbeEvidence::NotRequired,
    );
    eprintln!(
        "[seg-freeze] wrote {} {campaign} cells to {path}",
        frozen.len()
    );
}

/// Write [`SEG_PIN_DECISION_CELLS`] as the `pin-decision` freeze.
#[test]
#[ignore = "campaign freeze writer; BWD_SEG_FROZEN_CELLS_OUT names the output"]
fn bwd_seg_freeze_pin_decision() {
    write_predeclared_freeze("pin-decision", &SEG_PIN_DECISION_CELLS);
}

/// Write [`SEG_D3_ATTRIBUTION_CELLS`] as the `d3-attribution` freeze — its OWN tag,
/// because it is scored by its own rule ([`summarize_d3_attribution`]) and the pin
/// runner must refuse it exactly as it refuses the R0 freeze.
#[test]
#[ignore = "campaign freeze writer; BWD_SEG_FROZEN_CELLS_OUT names the output"]
fn bwd_seg_freeze_d3_attribution() {
    write_predeclared_freeze("d3-attribution", &SEG_D3_ATTRIBUTION_CELLS);
}

/// The confirmation run directories, GROUPED BY COLUMN, from `BWD_SEG_CONFIRM_DIRS`.
///
/// **Grammar: `<column>=<dir>:<dir>:<dir>;<column>=…`** — the same shape
/// `bwd_seg_aggregate_pin_decision` reads, and the shape the plan's step-4 block writes
/// (`"primary=…;secondary=…"`, one process, both columns, then
/// `grep 'column=primary'` / `grep 'column=secondary'` over the ONE log it produced).
///
/// It used to split on `':'` only, which is why that block could not run: the plan's
/// string parsed as five directories named `"primary=<d>"`, `"<d>"`,
/// `"<d>;secondary=<d>"`, `"<d>"`, `"<d>"`, and `aggregate_confirmation_runs` rejects any
/// count that is not the predeclared 3 or 5 — so the process aborted before classifying
/// anything, and the two columns could not have been told apart if it hadn't. Two
/// grammars for one variable across two aggregators in one pass is a defect on its own.
///
/// A group with no `=` keeps the single-column form legal and takes its name from
/// `BWD_SEG_CARVEOUT`, so one column can still be aggregated in isolation.
fn confirm_columns() -> Vec<(String, Vec<PathBuf>)> {
    let spec = std::env::var("BWD_SEG_CONFIRM_DIRS")
        .expect("BWD_SEG_CONFIRM_DIRS must name the confirmation run directories");
    let fallback = std::env::var("BWD_SEG_CARVEOUT").unwrap_or_else(|_| "fixed-bucket".to_owned());
    parse_confirm_columns(&spec, &fallback)
}

/// The grammar itself, separated from the environment so a CPU test can drive it without
/// mutating a process-global variable that every other test in the binary shares.
fn parse_confirm_columns(spec: &str, fallback: &str) -> Vec<(String, Vec<PathBuf>)> {
    let columns: Vec<(String, Vec<PathBuf>)> = spec
        .split(';')
        .filter(|group| !group.trim().is_empty())
        .map(|group| {
            let (name, dirs) = match group.split_once('=') {
                Some((name, dirs)) => (name.trim().to_owned(), dirs),
                None => (fallback.to_owned(), group),
            };
            let dirs: Vec<PathBuf> = dirs
                .split(':')
                .filter(|d| !d.trim().is_empty())
                .map(|d| PathBuf::from(d.trim()))
                .collect();
            assert!(
                !dirs.is_empty(),
                "BWD_SEG_CONFIRM_DIRS group {group:?} names no run directory"
            );
            (name, dirs)
        })
        .collect();
    assert!(
        !columns.is_empty(),
        "BWD_SEG_CONFIRM_DIRS names no column: {spec:?}"
    );
    // Distinct column names, so `column=primary` in the emitted log identifies exactly
    // one group. Two groups sharing a name would print two verdicts per cell under one
    // label and the plan's step-4 count check would pass on double the rows.
    let mut names: Vec<&String> = columns.iter().map(|(name, _)| name).collect();
    names.sort();
    let before = names.len();
    names.dedup();
    assert_eq!(
        before,
        names.len(),
        "BWD_SEG_CONFIRM_DIRS repeats a column name: {spec:?}"
    );
    columns
}

/// **§6(b)'s R0 headline aggregator.** Per COLUMN and per frozen shape, feeds that
/// column's three run directories to [`aggregate_confirmation_runs`] and prints the
/// [`SegConfirmSummary`]. §7.2.1's two columns are aggregated in ONE process — see
/// [`confirm_columns`] for the grammar and for why it is not `':'`-only.
///
/// **Which column is §7.2.1's PRIMARY is UNSETTLED — that column is UNPOPULATED pending RR**,
/// so this test names no column as the acceptance gate. It emits every column it is given and
/// **gates none of them**: the gate is the shell's exact-field match on whichever column the
/// ruling designates, because an aggregator that aborted on a non-inverted cell would also
/// abort before printing the columns it exists to report. `as-configured` is barred from
/// gating in any case (M7), and the `off` column is the production-configuration control.
///
/// The verdict is a machine-readable FIELD, not prose, because `NOT INVERTED` contains
/// the substring ` INVERTED` and a `grep -v` acceptance test therefore passes a
/// non-inverted cell silently (measured: the count came back 0). Every gated line
/// carries `outcome=` with exactly one UNDERSCORED token.
///
/// It also records the two things §6(b) requires *beside* the rule and never as a
/// substitute for it: SELECTION STABILITY (whether each process's best frozen cell is
/// the same cell) and, on any UNRESOLVED cell, the ESCALATION CHOICE — which of the two
/// predeclared responses was taken and why, read from
/// `BWD_SEG_ESCALATION_CHOICE` / `BWD_SEG_ESCALATION_WHY` rather than invented here.
#[test]
#[ignore = "campaign aggregator; BWD_SEG_CONFIRM_DIRS names the runs"]
fn bwd_seg_aggregate_r0_headline() {
    let columns = confirm_columns();
    let cells = frozen_cell_filter("r0-headline")
        .expect("BWD_SEG_FROZEN_CELLS must name the r0-headline freeze");
    // The raw files key cells as `<benchmark>|<shape label>`; the freeze names the
    // shape axis. Recovering the raw key from the freeze rather than guessing it is
    // what keeps the aggregator honest about which cell it summarized.
    let mut out = String::from("campaign,column,cell,outcome,median_ratio,min_ratio,max_ratio\n");
    let mut unresolved = 0usize;
    // BOTH columns in ONE process, each with its own three run directories and its own
    // three-outcome verdict per cell. Neither column's rows can dilute the other's: the
    // summaries are computed per group and the `column=` field separates them in the
    // emitted log and CSV.
    for (column, dirs) in &columns {
        let mut per_process_best: Vec<Vec<(String, f64)>> = vec![Vec::new(); dirs.len()];
        for cell in &cells {
            // The raw key `measure_shape` emitted for this cell: the benchmark name the
            // R0 matrix uses, and the shape the FREEZE names — not a hardcoded production
            // shape, which would silently summarize a different cell than the one frozen.
            let key = format!("add_sub L0 R0|{}", frozen_cell_shape(cell).label());
            let summary = aggregate_confirmation_runs(dirs, &key);
            let pooled = match &summary {
                SegConfirmSummary::Resolved {
                    median_ratio,
                    min_ratio,
                    max_ratio,
                    process_ratios,
                    ..
                } => {
                    for (index, ratio) in process_ratios.iter().enumerate() {
                        per_process_best[index].push((cell.label.clone(), *ratio));
                    }
                    Some((*median_ratio, *min_ratio, *max_ratio))
                }
                SegConfirmSummary::Unresolved { reason, .. } => {
                    unresolved += 1;
                    eprintln!(
                        "[seg-r0] column={column} cell={} reason={reason}",
                        cell.label
                    );
                    None
                }
            };
            // `outcome=` carries exactly one of INVERTED / NOT_INVERTED / UNRESOLVED —
            // UNDERSCORED, so no verdict is a substring of another and an exact-field
            // match is possible. Never print the human phrase "NOT INVERTED" on a gated
            // line.
            let outcome = match summary.outcome() {
                SegConfirmOutcome::Inverted => "INVERTED",
                SegConfirmOutcome::NotInverted => "NOT_INVERTED",
                SegConfirmOutcome::Unresolved => "UNRESOLVED",
            };
            eprintln!(
                "[seg-r0] column={column} cell={} outcome={outcome} median={} min={} max={}",
                cell.label,
                pooled.map_or("-".to_owned(), |(median, _, _)| format!("{median:.6}")),
                pooled.map_or("-".to_owned(), |(_, min, _)| format!("{min:.6}")),
                pooled.map_or("-".to_owned(), |(_, _, max)| format!("{max:.6}")),
            );
            writeln!(
                out,
                "r0-headline,{column},{},{outcome},{},{},{}",
                cell.label,
                pooled.map_or("-".to_owned(), |(median, _, _)| format!("{median:.6}")),
                pooled.map_or("-".to_owned(), |(_, min, _)| format!("{min:.6}")),
                pooled.map_or("-".to_owned(), |(_, _, max)| format!("{max:.6}")),
            )
            .expect("write String");
        }
        // SELECTION STABILITY, recorded SEPARATELY and never substituted for the rule
        // (§6(b)): the argmin frozen cell of each process, and whether the three agree.
        // PER COLUMN, because the two columns are two different configurations and a
        // pooled stability statement would describe neither.
        let argmins: Vec<String> = per_process_best
            .iter()
            .map(|ranked| {
                ranked
                    .iter()
                    .min_by(|a, b| a.1.partial_cmp(&b.1).expect("finite ratio"))
                    .map_or_else(|| "-".to_owned(), |(label, _)| label.clone())
            })
            .collect();
        let stable = argmins
            .first()
            .is_some_and(|first| first != "-" && argmins.iter().all(|a| a == first));
        eprintln!(
            "[seg-r0] column={column} selection_stability={} argmins={}",
            if stable { "STABLE" } else { "UNSTABLE" },
            argmins.join("|"),
        );
    }
    // The predeclared ESCALATION, when and only when something was unresolved. The
    // choice is the campaign operator's and is RECORDED, not inferred: §6(b) admits
    // exactly two responses and requires which was taken and why.
    if unresolved > 0 {
        let choice = std::env::var("BWD_SEG_ESCALATION_CHOICE").unwrap_or_else(|_| {
            panic!(
                "{unresolved} cell(s) are UNRESOLVED: BWD_SEG_ESCALATION_CHOICE must \
                 record the predeclared response (`five-processes` or `investigate`) \
                 and BWD_SEG_ESCALATION_WHY must say why"
            )
        });
        assert!(
            matches!(choice.as_str(), "five-processes" | "investigate"),
            "the rule admits exactly two escalations (a predeclared {SEG_ESCALATION_PROCESSES}-process \
             run, or investigating the disagreement as a defect); got {choice:?}"
        );
        let why = std::env::var("BWD_SEG_ESCALATION_WHY")
            .expect("BWD_SEG_ESCALATION_WHY must record why that escalation was chosen");
        eprintln!("[seg-r0] escalation={choice} why={why}");
        writeln!(out, "# escalation = {choice}\n# escalation_why = {why}").expect("write String");
    }
    // PERSISTED, not just printed: the fixed path is the latest view and `publish`
    // mirrors the same bytes into the reservation, where a later process cannot
    // overwrite them.
    publish(&seg_output_path("seg_r0_headline_confirmation.csv"), &out);
}

/// **§4.5's pin-decision aggregator.** Builds [`SegPinCellSummary`] per level per cell
/// from [`SegRatio::selectable`] (so an order-invalid process yields `None` and the rule
/// sees it), calls [`summarize_pin_decision`], and prints the per-cell table, the
/// aggregates, the drift spread, the reproduction gap, the tie set and the outcome.
///
/// `BWD_SEG_CONFIRM_DIRS` is `<level>=<dir>:<dir>:<dir>;<level>=…`, one group per level.
/// **The rule asserts the level set is exactly [`SEG_PIN_DECISION_LEVELS`]
/// (`{natural, 48}`) plus the mandatory `natural-repeat`** — so a three-group spec is what
/// an operator writes here. **`40` must NOT appear**: it is predeclared ineligible
/// ([`SEG_PIN_REFUSED_LEVELS`], measured `cudaFuncGetAttributes.localSizeBytes = 16` on
/// every decision cell), and passing it is refused loudly rather than dropped, so a spec
/// that names it aborts this test instead of yielding a decision over a level that cannot
/// launch. The refusal is reported as a per-level outcome regardless of the spec.
#[test]
#[ignore = "campaign aggregator; BWD_SEG_CONFIRM_DIRS names the runs"]
fn bwd_seg_aggregate_pin_decision() {
    let spec = std::env::var("BWD_SEG_CONFIRM_DIRS").expect("BWD_SEG_CONFIRM_DIRS");
    let mut per_level: Vec<(String, Vec<SegPinCellSummary>)> = Vec::new();
    for group in spec.split(';').filter(|g| !g.trim().is_empty()) {
        let (level, dirs) = group.split_once('=').unwrap_or_else(|| {
            panic!("BWD_SEG_CONFIRM_DIRS group {group:?} is not <level>=<dirs>")
        });
        let dirs: Vec<PathBuf> = dirs.split(':').map(PathBuf::from).collect();
        let arm = aggregate_arm(&dirs, &SEG_PIN_DECISION_CELLS);
        // The COMPILED pin of every run in a level group must be the level itself:
        // a group labelled `40` whose runs were built at `48` is the level
        // comparison silently voided.
        assert_eq!(
            arm.constant().pin_level,
            level_pin(level),
            "the {level} group's runs were compiled at {}",
            arm.constant().pin_level
        );
        per_level.push((level.to_owned(), arm.cells));
    }
    let summary = summarize_pin_decision(&per_level);
    let cells = match &summary {
        SegPinSummary::Resolved { cells, .. } | SegPinSummary::Unresolved { cells, .. } => cells,
    };
    for (level, level_cells) in cells {
        for cell in level_cells {
            let processes: Vec<String> = cell
                .process_ratios
                .iter()
                .map(|r| r.map_or("-".to_owned(), |v| format!("{v:.6}")))
                .collect();
            eprintln!(
                "[seg-pin] level={level} cell={} role={} estimate={} processes={}",
                cell.label,
                cell.role.label(),
                cell.estimate.map_or("-".to_owned(), |v| format!("{v:.6}")),
                processes.join("|"),
            );
        }
    }
    match &summary {
        SegPinSummary::Resolved {
            winner,
            aggregates,
            tie_set,
            drift,
            drift_spread_pct,
            reproduction_gap_pct,
            ..
        } => {
            for (level, value) in aggregates {
                eprintln!("[seg-pin] aggregate level={level} value={value:.6}");
            }
            for (level, value) in drift {
                eprintln!("[seg-pin] drift level={level} value={value:.6}");
            }
            eprintln!(
                "[seg-pin] drift_spread_pct={drift_spread_pct:.4} \
                 reproduction_gap_pct={reproduction_gap_pct:.4} tie_set={} winner={winner}",
                tie_set.join("|"),
            );
        }
        SegPinSummary::Unresolved {
            reason,
            drift,
            per_level_usable,
            ..
        } => {
            for (level, value) in drift {
                eprintln!("[seg-pin] drift level={level} value={value:.6}");
            }
            for (level, usable, total) in per_level_usable {
                eprintln!("[seg-pin] usable level={level} decision_cells={usable}/{total}");
            }
            eprintln!("[seg-pin] reason={reason}");
        }
    }
    // The REFUSED levels, on both paths: a level table that showed only the scored levels
    // would read as though the ineligible one had never been considered.
    let refused = match &summary {
        SegPinSummary::Resolved { refused, .. } | SegPinSummary::Unresolved { refused, .. } => {
            refused
        }
    };
    for (level, why) in refused {
        eprintln!("[seg-pin] level={level} outcome={why}");
    }
    eprintln!("[seg-pin] outcome={}", summary.outcome());
}

/// The COMPILED pin qualifier a level's runs must carry. `natural` and its repeat are
/// the same build knob, so both record `natural`; the two pinned levels record their
/// ceiling.
fn level_pin(level: &str) -> &str {
    match level {
        "natural-repeat" => "natural",
        other => other,
    }
}

/// **§4.5's δ3 attribution aggregator** — the flow that actually calls every helper in
/// this section, so none of them is decoration.
#[test]
#[ignore = "campaign aggregator; BWD_SEG_CONFIRM_DIRS names the runs"]
fn bwd_seg_aggregate_d3_attribution() {
    // The winner is read from the environment, NOT from the dirs spec: the whole point
    // is an INDEPENDENT reference the spec cannot satisfy by construction.
    let winner = std::env::var("BWD_SEG_WINNER_PIN")
        .expect("BWD_SEG_WINNER_PIN must carry the independently derived winning pin");
    let spec = std::env::var("BWD_SEG_CONFIRM_DIRS").expect("BWD_SEG_CONFIRM_DIRS");
    let expect_rolled = SegExpectedArm {
        run_label_prefix: "d3attr-rolled-",
        archive_sha256: std::env::var("BWD_SEG_ROLLED_ARCHIVE_SHA256").expect("rolled archive"),
        test_binary_sha256: std::env::var("BWD_SEG_ROLLED_TEST_BINARY_SHA256")
            .expect("rolled test binary"),
    };
    let expect_unrolled = SegExpectedArm {
        run_label_prefix: "d3attr-d3unroll-",
        archive_sha256: std::env::var("BWD_SEG_UNROLLED_ARCHIVE_SHA256").expect("unrolled archive"),
        test_binary_sha256: std::env::var("BWD_SEG_UNROLLED_TEST_BINARY_SHA256")
            .expect("unrolled test binary"),
    };
    let (rolled_dirs, unrolled_dirs) = split_d3_arms(&spec, &winner);
    let rolled = aggregate_arm(&rolled_dirs, &SEG_D3_ATTRIBUTION_CELLS);
    let unrolled = aggregate_arm(&unrolled_dirs, &SEG_D3_ATTRIBUTION_CELLS);
    // EVERY binding is checked BEFORE the directional call, because after it a swap is
    // indistinguishable from a real result.
    assert_d3_arm_identities(
        &winner,
        &rolled,
        &unrolled,
        &expect_rolled,
        &expect_unrolled,
    );
    let summary = summarize_d3_attribution(
        &[(winner.clone(), rolled.cells.clone())],
        &[("d3unroll".to_owned(), unrolled.cells)],
    );
    // Per cell, ALWAYS — the table IS the finding, on BOTH variants. Rendering only
    // the Scored case would make Task 10's "six per-cell lines" gate fail on exactly
    // the outcome the reader most needs to see.
    let render = |label: &str, r: Option<f64>, u: Option<f64>| {
        let f = |v: Option<f64>| v.map_or("-".to_owned(), |v| format!("{v:.6}"));
        let ratio = match (r, u) {
            (Some(r), Some(u)) => format!("{:.6}", u / r),
            _ => "-".to_owned(),
        };
        eprintln!(
            "[seg-d3] cell={label} rolled={} unrolled={} ratio={ratio}",
            f(r),
            f(u)
        );
    };
    match &summary {
        SegD3Attribution::Scored { cells, drift } => {
            for (label, r, u, ratio) in cells {
                eprintln!("[seg-d3] cell={label} rolled={r:.6} unrolled={u:.6} ratio={ratio:.6}");
            }
            eprintln!(
                "[seg-d3] control rolled={:.6} unrolled={:.6}",
                drift.0, drift.1
            );
        }
        SegD3Attribution::Unresolved { reason, cells } => {
            let control = SEG_D3_ATTRIBUTION_CELLS
                .iter()
                .find(|c| c.role == SegPinRole::DriftControl)
                .expect("one control");
            for (label, r, u) in cells {
                if label == control.label {
                    let f = |v: &Option<f64>| v.map_or("-".to_owned(), |v| format!("{v:.6}"));
                    eprintln!("[seg-d3] control rolled={} unrolled={}", f(r), f(u));
                } else {
                    render(label, *r, *u);
                }
            }
            eprintln!("[seg-d3] reason={reason}");
        }
    }
    // One machine-readable verdict, underscored like the R0 tokens so no outcome is a
    // substring of another.
    eprintln!(
        "[seg-d3] outcome={}",
        match &summary {
            SegD3Attribution::Scored { .. } => "SCORED",
            SegD3Attribution::Unresolved { .. } => "UNRESOLVED",
        }
    );
}

// ── Kernel attributes: the spec's register and spill gate, per instantiation ──

/// What the loaded module says about one instantiation.
///
/// Self-contained rather than borrowed from the cell-era harness: that module was
/// deleted with the cell executor, and this lineage's gate is a different one
/// anyway — `max_threads_per_block` has to admit `32 * k`, not a fixed 128-thread
/// block.
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

// ── The carveout plan's view of a pair (spec §3.2) ───────────────────────────

/// HOW the other arm of a paired cell is launched.
///
/// Two variants because the two kinds of baseline differ in WHEN they may be
/// staged, and that difference is the whole point of spec §3.2's ordering rule.
/// The incumbent compact evaluator is an opaque closure its caller staged long
/// before this cell existed and which stages nothing per cell, so it is safe to
/// carry as a callback. A segmented TWIN is a second shape of the SAME cell, and
/// `SegCell::prepare` launches the fold-weight prelude — so a twin prepared by the
/// caller would run that prelude at whatever preference the previous cell left
/// behind. Carrying the twin as a SHAPE rather than a prepared launchable is what
/// makes "the plan is applied before BOTH arms stage" structural instead of a
/// convention every caller has to remember.
pub(super) enum SegBaselineLaunch<'a> {
    /// A launch prepared outside this cell entirely (the incumbent compact
    /// evaluator). Staging is the caller's and happens once, not per cell.
    External(&'a dyn Fn(&ProverContext) -> CudaResult<()>),
    /// A second shape of the same [`SegCell`], prepared by `measure_shape` AFTER the
    /// plan is applied and BEFORE the candidate — the order the callers had.
    SegTwin(SegShape),
}

/// The other arm of a paired cell: its label, its launch, and its LAUNCH SHAPE.
///
/// The shape is explicit because the harness's baselines are heterogeneous — the
/// flat R0 incumbent (128 threads, zero dynamic smem, its own pinned occupancy) in
/// the R0 matrix, a segmented twin in the Stage-B ladder and in the corpus — and a
/// launch callback carries none of that. A plan that assumed "baseline == flat R0"
/// would configure a seg twin from the wrong demand and silently reintroduce
/// defect (a) on two of the three paired paths.
pub(super) struct SegBaselineArm<'a> {
    pub(super) label: &'static str,
    pub(super) launch: SegBaselineLaunch<'a>,
    pub(super) shape: CarveoutShape,
}

impl<'a> SegBaselineArm<'a> {
    /// The incumbent compact R0 evaluator, as an opaque callback.
    pub(super) fn incumbent(launch: &'a dyn Fn(&ProverContext) -> CudaResult<()>) -> Self {
        Self {
            label: INCUMBENT_R0_BASELINE_LABEL,
            launch: SegBaselineLaunch::External(launch),
            shape: incumbent_r0_carveout_shape(),
        }
    }

    /// A segmented twin of the same cell, named by `label` and staged inside
    /// `measure_shape`.
    pub(super) fn seg_twin(label: &'static str, regime: BwdRegime, shape: SegShape) -> Self {
        Self {
            label,
            launch: SegBaselineLaunch::SegTwin(shape),
            shape: seg_carveout_shape(regime, shape, "twin-baseline"),
        }
    }
}

/// The flat R0 incumbent's shape. [`PINNED_INCUMBENT_R0_BLOCKS_PER_SM`] is `i32`, so
/// the conversion is explicit rather than an implicit mismatch with
/// `CarveoutShape::target_blocks_per_sm`.
pub(super) fn incumbent_r0_carveout_shape() -> CarveoutShape {
    CarveoutShape {
        entry: incumbent_r0_kernel().as_ptr(),
        dynamic_smem_bytes: 0,
        target_blocks_per_sm: u32::try_from(PINNED_INCUMBENT_R0_BLOCKS_PER_SM)
            .expect("the pinned incumbent block count is positive"),
        label: "incumbent-flat-r0",
    }
}

/// A segmented shape's own carveout shape, from the attributes of the exact
/// executor it launches.
pub(super) fn seg_carveout_shape(
    regime: BwdRegime,
    shape: SegShape,
    label: &'static str,
) -> CarveoutShape {
    let attributes = shape_attributes(regime, shape);
    let k = u32::try_from(shape.k).expect("k fits u32");
    // `shape.acc` is an `Option<BwdSegAccPlacement>` — `None` is the fifteen release
    // symbols' register placement.
    let (entry, dynamic) = match shape.acc {
        Some(placement) => (
            bwd_seg_acc_entry_point(regime, placement),
            bwd_seg_acc_dynamic_smem_bytes(placement, k),
        ),
        None => (
            bwd_seg_entry_point(regime, shape.program, shape.coeff, shape.epilogue),
            bwd_seg_epilogue_smem_bytes(shape.epilogue, k),
        ),
    };
    CarveoutShape {
        entry,
        dynamic_smem_bytes: dynamic,
        target_blocks_per_sm: bwd_seg_register_bound_blocks_per_sm(
            u32::try_from(attributes.registers).expect("a positive register count"),
            k,
        ),
        label,
    }
}

/// §7.1.0 / §7.2.1's mode selector.
///
/// **No mode here is §7.2.1's primary column: that column is UNPOPULATED pending RR.** The
/// default is `fixed-bucket`, which is a default and nothing more — it was reached by
/// elimination (`common-bucket` failed the forced-convergence probe at the R0 headline cell,
/// and so did `fixed-bucket` at 64 KiB), not by a standing decision that it defines the
/// gate. Every mode's status is recorded in [`CarveoutMode`]; the measured convergence
/// results live in the campaign record.
///
/// The BUCKET is constrained, not free: the bare form binds to
/// [`SEG_REFERENCE_CLOCK_BUCKET_BYTES`] and `fixed-bucket:<bytes>` must name a documented
/// partition — see [`parse_carveout_mode`].
pub(super) fn carveout_mode() -> CarveoutMode {
    parse_carveout_mode(
        std::env::var("BWD_SEG_CARVEOUT")
            .unwrap_or_else(|_| "fixed-bucket".to_owned())
            .trim(),
    )
}

/// The mode grammar, separated from the environment so a CPU test can drive the parse and
/// the bucket validation without a device and without mutating a process-global variable.
///
/// **`fixed-bucket[:<bytes>]`.** Bare `fixed-bucket` keeps its meaning —
/// [`SEG_REFERENCE_CLOCK_BUCKET_BYTES`], the reference clock's predeclared partition — so no
/// existing caller changes. The explicit form exists because the R0 headline's forced pairs
/// were measured non-convergent at BOTH 32 KiB and 64 KiB, and the diagnostic that follows
/// from the floor law needs the pool maximum: `realized = max(driver heuristic, bucket)`, so
/// the one value the driver cannot exceed is the pool itself. Without this form that
/// diagnostic is unmeasurable, and "unmeasurable" was being recorded as a finding about the
/// device when it was a finding about the harness.
///
/// **The byte count is validated against [`BWD_SEG_SMEM_BUCKETS_BYTES`], the documented
/// device partition set**, whose largest member IS this part's pool. A request between
/// buckets would be silently rounded up by the driver and the emitted `carveout_mode` label
/// would then name a partition nothing realized — the exact confusion the realized-field
/// rule exists to prevent. `0` is refused separately: a zero partition cannot hold any
/// paired demand, so it would fail `CarveoutPlan::for_pair`'s containment assert with a
/// message about demand rather than about the nonsense value that caused it.
fn parse_carveout_mode(spec: &str) -> CarveoutMode {
    if let Some(bytes) = spec.strip_prefix("fixed-bucket:") {
        let bytes: usize = bytes.trim().parse().unwrap_or_else(|error| {
            panic!(
                "BWD_SEG_CARVEOUT=fixed-bucket:<bytes> needs a byte count, got {bytes:?}: {error}"
            )
        });
        assert!(
            bytes != 0,
            "a fixed bucket of 0 B holds no paired demand; name a real partition from {:?}",
            BWD_SEG_SMEM_BUCKETS_BYTES
        );
        assert!(
            BWD_SEG_SMEM_BUCKETS_BYTES.contains(&bytes),
            "fixed-bucket:{bytes} is not a supported realized partition on this part. The \
             device set is {:?} (its largest member is the SM pool). A value between buckets \
             would be rounded up by the driver and the emitted label would name a partition \
             nothing realized.",
            BWD_SEG_SMEM_BUCKETS_BYTES
        );
        return CarveoutMode::FixedBucket(bytes);
    }
    match spec {
        "off" => CarveoutMode::Off,
        "common-bucket" => CarveoutMode::CommonBucket,
        "as-configured" => CarveoutMode::AsConfigured,
        "fixed-bucket" => CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES),
        other => panic!(
            "BWD_SEG_CARVEOUT must be `off`, `common-bucket`, `as-configured`, \
             `fixed-bucket` or `fixed-bucket:<bytes>`, got {other:?}"
        ),
    }
}

/// **The generated carveout demand table (spec §3.1).** One row per REAL
/// `{symbol, pin, K, epilogue, placement}` tuple, from the helper's own formula.
/// No GPU timing — it queries device attributes and computes.
///
/// **No impossible rows.** The pin is a property of the SYMBOL, not a free axis:
/// `cont_const_*` are natural-50 and `cont_ptr_*` / `cont_const_progptr_*` are
/// natural-56, the R0 `plane`/`wide` are 40 and the R0 `staged` 44/48. Emitting
/// "generic cont at both 50 and 56" or "R0-plane/wide with a `staged` epilogue"
/// would publish tuples no build produces. `{staged, any K}` is deliberately NOT a
/// class either: its dynamic bytes are `K`-independent but its block count is not.
#[test]
#[ignore = "GPU device query; run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_carveout_demand_table() {
    use super::seg::{
        bwd_seg_carveout_pct, bwd_seg_expected_smem_bucket_bytes, bwd_seg_max_blocks_per_sm,
        bwd_seg_reserved_smem_bytes_per_block,
    };
    const UNIFIED_ARRAY_BYTES: usize = 128 * 1024;
    const DRIVER_BASELINE_L1_BYTES: usize = 64 * 1024;
    let reserve = bwd_seg_reserved_smem_bytes_per_block();
    // `#` comment lines are this pass's established artifact convention (Task 2's
    // frozen-cells TSV carries its `# campaign =` tag the same way), and the
    // residency rule has to be stated where the table is read: `blocks_per_sm` is the
    // REGISTER-BOUND count for every executor and rung row, but a launch whose grid
    // cannot fill an SM is capped by its GRID, and reserving shared memory for blocks
    // that can never coexist would overstate its demand.
    let mut out = String::from(
        "# blocks_per_sm is register-bound, EXCEPT where the launch geometry caps it: \
the build_fold_weights prelude is a grid-1 launch, so its row is 1 block.\n\
# THE BUCKET COLUMNS ARE A DEMAND QUANTIZATION, NOT A REALIZED PARTITION. The requested \
percentage is a FLOOR: realized = max(driver heuristic, bucket) (measured this pass). So \
any row whose demand bucket is below 65,536 B can be raised by the driver, and \
floor_override_risk says which. MEASURED counterexample: both 2,560 B/block rows \
(r0_const_epi_plane K=4 and cont_const_epi_plane pin 50 K=4) predict a 32,768 B bucket \
and +50.00% reclaim, and both REALIZE 65,536 B under ncu -- i.e. 0% reclaim against the \
64 KiB driver baseline. Read reclaim_if_demand_realized_pct as conditional on its own \
name; the gate is always the realized launch__shared_mem_config_size (spec 3.4).\n\
symbol,regime,loader,program,epilogue,placement,pin,pin_kind,k,dynamic_bytes,\
per_block_bytes,blocks_per_sm,sm_demand_bytes,requested_pct,demand_bucket_bytes,\
demand_l1_bytes,reclaim_if_demand_realized_pct,floor_override_risk\n",
    );
    let mut rows = 0usize;
    #[allow(clippy::too_many_arguments)]
    let mut push = |symbol: &str,
                    regime: &str,
                    loader: &str,
                    program: &str,
                    epi: &str,
                    placement: &str,
                    pin: u32,
                    pin_kind: &str,
                    k: u32,
                    dynamic: usize,
                    // `Some(n)` when the GRID, not the register allocation, is what
                    // bounds residency. The prelude is the only such launch.
                    grid_capped_blocks: Option<u32>| {
        let blocks =
            grid_capped_blocks.unwrap_or_else(|| bwd_seg_register_bound_blocks_per_sm(pin, k));
        let per_block = dynamic + reserve;
        let demand = blocks as usize * per_block;
        let bucket = bwd_seg_expected_smem_bucket_bytes(demand);
        let l1 = UNIFIED_ARRAY_BYTES - bucket;
        // **The floor law, made a COLUMN rather than a caveat.** `realized = max(driver
        // heuristic, bucket)`, so a demand that quantizes below the one bucket the driver
        // can never raise is a PREDICTION the driver may override upward — and when it
        // does, the reclaim on this row is not the number two fields to the left. The two
        // K=4 rows are the measured case: predicted 32,768 B, realized 65,536 B, so their
        // predicted +50.00% reclaim was actually 0%. Emitting the risk per row is what
        // stops the arithmetic being read as an observation.
        let floor_override_risk = if bucket < SEG_REFERENCE_CLOCK_BUCKET_BYTES {
            "yes"
        } else {
            "no"
        };
        writeln!(
            out,
            "{symbol},{regime},{loader},{program},{epi},{placement},{pin},{pin_kind},{k},\
             {dynamic},{per_block},{blocks},{demand},{},{bucket},{l1},{:+.2},\
             {floor_override_risk}",
            bwd_seg_carveout_pct(blocks, dynamic),
            (l1 as f64 / DRIVER_BASELINE_L1_BYTES as f64 - 1.0) * 100.0,
        )
        .expect("write String");
        rows += 1;
    };
    let epilogues = [
        (BwdSegEpilogue::Staged, "staged"),
        (BwdSegEpilogue::Plane, "plane"),
        (BwdSegEpilogue::Wide, "wide"),
    ];
    for k in STAGE_A_K.iter().map(|k| *k as u32) {
        for (epi, epi_label) in epilogues {
            let dynamic = bwd_seg_epilogue_smem_bytes(epi, k);
            // The SIX R0 executors, at the pin §4.3 gives each: 40 for
            // `plane`/`wide` (band 33-40, their current allocation), 48 for
            // `staged` (band top of 41-48, whose current allocation is 44).
            for loader in ["const", "ptr"] {
                let (pin, kind) = match epi {
                    BwdSegEpilogue::Staged => (48u32, "permanent-band-top"),
                    _ => (40u32, "permanent-band-top"),
                };
                push(
                    &format!("r0_{loader}_epi_{epi_label}"),
                    "r0",
                    loader,
                    "inline",
                    epi_label,
                    "registers",
                    pin,
                    kind,
                    k,
                    dynamic,
                    None,
                );
            }
            // The NINE swept continuation executors. Their NATURAL pin differs by
            // loader — `cont_const_*` allocate 50, `cont_ptr_*` and
            // `cont_const_progptr_*` allocate 56 — so `natural` is one row per
            // symbol, not two rows per class.
            for (loader, program, natural) in [
                ("const", "inline", 50u32),
                ("ptr", "inline", 56),
                ("const", "progptr", 56),
            ] {
                let symbol = if program == "progptr" {
                    format!("cont_{loader}_progptr_epi_{epi_label}")
                } else {
                    format!("cont_{loader}_epi_{epi_label}")
                };
                push(
                    &symbol,
                    "cont",
                    loader,
                    program,
                    epi_label,
                    "registers",
                    natural,
                    "swept-natural",
                    k,
                    dynamic,
                    None,
                );
                for pin in [48u32, 40] {
                    push(
                        &symbol,
                        "cont",
                        loader,
                        program,
                        epi_label,
                        "registers",
                        pin,
                        "swept",
                        k,
                        dynamic,
                        None,
                    );
                }
            }
        }
        // The FOUR acc rungs, at the pin §4.3 gives each. They exist only on the
        // `plane` epilogue with the `const` loader (BWD_SEG_ACC_RUNG_EPILOGUE), so
        // no other epilogue row is emitted for them.
        for (placement, label) in [
            (BwdSegAccPlacement::AccC2Smem, "acc2smem"),
            (BwdSegAccPlacement::AccBothSmem, "accbothsmem"),
        ] {
            let dynamic = bwd_seg_acc_dynamic_smem_bytes(placement, k);
            push(
                &format!("r0_const_epi_plane_{label}"),
                "r0",
                "const",
                "inline",
                "plane",
                label,
                48,
                "permanent-band-top",
                k,
                dynamic,
                None,
            );
            let (cont_pin, kind) = match placement {
                BwdSegAccPlacement::AccC2Smem => (56u32, "permanent-band-top"),
                BwdSegAccPlacement::AccBothSmem => (64u32, "permanent-launch-ceiling"),
            };
            push(
                &format!("cont_const_epi_plane_{label}"),
                "cont",
                "const",
                "inline",
                "plane",
                label,
                cont_pin,
                kind,
                k,
                dynamic,
                None,
            );
        }
    }
    // The prelude: grid 1, block 32, zero dynamic smem, a CONSTANT 0%, no pin.
    push(
        "build_fold_weights",
        "any",
        "none",
        "none",
        "none",
        "none",
        27,
        "exempt",
        1,
        0,
        // A grid-1 launch: ONE block on one SM for the whole device, so its row must
        // not claim the 24-block register-bound occupancy the formula would give it.
        Some(1),
    );
    let path = std::env::var("BWD_SEG_DEMAND_TABLE_OUT").map_or_else(
        |_| seg_output_path("seg_carveout_demand_table.csv"),
        PathBuf::from,
    );
    publish(&path, &out);
    // `l2=` is emitted HERE, pre-freeze, because Task 11's floor banding needs the
    // device attribute (`cudaDevAttrL2CacheSize`) as its authority and Task 11 is
    // data-only — it may not add a source edit to produce it.
    eprintln!(
        "[seg-carveout] reserve={reserve} B pool={} B block_cap={} l2={} rows={rows} -> {}",
        crate::primitives::utils::smem_pool_bytes_per_sm(),
        bwd_seg_max_blocks_per_sm(),
        super::seg::bwd_seg_l2_capacity_bytes(),
        path.display(),
    );
    // 7 K values x (6 R0 + 9 cont x 3 pins + 4 rungs) + 1 prelude.
    assert_eq!(rows, 7 * (6 + 27 + 4) + 1, "the enumeration must be exact");
    // Sanity against spec §3.1's own numbers. A different part is fine — the
    // arithmetic is queried — but it must be RECORDED as different, not silently
    // absorbed.
    assert_eq!(
        reserve, 1_024,
        "expected 1,024 B on this part; record the deviation"
    );
    assert_eq!(bwd_seg_max_blocks_per_sm(), 24, "expected 24 on this part");
}

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
    /// The paired estimate WITH its order gate fused in — never a bare
    /// [`RatioEstimate`], so an order-coupled cell has no ratio any consumer could
    /// read by forgetting to check a label (spec §6(a) step 6).
    pub(super) ratio: SegRatio,
    /// The RUN this row's paired numbers came from, or `"-"` for a solo row.
    ///
    /// The published CSV is a DERIVED table at a fixed path; the record of authority
    /// is the run directory's raw TSV. Carrying the run id in the row is what lets a
    /// quoted `median_ratio` be joined back to `seg_raw_samples.tsv` — and from there
    /// to the archive and test-binary SHA-256s — without guessing which process wrote
    /// the file (§7.3 criterion 4c). Solo rows carry no run identity because they emit
    /// no raw samples.
    pub(super) run_id: &'static str,
    /// WHAT the ratio is against, or `"-"` when the cell was timed solo.
    ///
    /// The ratio column carries two different comparisons — the R0 matrix pairs
    /// against the incumbent compact evaluator, Stage B pairs each rung against its
    /// own register-placement twin — and a reader cannot tell them apart from the
    /// number. Naming the baseline in the row is what keeps them distinguishable in
    /// the CSV and in every generated table.
    pub(super) baseline: &'static str,
    /// The lowering's per-launch compulsory-traffic floor (spec §7.2.2). A property of
    /// the LOWERING, so it is emitted for cells that never launched too — see
    /// [`SEG_CSV_HEADER`] for the zero convention.
    pub(super) floor: BwdSegTrafficFloor,
    /// How the cell's shared-memory carveout was configured (spec §3), or `"-"` when
    /// nothing was configured because the cell could not launch.
    pub(super) carveout_mode: &'static str,
    /// The percentage REQUESTED for the candidate's entry point. `None` in `off` mode
    /// and on an unlaunchable cell. It is a hint, never the gate — the gate is the
    /// realized `launch__shared_mem_config_size` (spec §3.4).
    pub(super) carveout_requested_pct: Option<i32>,
    /// WHICH arm's demand the request came from, and — when the two arms quantize to
    /// different buckets — the asymmetry statement that must travel with the number.
    pub(super) carveout_source: String,
    /// What this row is FOR in the §4.5 pin decision (and in the δ3 attribution, which
    /// reuses the roles). [`SegPinRole::Decision`] for every other caller, none of
    /// which reads it: the aggregators separate the two roles from the emitted column
    /// rather than re-deriving them from the label.
    pub(super) pin_role: SegPinRole,
    /// WHAT the two arms are to each other, which decides whether §6(b)'s inversion
    /// vocabulary applies to this row.
    ///
    /// **Keyed on the CAMPAIGN, never on the carveout mode.** It used to be inferred
    /// from `carveout_mode == "fixed-bucket"`, which was sound only while
    /// [`CarveoutMode::FixedBucket`] was reachable from the pin and δ3 runners alone. Once
    /// the R0 headline began timing candidate-vs-incumbent pairs at a fixed bucket too, a
    /// mode-keyed rule would have stamped `reference-clock` on the headline itself and erased
    /// the very verdict an acceptance gate reads. The headline runs at a fixed bucket
    /// regardless of which one §7.2.1 ends up designating, so the distinction has to come
    /// from the campaign and not from the configuration.
    pub(super) pairing: SegPairing,
}

/// The relationship between a paired row's two arms (see [`SegMatrixRow::pairing`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegPairing {
    /// The candidate against the evaluator it means to replace. §6(b)'s three-outcome
    /// rule applies and `verdict` carries its vocabulary. Every R0 headline row,
    /// including the R0 headline at any fixed bucket, and every Stage-B / corpus row.
    CandidateVsIncumbent,
    /// The candidate against a launch used only as a CLOCK — §4.5 mechanism 3's
    /// cross-build anchor. Applying §6(b)'s rule to a cross-build ratio is a category
    /// error, so `verdict` must not spell `INVERTED` here.
    ReferenceClock,
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
        if matches!(self.ratio, SegRatio::Solo) {
            "solo"
        } else {
            "paired"
        }
    }
}

/// The paired columns describe the PROTOCOL that produced them: `candidate_median_us`
/// is the median of the block candidate means, the ratio columns come from the
/// joint-stratified bootstrap, and the four `delta_order_*` / `order_gate` columns plus
/// the four order-conditional medians are emitted for EVERY paired row — that is how an
/// order-coupled cell stays visible while its pooled ratio columns render `-`.
///
/// **`floor_dram_read_bytes` / `floor_dram_write_bytes` are LOWERING properties, not
/// measurements** (spec §7.2.2), so they are emitted on every row including rows whose
/// cell never launched. **ZERO in both is reserved for "no lowering output"** — the
/// lowering was rejected, or was never attempted — and is distinguishable from a real
/// floor, which is always positive because the eq term alone is nonzero for any live
/// launch. That also keeps the v1/v2/v3 schema-tolerance default consistent: an absent
/// column, a rejected row and an over-budget row all read the same way, which is
/// correct, because none of them carries a measurement.
pub(super) const SEG_CSV_HEADER: &str = "benchmark,circuit,layer,regime,round,rows,saturated,k,\
epilogue,coeff,program,acc_placement,d2_policy,launchable,blocks_per_sm,theoretical_occupancy_percent,registers,\
local_spill_bytes,static_smem_bytes,max_threads_per_block,dynamic_smem_bytes,grid_blocks,waves,\
max_over_mean_work,parity,protocol,ratio_baseline,candidate_median_us,candidate_min_us,\
baseline_median_us,baseline_min_us,median_ratio,ci_low,ci_high,verdict,delta_order_pct,\
delta_order_ci_low,delta_order_ci_high,order_gate,abba_candidate_us,abba_incumbent_us,\
baab_candidate_us,baab_incumbent_us,run_id,carveout_mode,carveout_requested_pct,\
carveout_source,pin_role,floor_dram_read_bytes,floor_dram_write_bytes\n";

pub(super) fn render_matrix_csv(rows: &[SegMatrixRow]) -> String {
    let mut out = String::from(SEG_CSV_HEADER);
    for row in rows {
        // `-`, not a number, when no pooled estimate exists: a solo cell never had
        // one, and an order-coupled cell may not quote one (§6(a) step 6).
        let (ratio, low, high) = match row.ratio.reported_estimate() {
            Some(estimate) => (
                format!("{:.6}", estimate.median_ratio),
                format!("{:.6}", estimate.ci_low),
                format!("{:.6}", estimate.ci_high),
            ),
            None => ("-".to_owned(), "-".to_owned(), "-".to_owned()),
        };
        // **A REFERENCE-CLOCK pairing has no inversion question**, so the
        // machine-readable verdict field must not carry §6(b)'s vocabulary: §4.5 calls
        // applying §6(b)'s rule to a cross-build ratio a category error, and
        // `INVERTED` in a frozen artifact is exactly that error in the field a
        // consumer parses.
        //
        // **Keyed on the PAIRING, not on the carveout mode.** The mode-keyed form
        // (`carveout_mode == FixedBucket(0).label()`) was correct only while
        // `FixedBucket` belonged to the pin and δ3 runners alone. The R0 headline now puts
        // §7.2.1's primary column at the same bucket with candidate-vs-incumbent arms,
        // so that form would now stamp `reference-clock` over the headline's own
        // verdict — the acceptance gate would read a row that had been told it has no
        // inversion question. See `SegMatrixRow::pairing`.
        let verdict = match row.pairing {
            SegPairing::ReferenceClock => "reference-clock",
            SegPairing::CandidateVsIncumbent => row.ratio.verdict(),
        };
        let (delta, delta_low, delta_high, gate) = match row.ratio.order() {
            Some(order) => (
                format!("{:.4}", order.delta_order_pct),
                format!("{:.4}", order.ci_low_pct),
                format!("{:.4}", order.ci_high_pct),
                order.passes().to_string(),
            ),
            None => (
                "-".to_owned(),
                "-".to_owned(),
                "-".to_owned(),
                "-".to_owned(),
            ),
        };
        let conditional = match row.ratio.conditional_medians() {
            Some([abba_candidate, abba_incumbent, baab_candidate, baab_incumbent]) => format!(
                "{abba_candidate:.3},{abba_incumbent:.3},{baab_candidate:.3},{baab_incumbent:.3}"
            ),
            None => "-,-,-,-".to_owned(),
        };
        // The demand source is prose and CONTAINS commas (`"{winner}, {demand} B …"`);
        // this renderer emits unquoted fields, so the separator is neutralized rather
        // than the sentence truncated.
        let carveout_source = row.carveout_source.replace(',', ";");
        writeln!(
            out,
            "{},{},{},{:?},{},{},{},{},{},{},{},{},{},{},{},{:.2},{},{},{},{},{},{},{:.3},{:.4},\
             {},{},{},{:.3},{:.3},{:.3},{:.3},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
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
            delta,
            delta_low,
            delta_high,
            gate,
            conditional,
            row.run_id,
            row.carveout_mode,
            row.carveout_requested_pct
                .map_or_else(|| "-".to_owned(), |pct| pct.to_string()),
            carveout_source,
            row.pin_role.label(),
            row.floor.read_bytes,
            row.floor.write_bytes,
        )
        .expect("write String");
    }
    out
}

// The bound itself is `seg_lower.rs`'s; the BANDING of it is the report's.
use super::seg_lower::bwd_seg_floor_soft_bound;

/// How `realized` reads against a direction's floor (spec §7.2.2).
///
/// | realized vs bound | reading |
/// |---|---|
/// | `realized < soft_bound` | **Bug gate.** Even if L2 absorbed an entire cache's
/// |   worth of this direction's traffic, this much could not have been avoided.
/// |   The floor walk is wrong — a wrong span, a missed dedupe, a virtual source
/// |   counted as DRAM-backed, or the eq term at the old log2 error. A defect to
/// |   FIX, not a result to publish. |
/// | `soft_bound <= realized < floor` | **Cache retention, reported as a finding.**
/// |   Expected at small working sets and in the deep rounds, where the publish set
/// |   is `num_foldable * 2 * rows * 16 B` and rows halve every round. Not a
/// |   failure and not asserted against. |
/// | `realized >= floor` | The ordinary case; `realized / floor` is the
/// |   caching-effectiveness number. |
pub(super) fn seg_floor_band(realized: u64, floor: u64, l2: u64) -> &'static str {
    if realized < bwd_seg_floor_soft_bound(floor, l2) {
        "BUG-GATE"
    } else if realized < floor {
        "cache-retention"
    } else {
        "ordinary"
    }
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

/// Whether a selection may READ this row's timing at all (spec §6(a) step 6).
///
/// A SOLO row stays eligible: it never had an order contrast to fail. A PAIRED row is
/// eligible only through [`SegRatio::selectable`], which is `None` exactly when the
/// order gate failed — and a winner IS a headline, which §6(a) step 6 forbids
/// asserting for an order-coupled cell.
pub(super) fn is_selectable_row(row: &SegMatrixRow) -> bool {
    row.ratio.order().is_none() || row.ratio.selectable().is_some()
}

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
        .filter(|row| {
            row.launchable() && is_production_loader(&row.shape) && is_selectable_row(row)
        })
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
        .filter(|row| {
            row.launchable() && is_production_loader(&row.shape) && is_selectable_row(row)
        })
        .map(|row| row.candidate_median_us)
        .fold(f64::MAX, f64::min);
    let threshold = best * (1.0 + SEG_SELECTION_TIE_FRACTION);
    let _ = winner;
    rows.iter()
        .filter(|row| {
            row.launchable()
                && is_production_loader(&row.shape)
                && is_selectable_row(row)
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
         median (us) | ratio | 95% CI | verdict | order delta % |\n\
         |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for row in rows {
        if !row.launchable() {
            writeln!(
                body,
                "| {} | {} | {} | {} | {} | {} | {} | 0 | - | {} | UNLAUNCHABLE | - | - | - | - |",
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
        let (ratio, ci, verdict) = match row.ratio.reported_estimate() {
            Some(estimate) => (
                format!("{:.4}", estimate.median_ratio),
                format!("[{:.4}, {:.4}]", estimate.ci_low, estimate.ci_high),
                format!("{} vs {}", estimate.verdict(), row.baseline),
            ),
            // A solo cell has no baseline sampled beside it, so it gets no ratio and
            // no interval — printing either would invent a comparison the protocol
            // did not make.
            None if row.ratio.order().is_none() => {
                ("solo".to_owned(), "solo".to_owned(), "solo".to_owned())
            }
            // Paired, but order-coupled: the diagnostics print, the pooled ratio does
            // not exist to print (§6(a) step 6).
            None => (
                "-".to_owned(),
                "-".to_owned(),
                format!("{} vs {}", row.ratio.verdict(), row.baseline),
            ),
        };
        let order = match row.ratio.order() {
            Some(order) => format!(
                "{:+.3} [{:+.3}, {:+.3}] {}",
                order.delta_order_pct,
                order.ci_low_pct,
                order.ci_high_pct,
                if order.passes() { "pass" } else { "FAIL" },
            ),
            None => "-".to_owned(),
        };
        writeln!(
            body,
            "| {} | {} | {} | {} | {} | {} | {} | {} | {:.1} | {} | {:.3} | {ratio} | {ci} | \
             {verdict} | {order} |",
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
            &self.coord,
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
        // The prelude is continuation-only — round 0 has no challenges to fold — and
        // it must be enqueued AFTER the claim point it reads, on the same stream.
        // Staging, so outside every timed region by construction.
        if self.model.round >= 1 {
            launch_bwd_seg_build_fold_weights(u32::from(self.model.round), context)
                .expect("fold-weight prelude");
        }
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

/// **The headline benchmark.** `add_sub` layer-0 R0, the whole Stage-A matrix, paired
/// against the REAL incumbent compact evaluator in one process, one context, one
/// row count, one eq state and one contribution buffer.
///
/// It is one PROCESS of the §6(b) campaign, not a gate on its own: with no freeze set it
/// is discovery, with the `r0-headline` freeze set it is one of three confirmation
/// processes, and the verdict is [`bwd_seg_aggregate_r0_headline`]'s over all three.
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
    // **THERE IS NO PER-RUN INVERSION ASSERTION HERE, deliberately.** The acceptance
    // gate for this benchmark is the CAMPAIGN-level three-outcome verdict on §7.2.1's
    // primary column — `bwd_seg_aggregate_r0_headline` over three frozen confirmation
    // runs — and nothing else. A per-process `select_winner(..).ratio.inverts()` aborted
    // the process on a NOT-INVERTED or UNRESOLVED run, including on the secondary
    // column where non-inversion is a legitimate finding, so the three-outcome
    // aggregator would never have seen the runs it exists to classify. It could not be
    // gated either: gating on "a freeze exists" leaves it live during DISCOVERY, which
    // is exactly where a non-inverting result must be allowed, and gating on "no
    // `BWD_SEG_REQUIRE_PROVENANCE`" reserves it for a bare local run that can no longer
    // happen — `record_raw_samples` requires the reserved directory `seg_env` creates
    // and `seg_env` always sets that variable, so the guard's true branch is
    // unreachable. Anyone running this cell by hand calls `seg_env <label> <pin_level>`
    // first, exactly as every campaign process does.
}

/// **The live-path integration gate for Task 0.** Runs ONE small paired cell
/// through the migrated `measure_shape` and proves the protocol is actually in
/// use end to end: 16 blocks x 4 samples were emitted with their labels, the
/// order gate was computed, and re-deriving the interval from the emitted file
/// reproduces the in-process one bit for bit. A green unit suite with this test
/// absent would not distinguish "the protocol exists" from "the protocol runs".
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_protocol_emits_a_reconstructable_record() {
    let rows = run_r0_matrix(None);
    // `ratio` is a `SegRatio`, not an `Option`: a paired row is any non-`Solo`
    // variant, and an order-coupled one has diagnostics but no pooled estimate.
    let paired: Vec<&SegMatrixRow> = rows
        .iter()
        .filter(|row| !matches!(row.ratio, SegRatio::Solo))
        .collect();
    assert!(!paired.is_empty(), "the R0 matrix must produce paired rows");
    let meta = SegRunMeta::current();
    // The RESERVED directory, from the environment — not a path derived from the id.
    let path = PathBuf::from(std::env::var("BWD_SEG_RUN_DIR").expect("BWD_SEG_RUN_DIR"))
        .join(SEG_RAW_SAMPLES_TSV);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("the migrated path must emit raw samples: {error}"));
    let (back_meta, emitted) = parse_raw_samples_tsv(&text);
    assert_eq!(&back_meta, meta);
    let mut by_cell: std::collections::BTreeMap<String, Vec<SegBlockSample>> = Default::default();
    for (cell, block) in emitted {
        by_cell.entry(cell).or_default().push(block);
    }
    assert_eq!(
        by_cell.len(),
        paired.len(),
        "every paired cell emits exactly one raw-sample group"
    );
    for (cell, blocks) in &by_cell {
        assert_eq!(blocks.len(), SEG_TIMED_BLOCKS, "{cell}: 16 blocks");
        let samples = SegBlockedSamples {
            schedule: seg_schedule(back_meta.seed),
            blocks: blocks.clone(),
        };
        assert_eq!(samples.stratum_census(), [3, 5, 3, 5], "{cell}");
        let row = paired
            .iter()
            .find(|row| format!("{}|{}", row.benchmark, row.shape.label()) == *cell)
            .unwrap_or_else(|| panic!("{cell} has no matrix row"));
        // The order contrast exists for every paired cell.
        let recorded_order = row
            .ratio
            .order()
            .expect("a paired row has an order contrast");
        let rebuilt_order = samples.order_interaction();
        assert_eq!(
            recorded_order.ci_low_pct, rebuilt_order.ci_low_pct,
            "{cell}: the order CI must reconstruct"
        );
        // The pooled estimate exists IF AND ONLY IF the gate passed — and when it
        // does, it reconstructs bit for bit from the emitted rows.
        match row.ratio.reported_estimate() {
            Some(recorded) => {
                assert!(
                    rebuilt_order.passes(),
                    "{cell}: a Valid ratio implies a passing gate"
                );
                let estimate = samples.estimate_stratified();
                assert_eq!(estimate.ci_low, recorded.ci_low, "{cell}: CI low");
                assert_eq!(estimate.ci_high, recorded.ci_high, "{cell}: CI high");
            }
            None => {
                assert!(
                    !rebuilt_order.passes(),
                    "{cell}: no estimate implies a failed gate"
                );
                assert!(
                    row.ratio.conditional_medians().is_some(),
                    "{cell}: an order-coupled cell publishes its conditional medians"
                );
            }
        }
    }
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
/// The REAL incumbent plan, its staged coefficient bank, the shared eq and the fitted
/// candidate row count — the only path in this harness that produces them.
///
/// Extracted from [`run_r0_matrix`] so §4.5's pin decision can pair against the SAME
/// real incumbent launch §6(b)'s headline does, inside ONE context: a reference clock
/// is only a reference if every campaign's denominator is the same launch, and the
/// plan-and-bank walk is sixty lines of fixture traversal that cannot be duplicated
/// honestly.
///
/// **Field order is DROP order.** `eq_low`, the plan's round scratch and the layer state
/// are all pool-backed by `context`, so the context is declared LAST and therefore
/// dropped last.
struct SegR0Fixture {
    host_eq: HostEq,
    device: SegDeviceFacts,
    coord: Arc<SegCoordinate>,
    /// The candidate row count fitted to this coordinate, and whether it reached the
    /// incumbent's own.
    rows: usize,
    saturated: bool,
    incumbent_rows: usize,
    /// The incumbent plan's accumulator — both lineages write the same bytes.
    output_ptr: *mut E4,
    eq_low: DeviceAllocation<E4>,
    eq_sizes: EqSizes,
    plan: crate::prover::gkr::backward::GpuGKRMainLayerSumcheckLayerPlan<E4>,
    /// A KEEPALIVE: the plan's scratch is owned by this state, so it must outlive the
    /// plan and be dropped before the context. Never read.
    _main_state: crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
    context: ProverContext,
}

impl SegR0Fixture {
    /// The incumbent launch every paired R0 cell — and every pin-decision reference
    /// clock — is timed against.
    fn incumbent_launch(&self, context: &ProverContext) -> CudaResult<()> {
        use crate::prover::gkr::backward::compact;
        compact::launch_main_round0_constant::<E4>(
            &self
                .plan
                .flat_round0_template_compact
                .as_ref()
                .expect("incumbent round-0 descriptor")
                .static_desc,
            self.eq_low.as_ptr(),
            &self.eq_sizes,
            self.output_ptr,
            self.rows as u32,
            context,
        )
    }
}

#[allow(clippy::too_many_lines)]
fn seg_r0_fixture() -> SegR0Fixture {
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

    // The bank is staged and the descriptor validated; the fixture can now hand out its
    // launch. `staged` is dropped at the end of this function, which is safe because the
    // correctness launch and its D2H below SYNCHRONIZE the stream the copy was enqueued
    // on.
    let built = SegR0Fixture {
        host_eq,
        device,
        coord,
        rows,
        saturated,
        incumbent_rows,
        output_ptr,
        eq_low,
        eq_sizes,
        plan,
        _main_state: main_state,
        context,
    };
    let preflight = super::seg_compile::seg_ext(0x00a1, 0, 0);
    poison_contributions(output_ptr, rows, preflight, &built.context)
        .expect("poison the incumbent preflight");
    built
        .incumbent_launch(&built.context)
        .expect("incumbent correctness launch");
    let sample = SEG_IDENTITY_SAMPLE_ROWS.min(rows);
    let incumbent_output = download_e4(output_ptr, sample, &built.context);
    assert!(
        incumbent_output
            .iter()
            .any(|value| e4_bits(*value) != e4_bits(preflight)),
        "the incumbent round-0 launch left every sampled contribution poisoned"
    );
    built
}

#[allow(clippy::too_many_lines)]
fn run_r0_matrix(profile: Option<SegShape>) -> Vec<SegMatrixRow> {
    let fixture = seg_r0_fixture();
    let context = &fixture.context;
    let incumbent_launch = |ctx: &ProverContext| fixture.incumbent_launch(ctx);
    let (rows, saturated, incumbent_rows) =
        (fixture.rows, fixture.saturated, fixture.incumbent_rows);
    let (host_eq, device) = (&fixture.host_eq, &fixture.device);

    // ── the candidate's parity twin and timed cell ───────────────────────
    let parity = SegCell::build(
        Arc::clone(&fixture.coord),
        0,
        SEG_PARITY_ROWS,
        true,
        D2Policy::Inline,
        fixture.eq_low.as_ptr(),
        fixture.eq_sizes,
        context,
    );
    let timed = SegCell::build_into(
        Arc::clone(&fixture.coord),
        0,
        rows,
        saturated,
        D2Policy::Inline,
        fixture.eq_low.as_ptr(),
        fixture.eq_sizes,
        fixture.output_ptr,
        context,
    );

    // **DISCOVERY or CONFIRMATION, chosen by the freeze** (spec §6(b)). Absent
    // `BWD_SEG_FROZEN_CELLS` this is discovery and the whole matrix runs; with the
    // `r0-headline` freeze set the matrix times ONLY the frozen shapes — a
    // confirmation process that also timed the other forty cells would be measuring a
    // different thermal and cache history than the freeze was chosen under. Any OTHER
    // campaign's freeze is refused by `frozen_cell_filter`, because its cells are
    // scored by a different rule.
    let frozen = frozen_cell_filter("r0-headline");

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
    // CONFIRMATION restricts the shape list to the freeze. The circuit, layer and class
    // are fixed for this benchmark and `write_frozen_cells` already asserted the freeze
    // names exactly them, so the remaining axis is the SHAPE.
    let shapes: Vec<SegShape> = match &frozen {
        None => shapes,
        Some(cells) => shapes
            .into_iter()
            .filter(|shape| cells.iter().any(|cell| frozen_cell_shape(cell) == *shape))
            .collect(),
    };
    if frozen.is_some() {
        assert!(
            !shapes.is_empty(),
            "the r0-headline freeze names no shape this matrix builds: a confirmation \
             process that times NOTHING exits 0 and would be read as a passing run"
        );
    }
    let mut matrix = Vec::new();
    let mut reference: Option<Vec<E4>> = None;
    for shape in shapes {
        matrix.push(measure_shape(
            "add_sub L0 R0",
            None,
            &timed,
            &parity,
            shape,
            host_eq,
            device,
            &mut reference,
            Some(SegBaselineArm::incumbent(&incumbent_launch)),
            carveout_mode(),
            profile == Some(shape),
            context,
        ));
    }
    match &frozen {
        // DISCOVERY prints the ±1.0% shortlist and NO RANKING INSIDE IT: the band is
        // wider than the measured repeat noise, so an ordering within it is noise
        // presented as a result, and freezing on it would make that permanent.
        None => {
            let shortlist = discovery_shortlist(&matrix);
            eprintln!(
                "[seg-discovery] band=+{:.1}% members={} (unordered)",
                SEG_DISCOVERY_SHORTLIST_FRACTION * 100.0,
                shortlist.len(),
            );
            for label in &shortlist {
                eprintln!("[seg-discovery] member={label}");
            }
        }
        Some(cells) => eprintln!(
            "[seg-confirm] frozen cells timed: {} of {} named",
            matrix.len(),
            cells.len()
        ),
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
        .filter(|row| {
            row.ratio
                .selectable()
                .is_some_and(|(estimate, _)| estimate.inverts())
        })
        .collect();
    // An order-coupled winner has NO pooled ratio (§6(a) step 6), so the headline
    // prints its diagnostics rather than a number it may not assert. This log line is
    // not the gate — `bwd_seg_add_sub_l0_r0_matrix` is — so it reports instead of
    // aborting the run that produced the CSV above.
    let gate_line = match best.ratio.selectable() {
        Some((estimate, order)) => format!(
            "ratio={:.4} [{:.4}, {:.4}] {} (order delta {:+.3}% [{:+.3}, {:+.3}])",
            estimate.median_ratio,
            estimate.ci_low,
            estimate.ci_high,
            estimate.verdict(),
            order.delta_order_pct,
            order.ci_low_pct,
            order.ci_high_pct,
        ),
        None => format!(
            "ratio=- {} order={:?}",
            best.ratio.verdict(),
            best.ratio.order()
        ),
    };
    eprintln!(
        "[seg-spike] add/sub L0 R0 WINNER {} regs={} median={:.3}us {gate_line} \
         | tie band {} rows | raw argmin over all loaders {} at \
         {:.3}us | {} of {} launchable configurations invert",
        best.shape.label(),
        best.attributes.registers,
        best.candidate_median_us,
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
             {}\n\n\
             Rows {rows} (candidate) against the incumbent at the same `acc_size`; the real \
             plan's row count is {incumbent_rows} (saturated={saturated}). \
             {SEG_WARMUP_SUPERBLOCKS} warmup superblocks and {SEG_TIMED_BLOCKS} timed \
             two-pair blocks (spec §6(a)), so every block holds one candidate-first and \
             one incumbent-first pair. The statistic is the MEDIAN BLOCK RATIO with a \
             {SEG_BOOTSTRAP_RESAMPLES}-resample percentile bootstrap whose resample unit \
             is the block, stratified jointly on `(orientation, incoming class)`. A cell \
             whose order-interaction CI leaves +/-{SEG_ORDER_EQUIVALENCE_PCT}% has NO \
             quotable ratio. **Inversion is `ci_high < 1.0`.**\n\n\
             **Winner: `{}`, {} registers, {:.3} us, {}.** Chosen among PRODUCTION-loader rows \
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
            // PROVENANCE, in the published section itself: this table is a derived
            // summary at a fixed path, so a reader must be able to reach the raw
            // samples and the two SHA-256s from the number they are quoting (§7.3
            // criterion 4c). The `run_id` column of the CSV carries the same key
            // per row.
            {
                let meta = SegRunMeta::current();
                format!(
                    "Run `{}` (label `{}`, compiled pin `{}`), commit `{}`, archive \
                     `{}`, test binary `{}`. Raw samples: `{}`.",
                    meta.run_id,
                    meta.run_label,
                    meta.pin_level,
                    meta.commit,
                    meta.archive_sha256,
                    meta.test_binary_sha256,
                    seg_run_dir(meta).join(SEG_RAW_SAMPLES_TSV).display(),
                )
            },
            best.shape.label(),
            best.attributes.registers,
            best.candidate_median_us,
            gate_line,
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
    // `fixture` drops last, in field order: the eq allocation, the plan's round scratch,
    // the layer state, then the context that owns their pool.
    matrix
}

/// Discovery's ±[`SEG_DISCOVERY_SHORTLIST_FRACTION`] shortlist (spec §6(b) stage 1),
/// as an UNORDERED set of shape labels.
///
/// Only rows with a [`SegRatio::selectable`] ratio are eligible: an order-coupled cell
/// has no pooled ratio to be shortlisted on. The return is sorted LEXICOGRAPHICALLY, not
/// by ratio — the band is wider than the measured repeat noise, so a ranking inside it
/// would present noise as a result and the freeze would make it permanent.
fn discovery_shortlist(rows: &[SegMatrixRow]) -> Vec<String> {
    let ratios: Vec<(&SegMatrixRow, f64)> = rows
        .iter()
        .filter(|row| row.launchable())
        .filter_map(|row| {
            row.ratio
                .selectable()
                .map(|(estimate, _)| (row, estimate.median_ratio))
        })
        .collect();
    let Some(best) = ratios.iter().map(|(_, ratio)| *ratio).reduce(f64::min) else {
        return Vec::new();
    };
    let mut shortlist: Vec<String> = ratios
        .iter()
        .filter(|(_, ratio)| *ratio <= best * (1.0 + SEG_DISCOVERY_SHORTLIST_FRACTION))
        .map(|(row, _)| row.shape.label())
        .collect();
    shortlist.sort();
    shortlist
}

/// Split a published matrix CSV into header-keyed rows.
///
/// By NAME, not by position: [`SEG_CSV_HEADER`] has grown three times in this pass and a
/// positional reader would have silently shifted every field. [`render_matrix_csv`]
/// neutralizes the one field that can contain a comma, so the arity is exact and a row
/// that disagrees with the header is corruption rather than something to tolerate.
fn parse_matrix_csv_rows(text: &str) -> Vec<std::collections::BTreeMap<String, String>> {
    let mut lines = text.lines().filter(|line| !line.trim().is_empty());
    let header: Vec<&str> = lines
        .next()
        .expect("a matrix CSV has a header")
        .split(',')
        .collect();
    lines
        .map(|line| {
            let fields: Vec<&str> = line.split(',').collect();
            assert_eq!(fields.len(), header.len(), "matrix CSV row arity: {line}");
            header
                .iter()
                .map(|name| (*name).to_owned())
                .zip(fields.iter().map(|value| (*value).to_owned()))
                .collect()
        })
        .collect()
}

/// The round class a matrix row belongs to, from the three columns that determine it.
fn matrix_row_class(row: &std::collections::BTreeMap<String, String>) -> SegRoundClass {
    let field = |name: &str| -> &str {
        row.get(name)
            .unwrap_or_else(|| panic!("the matrix CSV has no {name} column"))
    };
    let round: u8 = field("round").parse().expect("round");
    match (round, field("d2_policy")) {
        (0, _) => SegRoundClass::R0,
        (1, _) => SegRoundClass::D1,
        (2, "materialize") => SegRoundClass::D2Materialize,
        (2, _) => SegRoundClass::D2Inline,
        (3, _) => SegRoundClass::D3,
        (other, _) => panic!("a matrix row names round {other}, which is not a swept class"),
    }
}

/// **§6(b) stage 2, EXECUTABLE.** Re-derive discovery's ±1.0% shortlist from the
/// emitted matrix CSV, intersect it with [`SEG_R0_PROBED_TUPLES`], and write the
/// `r0-headline` freeze.
///
/// Executable rather than hand-written because a hand-written freeze cannot be
/// re-derived or reviewed: the band, the selectability predicate and the probe
/// intersection are all rules, and a rule that lives in a shell transcript is not one.
/// [`write_frozen_cells`] re-asserts probe membership, so the predicate holds even if a
/// future caller forgets it here.
///
/// **An EMPTY intersection is a finding, not a fallback**: extend the probe set, re-probe
/// the forced-common-bucket precondition, and only then freeze.
#[test]
#[ignore = "campaign freeze writer; reads discovery's matrix CSV"]
fn bwd_seg_freeze_r0_headline() {
    let csv = std::env::var("BWD_SEG_DISCOVERY_CSV")
        .map(PathBuf::from)
        .unwrap_or_else(|_| seg_output_path(SEG_MATRIX_CSV));
    let text = std::fs::read_to_string(&csv)
        .unwrap_or_else(|error| panic!("read discovery's matrix {}: {error}", csv.display()));
    let frozen = r0_headline_freeze_cells(&text, &csv.display().to_string());
    let path = std::env::var("BWD_SEG_FROZEN_CELLS_OUT")
        .expect("BWD_SEG_FROZEN_CELLS_OUT must name the freeze to write");
    // The MEASURED probe verdicts, from `pair_gate.py`'s own output. Required, not
    // optional: a freeze written without them would rest on probe MEMBERSHIP, which
    // records that a capture was taken and not that the arms converged (F-9.3).
    //
    // `BWD_SEG_OFF_COLUMN_ONLY=<why>` is the ONE alternative: a freeze that will be consumed
    // only by §7.1.0's `off` control, which does not claim equal partitions. EXACTLY ONE of
    // the two must be set — both would leave it ambiguous which precondition the artifact
    // carries, and the artifact is the only place a later reader can look.
    let verdicts = std::env::var("BWD_SEG_PROBE_VERDICTS").ok();
    let off_only = std::env::var("BWD_SEG_OFF_COLUMN_ONLY").ok();
    let probes = match (verdicts, off_only) {
        (Some(_), Some(_)) => panic!(
            "BWD_SEG_PROBE_VERDICTS and BWD_SEG_OFF_COLUMN_ONLY are both set: the freeze \
             would carry two different preconditions. Set exactly one."
        ),
        (Some(path), None) => SegProbeEvidence::Measured {
            // The configuration this freeze is FOR, from the environment the confirmations
            // will run in — so the verdict that licenses it must have been measured at the
            // same bucket, not merely in some forced mode.
            mode_key: carveout_mode().mode_key(),
            verdicts: parse_probe_verdicts(
                &std::fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("read probe verdicts {path}: {error}")),
            ),
        },
        (None, Some(why)) => {
            assert!(
                !why.trim().is_empty(),
                "BWD_SEG_OFF_COLUMN_ONLY must SAY WHY convergence does not apply; the reason \
                 is written into the freeze header where a later reader will find it"
            );
            SegProbeEvidence::ConvergenceIndependent {
                why: why.trim().to_owned(),
            }
        }
        (None, None) => panic!(
            "the R0 freeze needs either BWD_SEG_PROBE_VERDICTS (the pair_gate.py convergence \
             verdicts for the probed tuples) or BWD_SEG_OFF_COLUMN_ONLY=<why> for an \
             off-column-only freeze; it may not be written without one (§9 item 2, F-9.3)"
        ),
    };
    write_frozen_cells(
        Path::new(&path),
        "r0-headline",
        &frozen,
        SEG_SCHEDULE_SEED,
        &probes,
    );
    for cell in &frozen {
        eprintln!("[seg-freeze] frozen cell={}", cell.label);
    }
}

/// The freeze SELECTION — band, probe intersection and name normalization — separated
/// from the environment and the file write so a CPU test can drive it end to end.
///
/// The test that drives it is what makes the `short_name` normalization below a covered
/// path rather than a claim: `render_matrix_csv` emits the LONG `..._layout_gkr.json`
/// form, so a version of this function without the call fails inside
/// `write_frozen_cells`'s coordinate assertion.
fn r0_headline_freeze_cells(text: &str, source: &str) -> Vec<SegFrozenCell> {
    let rows = parse_matrix_csv_rows(text);
    assert!(!rows.is_empty(), "{source}: no rows");
    // SELECTABLE rows only — the same predicate `SegRatio::selectable` applies, read off
    // the two columns the renderer derives from it. BOTH are required although either
    // alone would do: a renderer that ever emitted a ratio for a failed gate would be
    // caught here instead of silently widening the band.
    let candidates: Vec<(&std::collections::BTreeMap<String, String>, f64)> = rows
        .iter()
        .filter(|row| row["launchable"] == "true" && row["order_gate"] == "true")
        .filter_map(|row| {
            let ratio = row["median_ratio"].parse::<f64>().ok()?;
            Some((row, ratio))
        })
        .collect();
    assert!(
        !candidates.is_empty(),
        "{source}: no row carries a selectable ratio, so there is nothing to freeze"
    );
    let best = candidates
        .iter()
        .map(|(_, ratio)| *ratio)
        .reduce(f64::min)
        .expect("a non-empty candidate set");
    let band: Vec<&std::collections::BTreeMap<String, String>> = candidates
        .iter()
        .filter(|(_, ratio)| *ratio <= best * (1.0 + SEG_DISCOVERY_SHORTLIST_FRACTION))
        .map(|(row, _)| *row)
        .collect();
    // The intersection with the PROBED tuples. §9 item 2's forced-common-bucket
    // precondition is established only on the shapes the NCU probe covered.
    let frozen: Vec<SegFrozenCell> = band
        .iter()
        .filter(|row| {
            SEG_R0_PROBED_TUPLES.iter().any(|probed| {
                probed.epilogue == row["epilogue"]
                    && probed.k.to_string() == row["k"]
                    && probed.coeff == row["coeff"]
                    && probed.program == row["program"]
            })
        })
        .map(|row| SegFrozenCell {
            label: format!(
                "r0-{}-k{}-{}-{}",
                row["epilogue"], row["k"], row["coeff"], row["program"]
            ),
            // **The SHORT form.** `SegMatrixRow::circuit` carries the coordinate's file
            // name (`..._layout_gkr.json`) while every freeze predicate — and the
            // `write_frozen_cells` assertion below — compares against
            // `ADD_SUB_LAYOUT_SHORT`. Normalizing here is what keeps the two conventions
            // from meeting for the first time inside an assertion.
            circuit: short_name(&row["circuit"]).to_owned(),
            layer: row["layer"].parse().expect("layer"),
            class: matrix_row_class(row),
            k: row["k"].parse().expect("k"),
            epilogue: row["epilogue"].clone(),
            coeff: row["coeff"].clone(),
            program: row["program"].clone(),
        })
        .collect();
    eprintln!(
        "[seg-freeze] discovery band {} of {} selectable rows; {} intersect the probed set",
        band.len(),
        candidates.len(),
        frozen.len(),
    );
    assert!(
        !frozen.is_empty(),
        "the ±{:.1}% shortlist and the probed tuple set do not intersect: that is a \
         FINDING — extend SEG_R0_PROBED_TUPLES, re-probe the forced-common-bucket \
         precondition, and only then freeze (§9 item 2). Band members: {:?}",
        SEG_DISCOVERY_SHORTLIST_FRACTION * 100.0,
        band.iter()
            .map(|row| format!("{} K{}", row["epilogue"], row["k"]))
            .collect::<Vec<String>>(),
    );
    frozen
}

// ── §4.5's pin-decision and δ3-attribution runners ────────────────────────────

/// Device bytes ONE pin-decision cell may spend on synthetic backings.
///
/// Deliberately far below [`SEG_BACKING_BUDGET_BYTES`]: this runner holds a timed cell
/// for every distinct class it was asked for, simultaneously, inside the R0 fixture's own
/// context — which already holds the real trace and the incumbent plan. The Stage-A
/// per-cell budget would over-commit the device on the first two classes.
const SEG_PIN_CELL_BUDGET_BYTES: usize = 4 << 30;
/// The row target at round 0, halved per round exactly as the real sumcheck halves rows.
/// A CONSTANT, so every level and every arm times the same geometry: a row count derived
/// from anything session-dependent would make the levels incomparable.
const SEG_PIN_TARGET_ROWS: usize = 1 << 22;
/// The folding-step count the pin runner's shared eq is built at. Covers `2^23` rows, so
/// [`SEG_PIN_TARGET_ROWS`] is inside it at every round.
const SEG_PIN_EQ_FOLDING_STEPS: usize = 24;
const _: () = assert!(SEG_PIN_TARGET_ROWS <= 1 << (SEG_PIN_EQ_FOLDING_STEPS - 1));

/// Steps 1-5 of §4.5's construction contract, and nothing else.
///
/// Every row carries `cell.label` in `benchmark` (and as its raw-sample key) and
/// `cell.role` in [`SegMatrixRow::pin_role`], and the plan for every pair is exactly
/// `CarveoutPlan::for_pair(CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES),
/// seg_carveout_shape(regime, shape, "candidate"), incumbent_r0_carveout_shape(),
/// cell.class.round() >= 1)`, which is what [`measure_shape`] builds from the mode this
/// function passes — so no cell can reach a demand-derived bucket.
///
/// **Cells are built for the distinct classes of `wanted`, not of the whole set.** The
/// mapping `class -> (regime, round, d2)` is injective over [`SEG_ROUND_CLASSES`], so the
/// class IS the key; and a `BWD_SEG_PIN_ROLE_ONLY=control` smoke or a one-cell profiling
/// run must not allocate four class cells it will never time.
fn run_pin_decision_matrix(wanted: &[&SegPinCell]) -> Vec<SegMatrixRow> {
    assert!(!wanted.is_empty(), "a decision run times at least one cell");
    // Step 1: the real incumbent plan and its staged bank, in ONE context — so both arms
    // share a clock, a thermal state and a memory state at every sample.
    let fixture = seg_r0_fixture();
    let context = &fixture.context;
    let incumbent_launch = |ctx: &ProverContext| fixture.incumbent_launch(ctx);
    // Step 2: ONE shared eq, and one `(timed, parity)` pair per distinct class.
    //
    // This rebuilds the `ab_gkr_eq_high` symbol the fixture's own eq wrote. That is
    // deliberate and it does not weaken the reference clock: the incumbent's CORRECTNESS
    // was established inside `seg_r0_fixture` against its own eq, before this call, and
    // what the clock has to be afterwards is INVARIANT — the same launch, over the same
    // eq state, at every level and in both δ3 arms, which it is.
    let (eq_low, eq_sizes) = build_shared_eq(SEG_PIN_EQ_FOLDING_STEPS, context);
    let host_eq = HostEq::download(eq_low.as_ptr(), eq_sizes, context);
    let mut built: Vec<(SegRoundClass, SegCell, SegCell)> = Vec::new();
    for cell in wanted {
        if built.iter().any(|(class, _, _)| *class == cell.class) {
            continue;
        }
        let regime = if cell.class == SegRoundClass::R0 {
            DagBwdRegime::R0
        } else {
            DagBwdRegime::Ext
        };
        let round = cell.class.round();
        let d2 = cell.class.d2();
        let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, regime);
        let per_row = probe_bytes_per_row(&coord, round, d2);
        let (rows, saturated) = fit_rows(
            SEG_PIN_TARGET_ROWS >> round,
            per_row,
            SEG_PIN_CELL_BUDGET_BYTES,
            SEG_MIN_TIMED_ROWS,
        );
        eprintln!(
            "[seg-pin] class={} {per_row} B/row -> {rows} rows ({:.2} GiB, \
             saturated={saturated})",
            cell.class.label(),
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
            context,
        );
        let timed = SegCell::build(
            Arc::clone(&coord),
            round,
            rows,
            saturated,
            d2,
            eq_low.as_ptr(),
            eq_sizes,
            context,
        );
        built.push((cell.class, timed, parity));
    }
    // The identity reference is PER CLASS: two classes launch different rounds into
    // different buffers, so a shared reference would compare unrelated contributions.
    let mut reference: Vec<(SegRoundClass, Option<Vec<E4>>)> =
        built.iter().map(|(class, _, _)| (*class, None)).collect();
    // The profiling selector, read here because it decides which launches are
    // NVTX-WRAPPED; the caller has already asserted that it selects exactly one cell.
    let profile_cell = std::env::var("BWD_SEG_PIN_PROFILE_CELL").ok();
    let mut matrix = Vec::with_capacity(wanted.len());
    // Steps 3-5, in ARRAY ORDER.
    for cell in wanted {
        let (_, timed, parity) = built
            .iter()
            .find(|(class, _, _)| *class == cell.class)
            .expect("a cell was built for every class in `wanted`");
        let shape = SegShape::regs(
            cell.k,
            CoeffMode::Constant,
            ProgramMode::Inline,
            BwdSegEpilogue::Plane,
        );
        let slot = reference
            .iter_mut()
            .find(|(class, _)| *class == cell.class)
            .map(|(_, slot)| slot)
            .expect("a reference slot per built class");
        let mut row = measure_shape(
            cell.label,
            // The raw key is the predeclared LABEL, because `aggregate_arm` looks a cell
            // up by exactly that.
            Some(cell.label),
            timed,
            parity,
            shape,
            &host_eq,
            &fixture.device,
            slot,
            Some(SegBaselineArm {
                label: "flat-r0-reference-clock",
                launch: SegBaselineLaunch::External(&incumbent_launch),
                shape: incumbent_r0_carveout_shape(),
            }),
            CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES),
            profile_cell.as_deref() == Some(cell.label),
            context,
        );
        // Step 4: the role travels with the row, so the aggregator separates Decision
        // from DriftControl without re-deriving either.
        row.pin_role = cell.role;
        // THIS is the reference-clock campaign — the only one. The baseline above is
        // literally labelled `flat-r0-reference-clock`, and §4.5 forbids reading §6(b)'s
        // inversion rule off a cross-build ratio. Set here rather than inferred from the
        // carveout mode, because the headline pairs now share that mode.
        row.pairing = SegPairing::ReferenceClock;
        matrix.push(row);
    }
    let csv = seg_output_path("seg_pin_decision_matrix.csv");
    publish(&csv, &render_matrix_csv(&matrix));
    for (_, timed, parity) in built {
        drop(timed);
        drop(parity);
    }
    drop(eq_low);
    matrix
}

/// **§4.5's pin decision cells.** Candidates are CONTINUATION shapes — the only
/// symbols the sweep touches — each paired against the flat R0 incumbent as a
/// **REFERENCE CLOCK**, plus the R0 seg drift control.
///
/// **Why an R0 kernel is the right denominator for a continuation candidate.** It
/// is not a semantic baseline and is never reported as one. §4.5's cross-build
/// argument is that "the incumbent is not compiled from the seg kernel matrix and
/// the pin knob does not touch it, so it is invariant across the three level builds
/// and every level's number is a ratio against the same reference rather than an
/// absolute time carrying that build's session drift." The flat R0 kernel is the one
/// such symbol this harness already stages, and Task 8's SASS gate PROVES its
/// normalized body identical across every level. Every quotation of these ratios
/// carries the label `cont-vs-flat-r0 reference clock`, never `speedup`.
///
/// **The pairs run at `FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES)`**, not
/// `CommonBucket`: a demand-derived bucket would put the reference clock at 16 KiB
/// at the natural band and 32 KiB at a 40-pin, and a denominator whose own cache
/// configuration moves with the level is not invariant.
///
/// `BWD_SEG_PIN_ROLE_ONLY=control` restricts to the drift control, for a cheap smoke
/// run that proves the plumbing before nine real processes are spent.
///
/// **`BWD_SEG_PIN_PROFILE_CELL=<label>` is the PROFILING selector, and it is
/// required for any NCU capture.** All seven cells launch through the same two entry
/// points and the same two NVTX range names, so `ncu --launch-count 1` on a full
/// seven-cell run captures the FIRST wrapped launch every time — the same cell,
/// relabelled. With this set the runner times **only that one cell** (plus nothing
/// else) and wraps only its launches, so `--launch-count 1` is unambiguous. It also
/// makes `BWD_SEG_PROFILE_K` / `BWD_SEG_PROFILE_EPILOGUE` irrelevant here: those are
/// [`profile_shape`]'s variables and this runner does not read them, which is why an
/// earlier draft's capture loop was measuring a shape it had not selected.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_pin_decision_cells() {
    let only_control = std::env::var("BWD_SEG_PIN_ROLE_ONLY").as_deref() == Ok("control");
    // The profiling selector: exactly one cell, by label, and it is the ONLY cell
    // whose launches are NVTX-wrapped, so `--launch-count 1` is unambiguous.
    let profile_cell = std::env::var("BWD_SEG_PIN_PROFILE_CELL").ok();
    if let Some(label) = &profile_cell {
        assert!(
            SEG_PIN_DECISION_CELLS.iter().any(|c| c.label == label),
            "BWD_SEG_PIN_PROFILE_CELL={label:?} is not a predeclared decision cell"
        );
    }
    // Only the PIN freeze. The R0 freeze names shapes this runner does not have, and
    // the δ3 freeze names cells scored by a different rule — both would silently
    // change what the decision measures.
    let frozen = frozen_cell_filter("pin-decision");
    let wanted: Vec<&SegPinCell> = SEG_PIN_DECISION_CELLS
        .iter()
        .filter(|cell| {
            // The drift control always runs (mechanism 3). Decision cells run when
            // no freeze is active, or when the freeze names them.
            // With a profile cell selected, ONLY that cell runs — including instead
            // of the drift control, because a capture must be unambiguous.
            if let Some(label) = &profile_cell {
                return cell.label == label;
            }
            cell.role == SegPinRole::DriftControl
                || (!only_control
                    && frozen
                        .as_ref()
                        .map_or(true, |cells| cells.iter().any(|f| f.label == cell.label)))
        })
        .collect();
    // The drift-control requirement is a TIMING-process requirement. A profiling run
    // deliberately times ONE cell so `--launch-count 1` is unambiguous, so demanding a
    // drift control there would fail every capture by construction.
    match &profile_cell {
        None => assert!(
            wanted.iter().any(|c| c.role == SegPinRole::DriftControl),
            "the drift control must run in EVERY timing process (§4.5 mechanism 3)"
        ),
        Some(_) => assert_eq!(wanted.len(), 1, "a profiling run times exactly one cell"),
    }
    let rows = run_pin_decision_matrix(&wanted);
    // The construction contract, asserted rather than described.
    let observed: Vec<&str> = rows.iter().map(|r| r.benchmark.as_str()).collect();
    let expected: Vec<&str> = wanted.iter().map(|c| c.label).collect();
    assert_eq!(
        observed, expected,
        "observed cells must equal the contract, in order"
    );
    // MODE-AWARE, like the pre-run assertion: a profiling run times exactly one cell,
    // which is frequently NOT the drift control. An unconditional
    // `DriftControl == 1` here failed every capture — the same class of defect as the
    // selector-side assertion, at a second site.
    match &profile_cell {
        None => assert_eq!(
            rows.iter()
                .filter(|r| r.pin_role == SegPinRole::DriftControl)
                .count(),
            1,
            "a TIMING run carries exactly one drift control, no more and no less"
        ),
        Some(label) => {
            assert_eq!(rows.len(), 1, "a profiling run emits exactly one row");
            assert_eq!(&rows[0].benchmark, label, "and it is the selected cell");
        }
    }
    for row in &rows {
        // **This asserts the REQUEST landed, not the realized partition** (ruling R8) — the
        // realized field is an `ncu` metric this process cannot observe. It is still a gate
        // and not a note: a request that silently failed to land would put the two levels on
        // different configurations for a reason invisible in the raw rows.
        //
        // The realized side is verified out of process, per level, and what it asserts is
        // **per-arm level-invariance, not pair equality**: §4.5's number is a ratio of
        // ratios, so the partition has to cancel BETWEEN LEVELS, which needs each arm
        // constant across levels — not the two arms equal to each other (that is §7.2.1's
        // question). Measured: clock 65,536 B at every level and hash-identical SASS;
        // candidate 102,400 B (pool max, clamped) at every measurable level, 0.26 pp L1
        // spread. See `SEG_REFERENCE_CLOCK_BUCKET_BYTES` for the full argument.
        assert_eq!(
            row.carveout_requested_pct,
            Some(bwd_seg_carveout_pct_for_bucket(
                SEG_REFERENCE_CLOCK_BUCKET_BYTES
            )),
            "{}: every decision pair REQUESTS the predeclared fixed bucket",
            row.benchmark
        );
    }
}

/// **§4.5's δ3 loop-form attribution cells.** The pin runner's contract, restated over
/// [`SEG_D3_ATTRIBUTION_CELLS`] — the δ3-BEARING shapes — and scored by
/// [`summarize_d3_attribution`], not by the pin rule.
///
/// One arm of this runs per loop form at the WINNING pin, so its cells must be identical
/// across the two builds; that is why the set is a predeclared constant and the freeze
/// writer serializes it rather than selecting anything.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_d3_attribution_cells() {
    let only_control = std::env::var("BWD_SEG_PIN_ROLE_ONLY").as_deref() == Ok("control");
    let profile_cell = std::env::var("BWD_SEG_PIN_PROFILE_CELL").ok();
    if let Some(label) = &profile_cell {
        assert!(
            SEG_D3_ATTRIBUTION_CELLS.iter().any(|c| c.label == label),
            "BWD_SEG_PIN_PROFILE_CELL={label:?} is not a predeclared attribution cell"
        );
    }
    // Only the δ3 freeze: the pin freeze names cells scored by a different rule and the
    // R0 freeze names shapes this runner does not have.
    let frozen = frozen_cell_filter("d3-attribution");
    let wanted: Vec<&SegPinCell> = SEG_D3_ATTRIBUTION_CELLS
        .iter()
        .filter(|cell| {
            if let Some(label) = &profile_cell {
                return cell.label == label;
            }
            cell.role == SegPinRole::DriftControl
                || (!only_control
                    && frozen
                        .as_ref()
                        .map_or(true, |cells| cells.iter().any(|f| f.label == cell.label)))
        })
        .collect();
    match &profile_cell {
        None => assert!(
            wanted.iter().any(|c| c.role == SegPinRole::DriftControl),
            "the drift control must run in EVERY timing process (§4.5 mechanism 3)"
        ),
        Some(_) => assert_eq!(wanted.len(), 1, "a profiling run times exactly one cell"),
    }
    let rows = run_pin_decision_matrix(&wanted);
    let observed: Vec<&str> = rows.iter().map(|r| r.benchmark.as_str()).collect();
    let expected: Vec<&str> = wanted.iter().map(|c| c.label).collect();
    assert_eq!(
        observed, expected,
        "observed cells must equal the contract, in order"
    );
    match &profile_cell {
        None => assert_eq!(
            rows.iter()
                .filter(|r| r.pin_role == SegPinRole::DriftControl)
                .count(),
            1,
            "a TIMING run carries exactly one drift control, no more and no less"
        ),
        Some(label) => {
            assert_eq!(rows.len(), 1, "a profiling run emits exactly one row");
            assert_eq!(&rows[0].benchmark, label, "and it is the selected cell");
        }
    }
    for row in &rows {
        assert_eq!(
            row.carveout_requested_pct,
            Some(bwd_seg_carveout_pct_for_bucket(
                SEG_REFERENCE_CLOCK_BUCKET_BYTES
            )),
            "{}: every attribution pair runs at the predeclared fixed bucket",
            row.benchmark
        );
    }
}

/// Probe, certify and time ONE matrix coordinate.
///
/// The order is load-bearing: launchability first (a cell that cannot run is
/// recorded, never skipped), then both CPU oracles on the parity twin, then the
/// timed cell's preflight and identity check, and only then the timing loop.
#[allow(clippy::too_many_arguments)]
fn measure_shape(
    benchmark: &str,
    // The RAW-SAMPLE KEY. `None` keys the emitted samples `{benchmark}|{shape label}`,
    // which is what a matrix driver needs: one benchmark times many shapes and they must
    // not collide in one raw file. The pin and δ3 campaigns pass `Some(cell.label)`,
    // because `aggregate_arm` looks a predeclared cell up by EXACTLY its label — a
    // composite key would make every cell missing and the arm unreadable.
    raw_cell_key: Option<&str>,
    timed: &SegCell,
    parity: &SegCell,
    shape: SegShape,
    eq: &HostEq,
    device: &SegDeviceFacts,
    reference: &mut Option<Vec<E4>>,
    // `baseline`: what this shape is PAIRED against, its label, and its LAUNCH
    // SHAPE — the plan cannot compute a two-arm maximum from an opaque callback.
    // `None` falls back to solo timing, which the row records as such.
    baseline: Option<SegBaselineArm>,
    // The carveout configuration is a PARAMETER, not a global read: `carveout_mode()`
    // parses an env var and cannot yield `FixedBucket`, so the pin-decision runner —
    // whose reference clock must sit at ONE level-invariant partition — has to be able
    // to pass it.
    carveout: CarveoutMode,
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
        ratio: SegRatio::Solo,
        run_id: "-",
        baseline: baseline.as_ref().map_or("-", |arm| arm.label),
        // Filled below from the lowering, on both paths: the floor is a property of the
        // lowering, so an UNLAUNCHABLE row carries one too. Zero survives only where
        // there is no lowering output at all to walk.
        floor: BwdSegTrafficFloor::default(),
        // An unlaunchable cell returns before the plan is built, and `-` is then the
        // truth: nothing was configured.
        carveout_mode: "-",
        carveout_requested_pct: None,
        carveout_source: "-".to_owned(),
        // The pin-decision runner OVERWRITES this per cell; every other caller leaves
        // the default and never reads it.
        pin_role: SegPinRole::Decision,
        // Candidate-vs-incumbent is the DEFAULT because it is what almost every caller
        // is: the R0 headline (at any fixed bucket included), the Stage-B
        // ladder and the corpus sweep all pair against something they mean to replace.
        // The pin / δ3 runner overwrites it beside `pin_role`, at the one call site that
        // pairs against a clock.
        pairing: SegPairing::CandidateVsIncumbent,
    };
    if blocks_per_sm == 0 {
        // The cell is never staged, so the floor comes from a bare lowering. A lowering
        // REJECTION leaves the zero, which is the "no lowering output" reading.
        if let Ok(setup) = timed.try_lower(shape) {
            row.floor = bwd_seg_traffic_floor(&setup, shape.coeff, shape.program);
        }
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

    // Held for the whole cell. Built here because this is the only site that sees
    // both arms; applied before EITHER arm stages because `SegCell::stage` launches
    // the fold-weight prelude. RAII restores the exact prior values on the way out —
    // declared before both launchables, so the restore is the last thing to run.
    let candidate_shape = seg_carveout_shape(regime, shape, "candidate");
    let mut carveout_plan = match &baseline {
        Some(arm) => {
            CarveoutPlan::for_pair(carveout, candidate_shape, arm.shape, timed.model.round >= 1)
        }
        None => CarveoutPlan::for_solo(carveout, candidate_shape, timed.model.round >= 1),
    };
    carveout_plan.apply();
    row.carveout_mode = carveout_plan.mode().label();
    row.carveout_requested_pct = carveout_plan.requested_pct_of(candidate_shape.entry);
    row.carveout_source = carveout_plan.demand_source_label().to_owned();

    // A segmented twin stages HERE — under the applied plan, and BEFORE the
    // candidate, which is the order the callers that used to prepare it had.
    let twin = match baseline.as_ref().map(|arm| &arm.launch) {
        Some(SegBaselineLaunch::SegTwin(twin_shape)) => Some(timed.prepare(*twin_shape, context)),
        _ => None,
    };

    // Rung 2: the timed cell's own preflight and prefix identity.
    let launchable = timed.prepare(shape, context);
    row.max_over_mean_work = launchable.setup.work.max_over_mean;
    row.floor = bwd_seg_traffic_floor(&launchable.setup, shape.coeff, shape.program);
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
    // One launch expression for both baseline kinds: the external callback, or the
    // twin this function staged above.
    let launch_baseline = |ctx: &ProverContext| -> CudaResult<()> {
        match &baseline
            .as_ref()
            .expect("a baseline launch is only asked for on a paired cell")
            .launch
        {
            SegBaselineLaunch::External(launch) => launch(ctx),
            SegBaselineLaunch::SegTwin(_) => twin
                .as_ref()
                .expect("a `SegTwin` baseline is prepared before the timing loop")
                .launch(ctx),
        }
    };
    match &baseline {
        Some(arm) => {
            let label = arm.label;
            // The BALANCED protocol (spec §6(a)): seeded two-pair blocks, a
            // joint-stratified block bootstrap, and the order contrast as a gate.
            // `time_paired`'s fixed candidate-then-incumbent order cannot identify an
            // order effect at all, which is defect §1(d).
            let blocked = time_paired_blocked(
                stream,
                || launchable.launch(context),
                || launch_baseline(context),
                &seg_schedule(SEG_SCHEDULE_SEED),
            )
            .expect("balanced two-pair paired timing");
            let ratio = SegRatio::of(&blocked);
            let order = blocked.order_interaction();
            // The medians a paired row reports come from the BLOCK MEANS, so the CSV's
            // median columns describe the protocol that produced the ratio.
            let candidate_means: Vec<f64> = blocked
                .blocks
                .iter()
                .map(SegBlockSample::candidate_mean)
                .collect();
            let incumbent_means: Vec<f64> = blocked
                .blocks
                .iter()
                .map(SegBlockSample::incumbent_mean)
                .collect();
            let reported = match ratio.reported_estimate() {
                Some(estimate) => format!(
                    "{:.4} [{:.4}, {:.4}] {}",
                    estimate.median_ratio,
                    estimate.ci_low,
                    estimate.ci_high,
                    estimate.verdict(),
                ),
                None => format!("- {}", ratio.verdict()),
            };
            eprintln!(
                "[seg-spike] {benchmark} {}: candidate {:.3}us vs {label} {:.3}us -> \
                 {reported} | order delta {:+.3}% [{:+.3}, {:+.3}] gate={}",
                shape.label(),
                median(&candidate_means),
                median(&incumbent_means),
                order.delta_order_pct,
                order.ci_low_pct,
                order.ci_high_pct,
                order.passes(),
            );
            // The RECORD, into the run's reserved directory: every sample with its
            // block, orientation, incoming class and order id, so every §6 analysis is
            // reproducible after the process has exited.
            let meta = SegRunMeta::current();
            record_raw_samples(
                meta,
                &raw_cell_key
                    .map_or_else(|| format!("{benchmark}|{}", shape.label()), str::to_owned),
                &blocked,
            );
            row.run_id = meta.run_id.as_str();
            row.candidate_median_us = median(&candidate_means);
            row.candidate_min_us = blocked
                .blocks
                .iter()
                .flat_map(|block| block.candidate_us)
                .fold(f64::MAX, f64::min);
            row.incumbent_median_us = Some(median(&incumbent_means));
            row.incumbent_min_us = Some(
                blocked
                    .blocks
                    .iter()
                    .flat_map(|block| block.incumbent_us)
                    .fold(f64::MAX, f64::min),
            );
            row.ratio = ratio;
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
        if baseline.is_some() {
            let _range = crate::primitives::nvtx::scoped_range(
                Some(SEG_NVTX_DOMAIN),
                SEG_NVTX_INCUMBENT_MESSAGE,
            );
            launch_baseline(context).expect("profiled baseline");
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
                        None,
                        &timed,
                        &parity,
                        shape,
                        &host_eq,
                        &device,
                        &mut reference,
                        None,
                        carveout_mode(),
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

/// Back-to-back prelude launches inside one event window, for the amortized arm.
///
/// The serialized arm records an event pair around ONE launch on an idle stream, so
/// its number carries the dispatch bubble as well as the kernel; this arm divides a
/// window that holds many launches by their count, which bounds the same cost from
/// below. Both bounds are reported — the production round's true charge is between
/// them, and which end it sits at depends on how far ahead the round's launches are
/// enqueued.
const SEG_PRELUDE_BATCH: usize = 32;

/// **The prelude's own cost — the term every continuation median in this module
/// omits.**
///
/// [`SegCell::stage`] enqueues `ab_gkr_bwd_seg_build_fold_weights_kernel` once per
/// shape and staging is outside every timed loop by construction ("Never called from
/// inside a timed loop"), so every continuation number this module publishes is
/// EXECUTOR-ONLY while a production continuation round pays one prelude launch per
/// round on top of it. Reporting a total without measuring this term would be a
/// guess, and reporting the executor alone as the round's cost would be wrong; this
/// cell measures it so both columns exist.
///
/// Three things are measured, none of them assumed:
/// - the prelude alone, serialized (upper bound) and amortized over
///   [`SEG_PRELUDE_BATCH`] launches (lower bound), at four rounds — the round axis
///   CHECKS the "one warp, 11 slots, cost independent of round" claim rather than
///   resting on it, `round = 8` being the beyond-every-fold-depth case;
/// - the same prelude INTERLEAVED against a real continuation executor in one
///   process, so the fraction is a paired ratio with an interval rather than a
///   quotient of two runs' medians.
///
/// The executor side is a DENOMINATOR, not a claim: its parity is the ladder's and
/// the matrices' business, and nothing here divides two medians from two processes.
#[test]
#[ignore = "GPU timing; build unlocked and run the executable under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_fold_weight_prelude_cost() {
    let context = make_seg_spike_context(SEG_CONT_ARENA_BYTES);
    let stream = context.get_exec_stream();

    let mut solo = String::from(
        "| round | serialized median (us) | serialized min (us) | amortized per launch (us) |\n\
         |---|---|---|---|\n",
    );
    for round in [1u8, 2, 3, 8] {
        stage_claim_point(&super::seg_compile::seg_claim_point(round), &context);
        stream.synchronize().expect("claim point staged");
        let one = time_solo(stream, || {
            launch_bwd_seg_build_fold_weights(u32::from(round), &context)
        })
        .expect("serialized prelude timing");
        let batched = time_solo(stream, || {
            for _ in 0..SEG_PRELUDE_BATCH {
                launch_bwd_seg_build_fold_weights(u32::from(round), &context)?;
            }
            Ok(())
        })
        .expect("amortized prelude timing");
        let median_us = median(&one);
        let min_us = one.iter().copied().fold(f64::MAX, f64::min);
        let amortized = median(&batched) / SEG_PRELUDE_BATCH as f64;
        eprintln!(
            "[seg-spike] prelude r{round}: serialized {median_us:.3}us median / {min_us:.3}us \
             min, amortized {amortized:.3}us per launch over {SEG_PRELUDE_BATCH}"
        );
        writeln!(
            solo,
            "| {round} | {median_us:.3} | {min_us:.3} | {amortized:.3} |"
        )
        .expect("write String");
    }

    // The paired arm: the same row counts and the same production-loader shape the
    // continuation matrix reports, so the ratio below divides two numbers that were
    // measured in one loop against each other.
    let (eq_low, eq_sizes) = build_shared_eq(24, &context);
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, DagBwdRegime::Ext);
    let shape = SegShape::regs(
        4,
        CoeffMode::Constant,
        ProgramMode::Inline,
        BwdSegEpilogue::Plane,
    );
    let mut paired_body = String::from(
        "| cell | rows | shape | prelude (us) | executor (us) | prelude / executor | 95% CI |\n\
         |---|---|---|---|---|---|---|\n",
    );
    // Round 1's two medians, from the SAME interleaved loop, are what the per-proof
    // share below is computed from: `T1` is the widest round's executor and the prelude
    // is flat in round, so nothing here divides two numbers from two processes.
    let mut round1: Option<(f64, f64)> = None;
    for round in [1u8, 2] {
        let per_row = probe_bytes_per_row(&coord, round, D2Policy::Inline);
        let target = (1usize << 23) >> usize::from(round);
        let (rows, _saturated) = fit_rows(
            target,
            per_row,
            SEG_BACKING_BUDGET_BYTES,
            SEG_MIN_TIMED_ROWS,
        );
        let cell = SegCell::build(
            Arc::clone(&coord),
            round,
            rows,
            false,
            D2Policy::Inline,
            eq_low.as_ptr(),
            eq_sizes,
            &context,
        );
        let launchable = cell.prepare(shape, &context);
        // The LEGACY IID protocol on purpose, and NOT a §6 A/B: the two arms are
        // DIFFERENT kernels three orders of magnitude apart, so this ratio is a cost
        // FRACTION ("how much of a round is the prelude"), not a candidate-versus-
        // incumbent verdict. §6(a)'s balanced blocks and its ±0.30% equivalence gate
        // answer the other question, and applying them here would suppress a
        // perfectly readable fraction on a contrast that cannot change its reading.
        // This interval is therefore NOT admissible as a §6 result and the published
        // section says so.
        let paired = time_paired(
            stream,
            || launch_bwd_seg_build_fold_weights(u32::from(round), &context),
            || launchable.launch(&context),
        )
        .expect("interleaved prelude-vs-executor timing");
        let estimate = paired.estimate();
        eprintln!(
            "[seg-spike] prelude r{round} vs executor {}: prelude {:.3}us vs executor \
             {:.3}us -> {:.6} [{:.6}, {:.6}] ({rows} rows)",
            shape.label(),
            paired.candidate_median(),
            paired.incumbent_median(),
            estimate.median_ratio,
            estimate.ci_low,
            estimate.ci_high,
        );
        writeln!(
            paired_body,
            "| add_sub L0 D{round} inline | {rows} | {} | {:.3} | {:.1} | {:.6} | [{:.6}, \
             {:.6}] |",
            shape.label(),
            paired.candidate_median(),
            paired.incumbent_median(),
            estimate.median_ratio,
            estimate.ci_low,
            estimate.ci_high,
        )
        .expect("write String");
        if round == 1 {
            round1 = Some((paired.candidate_median(), paired.incumbent_median()));
        }
        drop(launchable);
        drop(cell);
    }
    drop(eq_low);

    // The per-PROOF share is the decision-relevant number, not the widest round's
    // ratio: the prelude is one launch per continuation round, so with `R` rounds it
    // costs `R * prelude` against a proof whose executor time is dominated by the
    // first two rounds (~`2 * T1`). At the measured 4.32 us flat-in-round prelude and
    // `T1 = 8,220.9 us`, `R = 23` gives 99 us against ~16.4 ms = **0.60%**, ~12x the
    // previously published 0.05%; the crossover where the prelude costs more than the
    // executor it gates is round ~12.
    //
    // ENVELOPE, stated rather than claimed: `SEG_MIN_TIMED_ROWS = 1 << 16` is a ROW
    // floor, so nothing past round ~7 is measured at all, and the entire region where
    // the prelude dominates is OUTSIDE the measured envelope by construction. This pass
    // adds no below-floor timing mode.
    let (prelude_median_us, t1_median_us) =
        round1.expect("round 1 is the widest measured continuation round");
    let rounds: u32 = std::env::var("BWD_SEG_PRELUDE_ROUNDS")
        .ok()
        .and_then(|value| value.trim().parse().ok())
        .unwrap_or(23);
    let per_proof_share = f64::from(rounds) * prelude_median_us / (2.0 * t1_median_us);
    // The cell's OWN row progression halves rows per round (`target = (1 << 23) >>
    // round`), so the executor median at round `r` is `T1 / 2^(r - 1)`; the crossover is
    // the first round whose executor falls below one prelude launch.
    let mut crossover_round = 1u32;
    let mut executor_us = t1_median_us;
    while executor_us >= prelude_median_us && crossover_round < 64 {
        crossover_round += 1;
        executor_us /= 2.0;
    }
    eprintln!(
        "[seg-prelude] prelude {prelude_median_us:.3}us x R={rounds} against 2*T1 \
         {:.1}us -> per-proof share {:.4}%; crossover at round ~{crossover_round}; \
         rows floor {SEG_MIN_TIMED_ROWS} means nothing past round ~7 is measured",
        2.0 * t1_median_us,
        per_proof_share * 100.0,
    );

    record_summary_section(
        "Continuation prelude: the fold-weight build's own per-round cost",
        &format!(
            "One warp, grid 1, 11 slots. Staged OUTSIDE every timed loop, so every \
             continuation median elsewhere in this report is EXECUTOR-ONLY and a production \
             round's cost is `executor + one prelude`.\n\n\
             Serialized = an event pair around one launch on an idle stream (carries the \
             dispatch bubble); amortized = one window holding {SEG_PRELUDE_BATCH} launches, \
             divided by {SEG_PRELUDE_BATCH} (kernel-bound lower bound). \
             {SEG_WARMUP_ITERS} warmups and {SEG_TIMING_ITERS} samples per arm.\n\n{solo}\n\
             Interleaved against a real continuation executor, one process, one loop. \
             **This fraction is NOT a §6 A/B result and must not be quoted as one:** its \
             two arms are different kernels three orders of magnitude apart, it uses the \
             LEGACY interleaved protocol (fixed arm order, IID bootstrap over pairs), and \
             it emits no raw samples and no order contrast. It answers \"how much of a \
             round is the prelude\", nothing else.\n\n\
             {paired_body}\n\
             **The REPORTED quantity is the per-PROOF share, not the widest round's \
             ratio** (spec §7.2 row 7). The prelude is one launch per continuation round, \
             so with `R` rounds it costs `R * prelude` against a proof whose executor time \
             is dominated by the first two rounds (~`2 * T1`): `{rounds} x \
             {prelude_median_us:.3} us = {:.1} us` against `2 * T1 = {:.1} us` -> \
             **{:.4}%**, against the widest round's own ratio of {:.4}%. The crossover — \
             where one prelude launch costs more than the executor it gates — is at round \
             ~{crossover_round}, taking the executor to halve with the row count as this \
             cell's own progression does. `R` is `BWD_SEG_PRELUDE_ROUNDS` (default 23).\n\n\
             **ENVELOPE, stated rather than claimed.** `SEG_MIN_TIMED_ROWS = \
             {SEG_MIN_TIMED_ROWS}` is a ROW floor, so nothing past round ~7 is measured at \
             all and the entire region where the prelude dominates sits OUTSIDE the \
             measured envelope by construction. This pass adds no below-floor timing \
             mode; the tail rounds are out of scope, not claimed.\n",
            f64::from(rounds) * prelude_median_us,
            2.0 * t1_median_us,
            per_proof_share * 100.0,
            prelude_median_us / t1_median_us * 100.0,
        ),
    );
}

/// **Stage B: the AccPlacement ladder**, measured on the Stage-A winner.
///
/// Design section 6 offers three placements for a loop that lands above the
/// 40-register target, and the task's condition for building rungs (b) and (c) is
/// that the winner records more than 40 registers. On this device the GATE
/// benchmark's winner does NOT — the R0 `plane` executor is exactly 40 — but the
/// nine CONTINUATION symbols are 50-56, so the ladder is measured where the
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
                None,
                &timed,
                &parity,
                twin_shape,
                &host_eq,
                &device,
                &mut reference,
                None,
                carveout_mode(),
                false,
                &context,
            ));
            // A live twin to pair against. Rung-vs-twin is exactly a pairable
            // comparison — same cell, same rows, same buffer — so it gets the
            // NORMATIVE protocol rather than a quotient of two separately-timed
            // medians, which would carry a fixed-direction drift bias (the twin is
            // always measured first) and no interval at all.
            //
            // The twin is passed as a SHAPE, not as a prepared launchable:
            // `SegCell::prepare` launches the fold-weight prelude, so staging it here
            // would run that prelude at the PREVIOUS cell's carveout preference.
            // `measure_shape` stages it after applying the pair's plan.
            for placement in [
                BwdSegAccPlacement::AccC2Smem,
                BwdSegAccPlacement::AccBothSmem,
            ] {
                matrix.push(measure_shape(
                    benchmark,
                    None,
                    &timed,
                    &parity,
                    SegShape::rung(k, placement),
                    &host_eq,
                    &device,
                    &mut reference,
                    Some(SegBaselineArm::seg_twin(
                        STAGE_B_TWIN_BASELINE_LABEL,
                        timed.coord.regime,
                        twin_shape,
                    )),
                    carveout_mode(),
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
        let (ratio, ci, verdict) = match row.ratio.reported_estimate() {
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
            // The register-placement twin itself is timed solo; an order-coupled rung
            // has diagnostics but no quotable ratio.
            None if row.ratio.order().is_none() => {
                ("baseline".to_owned(), "-".to_owned(), "-".to_owned())
            }
            None => (
                "-".to_owned(),
                "-".to_owned(),
                row.ratio.verdict().to_owned(),
            ),
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
                None,
                &timed,
                &parity,
                shape,
                &host_eq,
                &device,
                &mut reference,
                None,
                carveout_mode(),
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
    /// The lowering's per-launch compulsory-traffic floor (spec §7.2.2) — emitted on
    /// every row, launchable or not. See [`SEG_CORPUS_CSV_HEADER`] for the zero
    /// convention.
    pub(super) floor: BwdSegTrafficFloor,
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
            // A row that produced no launch produced no descriptor either — the sweep
            // returns `OverBudget` BEFORE `try_lower`, and `LowerRejected` means there
            // is nothing to walk. Zero is the "no lowering output" reading.
            floor: BwdSegTrafficFloor::default(),
        }
    }

    /// Which timing protocol produced this row — from PAIRED-NESS, never from
    /// whether a ratio survived.
    ///
    /// A row is paired iff a baseline arm was sampled beside it. Inferring that from
    /// `ratio_vs_baseline` alone breaks under §6(a) step 6: an order-coupled cell IS
    /// timed against its baseline but carries no interval, and the old predicate then
    /// published `protocol = solo` on a row that also carried
    /// `baseline_median_us` — a self-contradiction, in the very column that exists so
    /// no table can quietly mix the two protocols.
    ///
    /// The ratio is still consulted so a schema-v1 chunk (which predates
    /// [`SEG_CORPUS_V2_COLUMN`] and therefore has no `baseline_median_us`) keeps
    /// reporting `paired`. On a v2 row the two together are unambiguous: `paired`
    /// with an empty `ratio_vs_k4` means the order gate withheld the interval, and a
    /// baseline rung says `solo` because nothing was sampled beside it.
    pub(super) fn protocol(&self) -> &'static str {
        if !self.status.measured() {
            "-"
        } else if self.baseline_median_us.is_some() || self.ratio_vs_baseline.is_some() {
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
/// **Schema v3.** v1 was this without `baseline_median_us`, v2 without the two floor
/// columns, and the reader accepts all three — see [`parse_corpus_csv`].
/// `baseline_median_us` was added because the row already computed the paired
/// baseline's median and then threw it away, which left `median_us` carrying two
/// different protocols in one column (a solo median on the `K = 4` baseline row, an
/// interleaved candidate median on every other row) with no way to recover the missing
/// half. The `K` policy never saw it — it reads paired ratios only — but the D2 verdict
/// consumes raw medians, and a reader cannot tell the two apart from the number.
///
/// **`floor_dram_read_bytes` / `floor_dram_write_bytes` are LOWERING properties, not
/// measurements** (spec §7.2.2), so they are emitted on every row including rows whose
/// cell never launched. **ZERO in both is reserved for "no lowering output"** — the
/// lowering was rejected, or the coordinate was over budget and therefore never lowered
/// — and is distinguishable from a real floor, which is always positive because the eq
/// term alone is nonzero for any live launch. An absent column, a rejected row and an
/// over-budget row therefore all read the same way, which is correct: none of them
/// carries a measurement.
pub(super) const SEG_CORPUS_CSV_HEADER: &str = "circuit,layer,class,regime,round,d2_policy,terms,\
sources,windows,bf_sources,e4_sources,procedural_sources,total_static_work,bytes_per_row,rows,\
grid_blocks,k,status,blocks_per_sm,theoretical_occupancy_percent,registers,dynamic_smem_bytes,\
waves,max_over_mean_work,parity,protocol,median_us,min_us,baseline_median_us,ratio_vs_k4,ci_low,\
ci_high,floor_dram_read_bytes,floor_dram_write_bytes\n";

/// The one column schema v1 lacks. Absent from an on-disk v1 chunk, and its
/// absence is not an error: the sweeps that produced this workspace's tables ran
/// before it existed, and regenerating 12 locked chunk runs to add a column that
/// no conclusion depends on would be a worse trade than reading both schemas.
pub(super) const SEG_CORPUS_V2_COLUMN: &str = "baseline_median_us";

/// The FIRST of the two columns schema v2 lacks, and the marker for the pair: the
/// locked chunk runs on disk predate the traffic floors, so their absence defaults both
/// fields to zero — which is exactly the "no lowering output" reading a v2 row honestly
/// has. Same precedent, same reason as [`SEG_CORPUS_V2_COLUMN`].
pub(super) const SEG_CORPUS_V3_COLUMN: &str = "floor_dram_read_bytes";

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
             {},{},{},{},{},{ratio},{low},{high},{},{}",
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
            row.floor.read_bytes,
            row.floor.write_bytes,
        )
        .expect("write String");
    }
    out
}

/// Read a corpus CSV back, schema v1, v2 or v3.
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
    // The two floor columns arrived together, so the v3 marker covers both.
    let optional_column = |column: &str| {
        column == SEG_CORPUS_V2_COLUMN
            || column == SEG_CORPUS_V3_COLUMN
            || column == "floor_dram_write_bytes"
    };
    for column in SEG_CORPUS_CSV_HEADER.trim_end().split(',') {
        assert!(
            index(column).is_some() || optional_column(column),
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
    let (floor_read, floor_write) = (index(SEG_CORPUS_V3_COLUMN), index("floor_dram_write_bytes"));
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
                // A v1/v2 chunk has no floor columns; zero is its honest reading.
                floor: BwdSegTrafficFloor {
                    read_bytes: floor_read
                        .map_or(0, |at| field[at].parse().expect("floor read bytes")),
                    write_bytes: floor_write
                        .map_or(0, |at| field[at].parse().expect("floor write bytes")),
                },
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

/// Rows every census cell is lowered at.
///
/// The census's two DISTRIBUTIONS (`num_foldable`, `n_coefficients`) are row-INDEPENDENT
/// lowering properties, so lowering at the parity twin's row count keeps the walk cheap
/// while the footprint bound below is stated at the corpus's own median FITTED row count
/// instead.
///
/// **THE TWO FLOOR COLUMNS DO NOT RESCALE THE SAME WAY, and a naive rescale of the read
/// column is badly wrong.** The WRITE floor is row-LINEAR: it is
/// `(num_foldable * 2 + 2) * rows * 16` and nothing else. The READ floor is AFFINE — a
/// row-linear source part plus terms that do NOT move with rows:
///
///   * the eq slab `min(rows, 1 << eq_sizes.low) * 16`, which SATURATES at
///     `(1 << low) * 16` once `rows >= 1 << low` and is then a constant; and
///   * under `CoeffMode::DevPtr` / `ProgramMode::DevPtr`, the coefficient and program
///     payloads (`n_coefficients * 16` and `program_words * 2`), which are properties of
///     the program, not of the row count. (The census emits `const`/`inline` only, so its
///     own rows carry neither — but a rescaler reading this convention elsewhere must.)
///
/// Multiplying a census read floor by `N / SEG_CENSUS_ROWS` therefore multiplies the
/// saturated slab too, and the error is the whole slab scaled: `slab * (N/rows − 1)`. Its
/// SIZE relative to the floor is what varies — the thinner a coordinate's row-linear part,
/// or the smaller the row basis, the worse it gets, without bound. **Correct rescaling
/// subtracts the row-independent terms, scales only the row-linear remainder, and adds them
/// back**; the emitted census line names the slab's size, so the subtraction is available to
/// a reader, and reports the worst overstatement a naive rescale of THIS census would
/// actually produce rather than a hypothetical one.
const SEG_CENSUS_ROWS: usize = SEG_PARITY_ROWS;

/// **P5(b): the per-launch distribution of `num_foldable` and `n_coefficients`,
/// from a lowering walk over the corpus.** No GPU TIMING and no runtime readback —
/// but it is GPU WORK, because `SegCell::build` allocates device memory and the
/// round binding carries device pointers, so `try_lower` is not reachable from a
/// host-only path without a second lowering entry point this pass has no mandate to
/// add. Runs under the lock; the numbers are still a lowering property.
///
/// **What it does and does not do (M6).** It bounds CAPACITY FEASIBILITY; it does
/// NOT decide residency. `num_foldable KiB x resident_blocks` counts *published
/// endpoint* bytes only — not raw fold traffic, not program/constant/eq traffic,
/// not replacement, and not which published sources are actually re-read;
/// `n_coefficients` likewise omits access frequency and distribution. So these are
/// FOOTPRINT BOUNDS AND CORRELATES, reported as such. A residency conclusion would
/// additionally need live fold-source and read-use counts plus a coefficient
/// working-set/access histogram, which is out of scope here and belongs with the
/// phase model.
#[test]
#[ignore = "corpus lowering walk over device-bound cells; run under with_gpu_lock.sh"]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_seg_lowering_footprint_census() {
    let budget = corpus_budget_bytes();
    let context = make_seg_spike_context(SEG_CONT_ARENA_BYTES);
    let (eq_low, eq_sizes) = build_shared_eq(24, &context);

    let mut foldable: Vec<u32> = Vec::new();
    let mut coefficients: Vec<u32> = Vec::new();
    // The corpus's own fitted row counts, so the footprint bound below is stated at the
    // depth the sweep actually measures rather than at the census's cheap one.
    let mut fitted_rows: Vec<usize> = Vec::new();
    let mut rejections: Vec<String> = Vec::new();
    let mut over_budget = 0usize;
    // The read floor's ROW-INDEPENDENT part, so a reader can subtract it before rescaling.
    // It is one number for the whole census: every cell shares this eq table and this row
    // count, and the census emits `const`/`inline` only, so there is no DevPtr payload to
    // add to it.
    let mut eq_slab_bytes: Option<u64> = None;
    // The thinnest read floor the census lowered — the cell where a naive rescale of the
    // read column is worst, and therefore the one that bounds the warning.
    let mut min_read: Option<u64> = None;
    let mut out = String::from(
        "circuit,layer,class,k,coeff,program,status,num_foldable,n_coefficients,\
floor_dram_read_bytes,floor_dram_write_bytes,sources_priced,dead_sources,distinct_backings\n",
    );

    // The coordinates `bwd_seg_corpus_sweep` walks, through its OWN enumeration
    // (`SEG_CORPUS_LAYOUTS` x `seg_coordinate_layers` x `SEG_ROUND_CLASSES` x
    // `SEG_CORPUS_K`) rather than a restatement of it.
    for circuit in SEG_CORPUS_LAYOUTS {
        for layer in seg_coordinate_layers(circuit) {
            for class in SEG_ROUND_CLASSES {
                let regime = class.regime();
                let coord = lean_coordinate(circuit, layer, regime);
                let round = class.round();
                let d2 = class.d2();
                let probe = probe_geometry(&coord, round, d2);
                let (top_rows, _) = fit_rows(
                    SEG_CORPUS_TARGET_ROWS,
                    probe.bytes_per_row,
                    budget,
                    SEG_CORPUS_MIN_ROWS,
                );
                // The sweep returns `OverBudget` BEFORE lowering, so the census records
                // the same verdict rather than inventing a lowering the sweep never did.
                let budgeted = top_rows.saturating_mul(probe.bytes_per_row) <= budget;
                if !budgeted {
                    over_budget += 1;
                }
                let cell = budgeted.then(|| {
                    SegCell::build(
                        Arc::clone(&coord),
                        round,
                        SEG_CENSUS_ROWS,
                        false,
                        d2,
                        eq_low.as_ptr(),
                        eq_sizes,
                        &context,
                    )
                });
                let mut counted = false;
                for k in SEG_CORPUS_K {
                    let shape = corpus_shape(k);
                    let label = format!(
                        "{},{layer},{},{k},{},{}",
                        short_name(circuit),
                        class.label(),
                        coeff_label(shape.coeff),
                        program_label(shape.program),
                    );
                    let Some(cell) = cell.as_ref() else {
                        writeln!(out, "{label},over-budget,0,0,0,0,0,0,0").expect("write String");
                        continue;
                    };
                    // A coordinate host lowering REJECTS is recorded with its rejection;
                    // it must not take the chunk with it.
                    match cell.try_lower(shape) {
                        Err(error) => {
                            rejections.push(format!("{label} -> {error:?}"));
                            writeln!(out, "{label},lower-rejected,0,0,0,0,0,0,0")
                                .expect("write String");
                        }
                        Ok(setup) => {
                            let (num_foldable, n_coefficients, eq_low_bits, logical_rows) =
                                match &setup.desc {
                                    BwdSegLaunchDesc::Inline(desc) => (
                                        u32::from(desc.num_foldable),
                                        desc.n_coefficients,
                                        desc.eq_sizes.low,
                                        u64::from(desc.logical_rows),
                                    ),
                                    BwdSegLaunchDesc::ProgPtr(desc) => (
                                        u32::from(desc.num_foldable),
                                        desc.n_coefficients,
                                        desc.eq_sizes.low,
                                        u64::from(desc.logical_rows),
                                    ),
                                };
                            // The eq slab, by the walk's own rule. Recorded once and
                            // asserted stable: if it ever differs between two census cells
                            // the "one row-independent part" statement below is wrong.
                            let slab = if eq_low_bits >= 63 {
                                logical_rows
                            } else {
                                logical_rows.min(1u64 << eq_low_bits)
                            } * size_of::<E4>() as u64;
                            match eq_slab_bytes {
                                None => eq_slab_bytes = Some(slab),
                                Some(seen) => assert_eq!(
                                    seen, slab,
                                    "{label}: the census assumes ONE eq slab for every cell",
                                ),
                            }
                            let floor = bwd_seg_traffic_floor(&setup, shape.coeff, shape.program);
                            // The THINNEST read floor is where a naive rescale is worst, so
                            // the warning below quotes a measured bound, not a guess.
                            min_read = Some(min_read.unwrap_or(u64::MAX).min(floor.read_bytes));
                            // The §7.3 discriminator columns (R11): dead slots the
                            // walk must not price, and `(window, column)` keys per
                            // physical backing.
                            let backing = bwd_seg_floor_backing_census(&setup);
                            foldable.push(num_foldable);
                            coefficients.push(n_coefficients);
                            counted = true;
                            writeln!(
                                out,
                                "{label},lowered,{num_foldable},{n_coefficients},{},{},{},{},{}",
                                floor.read_bytes,
                                floor.write_bytes,
                                backing.priced_sources,
                                setup.dead_sources.len(),
                                backing.distinct_backings,
                            )
                            .expect("write String");
                        }
                    }
                }
                if counted {
                    fitted_rows.push(top_rows);
                }
                drop(cell);
            }
        }
    }

    let path = seg_output_path("seg_lowering_footprint_census.csv");
    publish(&path, &out);
    assert!(
        !foldable.is_empty() && !coefficients.is_empty(),
        "the census is non-vacuous"
    );

    let quantiles = |values: &mut Vec<u32>| -> (u32, u32, u32, u32) {
        values.sort_unstable();
        let at = |fraction: f64| values[((values.len() - 1) as f64 * fraction) as usize];
        (values[0], at(0.5), at(0.9), values[values.len() - 1])
    };
    let count = foldable.len();
    let (fold_min, fold_median, fold_p90, fold_max) = quantiles(&mut foldable);
    let (coeff_min, coeff_median, coeff_p90, coeff_max) = quantiles(&mut coefficients);
    fitted_rows.sort_unstable();
    let median_rows = fitted_rows[fitted_rows.len() / 2];
    // The published-endpoint footprint BOUND, not a residency claim: only the bytes
    // `seg_fold_and_publish` stores, at the corpus's median fitted row count.
    let endpoint_bytes = |num_foldable: u32| -> u64 {
        u64::from(num_foldable) * 2 * median_rows as u64 * size_of::<E4>() as u64
    };
    eprintln!(
        "[seg-census] {count} lowered cells over {} coordinates ({over_budget} over-budget \
         coordinates, {} lowering rejections)\n\
         [seg-census] num_foldable:    min {fold_min} median {fold_median} p90 {fold_p90} \
         max {fold_max}\n\
         [seg-census] n_coefficients: min {coeff_min} median {coeff_median} p90 {coeff_p90} \
         max {coeff_max}\n\
         [seg-census] published-endpoint footprint BOUND at the corpus median {median_rows} \
         rows (`num_foldable * 2 * rows * 16 B`): median {:.1} MiB, p90 {:.1} MiB, max {:.1} \
         MiB -- a CAPACITY-FEASIBILITY bound, NOT a residency conclusion\n\
         [seg-census] -> {}",
        fitted_rows.len(),
        rejections.len(),
        endpoint_bytes(fold_median) as f64 / (1u64 << 20) as f64,
        endpoint_bytes(fold_p90) as f64 / (1u64 << 20) as f64,
        endpoint_bytes(fold_max) as f64 / (1u64 << 20) as f64,
        path.display(),
    );
    // The CSV's own floor basis AND its rescaling rule, stated where a reader of the table
    // will see it. The two columns do NOT rescale the same way and the read column is the
    // trap: multiplying it by `fitted_rows / SEG_CENSUS_ROWS` multiplies the eq slab too,
    // which does not move with rows.
    let slab = eq_slab_bytes.expect("a non-vacuous census recorded its eq slab");
    let thinnest = min_read.expect("a non-vacuous census lowered at least one cell");
    // The worst a naive whole-column rescale to the corpus median would overstate: it is
    // maximized at the thinnest read floor, because the error is the fixed slab scaled.
    let factor = median_rows as f64 / SEG_CENSUS_ROWS as f64;
    let naive = thinnest as f64 * factor;
    let correct = (thinnest - slab) as f64 * factor + slab as f64;
    eprintln!(
        "[seg-census] the CSV's floor columns are at {SEG_CENSUS_ROWS} rows. \
         floor_dram_write_bytes is row-LINEAR: `(num_foldable * 2 + 2) * rows * 16`. \
         floor_dram_read_bytes is AFFINE, NOT linear -- a row-linear source part PLUS \
         row-independent terms: the eq slab, {slab} B here (`min(rows, 1 << eq_sizes.low) \
         * 16`, saturated at this row count and identical for every census cell), and under \
         a DevPtr loader the coefficient / program payloads (these rows are const/inline, so \
         they carry none).\n\
         [seg-census] TO RESCALE a read floor to N rows: SUBTRACT {slab} B, scale the \
         remainder by N/{SEG_CENSUS_ROWS}, add {slab} B back. Scaling the WHOLE column \
         scales the slab too and overstates the floor; on this census's thinnest cell \
         ({thinnest} B) a naive rescale to the corpus median {median_rows} rows reads \
         {:.2} MB against the correct {:.2} MB (+{:.1}%), and the gap grows without bound \
         as the row-linear part thins. The footprint bound above is the one figure already \
         restated at the corpus median.",
        naive / 1e6,
        correct / 1e6,
        (naive / correct - 1.0) * 100.0,
    );
    for rejection in &rejections {
        eprintln!("[seg-census] LOWER REJECTED {rejection}");
    }
    drop(eq_low);
}

/// **The fragment-vs-term coefficient-mul census (RR, 2026-07-30).** The NCU
/// stall capture put the continuation bottleneck on the FMA-heavy pipe, and the
/// eval loop's full `E4 x E4` muls are what feeds it. Distribution folded
/// `challenge_core x bf_immediate` into one opaque per-term bank coefficient, so
/// every term pays a FULL coefficient mul per projection; an undistributed
/// (fragment/relation) evaluation on the SAME thread-owns-row executor would pay
/// a `BF x E4` immediate mul per term plus ONE full core mul per group instead.
/// This census reconstructs the grouping post-hoc from the symbolic recipes —
/// two terms share a group iff their `NormalizedCoefficientRecipe`s are equal
/// after dividing out the leading scalar (the scalar IS the BF immediate; the
/// quotient is the challenge core, and an internal challenge factor lands in the
/// core, splitting the group, which prices it correctly) — and counts the mul
/// work of both forms.
///
/// Ext regime only (per RR: R0's semantics differ and it is DRAM-bound anyway).
/// What is IDENTICAL in both forms and therefore excluded: the source-product
/// muls per term are COUNTED but do not move; fold/resolve work; the eq factor;
/// `c_init`; the epilogue; e4 adds (a group adds one extra accumulate per term
/// and one per group, against the fma-folded adds of the term form — mul-pipe
/// pressure is the question, and adds are not muls). Weightings: a full
/// `E4 x E4` at 9 bf-mul units (Karatsuba, charitable to the current form) and
/// 16 (schoolbook); `BF x E4` is exactly 4.
///
/// Pure lowering walk — no GPU, no timing, no context.
#[test]
fn bwd_seg_fragment_coefficient_census() {
    use std::collections::HashMap;

    use gkr_eval_isa::bwd::coeff::model::{
        CoeffProduct, CoeffTerm, CoefficientRecipeId, NormalizedCoefficientRecipe,
    };

    use crate::primitives::field::BF;
    use crate::upstream::PrimeField;

    let bf = BF::from_u32_with_reduction;
    let neg_one = {
        let mut v = BF::ONE;
        v.negate();
        v.as_u32_reduced()
    };

    // (core, immediate): the challenge core with its leading scalar divided out
    // (`None` = trivial core, i.e. the recipe is a bare scalar), and the reduced
    // immediate.
    let split = |layer: &gkr_eval_isa::bwd::coeff::model::CoeffLayer,
                 id: CoefficientRecipeId|
     -> (Option<NormalizedCoefficientRecipe>, u32) {
        if id == CoefficientRecipeId::ONE {
            return (None, 1);
        }
        if id == CoefficientRecipeId::NEG_ONE {
            return (None, neg_one);
        }
        let recipe = layer
            .banked_recipe(id)
            .expect("a committed layer banks every non-reserved coefficient id");
        assert!(
            !recipe.terms.is_empty(),
            "a zero coefficient is never encoded"
        );
        let immediate = recipe.terms[0].scalar;
        if recipe.terms.len() == 1 && recipe.terms[0].challenges.is_empty() {
            return (None, immediate);
        }
        let inverse = bf(immediate)
            .inverse()
            .expect("a banked scalar is nonzero and BF is a field");
        let core = NormalizedCoefficientRecipe::from_terms(
            recipe
                .terms
                .iter()
                .map(|product| {
                    let mut scaled = bf(product.scalar);
                    scaled.mul_assign(&inverse);
                    CoeffProduct {
                        scalar: scaled.as_u32_reduced(),
                        challenges: product.challenges.clone(),
                    }
                })
                .collect(),
        );
        (Some(core), immediate)
    };

    let mut out = String::from(
        "circuit,layer,terms,t_c0lin,t_c2,t_dual,t_standalone,groups,group_median,\
group_p90,group_max,imm_free,imm_bf,full_term,full_rel,bfe4_rel,\
saving_pct_karatsuba,saving_pct_schoolbook\n",
    );
    let mut corpus_full_term = 0u64;
    let mut corpus_full_rel = 0u64;
    let mut corpus_bfe4_rel = 0u64;
    let mut corpus_terms = 0u64;
    let mut corpus_groups = 0u64;

    for circuit in SEG_CORPUS_LAYOUTS {
        for layer_index in seg_coordinate_layers(circuit) {
            let coord = lean_coordinate(circuit, layer_index, BwdRegime::Ext);
            let layer = &coord.layer;

            let (mut t_c0lin, mut t_c2, mut t_dual) = (0u64, 0u64, 0u64);
            let (mut imm_free, mut imm_bf) = (0u64, 0u64);
            // Full muls the CURRENT form pays: per-projection coefficient muls
            // plus the (representation-invariant) source products.
            let mut full_term = 0u64;
            // The relation form: unchanged products + per-group core muls; the
            // immediates move to the BF x E4 column.
            let mut full_rel = 0u64;
            let mut bfe4_rel = 0u64;
            // group -> (has_c0_content, has_c2_content, member terms)
            let mut groups: HashMap<NormalizedCoefficientRecipe, (bool, bool, u64)> =
                HashMap::new();

            for term in &layer.terms {
                let (products, coeff_uses, c0, c2, coefficient) = match term {
                    CoeffTerm::C0Linear { coefficient, .. } => {
                        (0u64, 1u64, true, false, coefficient)
                    }
                    CoeffTerm::C2Product { coefficient, .. } => (1, 1, false, true, coefficient),
                    CoeffTerm::DualProduct { coefficient, .. } => (2, 2, true, true, coefficient),
                };
                match term {
                    CoeffTerm::C0Linear { .. } => t_c0lin += 1,
                    CoeffTerm::C2Product { .. } => t_c2 += 1,
                    CoeffTerm::DualProduct { .. } => t_dual += 1,
                }
                full_term += products + coeff_uses;
                full_rel += products;
                let (core, immediate) = split(layer, *coefficient);
                if immediate == 1 || immediate == neg_one {
                    imm_free += 1;
                } else {
                    imm_bf += 1;
                    bfe4_rel += coeff_uses;
                }
                if let Some(core) = core {
                    let entry = groups.entry(core).or_insert((false, false, 0));
                    entry.0 |= c0;
                    entry.1 |= c2;
                    entry.2 += 1;
                }
            }
            let group_count = groups.len() as u64;
            let mut grouped_terms = 0u64;
            for (has_c0, has_c2, members) in groups.values() {
                full_rel += u64::from(*has_c0) + u64::from(*has_c2);
                grouped_terms += members;
            }
            // The K-split takes GROUPS as its unit (a term-granular stripe would
            // scatter every ~2-term group across warps and re-pay the core mul
            // per fragment per warp), so the balance question is the group-size
            // TAIL: a monster group pins one warp. Standalone terms (bare-scalar
            // coefficients, no core) stripe freely as today.
            let mut sizes: Vec<u64> = groups.values().map(|(_, _, members)| *members).collect();
            sizes.sort_unstable();
            let at = |fraction: f64| -> u64 {
                if sizes.is_empty() {
                    0
                } else {
                    sizes[((sizes.len() - 1) as f64 * fraction) as usize]
                }
            };
            let (group_median, group_p90, group_max) =
                (at(0.5), at(0.9), sizes.last().copied().unwrap_or(0));

            let terms = layer.terms.len() as u64;
            let t_standalone = terms - grouped_terms;
            let saving = |full_weight: f64| -> f64 {
                let term_units = full_term as f64 * full_weight;
                let rel_units = full_rel as f64 * full_weight + bfe4_rel as f64 * 4.0;
                (1.0 - rel_units / term_units) * 100.0
            };
            writeln!(
                out,
                "{},{layer_index},{terms},{t_c0lin},{t_c2},{t_dual},{t_standalone},\
{group_count},{group_median},{group_p90},{group_max},{imm_free},{imm_bf},\
{full_term},{full_rel},{bfe4_rel},{:.2},{:.2}",
                short_name(circuit),
                saving(9.0),
                saving(16.0),
            )
            .expect("write String");

            corpus_full_term += full_term;
            corpus_full_rel += full_rel;
            corpus_bfe4_rel += bfe4_rel;
            corpus_terms += terms;
            corpus_groups += group_count;
        }
    }

    let path = seg_output_path("seg_fragment_coeff_census.csv");
    publish(&path, &out);
    assert!(corpus_terms > 0, "the census is non-vacuous");
    let total = |weight: f64| -> (f64, f64) {
        let term_units = corpus_full_term as f64 * weight;
        let rel_units = corpus_full_rel as f64 * weight + corpus_bfe4_rel as f64 * 4.0;
        (term_units, rel_units)
    };
    let (term9, rel9) = total(9.0);
    let (term16, rel16) = total(16.0);
    eprintln!(
        "[seg-frag-census] Ext corpus: {corpus_terms} terms -> {corpus_groups} nontrivial \
         challenge-core groups; full E4xE4 muls {corpus_full_term} (term form) vs \
         {corpus_full_rel} + {corpus_bfe4_rel} BFxE4 (relation form)\n\
         [seg-frag-census] eval-loop mul-work saving: {:.2}% at 9:4 (Karatsuba), {:.2}% at \
         16:4 (schoolbook) -- products, folds, eq, adds identical in both forms and excluded\n\
         [seg-frag-census] -> {}",
        (1.0 - rel9 / term9) * 100.0,
        (1.0 - rel16 / term16) * 100.0,
        path.display(),
    );
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

    // Lower every `K` BEFORE launching anything. The work model AND the traffic floor
    // are properties of the lowering, so this is also how an unlaunchable or rejected
    // cell still contributes its `max_over_mean` and its floor.
    let lowered: Vec<Result<(ListWorkStats, BwdSegTrafficFloor), BwdSegLowerError>> = SEG_CORPUS_K
        .into_iter()
        .map(|k| {
            let shape = corpus_shape(k);
            timed.try_lower(shape).map(|setup| {
                let floor = bwd_seg_traffic_floor(&setup, shape.coeff, shape.program);
                (setup.work, floor)
            })
        })
        .collect();
    facts.total_static_work = SEG_CORPUS_K
        .into_iter()
        .zip(lowered.iter())
        .find_map(|(k, lowering)| {
            lowering
                .as_ref()
                .ok()
                .map(|(work, _)| (work.mean_work * k as f64).round() as u64)
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
    // The twin is carried as a SHAPE, not as a prepared launchable: `SegCell::prepare`
    // launches the fold-weight prelude, so staging it out here would run that prelude
    // at the previous cell's carveout preference on every subsequent `K`.
    // `measure_shape` stages it per cell, after applying that cell's plan.
    let twin: Option<SegShape> = match &lowered[0] {
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
        Ok((work, floor)) => {
            let row = measure_shape(
                &benchmark,
                None,
                &timed,
                parity,
                baseline_shape,
                eq,
                device,
                &mut reference,
                None,
                carveout_mode(),
                profile_k == Some(SEG_CORPUS_BASELINE_K),
                context,
            );
            let launchable = row.launchable();
            out.push(corpus_row(facts.clone(), *work, *floor, &row, below_floor));
            launchable.then_some(baseline_shape)
        }
    };

    for (index, k) in SEG_CORPUS_K.into_iter().enumerate().skip(1) {
        let (work, floor) = match &lowered[index] {
            Err(error) => {
                eprintln!("[seg-corpus] {benchmark} K{k}: LOWER REJECTED {error:?}");
                out.push(SegCorpusRow::untimed(
                    facts.clone(),
                    k,
                    SegCorpusStatus::LowerRejected,
                ));
                continue;
            }
            Ok((work, floor)) => (*work, *floor),
        };
        let shape = corpus_shape(k);
        let row = measure_shape(
            &benchmark,
            None,
            &timed,
            parity,
            shape,
            eq,
            device,
            &mut reference,
            twin.map(|twin_shape| {
                SegBaselineArm::seg_twin(SEG_CORPUS_BASELINE_LABEL, timed.coord.regime, twin_shape)
            }),
            carveout_mode(),
            profile_k == Some(k),
            context,
        );
        out.push(corpus_row(facts.clone(), work, floor, &row, below_floor));
    }

    drop(timed);
    out
}

/// Fold one measured [`SegMatrixRow`] and the coordinate's facts into a corpus row.
fn corpus_row(
    facts: SegCoordFacts,
    work: ListWorkStats,
    floor: BwdSegTrafficFloor,
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
        // Through `selectable()`: the corpus ratio feeds `corpus_best_k`, which is a
        // DECISION, so an order-coupled cell contributes no ratio to it.
        ratio_vs_baseline: status
            .measured()
            .then(|| row.ratio.selectable().map(|(estimate, _)| estimate))
            .flatten(),
        // NOT gated on `measured()`: the floor is a lowering property, and this row's
        // lowering succeeded regardless of whether the cell could be launched or timed.
        floor,
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

    /// A blocked sample set from a per-sample cost function, so the census and
    /// bootstrap properties are testable without a GPU. The cost sees the block's
    /// ORIENTATION and the sample's WITHIN-BLOCK SLOT as well as the global order,
    /// because an order effect is a function of what ran before — a cost that depends
    /// only on `order % 2` is invisible to the contrast (each orientation gets one
    /// even and one odd candidate slot, so the means match identically).
    fn blocked_fixture(
        seed: u64,
        cost: impl Fn(SegArm, SegBlockOrientation, usize, usize) -> f64,
    ) -> SegBlockedSamples {
        let schedule = seg_schedule(seed);
        let mut order_id = 0usize;
        let blocks = schedule
            .blocks
            .iter()
            .map(|plan| {
                let first_order_id = order_id;
                let mut cand = Vec::new();
                let mut inc = Vec::new();
                for (slot, arm) in plan.orientation.arms().into_iter().enumerate() {
                    let micros = cost(arm, plan.orientation, slot, order_id);
                    match arm {
                        SegArm::A => cand.push(micros),
                        SegArm::B => inc.push(micros),
                    }
                    order_id += 1;
                }
                SegBlockSample {
                    plan: *plan,
                    first_order_id,
                    candidate_us: [cand[0], cand[1]],
                    incumbent_us: [inc[0], inc[1]],
                }
            })
            .collect();
        SegBlockedSamples { schedule, blocks }
    }

    fn flat_cost(
        candidate: f64,
        incumbent: f64,
    ) -> impl Fn(SegArm, SegBlockOrientation, usize, usize) -> f64 {
        move |arm, _, _, _| match arm {
            SegArm::A => candidate,
            SegArm::B => incumbent,
        }
    }

    #[test]
    fn the_schedule_balances_orientation_and_the_superblock_census() {
        for seed in [SEG_SCHEDULE_SEED, SEG_SCHEDULE_SEED ^ 1] {
            let schedule = seg_schedule(seed);
            assert_eq!(schedule.timed.len(), 8, "8 timed superblocks");
            assert_eq!(schedule.blocks.len(), 16, "16 two-pair blocks");
            let abba = schedule
                .blocks
                .iter()
                .filter(|b| b.orientation == SegBlockOrientation::Abba)
                .count();
            assert_eq!(
                (abba, 16 - abba),
                (8, 8),
                "orientation balance is exact 8/8"
            );
            // The warmup's last superblock leads the timed sequence, so the leading
            // boundary is COUNTED and nothing is excluded.
            assert_eq!(*schedule.warmup.last().unwrap(), schedule.timed[0]);
            assert_eq!(
                schedule
                    .blocks
                    .iter()
                    .filter(|b| b.boundary_source == SegBoundarySource::WarmupSupplied)
                    .count(),
                1,
                "exactly one warmup-supplied boundary; the other 15 are internal"
            );
            // Superblock-level census: self 3/3, cross 1/1 — exact, no residual.
            let types = {
                let mut all = schedule.warmup.clone();
                all.extend(schedule.timed.iter().copied());
                all
            };
            let mut census = std::collections::BTreeMap::new();
            for pair in types.windows(2).skip(SEG_WARMUP_SUPERBLOCKS - 1) {
                let class = match (pair[0], pair[1]) {
                    (SegSuperblockType::X, SegSuperblockType::Y) => SegTransitionClass::SelfB,
                    (SegSuperblockType::Y, SegSuperblockType::X) => SegTransitionClass::SelfA,
                    (SegSuperblockType::X, SegSuperblockType::X) => SegTransitionClass::BToA,
                    (SegSuperblockType::Y, SegSuperblockType::Y) => SegTransitionClass::AToB,
                };
                *census.entry(class).or_insert(0usize) += 1;
            }
            assert_eq!(census[&SegTransitionClass::SelfA], 3);
            assert_eq!(census[&SegTransitionClass::SelfB], 3);
            assert_eq!(census[&SegTransitionClass::AToB], 1);
            assert_eq!(census[&SegTransitionClass::BToA], 1);
        }
    }

    /// Spec §6(a)'s STRONGEST form of the balance claim: over the whole timed
    /// sequence the census is balanced in both directions — 64 incoming transitions
    /// (8 outer + 56 interior) split self-A 11 / self-B 11 / A->B 21 / B->A 21.
    /// Verified here by enumeration, in both mirrors.
    #[test]
    fn the_sample_level_census_is_eleven_eleven_twentyone_twentyone() {
        for seed in [SEG_SCHEDULE_SEED, SEG_SCHEDULE_SEED ^ 1] {
            let schedule = seg_schedule(seed);
            let mut previous = schedule.warmup.last().unwrap().blocks()[1].last();
            let mut census = std::collections::BTreeMap::new();
            let mut total = 0usize;
            for block in &schedule.blocks {
                for arm in block.orientation.arms() {
                    *census
                        .entry(SegTransitionClass::of(previous, arm))
                        .or_insert(0usize) += 1;
                    previous = arm;
                    total += 1;
                }
            }
            assert_eq!(total, 64, "16 blocks x 4 samples");
            assert_eq!(census[&SegTransitionClass::SelfA], 11);
            assert_eq!(census[&SegTransitionClass::SelfB], 11);
            assert_eq!(census[&SegTransitionClass::AToB], 21);
            assert_eq!(census[&SegTransitionClass::BToA], 21);
        }
    }

    #[test]
    fn the_joint_stratum_census_is_three_five_three_five_in_both_mirrors() {
        for seed in [SEG_SCHEDULE_SEED, SEG_SCHEDULE_SEED ^ 1] {
            let samples = blocked_fixture(seed, flat_cost(90.0, 100.0));
            assert_eq!(
                samples.stratum_census(),
                [3, 5, 3, 5],
                "joint (orientation, incoming) census is fixed by construction"
            );
            assert!((samples.point_ratio() - 0.9).abs() < 1e-12);
        }
    }

    /// Inspects ACTUAL REPLICATES, not the observed set: the invariant is that every
    /// replicate reproduces both the 3/5/3/5 stratum composition and, from it, the
    /// 8/8 orientation balance.
    #[test]
    fn every_replicate_preserves_both_compositions() {
        let samples = blocked_fixture(SEG_SCHEDULE_SEED, |arm, _, _, order| match arm {
            SegArm::A => 90.0 + order as f64,
            SegArm::B => 100.0,
        });
        assert_eq!(samples.stratum_census(), [3, 5, 3, 5]);
        let counts = samples.replicate_stratum_counts(512);
        assert_eq!(counts.len(), 512);
        for (index, counts) in counts.iter().enumerate() {
            assert_eq!(
                *counts,
                [3, 5, 3, 5],
                "replicate {index} lost its composition"
            );
            assert_eq!(counts.iter().sum::<usize>(), SEG_TIMED_BLOCKS);
            assert_eq!(counts[0] + counts[1], 8, "replicate {index}: ABBA balance");
            assert_eq!(counts[2] + counts[3], 8, "replicate {index}: BAAB balance");
        }
    }

    #[test]
    fn the_stratified_bootstrap_reproduces_a_known_interval() {
        // A constant ratio must give a degenerate interval, exactly. Any resampling
        // that mixed arms or lost the pairing would widen it.
        let samples = blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(80.0, 100.0));
        let estimate = samples.estimate_stratified();
        for value in [estimate.median_ratio, estimate.ci_low, estimate.ci_high] {
            assert!((value - 0.8).abs() < 1e-12, "{estimate:?}");
        }
        // Seeded: re-deriving from the same samples gives the same numbers.
        let again = samples.estimate_stratified();
        assert_eq!(
            (estimate.ci_low, estimate.ci_high),
            (again.ci_low, again.ci_high)
        );
    }

    #[test]
    fn the_order_contrast_is_zero_on_order_independent_input() {
        let samples = blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(95.0, 100.0));
        let order = samples.order_interaction();
        assert!(order.delta_order_pct.abs() < 1e-9, "{order:?}");
        assert!(order.passes(), "{order:?}");
    }

    /// The gate must genuinely FIRE. The coupling is made a function of the block's
    /// ORIENTATION — the candidate pays 4% more in `BAAB` blocks, where it never
    /// leads — which is exactly the confound §1(d) says is unidentifiable from the
    /// existing fixed-order samples.
    #[test]
    fn the_order_gate_fails_on_a_materially_order_coupled_cell() {
        let samples = blocked_fixture(SEG_SCHEDULE_SEED, |arm, orientation, _, _| match arm {
            SegArm::A => {
                if orientation == SegBlockOrientation::Baab {
                    104.0
                } else {
                    100.0
                }
            }
            SegArm::B => 100.0,
        });
        let order = samples.order_interaction();
        assert!(
            order.delta_order_pct < -3.0,
            "the fixture must produce a real contrast; got {order:?}"
        );
        assert!(
            !order.passes(),
            "the WHOLE CI must sit inside +/-{SEG_ORDER_EQUIVALENCE_PCT}%; got {order:?}"
        );
    }

    #[test]
    fn the_decision_rule_returns_unresolved_on_two_of_three() {
        let ok = SegOrderInteraction {
            delta_order_pct: 0.0,
            ci_low_pct: -0.05,
            ci_high_pct: 0.05,
        };
        let inverted = RatioEstimate {
            median_ratio: 0.97,
            ci_low: 0.965,
            ci_high: 0.975,
        };
        let straddles = RatioEstimate {
            median_ratio: 0.999,
            ci_low: 0.99,
            ci_high: 1.01,
        };
        let regressed = RatioEstimate {
            median_ratio: 1.03,
            ci_low: 1.02,
            ci_high: 1.04,
        };
        assert_eq!(
            classify_confirmation(&[(inverted, ok); 3]),
            SegConfirmOutcome::Inverted
        );
        assert_eq!(
            classify_confirmation(&[(regressed, ok); 3]),
            SegConfirmOutcome::NotInverted
        );
        // 2 of 3 inverted is NOT a result.
        assert_eq!(
            classify_confirmation(&[(inverted, ok), (inverted, ok), (straddles, ok)]),
            SegConfirmOutcome::Unresolved
        );
        // A mixture of directions is not a result either.
        assert_eq!(
            classify_confirmation(&[(inverted, ok), (inverted, ok), (regressed, ok)]),
            SegConfirmOutcome::Unresolved
        );
        // A failed interaction gate voids the cell regardless of the intervals.
        let bad = SegOrderInteraction {
            delta_order_pct: 0.9,
            ci_low_pct: 0.5,
            ci_high_pct: 1.3,
        };
        assert_eq!(
            classify_confirmation(&[(inverted, ok), (inverted, ok), (inverted, bad)]),
            SegConfirmOutcome::Unresolved
        );
    }

    /// Four processes is the ad-hoc addition §6(b) forbids, so the API rejects it.
    #[test]
    #[should_panic(expected = "admits exactly")]
    fn the_decision_rule_rejects_a_fourth_process() {
        let ok = SegOrderInteraction {
            delta_order_pct: 0.0,
            ci_low_pct: -0.05,
            ci_high_pct: 0.05,
        };
        let inverted = RatioEstimate {
            median_ratio: 0.97,
            ci_low: 0.965,
            ci_high: 0.975,
        };
        let _ = classify_confirmation(&[(inverted, ok); 4]);
    }

    #[test]
    fn the_confirmation_summary_carries_the_three_number_report() {
        let processes: Vec<SegBlockedSamples> = [0.970_f64, 0.972, 0.968]
            .into_iter()
            .map(|ratio| blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(100.0 * ratio, 100.0)))
            .collect();
        // `SegConfirmSummary` is an ENUM: the pooled numbers exist only on `Resolved`,
        // so this destructures rather than reading fields off a struct.
        match summarize_confirmation(&processes) {
            SegConfirmSummary::Resolved {
                inverted,
                ref process_ratios,
                median_ratio,
                min_ratio,
                max_ratio,
                ref conditional_medians,
                ..
            } => {
                assert!(inverted, "all three intervals lie strictly below 1.0");
                assert_eq!(process_ratios.len(), SEG_CONFIRM_PROCESSES);
                assert!((median_ratio - 0.970).abs() < 1e-9);
                assert!((min_ratio - 0.968).abs() < 1e-9);
                assert!((max_ratio - 0.972).abs() < 1e-9);
                // §7.2.1's secondary column needs these, and they are carried on the
                // VALID path too — not only on order-coupled cells.
                assert_eq!(conditional_medians.len(), SEG_CONFIRM_PROCESSES);
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
        assert_eq!(
            summarize_confirmation(&processes).outcome(),
            SegConfirmOutcome::Inverted
        );
    }

    /// An order-coupled process yields an `Unresolved` summary with **no pooled fields
    /// at all** — the type has none on that path, which is the point.
    #[test]
    fn an_unresolved_confirmation_carries_no_pooled_numbers() {
        let clean = blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(97.0, 100.0));
        let coupled = blocked_fixture(SEG_SCHEDULE_SEED, |arm, orientation, _, _| match arm {
            SegArm::A => {
                if orientation == SegBlockOrientation::Baab {
                    101.0
                } else {
                    97.0
                }
            }
            SegArm::B => 100.0,
        });
        let summary = summarize_confirmation(&[clean.clone(), clean, coupled]);
        match summary {
            SegConfirmSummary::Unresolved {
                ref reason,
                ref per_process,
                ref order,
                ref conditional_medians,
            } => {
                assert!(reason.contains("order gate failed"), "{reason}");
                assert_eq!(per_process.len(), SEG_CONFIRM_PROCESSES);
                assert!(
                    per_process[2].is_none(),
                    "the coupled process has no interval"
                );
                assert_eq!(order.len(), SEG_CONFIRM_PROCESSES);
                assert_eq!(conditional_medians.len(), SEG_CONFIRM_PROCESSES);
            }
            other => panic!("expected Unresolved, got {other:?}"),
        }
        assert_eq!(summary.outcome(), SegConfirmOutcome::Unresolved);
    }

    #[test]
    fn the_raw_sample_schema_round_trips_exactly() {
        let meta = SegRunMeta {
            run_id: "r0001-0123456789ab".to_owned(),
            commit: "9bf7a80e".to_owned(),
            feature_set: "bench".to_owned(),
            run_label: "natural-r0-primary-1".to_owned(),
            pin_level: "natural".to_owned(),
            archive_sha256: "0".repeat(64),
            test_binary_sha256: "1".repeat(64),
            // A comma-bearing field, which is exactly why the raw file is TSV.
            device: "NVIDIA Test Device, 32 GiB".to_owned(),
            toolkit: "Build cuda_13.3, r13.3".to_owned(),
            seed: SEG_SCHEDULE_SEED,
        };
        let samples = blocked_fixture(SEG_SCHEDULE_SEED, |arm, _, slot, order| match arm {
            SegArm::A => 90.0 + order as f64 / 7.0 + slot as f64 / 13.0,
            SegArm::B => 100.0 + order as f64 / 11.0,
        });
        let tsv = render_raw_samples_tsv(&meta, "r0-primary", &samples);
        for column in [
            "run_id",
            "archive_sha256",
            "seed",
            "block_id",
            "superblock_id",
            "orientation",
            "incoming_class",
            "boundary_source",
            "order_id",
            "arm",
            "sample_us",
        ] {
            assert!(tsv.contains(column), "missing column {column}");
        }
        assert_eq!(tsv.lines().count(), 1 + 4 * SEG_TIMED_BLOCKS);
        let (back_meta, rows) = parse_raw_samples_tsv(&tsv);
        assert_eq!(
            back_meta, meta,
            "metadata must survive the round trip verbatim"
        );
        assert_eq!(rows.len(), SEG_TIMED_BLOCKS);
        let rebuilt = SegBlockedSamples {
            schedule: seg_schedule(back_meta.seed),
            blocks: rows.into_iter().map(|(_, block)| block).collect(),
        };
        assert_eq!(rebuilt.stratum_census(), samples.stratum_census());
        // Exact, not approximate: `{:?}` is round-trip-safe, `{:.3}` is not.
        for (a, b) in rebuilt.blocks.iter().zip(samples.blocks.iter()) {
            assert_eq!(a.candidate_us, b.candidate_us);
            assert_eq!(a.incumbent_us, b.incumbent_us);
        }
        let (x, y) = (rebuilt.estimate_stratified(), samples.estimate_stratified());
        assert_eq!((x.ci_low, x.ci_high), (y.ci_low, y.ci_high));
    }

    /// **`aggregate_confirmation_runs` is DRIVEN too**, to the same standard as
    /// `aggregate_arm`: it goes through `read_run`/`shared_identity`, and a rewrite
    /// nothing executes is a rewrite nobody has checked. Three real headered TSVs, written
    /// by the real writer, one of them order-coupled.
    #[test]
    #[serial_test::serial]
    fn aggregate_confirmation_runs_uses_the_shared_reader_end_to_end() {
        let root = std::env::temp_dir().join(format!("seg_conf_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let cell = "r0-primary";
        let mut dirs = Vec::new();
        for run in 0..SEG_CONFIRM_PROCESSES {
            let dir = root.join(format!("r{run}"));
            std::fs::create_dir_all(&dir).expect("run dir");
            let meta = SegRunMeta {
                run_id: format!("r001{run}-cccccccccccc"),
                commit: "c".to_owned(),
                feature_set: "bench".to_owned(),
                run_label: format!("natural-r0-primary-{run}"),
                pin_level: "natural".to_owned(),
                archive_sha256: "e".repeat(64),
                test_binary_sha256: "f".repeat(64),
                toolkit: "13.3".to_owned(),
                device: "d".to_owned(),
                seed: SEG_SCHEDULE_SEED,
            };
            let samples = blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(97.0, 100.0));
            std::env::set_var("BWD_SEG_RUN_DIR", &dir);
            record_raw_samples(&meta, cell, &samples);
            dirs.push(dir);
        }
        std::env::remove_var("BWD_SEG_RUN_DIR");
        // EVERY file must carry its own header — the per-path start state is what makes
        // three runs in one process possible at all.
        for dir in &dirs {
            let text = std::fs::read_to_string(dir.join(SEG_RAW_SAMPLES_TSV)).expect("raw");
            assert!(
                text.starts_with(SEG_RAW_TSV_HEADER),
                "{} is headerless — the writer's start state is not per-path",
                dir.display()
            );
        }
        match aggregate_confirmation_runs(&dirs, cell) {
            SegConfirmSummary::Resolved {
                inverted,
                median_ratio,
                ..
            } => {
                assert!(inverted);
                assert!((median_ratio - 0.97).abs() < 1e-9);
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
        // A shared run id is refused by the SHARED rule, not by a local copy of it.
        let dup = root.join("dup");
        std::fs::create_dir_all(&dup).expect("dup dir");
        let meta = SegRunMeta {
            run_id: "r0010-cccccccccccc".to_owned(), // collides with run 0
            commit: "c".to_owned(),
            feature_set: "bench".to_owned(),
            run_label: "natural-r0-primary-dup".to_owned(),
            pin_level: "natural".to_owned(),
            archive_sha256: "e".repeat(64),
            test_binary_sha256: "f".repeat(64),
            toolkit: "13.3".to_owned(),
            device: "d".to_owned(),
            seed: SEG_SCHEDULE_SEED,
        };
        std::env::set_var("BWD_SEG_RUN_DIR", &dup);
        record_raw_samples(
            &meta,
            cell,
            &blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(97.0, 100.0)),
        );
        std::env::remove_var("BWD_SEG_RUN_DIR");
        let collided = vec![dirs[0].clone(), dirs[1].clone(), dup];
        assert!(
            std::panic::catch_unwind(move || { aggregate_confirmation_runs(&collided, cell) })
                .is_err()
        );
        let _ = std::fs::remove_dir_all(&root);
    }

    /// **The generic reader and provenance rule, driven with real TSVs, one defect at a
    /// time.** These belong here because `read_run` and `shared_identity` are defined here:
    /// they are the single parser and the single provenance rule for EVERY caller, so their
    /// negatives cannot live in a task six steps later that merely happens to be their
    /// first D3 consumer.
    #[test]
    #[serial_test::serial]
    fn the_shared_reader_rejects_every_generic_identity_defect() {
        let cell = "generic-cell";
        let base = |run: usize| SegRunMeta {
            run_id: format!("r020{run}-aaaaaaaaaaaa"),
            commit: "c".to_owned(),
            feature_set: "bench".to_owned(),
            run_label: format!("generic-{run}"),
            pin_level: "natural".to_owned(),
            archive_sha256: "a".repeat(64),
            test_binary_sha256: "b".repeat(64),
            toolkit: "13.3".to_owned(),
            device: "d".to_owned(),
            seed: SEG_SCHEDULE_SEED,
        };
        // Three runs; `mutate` damages run 3's metadata only.
        let build = |tag: &str, mutate: &dyn Fn(&mut SegRunMeta)| {
            let root = std::env::temp_dir().join(format!("seg_gen_{tag}_{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&root);
            let mut dirs = Vec::new();
            for run in 1..=SEG_CONFIRM_PROCESSES {
                let dir = root.join(format!("r{run}"));
                std::fs::create_dir_all(&dir).expect("run dir");
                let mut meta = base(run);
                if run == SEG_CONFIRM_PROCESSES {
                    mutate(&mut meta);
                }
                std::env::set_var("BWD_SEG_RUN_DIR", &dir);
                record_raw_samples(
                    &meta,
                    cell,
                    &blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(90.0, 100.0)),
                );
                dirs.push(dir);
            }
            std::env::remove_var("BWD_SEG_RUN_DIR");
            (root, dirs)
        };
        // POSITIVE control: `read_run` parses each file and `shared_identity` accepts them.
        let (root, dirs) = build("ok", &|_| {});
        let ids: Vec<SegRunMeta> = dirs.iter().map(|d| read_run(d).0).collect();
        assert_eq!(shared_identity(&ids).archive_sha256, "a".repeat(64));
        // And every file carries its own header — the per-path writer state in one assertion.
        for dir in &dirs {
            let text = std::fs::read_to_string(dir.join(SEG_RAW_SAMPLES_TSV)).expect("raw");
            assert!(
                text.starts_with(SEG_RAW_TSV_HEADER),
                "{} is headerless",
                dir.display()
            );
        }
        let _ = std::fs::remove_dir_all(&root);
        // Every generic defect, one at a time, through `read_run` + `shared_identity`.
        let cases: Vec<(&str, Box<dyn Fn(&mut SegRunMeta)>)> = vec![
            (
                "dupid",
                Box::new(|m: &mut SegRunMeta| m.run_id = "r0201-aaaaaaaaaaaa".to_owned()),
            ),
            (
                "archive",
                Box::new(|m: &mut SegRunMeta| m.archive_sha256 = "9".repeat(64)),
            ),
            (
                "testbin",
                Box::new(|m: &mut SegRunMeta| m.test_binary_sha256 = "9".repeat(64)),
            ),
            (
                "commit",
                Box::new(|m: &mut SegRunMeta| m.commit = "other".to_owned()),
            ),
            (
                "pin",
                Box::new(|m: &mut SegRunMeta| m.pin_level = "48".to_owned()),
            ),
            (
                "features",
                Box::new(|m: &mut SegRunMeta| m.feature_set = "plain".to_owned()),
            ),
            (
                "toolkit",
                Box::new(|m: &mut SegRunMeta| m.toolkit = "12.9".to_owned()),
            ),
            (
                "device",
                Box::new(|m: &mut SegRunMeta| m.device = "other".to_owned()),
            ),
            (
                "seed",
                Box::new(|m: &mut SegRunMeta| m.seed = SEG_SCHEDULE_SEED ^ 1),
            ),
        ];
        for (tag, mutate) in cases {
            let (root, dirs) = build(tag, mutate.as_ref());
            let attempt = std::panic::catch_unwind(|| {
                let ids: Vec<SegRunMeta> = dirs.iter().map(|d| read_run(d).0).collect();
                shared_identity(&ids)
            });
            assert!(
                attempt.is_err(),
                "the shared reader accepted defect {tag:?}"
            );
            let _ = std::fs::remove_dir_all(&root);
        }
        // A per-run LABEL difference is accepted on purpose: labels differ by design, and
        // binding a label to an arm is the D3 layer's job (Task 7), not the reader's.
        let (root, dirs) = build("label", &|m: &mut SegRunMeta| {
            m.run_label = "other-9".to_owned()
        });
        let ids: Vec<SegRunMeta> = dirs.iter().map(|d| read_run(d).0).collect();
        shared_identity(&ids);
        let _ = std::fs::remove_dir_all(&root);
    }

    /// SERIAL: it mutates `BWD_SEG_RUN_DIR`, which is process-wide state that every other
    /// paired-path test reads. Two of these running concurrently would each see the other's
    /// reservation.
    #[test]
    #[serial_test::serial]
    fn a_unique_run_directory_per_process_cannot_overwrite() {
        // `seg_run_dir` reads the RESERVED directory from the environment (the launcher
        // claims it with `mkdir`), so what this pins is that two runs cannot be handed
        // the same reservation and that the reservation is what is used.
        let base = SegRunMeta {
            run_id: "r0001-aaaaaaaaaaaa".to_owned(),
            commit: "c".to_owned(),
            feature_set: "bench".to_owned(),
            run_label: "40-1".to_owned(),
            pin_level: "40".to_owned(),
            archive_sha256: "a".repeat(64),
            test_binary_sha256: "b".repeat(64),
            toolkit: "13.3".to_owned(),
            device: "d".to_owned(),
            seed: SEG_SCHEDULE_SEED,
        };
        let first = std::env::temp_dir().join(format!("seg_rd_a_{}", std::process::id()));
        let second = std::env::temp_dir().join(format!("seg_rd_b_{}", std::process::id()));
        // SAFETY: single-threaded test; the harness reads this once per process.
        std::env::set_var("BWD_SEG_RUN_DIR", &first);
        assert_eq!(seg_run_dir(&base), first);
        std::env::set_var("BWD_SEG_RUN_DIR", &second);
        assert_ne!(
            seg_run_dir(&base),
            first,
            "the reservation is the only source"
        );
        assert_eq!(seg_run_dir(&base), second);
        std::env::remove_var("BWD_SEG_RUN_DIR");
    }

    #[test]
    fn the_freeze_round_trips_and_its_hash_is_stable() {
        // Tagged `pin-decision`, because the cell is a CONTINUATION shape and the
        // `r0-headline` predicate (class == R0, add_sub layer 0, probed tuple) would — and
        // should — refuse it. A generic round-trip fixture must name a cell its campaign
        // actually admits.
        let cells = vec![SegFrozenCell {
            label: "cont-d1-k4-plane-const-inline".to_owned(),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: SegRoundClass::D1,
            k: 4,
            epilogue: "plane".to_owned(),
            coeff: "const".to_owned(),
            program: "inline".to_owned(),
        }];
        let dir = std::env::temp_dir().join(format!("seg_freeze_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "pin-decision",
            &cells,
            SEG_SCHEDULE_SEED,
            &SegProbeEvidence::NotRequired,
        );
        assert_eq!(
            read_frozen_cells(&path, "pin-decision"),
            cells,
            "the freeze must round-trip verbatim"
        );
        // Byte-stability, so the shell's sha256sum comparison is meaningful: writing
        // the same freeze twice must produce identical bytes.
        let first = std::fs::read(&path).expect("read freeze");
        write_frozen_cells(
            &path,
            "pin-decision",
            &cells,
            SEG_SCHEDULE_SEED,
            &SegProbeEvidence::NotRequired,
        );
        assert_eq!(first, std::fs::read(&path).expect("read freeze"));
    }

    /// An UNPROBED tuple is refused at write time, so §9 item 2's precondition cannot be
    /// carried into the acceptance gate on a shape it was never established for.
    /// A CONTINUATION cell whose shape happens to be probed is still refused: the
    /// precondition was established on an R0 launch, on a different data path.
    #[test]
    #[should_panic(expected = "may only name R0 cells")]
    fn the_r0_freeze_refuses_a_continuation_class() {
        let dir = std::env::temp_dir().join(format!("seg_probe_d1_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        write_frozen_cells(
            &dir.join(SEG_FROZEN_CELLS_TSV),
            "r0-headline",
            &[SegFrozenCell {
                label: "d1-masquerading-as-probed".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                // The shape (plane / K4 / const / inline) IS in the probed set; only the
                // class differs. That must be enough to refuse it.
                class: SegRoundClass::D1,
                k: 4,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            // Converged evidence deliberately: the CLASS must refuse this cell on its
            // own, before any probe question is asked.
            &converged_probes(),
        );
    }

    #[test]
    #[should_panic(expected = "UNPROBED tuple")]
    fn the_r0_freeze_refuses_an_unprobed_tuple() {
        let cell = |k: usize, epi: &str| SegFrozenCell {
            label: format!("r0-k{k}-{epi}"),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: SegRoundClass::R0,
            k,
            epilogue: epi.to_owned(),
            coeff: "const".to_owned(),
            program: "inline".to_owned(),
        };
        let dir = std::env::temp_dir().join(format!("seg_probe_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        // A MIXED set: K=4 plane is probed, K=8 plane is not. The probed member must not
        // license the unprobed one.
        write_frozen_cells(
            &dir.join(SEG_FROZEN_CELLS_TSV),
            "r0-headline",
            &[cell(4, "plane"), cell(8, "plane")],
            SEG_SCHEDULE_SEED,
            &converged_probes(),
        );
    }

    /// A fully probed set is accepted, and the pin campaign is not subject to the R0
    /// predicate at all (its cells are continuation shapes by construction).
    #[test]
    fn the_r0_freeze_accepts_probed_tuples_and_ignores_pin_cells() {
        let probed = SegFrozenCell {
            label: "r0-k24-plane".to_owned(),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: SegRoundClass::R0,
            k: 24,
            epilogue: "plane".to_owned(),
            coeff: "const".to_owned(),
            program: "inline".to_owned(),
        };
        let dir = std::env::temp_dir().join(format!("seg_probe_ok_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "r0-headline",
            &[probed.clone()],
            SEG_SCHEDULE_SEED,
            &converged_probes(),
        );
        assert_eq!(read_frozen_cells(&path, "r0-headline"), vec![probed]);
        // The pin campaign's K=8 continuation cell is fine: the predicate is R0-only.
        let pin = SegFrozenCell {
            label: "cont-d1-k8".to_owned(),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: SegRoundClass::D1,
            k: 8,
            epilogue: "plane".to_owned(),
            coeff: "const".to_owned(),
            program: "inline".to_owned(),
        };
        write_frozen_cells(
            &path,
            "pin-decision",
            &[pin],
            SEG_SCHEDULE_SEED,
            &SegProbeEvidence::NotRequired,
        );
    }

    /// The other campaign's freeze is REFUSED, not silently accepted: a pin runner handed
    /// the R0 freeze would time shapes it does not have and shrink the decision set.
    #[test]
    #[should_panic(expected = "refuses it")]
    fn a_campaign_refuses_the_other_campaigns_freeze() {
        // A VALID `r0-headline` cell: R0 class, add_sub layer 0, a probed tuple. Writing a
        // D1 cell under `r0-headline` would panic in the WRITER with the class message and
        // never reach the reader — testing the wrong thing.
        let cells = vec![SegFrozenCell {
            label: "r0-k4-plane".to_owned(),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: SegRoundClass::R0,
            k: 4,
            epilogue: "plane".to_owned(),
            coeff: "const".to_owned(),
            program: "inline".to_owned(),
        }];
        let dir = std::env::temp_dir().join(format!("seg_freeze_x_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "r0-headline",
            &cells,
            SEG_SCHEDULE_SEED,
            &converged_probes(),
        );
        let _ = read_frozen_cells(&path, "pin-decision");
    }

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
            // The order diagnostics and the four order-conditional medians are
            // emitted for EVERY paired row (spec §6(a) step 5, §7.2.1), and `run_id`
            // is what joins a quoted number to its raw samples and its SHA-256s.
            "delta_order_pct",
            "delta_order_ci_low",
            "delta_order_ci_high",
            "order_gate",
            "abba_candidate_us",
            "abba_incumbent_us",
            "baab_candidate_us",
            "baab_incumbent_us",
            "run_id",
            // The carveout configuration is part of a row's provenance, not a side
            // note: a ratio measured at a different SM partition is a different
            // measurement (spec §3.4).
            "carveout_mode",
            "carveout_requested_pct",
            "carveout_source",
            // The §4.5 role, so the pin aggregator separates Decision from
            // DriftControl from the emitted column rather than from a label pattern.
            "pin_role",
            // The per-launch traffic floors ride on EVERY row, launchable or not
            // (spec §7.2.2 Emission).
            "floor_dram_read_bytes",
            "floor_dram_write_bytes",
        ] {
            assert!(csv.contains(column), "missing column {column}");
        }
        // The floors are LOWERING properties, so the unlaunchable row carries them too
        // and the zero convention stays a statement about lowering output, not about
        // launchability.
        let dead = render_matrix_csv(&[row_fixture(32, 0, None)]);
        assert!(dead.ends_with(",1073741824,268435456\n"), "{dead}");
        // The demand-source prose contains a comma; the renderer must neutralize it
        // rather than let it split the row into an extra field.
        assert!(
            csv.contains("common-bucket,31,candidate; 30720 B (both arms quantize alike)"),
            "{csv}"
        );
        assert_eq!(
            csv.lines().next().expect("a header").matches(',').count(),
            csv.lines().nth(1).expect("a row").matches(',').count(),
            "the row must have exactly as many separators as the header"
        );
        assert!(csv.contains("INVERTED"), "{csv}");
        // A paired row says so and names what it was paired against; a solo row
        // says THAT, and carries no ratio to be divided by anything.
        assert!(csv.contains("paired,incumbent"), "{csv}");
        let solo = render_matrix_csv(&[row_fixture(4, 6, None)]);
        assert!(solo.contains("solo,-,"), "{solo}");
        assert!(render_matrix_table(&[row_fixture(4, 6, None)]).contains("| solo | solo | solo |"));
        // **A REFERENCE-CLOCK row carries no inversion verdict.** The pin and δ3 runners
        // pair a continuation candidate against the flat R0 kernel as a CLOCK, and §4.5
        // calls scoring such a ratio by §6(b)'s rule a category error — so the
        // machine-readable `verdict` field of a `FixedBucket` row must not spell any of
        // §6(b)'s tokens. Measured on the live smoke run before this was fixed: the
        // frozen artifact carried `0.245246,…,INVERTED`.
        //
        // **Keyed on the PAIRING, not on the mode.** The mode-keyed form was sound only
        // while `FixedBucket` was the pin/δ3 runners' alone; the R0 headline now times
        // candidate-vs-incumbent pairs at the SAME bucket, so the
        // second half of this test pins the other direction — same mode, opposite verdict
        // vocabulary — and a regression to mode-keying fails one half or the other.
        let inverting = || {
            Some(RatioEstimate {
                median_ratio: 0.245_246,
                ci_low: 0.245_1,
                ci_high: 0.245_3,
            })
        };
        let clock = SegMatrixRow {
            carveout_mode: CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES).label(),
            pairing: SegPairing::ReferenceClock,
            ..row_fixture(4, 6, inverting())
        };
        let clock_csv = render_matrix_csv(&[clock]);
        assert!(clock_csv.contains(",reference-clock,"), "{clock_csv}");
        assert!(
            !clock_csv.contains("INVERTED"),
            "a reference-clock pairing is not an inversion question: {clock_csv}"
        );
        // The ratio columns still render — only the VERDICT vocabulary changes.
        assert!(clock_csv.contains("0.245246"), "{clock_csv}");

        // **The R0 HEADLINE at a fixed bucket: same mode as the clock, candidate-vs-incumbent
        // arms, and §6(b)'s vocabulary INTACT.** If this row were stamped `reference-clock`,
        // an acceptance gate would be reading a field that had been told the headline has no
        // inversion question — the whole verdict erased by a configuration change that was
        // supposed to be about cache partitions. Holds for ANY fixed bucket, so it does not
        // depend on which one §7.2.1 designates.
        let headline = SegMatrixRow {
            carveout_mode: CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES).label(),
            pairing: SegPairing::CandidateVsIncumbent,
            ..row_fixture(4, 6, inverting())
        };
        let headline_csv = render_matrix_csv(&[headline]);
        assert!(
            headline_csv.contains("fixed-bucket"),
            "the primary column runs at the fixed bucket: {headline_csv}"
        );
        assert!(
            headline_csv.contains("INVERTED"),
            "the R0 headline is candidate-vs-incumbent, so §6(b)'s verdict must \
             survive the fixed bucket: {headline_csv}"
        );
        assert!(
            !headline_csv.contains("reference-clock"),
            "the verdict must key on the PAIRING, never on the carveout mode: \
             {headline_csv}"
        );
    }

    /// Probe evidence saying every [`SEG_R0_PROBED_TUPLES`] member CONVERGED under the
    /// primary forced mode — the fixture an `r0-headline` freeze-writer test needs now
    /// that membership alone is not enough (F-9.3).
    fn converged_probes() -> SegProbeEvidence {
        converged_probes_at(&CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES).mode_key())
    }

    /// The same fixture at an explicit configuration key, so a test can prove that evidence
    /// measured at one bucket does not license a freeze written for another.
    fn converged_probes_at(mode_key: &str) -> SegProbeEvidence {
        SegProbeEvidence::Measured {
            mode_key: mode_key.to_owned(),
            verdicts: SEG_R0_PROBED_TUPLES
                .iter()
                .map(|probed| SegProbeVerdict {
                    epilogue: probed.epilogue.to_owned(),
                    k: probed.k,
                    coeff: probed.coeff.to_owned(),
                    program: probed.program.to_owned(),
                    mode: mode_key.to_owned(),
                    converged: true,
                })
                .collect(),
        }
    }

    /// The parser rejects what it cannot mean, rather than defaulting: an unknown verdict
    /// token silently meaning "diverged" would block a sound freeze and silently meaning
    /// "converged" would pass an unsound one.
    #[test]
    fn probe_verdicts_parse_and_reject_what_they_cannot_mean() {
        let ok = parse_probe_verdicts(
            "# a comment\n\
             plane\t4\tconst\tinline\tfixed-bucket:102400\tCONVERGED\n\
             \n\
             plane\t24\tconst\tinline\tcommon-bucket\tDIVERGED\n",
        );
        assert_eq!(ok.len(), 2);
        assert!(ok[0].converged);
        assert_eq!(ok[0].k, 4);
        assert!(!ok[1].converged);
        assert_eq!(ok[0].mode, "fixed-bucket:102400");
        assert_eq!(ok[1].mode, "common-bucket");
    }

    #[test]
    #[should_panic(expected = "CONVERGED or DIVERGED")]
    fn probe_verdicts_reject_an_unknown_token() {
        let _ = parse_probe_verdicts("plane\t4\tconst\tinline\tfixed-bucket:102400\tok\n");
    }

    /// `off` is the driver-default control, where divergence is the EXPECTED outcome — a
    /// convergence probe in that mode is not evidence of anything and must not be
    /// accepted as such.
    #[test]
    #[should_panic(expected = "FORCES one partition")]
    fn probe_verdicts_reject_an_unforced_mode() {
        let _ = parse_probe_verdicts("plane\t4\tconst\tinline\toff\tCONVERGED\n");
    }

    /// **F-9.3, the case that motivated the guard.** `plane K4 const inline` IS a probed
    /// tuple, and its `common-bucket` probe realized 65,536 B against 32,768 B. Membership
    /// passes; the freeze must still be refused.
    #[test]
    #[should_panic(expected = "DIVERGED")]
    fn the_r0_freeze_refuses_a_tuple_whose_probe_diverged() {
        let dir = std::env::temp_dir().join(format!("seg_probe_div_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        write_frozen_cells(
            &dir.join(SEG_FROZEN_CELLS_TSV),
            "r0-headline",
            &[SegFrozenCell {
                label: "r0-plane-k4-const-inline".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                class: SegRoundClass::R0,
                k: 4,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            &SegProbeEvidence::Measured {
                mode_key: "common-bucket".to_owned(),
                verdicts: vec![SegProbeVerdict {
                    epilogue: "plane".to_owned(),
                    k: 4,
                    coeff: "const".to_owned(),
                    program: "inline".to_owned(),
                    mode: "common-bucket".to_owned(),
                    converged: false,
                }],
            },
        );
    }

    /// **R7 item 1: the explicit diagnostic bucket parses and validates.** The bare form
    /// must keep meaning the reference clock's partition, or every existing caller moves.
    #[test]
    fn the_carveout_mode_grammar_accepts_an_explicit_validated_bucket() {
        assert_eq!(parse_carveout_mode("off"), CarveoutMode::Off);
        assert_eq!(
            parse_carveout_mode("common-bucket"),
            CarveoutMode::CommonBucket
        );
        assert_eq!(
            parse_carveout_mode("as-configured"),
            CarveoutMode::AsConfigured
        );
        assert_eq!(
            parse_carveout_mode("fixed-bucket"),
            CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES),
            "the bare form must still mean the reference clock's predeclared partition"
        );
        // The pool maximum — the diagnostic R7 exists to make expressible, and the one
        // value `realized = max(driver heuristic, bucket)` cannot exceed.
        assert_eq!(
            parse_carveout_mode("fixed-bucket:102400"),
            CarveoutMode::FixedBucket(102_400)
        );
        assert_eq!(
            *BWD_SEG_SMEM_BUCKETS_BYTES
                .last()
                .expect("a non-empty bucket set"),
            102_400,
            "the largest documented partition IS the pool on this part, which is what makes \
             the containment check a pool-max check too"
        );
        // Every documented bucket except 0 is expressible; whitespace is tolerated.
        for bucket in BWD_SEG_SMEM_BUCKETS_BYTES.into_iter().filter(|b| *b != 0) {
            assert_eq!(
                parse_carveout_mode(&format!("fixed-bucket: {bucket} ")),
                CarveoutMode::FixedBucket(bucket)
            );
        }
        // The label is mode-only, so an explicit bucket does not invent a new column name.
        assert_eq!(
            parse_carveout_mode("fixed-bucket:102400").label(),
            "fixed-bucket"
        );
    }

    /// A partition between buckets would be rounded up by the driver, and the emitted
    /// `carveout_mode` label would then name something nothing realized.
    #[test]
    #[should_panic(expected = "not a supported realized partition")]
    fn the_carveout_mode_grammar_refuses_a_bucket_off_the_device_set() {
        let _ = parse_carveout_mode("fixed-bucket:49152");
    }

    /// Above the pool there is no partition at all — the same containment check catches it,
    /// because the device set's largest member is the pool.
    #[test]
    #[should_panic(expected = "not a supported realized partition")]
    fn the_carveout_mode_grammar_refuses_a_bucket_above_the_pool() {
        let _ = parse_carveout_mode("fixed-bucket:131072");
    }

    #[test]
    #[should_panic(expected = "holds no paired demand")]
    fn the_carveout_mode_grammar_refuses_a_zero_bucket() {
        let _ = parse_carveout_mode("fixed-bucket:0");
    }

    #[test]
    #[should_panic(expected = "needs a byte count")]
    fn the_carveout_mode_grammar_refuses_a_non_numeric_bucket() {
        let _ = parse_carveout_mode("fixed-bucket:sixtyfour");
    }

    /// **R7 item 2: an off-column-only freeze is accepted, and SAYS SO in the artifact.**
    /// The cell here is the one whose forced probes all diverged — the case the variant
    /// exists for.
    #[test]
    fn an_off_column_only_freeze_is_accepted_and_declares_itself() {
        let cell = SegFrozenCell {
            label: "r0-plane-k4-const-inline".to_owned(),
            circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
            layer: 0,
            class: SegRoundClass::R0,
            k: 4,
            epilogue: "plane".to_owned(),
            coeff: "const".to_owned(),
            program: "inline".to_owned(),
        };
        let dir = std::env::temp_dir().join(format!("seg_offcol_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "r0-headline",
            &[cell.clone()],
            SEG_SCHEDULE_SEED,
            &SegProbeEvidence::ConvergenceIndependent {
                why: "off control: the driver chooses per kernel and divergence is the data"
                    .to_owned(),
            },
        );
        // The cells still round-trip, so the off column is confirmable at all.
        assert_eq!(read_frozen_cells(&path, "r0-headline"), vec![cell]);
        // And the artifact ANNOUNCES which precondition it was written under, so no later
        // reader can mistake it for a forced-converged freeze.
        let text = std::fs::read_to_string(&path).expect("read freeze");
        let evidence = text
            .lines()
            .find_map(|line| line.strip_prefix("# probe_evidence = "))
            .expect("the freeze must state its probe evidence");
        assert!(
            evidence.contains("convergence-independent")
                && evidence.contains("NOT VALID FOR A FORCED COLUMN"),
            "{evidence}"
        );
        assert!(evidence.contains("divergence is the data"), "{evidence}");
    }

    /// The forced path stays EXACTLY as fail-closed as F-9.3 made it: a forced-converged
    /// freeze names its evidence, and the diverged cell is still refused (covered by
    /// `the_r0_freeze_refuses_a_tuple_whose_probe_diverged`). This pins the header tag on
    /// the forced path so the two artifacts are distinguishable in both directions.
    #[test]
    fn a_forced_freeze_declares_forced_converged_evidence() {
        let dir = std::env::temp_dir().join(format!("seg_forcedcol_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "r0-headline",
            &[SegFrozenCell {
                label: "r0-plane-k24-const-inline".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                class: SegRoundClass::R0,
                k: 24,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            &converged_probes(),
        );
        let text = std::fs::read_to_string(&path).expect("read freeze");
        let evidence = text
            .lines()
            .find_map(|line| line.strip_prefix("# probe_evidence = "))
            .expect("the freeze must state its probe evidence");
        assert!(evidence.starts_with("forced-converged"), "{evidence}");
        assert!(!evidence.contains("convergence-independent"), "{evidence}");
    }

    /// **4(c): a verdict measured at one bucket must not license a freeze written for
    /// another.** Measured on this device: `fixed-bucket:65536` DIVERGED at the R0 headline
    /// cell while `fixed-bucket:102400` CONVERGED, so keying evidence on the bare mode label
    /// would let each stand for the other.
    #[test]
    #[should_panic(expected = "no probe verdict")]
    fn a_verdict_from_one_bucket_does_not_license_another_bucket() {
        let dir = std::env::temp_dir().join(format!("seg_xmode_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        write_frozen_cells(
            &dir.join(SEG_FROZEN_CELLS_TSV),
            "r0-headline",
            &[SegFrozenCell {
                label: "r0-plane-k24-const-inline".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                class: SegRoundClass::R0,
                k: 24,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            // Converged — but at the POOL MAX, while the freeze is being written for 64 KiB.
            &SegProbeEvidence::Measured {
                mode_key: "fixed-bucket:65536".to_owned(),
                verdicts: vec![SegProbeVerdict {
                    epilogue: "plane".to_owned(),
                    k: 24,
                    coeff: "const".to_owned(),
                    program: "inline".to_owned(),
                    mode: "fixed-bucket:102400".to_owned(),
                    converged: true,
                }],
            },
        );
    }

    /// The same evidence at the MATCHING key is accepted, and the header names the bucket —
    /// so the pass above is about the key, not about some unrelated rejection.
    #[test]
    fn a_verdict_at_the_matching_bucket_licenses_the_freeze_and_names_it() {
        let dir = std::env::temp_dir().join(format!("seg_xmode_ok_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "r0-headline",
            &[SegFrozenCell {
                label: "r0-plane-k24-const-inline".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                class: SegRoundClass::R0,
                k: 24,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            &converged_probes_at("fixed-bucket:102400"),
        );
        let text = std::fs::read_to_string(&path).expect("read freeze");
        let evidence = frozen_probe_evidence(&text, &path);
        assert!(
            evidence.starts_with("forced-converged at fixed-bucket:102400"),
            "{evidence}"
        );
    }

    /// A bare `fixed-bucket` is ambiguous between buckets whose verdicts differ, so it is not
    /// a usable key on either side.
    #[test]
    fn a_bare_fixed_bucket_is_not_a_forced_mode_key() {
        assert!(is_forced_mode_key("common-bucket"));
        assert!(is_forced_mode_key("fixed-bucket:102400"));
        assert!(is_forced_mode_key("fixed-bucket:65536"));
        assert!(!is_forced_mode_key("fixed-bucket"));
        assert!(
            !is_forced_mode_key("fixed-bucket:49152"),
            "undocumented bucket"
        );
        assert!(!is_forced_mode_key("off"));
        assert!(!is_forced_mode_key("as-configured"));
        // And the two accessors agree with each other.
        assert_eq!(
            CarveoutMode::FixedBucket(102_400).mode_key(),
            "fixed-bucket:102400"
        );
        assert_eq!(CarveoutMode::CommonBucket.mode_key(), "common-bucket");
        assert!(CarveoutMode::CommonBucket.forces_one_partition());
        assert!(CarveoutMode::FixedBucket(102_400).forces_one_partition());
        assert!(!CarveoutMode::Off.forces_one_partition());
        assert!(!CarveoutMode::AsConfigured.forces_one_partition());
    }

    /// **4(a): a freeze with no `# probe_evidence` field is REFUSED on read**, at parity with
    /// the campaign tag. Before this, a field-less artifact read exactly like a
    /// forced-converged one — the absence of the strongest claim read as the safest.
    #[test]
    #[should_panic(expected = "no `# probe_evidence` field")]
    fn a_freeze_without_probe_evidence_is_refused_on_read() {
        let dir = std::env::temp_dir().join(format!("seg_noev_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        // A freeze that is otherwise perfectly well formed — campaign tag, seed, schema
        // header, one valid probed R0 cell — and carries no evidence field.
        let mut text = String::from("# campaign = r0-headline\n# seed = 0x1\n");
        text.push_str(SEG_FROZEN_TSV_HEADER);
        text.push_str(&format!(
            "r0-plane-k4-const-inline\t{ADD_SUB_LAYOUT_SHORT}\t0\tR0\t4\tplane\tconst\tinline\n"
        ));
        std::fs::write(&path, text).expect("write freeze");
        let _ = read_frozen_cells(&path, "r0-headline");
    }

    /// **4(b): an off-column-only freeze timed in a FORCED configuration is refused.** This is
    /// the consume-side half of the write-side variant: the freeze says convergence does not
    /// apply to its cells, so a forced column may not quote a number from them.
    #[test]
    #[should_panic(expected = "CONVERGENCE-INDEPENDENT freeze")]
    fn an_off_column_freeze_is_refused_in_a_forced_configuration() {
        assert_freeze_matches_column(
            "convergence-independent — NOT VALID FOR A FORCED COLUMN: off control",
            CarveoutMode::FixedBucket(102_400),
            "/tmp/seg_frozen_cells.tsv",
        );
    }

    #[test]
    #[should_panic(expected = "CONVERGENCE-INDEPENDENT freeze")]
    fn an_off_column_freeze_is_refused_under_common_bucket_too() {
        assert_freeze_matches_column(
            "convergence-independent — NOT VALID FOR A FORCED COLUMN: off control",
            CarveoutMode::CommonBucket,
            "/tmp/seg_frozen_cells.tsv",
        );
    }

    /// The combinations that ARE legal, so the gate is not simply refusing everything.
    ///
    /// Three rules, and the asymmetry between them is deliberate (ruling R8):
    ///   * an off-only freeze in a convergence-independent column — the property it declines
    ///     to claim is a property that column does not need;
    ///   * a forced-converged freeze at its OWN `mode_key`;
    ///   * a forced-converged freeze in a NON-forcing column, which is the reverse direction
    ///     and stays allowed: `off` / `as-configured` claim no equal-partition property, so
    ///     the evidence is merely unused there, never contradicted.
    #[test]
    fn the_column_gate_admits_every_matching_combination() {
        let off_only = "convergence-independent — NOT VALID FOR A FORCED COLUMN: off control";
        for mode in [CarveoutMode::Off, CarveoutMode::AsConfigured] {
            assert_freeze_matches_column(off_only, mode, "p");
        }
        let forced = "forced-converged at fixed-bucket:102400 (pair_gate.py, 2 verdict(s))";
        for mode in [
            CarveoutMode::Off,
            CarveoutMode::AsConfigured,
            // The MATCHING key — this is the acceptance half of the mode-key gate.
            CarveoutMode::FixedBucket(102_400),
        ] {
            assert_freeze_matches_column(forced, mode, "p");
        }
        // A common-bucket freeze is consumable under common-bucket, so the gate is keyed on
        // the mode_key and not hardcoded to `fixed-bucket`.
        assert_freeze_matches_column(
            "forced-converged at common-bucket (pair_gate.py, 1 verdict(s))",
            CarveoutMode::CommonBucket,
            "p",
        );
        // `not-required` carries no convergence claim, so no key can mismatch — this is the
        // pin / δ3 campaigns' evidence class, and it is legal in every column.
        for mode in [
            CarveoutMode::Off,
            CarveoutMode::AsConfigured,
            CarveoutMode::CommonBucket,
            CarveoutMode::FixedBucket(SEG_REFERENCE_CLOCK_BUCKET_BYTES),
        ] {
            assert_freeze_matches_column(
                "not-required (campaign carries no forced-bucket precondition)",
                mode,
                "p",
            );
        }
    }

    /// **The mode-key fail-open, closed (ruling R8): a CROSS-BUCKET consumption is refused.**
    ///
    /// Measured on this device: `fixed-bucket:65536` DIVERGED at the R0 headline cell where
    /// `fixed-bucket:102400` CONVERGED. The write side already keyed each verdict on its
    /// configuration, but consume did not re-check it — so the 100 KiB success licensed a
    /// 64 KiB confirmation and each could stand for the other.
    #[test]
    #[should_panic(expected = "FORCED-CONVERGED evidence measured at")]
    fn a_forced_freeze_is_refused_at_a_different_bucket() {
        assert_freeze_matches_column(
            "forced-converged at fixed-bucket:102400 (pair_gate.py, 2 verdict(s))",
            CarveoutMode::FixedBucket(65_536),
            "/tmp/seg_frozen_cells.tsv",
        );
    }

    /// And across MODES, not just buckets: a common-bucket verdict does not license a
    /// fixed-bucket confirmation, which is the same license in the other direction.
    #[test]
    #[should_panic(expected = "FORCED-CONVERGED evidence measured at")]
    fn a_common_bucket_freeze_is_refused_under_a_fixed_bucket() {
        assert_freeze_matches_column(
            "forced-converged at common-bucket (pair_gate.py, 1 verdict(s))",
            CarveoutMode::FixedBucket(102_400),
            "/tmp/seg_frozen_cells.tsv",
        );
    }

    /// A verdict for a DIFFERENT probed tuple does not license this one.
    #[test]
    #[should_panic(expected = "no probe verdict")]
    fn the_r0_freeze_refuses_a_tuple_with_no_verdict_of_its_own() {
        let dir = std::env::temp_dir().join(format!("seg_probe_none_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        write_frozen_cells(
            &dir.join(SEG_FROZEN_CELLS_TSV),
            "r0-headline",
            &[SegFrozenCell {
                label: "r0-plane-k4-const-inline".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                class: SegRoundClass::R0,
                k: 4,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            // K=24's verdict, for a K=4 cell.
            &SegProbeEvidence::Measured {
                mode_key: "fixed-bucket:65536".to_owned(),
                verdicts: vec![SegProbeVerdict {
                    epilogue: "plane".to_owned(),
                    k: 24,
                    coeff: "const".to_owned(),
                    program: "inline".to_owned(),
                    mode: "fixed-bucket:65536".to_owned(),
                    converged: true,
                }],
            },
        );
    }

    /// The R0 campaign may not opt OUT of the precondition by declaring it not required.
    #[test]
    #[should_panic(expected = "needs MEASURED probe verdicts")]
    fn the_r0_freeze_refuses_unmeasured_evidence() {
        let dir = std::env::temp_dir().join(format!("seg_probe_unmeas_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        write_frozen_cells(
            &dir.join(SEG_FROZEN_CELLS_TSV),
            "r0-headline",
            &[SegFrozenCell {
                label: "r0-plane-k24-const-inline".to_owned(),
                circuit: ADD_SUB_LAYOUT_SHORT.to_owned(),
                layer: 0,
                class: SegRoundClass::R0,
                k: 24,
                epilogue: "plane".to_owned(),
                coeff: "const".to_owned(),
                program: "inline".to_owned(),
            }],
            SEG_SCHEDULE_SEED,
            &SegProbeEvidence::NotRequired,
        );
    }

    /// §7.2.1's two columns in ONE process, which is what the plan's step-4 block writes.
    /// The `':'`-only reading is what made that block unrunnable — it would have produced
    /// five directories, two of them named `"primary=<dir>"` and `"<dir>;secondary=<dir>"`.
    #[test]
    fn confirm_columns_parses_the_two_column_grammar() {
        let columns = parse_confirm_columns("primary=a:b:c;secondary=d:e:f", "fixed-bucket");
        assert_eq!(columns.len(), 2, "{columns:?}");
        assert_eq!(columns[0].0, "primary");
        assert_eq!(columns[1].0, "secondary");
        assert_eq!(
            columns[0].1,
            vec![PathBuf::from("a"), PathBuf::from("b"), PathBuf::from("c")]
        );
        assert_eq!(
            columns[1].1,
            vec![PathBuf::from("d"), PathBuf::from("e"), PathBuf::from("f")]
        );
        // The single-column form stays legal, so one column can be aggregated alone, and
        // it takes its name from the carveout mode.
        let solo = parse_confirm_columns("a:b:c", "as-configured");
        assert_eq!(solo.len(), 1);
        assert_eq!(solo[0].0, "as-configured");
        assert_eq!(solo[0].1.len(), 3);
    }

    /// Two groups under one name would print two verdicts per cell under one `column=`
    /// label, and the plan's step-4 count check would pass on double the rows.
    #[test]
    #[should_panic(expected = "repeats a column name")]
    fn confirm_columns_refuse_a_repeated_column() {
        let _ = parse_confirm_columns("primary=a:b:c;primary=d:e:f", "fixed-bucket");
    }

    /// **The executable freeze path, driven end to end.**
    ///
    /// `bwd_seg_freeze_r0_headline` is `#[ignore]`d and environment-driven, so its chain —
    /// `parse_matrix_csv_rows`, `matrix_row_class`, the band, the probe intersection, the
    /// `short_name` normalization and `write_frozen_cells`'s own predicate — would
    /// otherwise first execute during the campaign. The fixture is rendered by the REAL
    /// `render_matrix_csv`, so `circuit` carries the long `..._layout_gkr.json` form:
    /// **delete the `short_name` call and this test panics on the first cell**, which is
    /// the whole point of covering it.
    #[test]
    fn the_r0_freeze_selects_the_band_intersects_the_probes_and_normalizes_the_circuit() {
        let paired = |k: usize, ratio: f64| {
            row_fixture(
                k,
                6,
                Some(RatioEstimate {
                    median_ratio: ratio,
                    ci_low: ratio - 0.001,
                    ci_high: ratio + 0.001,
                }),
            )
        };
        // An ORDER-COUPLED row at a probed K, with by far the best raw ratio. It must not
        // enter the band at all — and it must not become `best` either, which is the
        // stronger property: a missing selectability filter would set `best = 0.5`, empty
        // the band, and fire the intersection assertion instead of freezing the wrong cell.
        let coupled = SegMatrixRow {
            ratio: SegRatio::OrderInvalid {
                order: SegOrderInteraction {
                    delta_order_pct: 4.0,
                    ci_low_pct: 3.5,
                    ci_high_pct: 4.5,
                },
                conditional_medians: [50.0, 100.0, 52.0, 100.0],
            },
            ..paired(24, 0.500)
        };
        // K4 and K24 are the two PROBED tuples; K8 is inside the band but UNPROBED; K32 is
        // probed-shaped but outside it. Band edge: 0.900 * 1.010 = 0.9090.
        let rows = vec![
            paired(4, 0.900),
            paired(8, 0.900_5),
            paired(24, 0.904_0),
            paired(32, 1.200),
            coupled,
        ];
        let csv = render_matrix_csv(&rows);
        assert!(
            csv.contains("add_sub_lui_auipc_mop_layout_gkr.json"),
            "the fixture must carry the LONG circuit form, or it proves nothing"
        );
        // Discovery's own shortlist, over the same population: three members, unordered,
        // and the order-coupled row is absent despite being the fastest raw ratio.
        let shortlist = discovery_shortlist(&rows);
        assert_eq!(shortlist.len(), 3, "{shortlist:?}");
        assert!(shortlist.iter().all(|label| !label.starts_with("K32 ")));
        let mut sorted = shortlist.clone();
        sorted.sort();
        assert_eq!(
            shortlist, sorted,
            "the band is emitted unordered (sorted by label)"
        );
        // The freeze selection.
        let frozen = r0_headline_freeze_cells(&csv, "fixture");
        assert_eq!(
            frozen.len(),
            2,
            "K8 is unprobed and K32 is out of band: {frozen:?}"
        );
        let mut ks: Vec<usize> = frozen.iter().map(|cell| cell.k).collect();
        ks.sort_unstable();
        assert_eq!(ks, vec![4, 24]);
        for cell in &frozen {
            // The SHORT form, and the class recovered from `round` / `d2_policy`.
            assert_eq!(cell.circuit, ADD_SUB_LAYOUT_SHORT);
            assert_eq!(cell.class, SegRoundClass::R0);
            assert_eq!(cell.layer, 0);
            // And the shape round-trips back to the row that produced it.
            assert_eq!(
                frozen_cell_shape(cell),
                SegShape::regs(
                    cell.k,
                    CoeffMode::Constant,
                    ProgramMode::Inline,
                    BwdSegEpilogue::Plane
                )
            );
        }
        // The WRITE, which re-asserts the probed-tuple and coordinate predicates — this is
        // the assertion the long circuit form fails.
        let dir = std::env::temp_dir().join(format!("seg_freeze_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("freeze dir");
        let path = dir.join(SEG_FROZEN_CELLS_TSV);
        write_frozen_cells(
            &path,
            "r0-headline",
            &frozen,
            SEG_SCHEDULE_SEED,
            &converged_probes(),
        );
        assert_eq!(read_frozen_cells(&path, "r0-headline"), frozen);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The GATE's own predicate, on CPU: `select_winner(...).ratio.selectable()`
    /// inverts on an inverting matrix and does not on a regressed one.
    ///
    /// `run_r0_matrix` reports exactly this composition per process, and
    /// `bwd_seg_aggregate_r0_headline` is the campaign verdict over three of them;
    /// both need a GPU. Proving the composition DISCRIMINATES belongs here, or the
    /// gate would rest on "it passed once with the assert in place" — which is
    /// equally true of an assertion that can never fail.
    #[test]
    fn the_gate_predicate_separates_an_inverting_matrix_from_a_regressed_one() {
        let matrix_with = |ratio: RatioEstimate| vec![row_fixture(4, 6, Some(ratio))];
        let gate_holds = |rows: &[SegMatrixRow]| {
            select_winner(rows)
                .expect("a launchable production row")
                .ratio
                .selectable()
                .expect("a paired row whose order gate passed")
                .0
                .inverts()
        };

        // The shape the GPU gate actually measured: whole interval below one.
        assert!(gate_holds(&matrix_with(RatioEstimate {
            median_ratio: 0.9722,
            ci_low: 0.9722,
            ci_high: 0.9726,
        })));
        // Measurably slower — the regression the reviewer's finding was about.
        assert!(!gate_holds(&matrix_with(RatioEstimate {
            median_ratio: 1.0499,
            ci_low: 1.0499,
            ci_high: 1.0502,
        })));
        // Merely CLOSED: the median wins but the interval spans 1.0. The plan does
        // NOT accept this, and neither may the gate.
        assert!(!gate_holds(&matrix_with(RatioEstimate {
            median_ratio: 0.998,
            ci_low: 0.990,
            ci_high: 1.004,
        })));
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
            // A fixture's paired ratio is a PASSING one: the order-gate axis has its
            // own tests above, and a fixture that failed the gate would carry no
            // ratio at all.
            ratio: match ratio {
                Some(estimate) => SegRatio::Valid {
                    estimate,
                    order: SegOrderInteraction {
                        delta_order_pct: 0.0,
                        ci_low_pct: -0.02,
                        ci_high_pct: 0.02,
                    },
                    conditional_medians: [5_000.0, 6_101.5, 5_000.0, 6_101.5],
                },
                None => SegRatio::Solo,
            },
            run_id: if ratio.is_some() {
                "r0001-aaaaaaaaaaaa"
            } else {
                "-"
            },
            baseline: if ratio.is_some() { "incumbent" } else { "-" },
            // A LOWERING property, so it is present on the unlaunchable fixture too —
            // that is exactly the row the zero convention must stay distinguishable from.
            floor: BwdSegTrafficFloor {
                read_bytes: 1_073_741_824,
                write_bytes: 268_435_456,
            },
            carveout_mode: "common-bucket",
            carveout_requested_pct: Some(31),
            // Prose WITH a comma in it, so the renderer's separator handling is
            // exercised by the column test rather than assumed.
            carveout_source: "candidate, 30720 B (both arms quantize alike)".to_owned(),
            pin_role: SegPinRole::Decision,
            // The default the R0 headline and every replacement-candidate campaign carry;
            // the two tests that care about the reference-clock pairing override it.
            pairing: SegPairing::CandidateVsIncumbent,
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
            floor: BwdSegTrafficFloor {
                read_bytes: 33_554_432,
                write_bytes: 8_388_608,
            },
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
            assert_eq!(got.floor, want.floor, "the v3 floor columns round-trip");
        }
        // The zero convention is what an untimed row carries, and it survives the trip.
        assert_eq!(back[4].floor, BwdSegTrafficFloor::default());
        assert_eq!(back[5].floor, BwdSegTrafficFloor::default());
    }

    /// The corpus twin of `SegMatrixRow::protocol()`'s `SegRatio::Solo` discriminator:
    /// an ORDER-COUPLED paired cell has no interval, and inferring the protocol from
    /// the interval labelled it `solo` while it still carried `baseline_median_us`.
    /// The column exists so no table can quietly mix the two protocols, so this
    /// asserts the whole truth table — through the CSV as well, since the policy pass
    /// reads chunks back rather than the in-process rows.
    #[test]
    fn the_corpus_protocol_column_never_calls_a_paired_cell_solo() {
        // Paired and selectable: an interval survived.
        let paired = corpus_fixture(8, SegCorpusStatus::Timed, Some(0.97));
        assert_eq!(paired.protocol(), "paired");
        // Paired and ORDER-COUPLED: `selectable()` yielded `None`, so no interval was
        // recorded — but a baseline arm WAS sampled, and the row says so.
        let coupled = SegCorpusRow {
            ratio_vs_baseline: None,
            ..paired.clone()
        };
        assert!(
            coupled.baseline_median_us.is_some(),
            "the fixture is paired"
        );
        assert_eq!(
            coupled.protocol(),
            "paired",
            "an order-coupled cell was timed PAIRED; calling it solo contradicts its \
             own baseline_median_us"
        );
        // Genuinely solo: the baseline rung has nothing sampled beside it.
        let solo = corpus_fixture(4, SegCorpusStatus::Timed, None);
        assert_eq!(solo.protocol(), "solo");
        assert!(solo.baseline_median_us.is_none());
        // A schema-v1 chunk has no `baseline_median_us` at all; its ratio still
        // identifies it as paired.
        let v1_paired = SegCorpusRow {
            baseline_median_us: None,
            ..paired.clone()
        };
        assert_eq!(v1_paired.protocol(), "paired");
        // And an unmeasured row claims no protocol either way.
        assert_eq!(
            corpus_fixture(32, SegCorpusStatus::Unlaunchable, None).protocol(),
            "-"
        );
        // Through the CSV, which is what the policy pass actually reads.
        let back = parse_corpus_csv(&render_corpus_csv(&[coupled, solo]));
        assert_eq!(back[0].protocol(), "paired", "{back:?}");
        assert!(
            back[0].ratio_vs_baseline.is_none(),
            "the withheld interval stays withheld"
        );
        assert_eq!(back[1].protocol(), "solo", "{back:?}");
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
        // Six dashes — no median, no min, no baseline median, no interval — then the two
        // floor columns at the "no lowering output" zero, which is what an untimed row
        // honestly has.
        assert!(row.ends_with(",-,-,-,-,-,-,0,0"), "{row}");
    }

    /// The parse must not silently accept a table whose columns moved.
    #[test]
    #[should_panic(expected = "missing the required column")]
    fn a_shifted_corpus_header_is_rejected() {
        parse_corpus_csv("circuit,layer,class\nadd_sub,0,R0\n");
    }

    /// A schema-v1 chunk — everything measured before `baseline_median_us` existed —
    /// and a schema-v2 one, measured before the traffic floors existed, must still
    /// read, and must read the SAME values for every column they DO carry.
    ///
    /// Positional parsing made this impossible: adding one column would have meant
    /// re-running twelve locked GPU chunks. Name resolution is what keeps the
    /// on-disk record valid across every schema change.
    #[test]
    fn a_schema_v1_chunk_still_reads_and_agrees_with_v2() {
        let rows = vec![
            corpus_fixture(4, SegCorpusStatus::Timed, None),
            corpus_fixture(8, SegCorpusStatus::Timed, Some(0.97)),
        ];
        let v3 = render_corpus_csv(&rows);
        // Strip one NAMED column from the header and from every row.
        let strip = |text: &str, column: &str| -> String {
            let at = text
                .lines()
                .next()
                .expect("a header")
                .split(',')
                .position(|name| name == column)
                .unwrap_or_else(|| panic!("{column} is in the header"));
            text.lines()
                .map(|line| {
                    let mut field: Vec<&str> = line.split(',').collect();
                    field.remove(at);
                    format!("{}\n", field.join(","))
                })
                .collect()
        };
        // v2 = v3 without the two floor columns; v1 = v2 without the baseline median.
        let v2 = strip(&strip(&v3, "floor_dram_write_bytes"), SEG_CORPUS_V3_COLUMN);
        let v1 = strip(&v2, SEG_CORPUS_V2_COLUMN);
        assert!(!v2.contains(SEG_CORPUS_V3_COLUMN) && !v2.contains("floor_dram_write_bytes"));
        assert!(v2.contains(SEG_CORPUS_V2_COLUMN) && !v1.contains(SEG_CORPUS_V2_COLUMN));
        let from_v1 = parse_corpus_csv(&v1);
        let from_v2 = parse_corpus_csv(&v2);
        let from_v3 = parse_corpus_csv(&v3);
        assert_eq!(from_v1.len(), from_v3.len());
        assert_eq!(from_v2.len(), from_v3.len());
        for ((old, mid), new) in from_v1.iter().zip(from_v2.iter()).zip(from_v3.iter()) {
            assert_eq!(old.facts, new.facts);
            assert_eq!(old.median_us, new.median_us);
            assert_eq!(old.ratio_vs_baseline, new.ratio_vs_baseline);
            assert_eq!(mid.facts, new.facts);
            assert_eq!(mid.baseline_median_us, new.baseline_median_us);
            assert_eq!(
                old.baseline_median_us, None,
                "a v1 chunk cannot carry the baseline median"
            );
            // An absent floor column reads as the "no lowering output" zero — the same
            // way a rejected and an over-budget row read, which is correct: none of the
            // three carries a floor.
            assert_eq!(old.floor, BwdSegTrafficFloor::default());
            assert_eq!(mid.floor, BwdSegTrafficFloor::default());
            assert_eq!(new.floor, rows[0].floor);
        }
        assert!(from_v3[1].baseline_median_us.is_some());
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

    #[test]
    fn the_pin_decision_set_is_predeclared_and_well_formed() {
        assert_eq!(SEG_PIN_DECISION_CELLS.len(), 7);
        assert_eq!(
            SEG_PIN_DECISION_CELLS
                .iter()
                .filter(|c| c.role == SegPinRole::DriftControl)
                .count(),
            1
        );
        // The drift control MUST be R0 — that is the whole reason it is pin-invariant.
        let control = SEG_PIN_DECISION_CELLS
            .iter()
            .find(|c| c.role == SegPinRole::DriftControl)
            .unwrap();
        assert_eq!(control.class, SegRoundClass::R0);
        // Every decision cell MUST be a continuation class: R0 cannot decide a pin.
        for cell in SEG_PIN_DECISION_CELLS
            .iter()
            .filter(|c| c.role == SegPinRole::Decision)
        {
            assert_ne!(cell.class, SegRoundClass::R0, "{} is not swept", cell.label);
        }
    }

    #[test]
    fn the_d3_attribution_set_is_the_delta3_bearing_shapes() {
        assert_eq!(SEG_D3_ATTRIBUTION_CELLS.len(), 7);
        assert_eq!(
            SEG_D3_ATTRIBUTION_CELLS
                .iter()
                .filter(|c| c.role == SegPinRole::DriftControl)
                .count(),
            1
        );
        // Every decision cell is D3 or D2-materialize at K in {16, 24, 32} — the cells
        // results §2.6 shows moving. A cell outside that set carries no δ3 to attribute.
        for c in SEG_D3_ATTRIBUTION_CELLS
            .iter()
            .filter(|c| c.role == SegPinRole::Decision)
        {
            assert!(
                matches!(c.class, SegRoundClass::D3 | SegRoundClass::D2Materialize),
                "{} is not a δ3-bearing class",
                c.label
            );
            assert!(
                matches!(c.k, 16 | 24 | 32),
                "{} is not at K 16/24/32",
                c.label
            );
        }
        // And the two sets are disjoint in label, so a freeze cannot be misread.
        for a in &SEG_D3_ATTRIBUTION_CELLS {
            for b in &SEG_PIN_DECISION_CELLS {
                if a.role == SegPinRole::DriftControl && b.role == SegPinRole::DriftControl {
                    continue; // the shared drift control is deliberate
                }
                assert_ne!(a.label, b.label, "label {} is in both sets", a.label);
            }
        }
    }

    /// One cell summary whose three processes all carry `est`.
    ///
    /// `Vec<Option<f64>>`: a per-PROCESS `None` is what an order-invalid process looks
    /// like, and the rule must see it rather than a pre-reduced median.
    fn pin_cell_fixture(label: &str, role: SegPinRole, est: Option<f64>) -> SegPinCellSummary {
        SegPinCellSummary {
            label: label.to_owned(),
            role,
            estimate: est,
            process_ratios: vec![est, est, est],
        }
    }

    /// One LEVEL's seven predeclared pin cells.
    ///
    /// All seven, because `summarize_pin_decision` asserts the exact set per level. `base`
    /// drives all six decision cells with a deterministic spread (`base + i * 0.002`,
    /// i = 0..6), so the level aggregate is a genuine median OVER SIX VALUES and equals
    /// **`base + 0.005`** (`median` averages the two middle elements of an even count).
    /// An earlier fixture held four cells flat at `base`, which made the median equal
    /// `base` while the test asserted the mean of the first two; it passed for the wrong
    /// reason and tested only two of the six cells.
    fn pin_level_fixture(
        name: &str,
        base: Option<f64>,
        ctrl: f64,
    ) -> (String, Vec<SegPinCellSummary>) {
        let at = |i: usize| base.map(|b| b + i as f64 * 0.002);
        (
            name.to_owned(),
            vec![
                pin_cell_fixture("cont-d1-k4", SegPinRole::Decision, at(0)),
                pin_cell_fixture("cont-d1-k8", SegPinRole::Decision, at(1)),
                pin_cell_fixture("cont-d2i-k8", SegPinRole::Decision, at(2)),
                pin_cell_fixture("cont-d2i-k16", SegPinRole::Decision, at(3)),
                pin_cell_fixture("cont-d3-k16", SegPinRole::Decision, at(4)),
                pin_cell_fixture("cont-d3-k24", SegPinRole::Decision, at(5)),
                pin_cell_fixture("r0-drift-k4", SegPinRole::DriftControl, Some(ctrl)),
            ],
        )
    }

    /// The level aggregate `pin_level_fixture` produces for a given base.
    fn pin_expected_aggregate(base: f64) -> f64 {
        base + 0.005
    }

    /// The argmin level of a resolved decision's aggregates — what an implementation that
    /// skipped the tie set would return.
    fn pin_argmin(aggregates: &[(String, f64)]) -> String {
        aggregates
            .iter()
            .min_by(|a, b| a.1.partial_cmp(&b.1).expect("finite aggregate"))
            .expect("at least one decision level")
            .0
            .clone()
    }

    /// The pin rule is NOT the inversion rule, and it fails closed.
    #[test]
    fn the_pin_rule_is_distinct_and_fails_closed() {
        let cell = pin_cell_fixture;
        let level = pin_level_fixture;
        let expect_aggregate = pin_expected_aggregate;
        // Every fixture carries the MANDATORY natural-repeat, or `summarize_pin_decision`
        // panics on its own exact-set assertion before any rule runs. The scored set is
        // `SEG_PIN_DECISION_LEVELS` = {natural, 48}; `40` is refused (R4 + R8) and its
        // presence is a caller error, pinned by
        // `the_pin_rule_refuses_a_predeclared_ineligible_level`.
        let clean = vec![
            level("natural", Some(1.000), 1.0000),
            level("48", Some(0.960), 1.0001),
            level("natural-repeat", Some(1.001), 1.0000),
        ];
        assert!(matches!(
            summarize_pin_decision(&clean),
            SegPinSummary::Resolved { ref winner, .. } if winner == "48"
        ));
        // Ratios ABOVE 1.0 must not make the decision "not inverted" — that is §6(b)'s
        // question, not this one. The lowest-ceiling level still wins on aggregate.
        let above = vec![
            level("natural", Some(1.400), 1.0),
            level("48", Some(1.300), 1.0),
            level("natural-repeat", Some(1.401), 1.0),
        ];
        assert!(
            matches!(
                summarize_pin_decision(&above),
                SegPinSummary::Resolved { ref winner, .. } if winner == "48"
            ),
            "the pin decision is relative; 1.0 has no meaning in it"
        );
        // The REFUSED level is on the summary, on the resolved path too — a consumer cannot
        // render a level table that omits it.
        match summarize_pin_decision(&clean) {
            SegPinSummary::Resolved { ref refused, .. } => {
                assert_eq!(refused.len(), 1);
                assert_eq!(refused[0].0, "40");
                assert!(
                    refused[0].1.contains("localSizeBytes=16"),
                    "the refusal carries its MEASURED reason: {:?}",
                    refused[0].1
                );
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
        // An order-invalid cell anywhere ⇒ UNRESOLVED, never a shrunken cell set.
        let mut invalid = clean.clone();
        invalid[1].1[0].estimate = None;
        invalid[1].1[0].process_ratios = vec![None, Some(0.9), Some(0.9)];
        let s = summarize_pin_decision(&invalid);
        assert!(matches!(s, SegPinSummary::Unresolved { .. }));
        // And there is NO aggregate to read — the type has none on this path.
        if let SegPinSummary::Unresolved {
            ref per_level_usable,
            ..
        } = s
        {
            assert!(per_level_usable.iter().any(|(_, ok, total)| ok < total));
        }
        // A margin below the control's own drift ⇒ UNRESOLVED.
        let noisy = vec![
            level("natural", Some(1.000), 1.000),
            level("48", Some(0.998), 1.030),
            level("natural-repeat", Some(1.000), 1.000),
        ];
        assert!(matches!(
            summarize_pin_decision(&noisy),
            SegPinSummary::Unresolved { .. }
        ));
        // A repeat that does not reproduce ⇒ UNRESOLVED, and it is compared ONLY to
        // natural (never aggregated, never in the tie set, never in the drift spread).
        let mut repeat = clean.clone();
        repeat[2] = level("natural-repeat", Some(1.050), 1.0);
        assert!(matches!(
            summarize_pin_decision(&repeat),
            SegPinSummary::Unresolved { .. }
        ));
        // The control is EXCLUDED from the aggregate, and the resolved variant is the
        // ONLY one carrying aggregates at all.
        match summarize_pin_decision(&clean) {
            SegPinSummary::Resolved {
                winner,
                aggregates,
                tie_set,
                ..
            } => {
                assert_eq!(winner, "48");
                let agg48 = aggregates.iter().find(|(l, _)| l == "48").unwrap().1;
                assert!(
                    (agg48 - expect_aggregate(0.960)).abs() < 1e-9,
                    "the level aggregate is the median over ALL SIX decision cells \
                     (0.960..0.970), i.e. {}; got {agg48}",
                    expect_aggregate(0.960)
                );
                assert!(!tie_set.contains(&"natural-repeat".to_owned()));
                assert_eq!(
                    aggregates.len(),
                    SEG_PIN_DECISION_LEVELS.len(),
                    "the repeat is not a decision level, and the refused level is not one \
                     either"
                );
                assert!(!aggregates.iter().any(|(l, _)| l == "40"));
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    /// **The tie-break's DISCRIMINATING case.** Every fixture in
    /// `the_pin_rule_is_distinct_and_fails_closed` leaves the tie set a SINGLETON equal to
    /// the argmin, so an implementation that simply returned the fastest level passes all of
    /// them and the rule's actual content — "lowest register ceiling **within the tie set**"
    /// — stays untested. The fixture here makes the argmin and the rule's answer DIFFERENT
    /// levels, so `winner == pin_argmin(..)` fails it.
    ///
    /// **Only ONE discriminating case survives ruling R8**, and that is not a gap. With the
    /// eligible set `{natural, 48}` the ceilings are 56 and 48, so the sole way for the
    /// argmin to differ from the winner is `natural` fastest with `48` inside the band. The
    /// old second case (48 fastest, 40 tied ⇒ 40 wins) required a scoreable `40`, which the
    /// measured refusal removes; the rule it exercised is the same one this case exercises.
    #[test]
    fn the_pin_tie_break_prefers_the_lowest_ceiling_in_the_tie_set() {
        let level = pin_level_fixture;
        // natural is the ARGMIN and 48 is inside `SEG_PIN_TIE_FRACTION` of it, so the rule
        // must prefer the PINNED 48 over natural's 56. Aggregates are `base + 0.005`, so
        // 0.900 vs 0.905 — a 0.556% margin, inside the 0.93% band and above the control's
        // zero spread. This is R8's predeclared consequence: 48 is the lowest ELIGIBLE
        // ceiling, so a natural-vs-48 tie resolves to 48.
        let tied_with_natural = vec![
            level("natural", Some(0.895), 1.0),
            level("48", Some(0.900), 1.0),
            level("natural-repeat", Some(0.895), 1.0),
        ];
        match summarize_pin_decision(&tied_with_natural) {
            SegPinSummary::Resolved {
                winner,
                aggregates,
                tie_set,
                ..
            } => {
                assert!(
                    (aggregates.iter().find(|(l, _)| l == "48").expect("48").1
                        - pin_expected_aggregate(0.900))
                    .abs()
                        < 1e-9
                );
                assert_eq!(
                    pin_argmin(&aggregates),
                    "natural",
                    "natural is the fastest level here"
                );
                assert_eq!(
                    tie_set.len(),
                    2,
                    "both eligible levels are tied: {tie_set:?}"
                );
                assert_eq!(
                    winner, "48",
                    "48 < natural's 56, so the pinned level wins (R8: lowest ELIGIBLE ceiling)"
                );
                assert_ne!(
                    winner,
                    pin_argmin(&aggregates),
                    "an argmin-only selector would answer natural and pass every other fixture"
                );
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
        // And a level genuinely outside the band is NOT tied, so the tie-break cannot reach
        // it: natural 11% behind leaves 48 alone in the tie set.
        let untied = vec![
            level("natural", Some(0.995), 1.0),
            level("48", Some(0.895), 1.0),
            level("natural-repeat", Some(0.995), 1.0),
        ];
        match summarize_pin_decision(&untied) {
            SegPinSummary::Resolved {
                winner, tie_set, ..
            } => {
                assert_eq!(tie_set, vec!["48".to_owned()], "natural is 11% away");
                assert_eq!(winner, "48");
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    /// **A PREDECLARED-INELIGIBLE level in the input is REFUSED, not silently dropped.**
    ///
    /// This is the eligibility filter itself, and it must fail loudly. Dropping level `40`
    /// quietly would let a caller hand in a spilled level's numbers and receive a decision
    /// that looks like it scored three levels — the fail-open that the old
    /// mandatory-`40` array made impossible only by making the rule unreachable. R8 keeps
    /// the loudness and removes the unreachability.
    #[test]
    #[should_panic(expected = "PREDECLARED INELIGIBLE")]
    fn the_pin_rule_refuses_a_predeclared_ineligible_level() {
        let level = pin_level_fixture;
        let with_40 = vec![
            level("natural", Some(1.000), 1.0),
            level("48", Some(0.960), 1.0),
            level("40", Some(0.900), 1.0),
            level("natural-repeat", Some(1.001), 1.0),
        ];
        let _ = summarize_pin_decision(&with_40);
    }

    /// The δ3 rule is NOT the pin rule and NOT the inversion rule, and it fails closed.
    #[test]
    fn the_d3_attribution_rule_scores_two_arms_and_fails_closed() {
        let cell = |label: &str, role, est: Option<f64>| SegPinCellSummary {
            label: label.to_owned(),
            role,
            estimate: est,
            process_ratios: vec![est, est, est],
        };
        // All seven attribution cells, driven from a base so each is distinct.
        let arm = |name: &str, base: Option<f64>, ctrl: f64| {
            let at = |i: usize| base.map(|b| b + i as f64 * 0.01);
            (
                name.to_owned(),
                vec![
                    cell("d3-attr-d3-k16", SegPinRole::Decision, at(0)),
                    cell("d3-attr-d3-k24", SegPinRole::Decision, at(1)),
                    cell("d3-attr-d3-k32", SegPinRole::Decision, at(2)),
                    cell("d3-attr-d2m-k16", SegPinRole::Decision, at(3)),
                    cell("d3-attr-d2m-k24", SegPinRole::Decision, at(4)),
                    cell("d3-attr-d2m-k32", SegPinRole::Decision, at(5)),
                    cell("r0-drift-k4", SegPinRole::DriftControl, Some(ctrl)),
                ],
            )
        };
        let rolled = vec![arm("40", Some(1.000), 1.0)];
        let unrolled = vec![arm("d3unroll", Some(0.900), 1.0002)];
        match summarize_d3_attribution(&rolled, &unrolled) {
            SegD3Attribution::Scored { ref cells, drift } => {
                // SIX scored cells: the drift control is reported separately, never pooled.
                assert_eq!(cells.len(), 6);
                for (label, r, u, ratio) in cells {
                    assert!(u < r, "{label}: the unrolled arm is faster in this fixture");
                    assert!(
                        (ratio - u / r).abs() < 1e-12,
                        "{label}: ratio is unrolled/rolled"
                    );
                }
                assert!((drift.0 - 1.0).abs() < 1e-12 && (drift.1 - 1.0002).abs() < 1e-12);
            }
            other => panic!("expected Scored, got {other:?}"),
        }
        // An order-invalid cell on EITHER arm makes the attribution Unresolved, and the
        // Unresolved variant carries no ratios.
        let mut bad = unrolled.clone();
        bad[0].1[2].estimate = None;
        bad[0].1[2].process_ratios = vec![None, Some(0.9), Some(0.9)];
        match summarize_d3_attribution(&rolled, &bad) {
            SegD3Attribution::Unresolved {
                ref reason,
                ref cells,
            } => {
                assert!(reason.contains("d3-attr-d3-k32"), "{reason}");
                assert_eq!(cells.len(), SEG_D3_ATTRIBUTION_CELLS.len());
                assert!(cells.iter().any(|(_, _, u)| u.is_none()));
            }
            other => panic!("expected Unresolved, got {other:?}"),
        }
    }

    /// A SWAPPED or mismatched `BWD_SEG_CONFIRM_DIRS` is refused before the directional
    /// call, because `summarize_d3_attribution` cannot see the swap itself.
    #[test]
    fn the_arm_split_refuses_a_swapped_or_mismatched_spec() {
        let ok = "40=/a:/b:/c;d3unroll=/d:/e:/f";
        let (rolled, unrolled) = split_d3_arms(ok, "40");
        assert_eq!(rolled.len(), 3);
        assert_eq!(unrolled.len(), 3);
        assert_eq!(rolled[0], PathBuf::from("/a"));
        // The winner key must be present: a spec naming a DIFFERENT rolled level is not
        // the attribution the decision licensed.
        assert!(std::panic::catch_unwind(|| split_d3_arms(ok, "48")).is_err());
        // Two unrolled arms, no rolled arm.
        assert!(
            std::panic::catch_unwind(|| { split_d3_arms("d3unroll=/a;d3unroll=/b", "40") })
                .is_err()
        );
        // A third arm.
        assert!(
            std::panic::catch_unwind(|| { split_d3_arms("40=/a;d3unroll=/b;48=/c", "40") })
                .is_err()
        );
        // The winner cannot BE the unrolled arm.
        assert!(std::panic::catch_unwind(|| {
            split_d3_arms("d3unroll=/a;d3unroll=/b", "d3unroll")
        })
        .is_err());
        // A single arm.
        assert!(std::panic::catch_unwind(|| split_d3_arms("40=/a", "40")).is_err());
    }

    /// Group ORDER in the spec is irrelevant — the mapping is by key, not by position.
    #[test]
    fn the_arm_split_is_order_independent() {
        let (a, b) = split_d3_arms("40=/a:/b:/c;d3unroll=/d:/e:/f", "40");
        let (c, d) = split_d3_arms("d3unroll=/d:/e:/f;40=/a:/b:/c", "40");
        assert_eq!(a, c);
        assert_eq!(b, d);
        assert_eq!(a[0], PathBuf::from("/a"));
        assert_eq!(b[0], PathBuf::from("/d"));
    }

    /// The bindings must catch a full PAYLOAD SWAP, which exact keys alone cannot: swapping
    /// the two directory lists leaves both keys valid, both arms share `pin_level` by
    /// design, and "archives differ" is symmetric.
    #[test]
    fn the_arm_bindings_catch_a_payload_swap_and_its_neighbours() {
        // THREE identities per arm, labelled `<prefix><1..3>` exactly as the launcher
        // stamps them — the binding checks every run, so a one-run fixture would not even
        // reach the checks it is meant to exercise.
        let id = |prefix: &str, run: usize, arch: &str, bin: &str, pin: &str| SegRunMeta {
            run_id: format!("r000{run}-{arch}"),
            commit: "c".to_owned(),
            feature_set: "bench".to_owned(),
            run_label: format!("{prefix}{run}"),
            pin_level: pin.to_owned(),
            archive_sha256: arch.repeat(64),
            test_binary_sha256: bin.repeat(64),
            toolkit: "13.3".to_owned(),
            device: "d".to_owned(),
            seed: SEG_SCHEDULE_SEED,
        };
        let ev =
            |prefix: &'static str, arch: &'static str, bin: &'static str, pin: &'static str| {
                SegArmEvidence {
                    cells: Vec::new(),
                    identities: (1..=SEG_CONFIRM_PROCESSES)
                        .map(|run| id(prefix, run, arch, bin, pin))
                        .collect(),
                    dirs: Vec::new(),
                }
            };
        let want = |prefix: &'static str, arch: &str, bin: &str| SegExpectedArm {
            run_label_prefix: prefix,
            archive_sha256: arch.repeat(64),
            test_binary_sha256: bin.repeat(64),
        };
        let er = want("d3attr-rolled-", "a", "b");
        let eu = want("d3attr-d3unroll-", "c", "d");
        let rolled = ev("d3attr-rolled-", "a", "b", "40");
        let unrolled = ev("d3attr-d3unroll-", "c", "d", "40");
        // Positive: the correct mapping passes.
        assert_d3_arm_identities("40", &rolled, &unrolled, &er, &eu);
        // PAYLOAD SWAP: each arm's dirs carry the OTHER build's identity.
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities("40", &unrolled, &rolled, &er, &eu)
        })
        .is_err());
        // Same archive (the define did not reach nvcc).
        let same = ev("d3attr-d3unroll-", "a", "d", "40");
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities(
                "40",
                &rolled,
                &same,
                &er,
                &want("d3attr-d3unroll-", "a", "d"),
            )
        })
        .is_err());
        // Same TEST BINARY (one measurement twice) though the archives differ.
        let samebin = ev("d3attr-d3unroll-", "c", "b", "40");
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities(
                "40",
                &rolled,
                &samebin,
                &er,
                &want("d3attr-d3unroll-", "c", "b"),
            )
        })
        .is_err());
        // Pin MISMATCH between the arms.
        let otherpin = ev("d3attr-d3unroll-", "c", "d", "48");
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities("40", &rolled, &otherpin, &er, &eu)
        })
        .is_err());
        // The rolled arm's COMPILED pin is not the independently derived winner.
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities("48", &rolled, &unrolled, &er, &eu)
        })
        .is_err());
        // A wholly mislabelled arm (the second, independent binding).
        let mislabelled = ev("d3attr-d3unroll-", "a", "b", "40");
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities("40", &mislabelled, &unrolled, &er, &eu)
        })
        .is_err());
        // And the counterexample that a REPRESENTATIVE check accepts: run 1 correctly
        // labelled, runs 2 and 3 carrying the other arm's prefix, everything else right.
        let mut partial = ev("d3attr-rolled-", "a", "b", "40");
        for run in 2..=SEG_CONFIRM_PROCESSES {
            partial.identities[run - 1].run_label = format!("d3attr-d3unroll-{run}");
        }
        assert_eq!(
            partial.constant().run_label,
            "d3attr-rolled-1",
            "run 1 looks correct"
        );
        assert!(
            std::panic::catch_unwind(|| {
                assert_d3_arm_identities("40", &partial, &unrolled, &er, &eu)
            })
            .is_err(),
            "a per-run label defect slipped past the binding"
        );
        // A short arm (two runs) is refused: three processes are predeclared.
        let mut short = ev("d3attr-rolled-", "a", "b", "40");
        short.identities.pop();
        assert!(std::panic::catch_unwind(|| {
            assert_d3_arm_identities("40", &short, &unrolled, &er, &eu)
        })
        .is_err());
    }

    /// **`aggregate_arm` is DRIVEN, not merely defined.** None of the identity fixtures
    /// calls it (they synthesise `SegArmEvidence`), so without this the "executable
    /// integration" would rest on a function no test ever ran — and its first real call in
    /// Task 10 would be its first execution ever.
    #[test]
    #[serial_test::serial]
    fn aggregate_arm_returns_identity_and_per_cell_summaries() {
        let root = std::env::temp_dir().join(format!("seg_arm_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        // Three synthetic run dirs, each a real raw TSV written by the real writer, so the
        // fixture exercises the actual round trip rather than a hand-rolled file.
        let cells = &SEG_D3_ATTRIBUTION_CELLS;
        let mut dirs = Vec::new();
        // Labels are `-1/-2/-3`, exactly as `for RUN in 1 2 3` stamps them in Task 10 — the
        // per-run binding compares against `<prefix><index+1>`, so a 0-based fixture would
        // pass a test the production labels fail.
        for run in 1..=SEG_CONFIRM_PROCESSES {
            let dir = root.join(format!("r{run}"));
            std::fs::create_dir_all(&dir).expect("run dir");
            let meta = SegRunMeta {
                run_id: format!("r000{run}-aaaaaaaaaaaa"), // DISTINCT per run
                commit: "c".to_owned(),
                feature_set: "bench".to_owned(),
                run_label: format!("d3attr-rolled-{run}"),
                pin_level: "40".to_owned(),
                archive_sha256: "a".repeat(64),
                test_binary_sha256: "b".repeat(64),
                toolkit: "13.3".to_owned(),
                device: "d".to_owned(),
                seed: SEG_SCHEDULE_SEED,
            };
            // Cell 0 is order-INDEPENDENT (its gate passes); cell 1 is order-COUPLED in the
            // third run only, so the aggregate must report `None` for it and `Some` for the
            // other SIX (seven cells minus the one invalid).
            for (index, cell) in cells.iter().enumerate() {
                let coupled = index == 1 && run == SEG_CONFIRM_PROCESSES;
                let samples =
                    blocked_fixture(SEG_SCHEDULE_SEED, move |arm, orientation, _, _| match arm {
                        SegArm::A => {
                            if coupled && orientation == SegBlockOrientation::Baab {
                                104.0
                            } else {
                                90.0
                            }
                        }
                        SegArm::B => 100.0,
                    });
                // SAFETY-of-contract: `record_raw_samples` reads the reserved directory from
                // the environment, exactly as a campaign process does.
                std::env::set_var("BWD_SEG_RUN_DIR", &dir);
                record_raw_samples(&meta, cell.label, &samples);
            }
            dirs.push(dir);
        }
        std::env::remove_var("BWD_SEG_RUN_DIR");
        let arm = aggregate_arm(&dirs, cells);
        // The identity is RETURNED, validated across the three runs.
        assert_eq!(arm.constant().archive_sha256, "a".repeat(64));
        assert_eq!(arm.constant().test_binary_sha256, "b".repeat(64));
        assert_eq!(arm.constant().pin_level, "40");
        // ALL identities are preserved, with their per-run labels intact.
        assert_eq!(arm.identities.len(), SEG_CONFIRM_PROCESSES);
        for (index, id) in arm.identities.iter().enumerate() {
            assert_eq!(id.run_label, format!("d3attr-rolled-{}", index + 1));
        }
        assert_eq!(arm.dirs.len(), SEG_CONFIRM_PROCESSES);
        // One summary per predeclared cell, in order, with roles carried.
        assert_eq!(arm.cells.len(), cells.len());
        for (got, want) in arm.cells.iter().zip(cells.iter()) {
            assert_eq!(got.label, want.label);
            assert_eq!(got.role, want.role);
            assert_eq!(got.process_ratios.len(), SEG_CONFIRM_PROCESSES);
        }
        // Cell 0: every process usable, so the estimate is the median of three 0.9s.
        assert!((arm.cells[0].estimate.expect("usable") - 0.9).abs() < 1e-9);
        // Cell 1: the third process is order-coupled, so the CELL has no estimate — and the
        // per-process vector shows exactly which one failed. The other SIX are usable.
        assert!(
            arm.cells[1].estimate.is_none(),
            "one bad process voids the cell"
        );
        assert_eq!(
            arm.cells.iter().filter(|c| c.estimate.is_some()).count(),
            SEG_D3_ATTRIBUTION_CELLS.len() - 1
        );
        assert_eq!(
            arm.cells[1]
                .process_ratios
                .iter()
                .filter(|r| r.is_none())
                .count(),
            1
        );
        // And `summarize_d3_attribution` consumes this shape directly.
        let other = aggregate_arm(&dirs, cells);
        assert!(matches!(
            summarize_d3_attribution(
                &[("40".to_owned(), arm.cells.clone())],
                &[("d3unroll".to_owned(), other.cells)],
            ),
            SegD3Attribution::Unresolved { .. }
        ));
        let _ = std::fs::remove_dir_all(&root);
    }

    /// **The D3-SPECIFIC negatives.** The generic reader/provenance defects are Task 2's
    /// (`the_shared_reader_rejects_every_generic_identity_defect`, which drives `read_run`
    /// and `shared_identity` directly); what is left here is what only the D3 layer can get
    /// wrong: cell-set membership against `SEG_D3_ATTRIBUTION_CELLS`, and a per-run label
    /// defect that `shared_identity` correctly ignores and only the arm binding can catch.
    #[test]
    #[serial_test::serial]
    fn the_d3_layer_rejects_membership_and_per_run_label_defects() {
        let cells = &SEG_D3_ATTRIBUTION_CELLS;
        let base = |run: usize| SegRunMeta {
            run_id: format!("r010{run}-aaaaaaaaaaaa"),
            commit: "c".to_owned(),
            feature_set: "bench".to_owned(),
            run_label: format!("d3attr-rolled-{run}"),
            pin_level: "40".to_owned(),
            archive_sha256: "a".repeat(64),
            test_binary_sha256: "b".repeat(64),
            toolkit: "13.3".to_owned(),
            device: "d".to_owned(),
            seed: SEG_SCHEDULE_SEED,
        };
        // Write three runs, with `mutate` allowed to damage run 3's metadata and `skip` /
        // `extra` to damage its cell membership. Returns the three dirs.
        let build = |tag: &str,
                     mutate: &dyn Fn(&mut SegRunMeta),
                     skip: Option<&str>,
                     extra: Option<&str>| {
            let root = std::env::temp_dir().join(format!("seg_raw_{tag}_{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&root);
            let mut dirs = Vec::new();
            for run in 1..=SEG_CONFIRM_PROCESSES {
                let dir = root.join(format!("r{run}"));
                std::fs::create_dir_all(&dir).expect("run dir");
                let mut meta = base(run);
                if run == SEG_CONFIRM_PROCESSES {
                    mutate(&mut meta);
                }
                std::env::set_var("BWD_SEG_RUN_DIR", &dir);
                for cell in cells.iter() {
                    if run == SEG_CONFIRM_PROCESSES && skip == Some(cell.label) {
                        continue;
                    }
                    record_raw_samples(
                        &meta,
                        cell.label,
                        &blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(90.0, 100.0)),
                    );
                }
                if run == SEG_CONFIRM_PROCESSES {
                    if let Some(label) = extra {
                        record_raw_samples(
                            &meta,
                            label,
                            &blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(90.0, 100.0)),
                        );
                    }
                }
                dirs.push(dir);
            }
            std::env::remove_var("BWD_SEG_RUN_DIR");
            (root, dirs)
        };
        let nop: &dyn Fn(&mut SegRunMeta) = &|_| {};
        // POSITIVE control: the clean set aggregates.
        let (root, dirs) = build("ok", nop, None, None);
        assert_eq!(
            aggregate_arm(&dirs, cells).identities.len(),
            SEG_CONFIRM_PROCESSES
        );
        let _ = std::fs::remove_dir_all(&root);
        // Only the MEMBERSHIP defects here; the identity defects are Task 2's, on the
        // generic helpers, where they belong.
        let cases: Vec<(
            &str,
            Box<dyn Fn(&mut SegRunMeta)>,
            Option<&str>,
            Option<&str>,
        )> = vec![
            (
                "missing",
                Box::new(|_: &mut SegRunMeta| {}),
                Some("d3-attr-d3-k24"),
                None,
            ),
            (
                "extra",
                Box::new(|_: &mut SegRunMeta| {}),
                None,
                Some("not-a-decision-cell"),
            ),
        ];
        for (tag, mutate, skip, extra) in cases {
            let (root, dirs) = build(tag, mutate.as_ref(), skip, extra);
            let attempt = std::panic::catch_unwind(|| aggregate_arm(&dirs, cells));
            assert!(attempt.is_err(), "the raw path accepted defect {tag:?}");
            let _ = std::fs::remove_dir_all(&root);
        }
        // A MISLABELLED later run passes `shared_identity` (labels differ by design) and is
        // caught only by the arm binding — which is why that binding checks every run.
        let (root, dirs) = build(
            "mislabel",
            &|m: &mut SegRunMeta| m.run_label = "d3attr-d3unroll-3".to_owned(),
            None,
            None,
        );
        let arm = aggregate_arm(&dirs, cells); // aggregation itself is fine
        let want = SegExpectedArm {
            run_label_prefix: "d3attr-rolled-",
            archive_sha256: "a".repeat(64),
            test_binary_sha256: "b".repeat(64),
        };
        let other = SegExpectedArm {
            run_label_prefix: "d3attr-d3unroll-",
            archive_sha256: "c".repeat(64),
            test_binary_sha256: "e".repeat(64),
        };
        let fake_unrolled = SegArmEvidence {
            cells: arm.cells.clone(),
            identities: (1..=SEG_CONFIRM_PROCESSES)
                .map(|run| {
                    let mut m = base(run);
                    m.run_label = format!("d3attr-d3unroll-{run}");
                    m.archive_sha256 = "c".repeat(64);
                    m.test_binary_sha256 = "e".repeat(64);
                    m
                })
                .collect(),
            dirs: arm.dirs.clone(),
        };
        assert!(
            std::panic::catch_unwind(|| {
                assert_d3_arm_identities("40", &arm, &fake_unrolled, &want, &other)
            })
            .is_err(),
            "a mislabelled later run slipped past the arm binding"
        );
        let _ = std::fs::remove_dir_all(&root);
    }

    /// An order-invalid row has no selectable ratio, so nothing can select on it.
    /// `SegRatio::of` takes the SAMPLES (it must, to compute both the estimate and the
    /// conditional medians), so this drives it through two fixtures: one order-coupled,
    /// one not. The coupled one would otherwise WIN — it is the fastest ratio here.
    #[test]
    fn an_order_invalid_row_is_structurally_unselectable() {
        // 4% slower whenever the candidate does not lead: a large, real order contrast.
        let coupled = blocked_fixture(SEG_SCHEDULE_SEED, |arm, orientation, _, _| match arm {
            SegArm::A => {
                if orientation == SegBlockOrientation::Baab {
                    52.0
                } else {
                    50.0
                }
            }
            SegArm::B => 100.0,
        });
        let clean = blocked_fixture(SEG_SCHEDULE_SEED, flat_cost(90.0, 100.0));
        let bad = SegRatio::of(&coupled);
        let good = SegRatio::of(&clean);
        assert!(matches!(bad, SegRatio::OrderInvalid { .. }));
        assert!(matches!(good, SegRatio::Valid { .. }));
        // The coupled cell has the better raw ratio (~0.51 vs 0.90) and STILL cannot be
        // selected — that is the point of putting the gate in the type.
        assert!(
            bad.selectable().is_none(),
            "an order-coupled cell is not selectable"
        );
        assert!(
            bad.reported_estimate().is_none(),
            "and carries no pooled estimate"
        );
        assert!(bad.order().is_some(), "but its order contrast is published");
        assert!(
            bad.conditional_medians().is_some(),
            "and its conditional medians are"
        );
        assert_eq!(bad.verdict(), "ORDER-COUPLED");
        assert!(good.selectable().is_some());
        assert!(
            good.conditional_medians().is_some(),
            "valid cells carry them too"
        );
    }
}
