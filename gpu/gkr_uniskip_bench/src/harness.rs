//! Device allocations, descriptor upload and the LDE pass.

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::abi::*;
use crate::cache::CachePlan;
use crate::compact::{self, BankPerm};
use crate::coset_cache::{
    self, CacheArm, CacheArmState, CacheLane, CacheMutation, LaneCarrier, LaneKernel, LaneSet,
    PrologueOrder,
};
use crate::domain::lde_matrix;
use crate::geometry::Geometry;
use crate::kernels;
use crate::reference;
use crate::seg::{self, SegPlan};
use crate::synth::SynthProgram;

/// Backing classes: one tap allocation and one coset allocation each.
pub const CLASS_BF: usize = 0;
pub const CLASS_E4: usize = 1;
pub const CLASSES: usize = 2;
/// `u32` words per field element of each class.
pub const CLASS_WORDS: [usize; CLASSES] = [1, 4];

pub fn class_index(source_class: u8) -> usize {
    match source_class {
        UNISKIP_SRC_BF_GLOBAL => CLASS_BF,
        UNISKIP_SRC_E4_GLOBAL => CLASS_E4,
        other => panic!("source class {other} has no backing"),
    }
}

/// Where a window sits inside its class backing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WindowPlacement {
    pub class: usize,
    pub columns: u32,
    /// Field-element offset of the window inside its class backing.
    pub offset: u64,
}

/// ALLOCATION LAYOUT. The windows of one field class share a single tap backing
/// (and an identically shaped coset backing), packed in window order; a window
/// occupies `columns * UNISKIP_TAPS * 2^log_rows` field elements. The init
/// generator's index is the ABSOLUTE element index inside that backing, so
/// `reference.rs` must go through this type rather than the `(window, column)`
/// view — two windows of the same class would otherwise generate identical data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub log_rows: u32,
    pub rows: u64,
    pub windows: [WindowPlacement; UNISKIP_WINDOWS],
    /// Field elements in each class's tap (and coset) backing.
    pub class_elements: [u64; CLASSES],
    /// Element ordering inside a column block. The backing sizes and the window
    /// packing are identical either way — only [`Layout::source_offset`] changes.
    pub source_layout: SourceLayout,
}

impl Layout {
    pub fn new(program: &SynthProgram, geometry: &Geometry, source_layout: SourceLayout) -> Self {
        let mut class_elements = [0u64; CLASSES];
        let mut windows = [WindowPlacement {
            class: CLASS_BF,
            columns: 0,
            offset: 0,
        }; UNISKIP_WINDOWS];
        for (w, placement) in windows.iter_mut().enumerate() {
            let spec = program.windows[w];
            let class = class_index(spec.kind.source_class());
            *placement = WindowPlacement {
                class,
                columns: spec.columns,
                offset: class_elements[class],
            };
            class_elements[class] +=
                u64::from(spec.columns) * UNISKIP_TAPS as u64 * geometry.logical_rows;
        }
        Self {
            log_rows: geometry.log_rows,
            rows: geometry.logical_rows,
            windows,
            class_elements,
            source_layout,
        }
    }

    /// The active ordering's host mirror of the device accessor: the allocation a
    /// `(source, cell)` pair reads and the element offset of `row` inside its window.
    /// [`SourceLayout::LsbGroup`] has no coset allocation at all, so asking it for a
    /// coset cell is a bug, not a fallback.
    pub fn source_offset(
        &self,
        rec: UniskipSourceRecord,
        cell: usize,
        row: u64,
    ) -> (CellBuffer, u64) {
        match self.source_layout {
            SourceLayout::PlaneMajor => source_offset(rec, cell, row, self.log_rows),
            SourceLayout::LsbGroup => {
                let tap = tap_for_cell(cell).unwrap_or_else(|| {
                    panic!(
                        "the LSB ordering has no coset allocation; cell {cell} is produced, not stored"
                    )
                });
                (
                    CellBuffer::Tap,
                    lsb_source_offset(rec, tap, row, self.log_rows),
                )
            }
        }
    }

    /// Byte offset of a window inside its class backing. E4 ALIGNMENT INVARIANT:
    /// the device `load<e4>` reinterprets to `uint4 *`, so every e4 base must be
    /// 16-byte aligned. Offsets count whole field elements, so an e4 window's byte
    /// offset is a multiple of 16, and `cudaMalloc` aligns the backing itself to
    /// far more than that.
    pub fn window_byte_offset(&self, window: usize) -> usize {
        let placement = self.windows[window];
        placement.offset as usize * CLASS_WORDS[placement.class] * size_of::<u32>()
    }

    /// Field elements of one column's 16-plane block.
    pub fn column_elements(&self) -> u64 {
        UNISKIP_TAPS as u64 * self.rows
    }

    /// Element index of `(window, column)`'s block inside its class backing.
    pub fn column_base(&self, window: usize, column: usize) -> u64 {
        self.windows[window].offset + column as u64 * self.column_elements()
    }

    /// Words of each class's backing (both tap and coset).
    pub fn class_words(&self, class: usize) -> usize {
        self.class_elements[class] as usize * CLASS_WORDS[class]
    }

    /// Bytes of the tap backings of both classes; the coset backings match.
    pub fn backing_bytes(&self) -> u64 {
        (0..CLASSES)
            .map(|class| self.class_words(class) as u64 * size_of::<u32>() as u64)
            .sum()
    }
}

/// Grid shape of the coset LDE. `Cell` is the v1 shape — one thread per
/// (job, cell, row), so a row's 16 taps are re-read once per coset cell. `Row` is the
/// intra-thread reshape — one thread per (job, row), per (job, row, limb) for `e4` —
/// which reads each tap once and emits all 16 cells. Both write the same bytes, so
/// they are interchangeable for every consumer and for validation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum LdeShape {
    Cell,
    #[default]
    Row,
}

impl LdeShape {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Cell => "cell",
            Self::Row => "row",
        }
    }
}

/// Where the coset cells come from. `Unfused` materializes them in a separate LDE
/// stage and the eval kernel reads them back — the v1 pass. `FusedRecompute` drops
/// both the LDE launches and the coset backing: the accessor extends the source's
/// 16 taps on read. `FusedCached` adds a fixed shared-memory assignment on top of it,
/// so the planned sources' coset slabs are produced once per 32-row tile instead of
/// once per reference. All three produce the same `q`.
/// `LsbRecompute` is the v3 R0 arm and shares none of that machinery: it re-lays the
/// taps LSB-first (a group is 16 adjacent elements), runs one half-warp per group with
/// lane = tap, and produces all 16 coset cells with a shuffle-NTT per reference. W = 0
/// by construction — no window, no cache, no fold stage.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum EvalMode {
    #[default]
    Unfused,
    FusedRecompute,
    FusedCached,
    LsbRecompute,
    LsbCompact,
    LsbPair,
}

impl EvalMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unfused => "unfused",
            Self::FusedRecompute => "fused-recompute",
            Self::FusedCached => "fused-cached",
            Self::LsbRecompute => "lsb-recompute",
            Self::LsbCompact => "lsb-compact",
            Self::LsbPair => "lsb-pair",
        }
    }

    /// Whether the pass writes a coset backing at all.
    pub fn materializes_coset(self) -> bool {
        self == Self::Unfused
    }

    /// Whether the pass reads the shared-memory cache plan.
    pub fn uses_cache(self) -> bool {
        self == Self::FusedCached
    }

    /// Whether `--pair-arm` names an arm this mode runs.
    pub fn uses_pair_arm(self) -> bool {
        self == Self::LsbPair
    }

    /// Element ordering of the tap backing this mode's accessor expects.
    pub fn source_layout(self) -> SourceLayout {
        match self {
            Self::LsbRecompute | Self::LsbCompact | Self::LsbPair => SourceLayout::LsbGroup,
            _ => SourceLayout::PlaneMajor,
        }
    }

    /// Whether `--compact-groups` / `--bank-perm` name knobs this mode runs.
    pub fn uses_compact_groups(self) -> bool {
        self == Self::LsbCompact
    }

    /// Logical rows one eval block covers — 32 for the lane = row modes, 16 for the
    /// LSB mode, where a 16-lane half-warp is one group.
    pub fn rows_per_block(self) -> u32 {
        match self {
            Self::LsbRecompute => UNISKIP_LSB_ROWS_PER_BLOCK as u32,
            Self::LsbPair => UNISKIP_PAIR_ROWS_PER_BLOCK as u32,
            _ => UNISKIP_ROWS_PER_BLOCK as u32,
        }
    }

    /// Whether the pass runs the fold stage. The v3 R0 rung is descoped to one kernel
    /// plus `finalize`: the fold kernels address plane-major taps, and no fold has been
    /// written for the LSB ordering (spec R4).
    pub fn runs_fold(self) -> bool {
        !matches!(self, Self::LsbRecompute | Self::LsbCompact | Self::LsbPair)
    }

    /// Whether `--lde-shape` names a grid this mode runs.
    pub fn uses_lde_shape(self) -> bool {
        self == Self::Unfused
    }

    /// Whether `--cell-map` names a warp map this mode runs. Every LSB mode fixes its own
    /// lane map — `lsb-recompute` lane = tap at two groups per warp, `lsb-pair`
    /// pair-resident at eight lanes per group and four groups per warp — so the knob is
    /// rejected for all of them.
    pub fn uses_cell_map(self) -> bool {
        matches!(self, Self::FusedRecompute | Self::FusedCached)
    }

    /// Logical rows one eval block covers, given the compaction geometry (ignored by
    /// every mode but [`Self::LsbCompact`], whose block is 8 warps x `groups` rows).
    pub fn rows_per_block_with(self, groups: u32) -> u32 {
        match self {
            Self::LsbCompact => UNISKIP_WARPS_PER_BLOCK as u32 * groups,
            _ => self.rows_per_block(),
        }
    }
}

/// Which four of the 32 cells a warp owns. `Block` is the v1 map (warp `w` takes
/// cells `4w..4w+3`, so warps 0-3 are all-H and warps 4-7 all-coset); `Interleave`
/// gives warp `w` the cells `{w, w+8, w+16, w+24}`, two of each. Fused modes only —
/// it exists to spread the recompute across all eight warps.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum CellMap {
    #[default]
    Block,
    Interleave,
}

impl CellMap {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Block => "block",
            Self::Interleave => "interleave",
        }
    }
}

/// v3 R3 arms of `--mode lsb-pair`, the factorial's cells. `Control` is R2 exactly —
/// same kernel, same wire, no side descriptor — so a bare `--mode lsb-pair` is unchanged.
/// `T` is `__launch_bounds__(256, 3)` alone; it was built to test the twiddle-remat lever
/// and MEASURED NOT TO — bank-3 twiddle loads are byte-identical with and without it, and
/// what moved was a bank-0 stream from the uniform to the vector datapath. `W` is the
/// coset-only top-4-BF window alone, `Wt` both, and `Wnone` the WØ diagnostic: the window
/// kernel and its side descriptor with an all-`none` tag stream, which pays the window's
/// register and branch cost and takes none of its saving.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum PairArm {
    #[default]
    Control,
    T,
    W,
    Wt,
    Wnone,
    /// The 3-block WØ: the `wt` kernel with an all-`none` stream. With `t` it splits
    /// `wt - t` into machinery alone and removal alone, both at 3 blocks.
    Wtnone,
}

impl PairArm {
    /// The factorial's arms in rotation order.
    pub const FACTORIAL: [Self; 6] = [
        Self::Control,
        Self::T,
        Self::W,
        Self::Wt,
        Self::Wnone,
        Self::Wtnone,
    ];

    /// Compiled registers and the resulting blocks/SM on sm_120 (8-register allocation
    /// granularity). `w`/`wnone` are 2-block arms: they are over the 80-register cliff, so
    /// a contrast against the 3-block control is NOT occupancy-neutral.
    pub fn occupancy(self) -> (u32, u32) {
        match self {
            Self::Control => (72, 3),
            Self::T => (79, 3),
            Self::W | Self::Wnone => (82, 2),
            Self::Wt | Self::Wtnone => (80, 3),
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Control => "control",
            Self::T => "t",
            Self::W => "w",
            Self::Wt => "wt",
            Self::Wnone => "wnone",
            Self::Wtnone => "wtnone",
        }
    }

    /// Whether the arm ships a window side descriptor at all.
    pub fn uses_window(self) -> bool {
        matches!(self, Self::W | Self::Wt | Self::Wnone | Self::Wtnone)
    }

    /// Whether the descriptor carries a planned schedule rather than the all-`none`
    /// stream. `Wnone` is the difference between the two.
    pub fn uses_schedule(self) -> bool {
        matches!(self, Self::W | Self::Wt)
    }

    /// The window kernel an arm launches, or `None` for the arms that take no side
    /// descriptor. Single-arm and factorial paths both go through this, so an arm cannot
    /// be wired two different ways.
    pub fn kernel_for(self) -> Option<WindowLaunch> {
        match self {
            Self::Control | Self::T => None,
            Self::W | Self::Wnone => Some(kernels::eval_lsb_pair_win),
            Self::Wt | Self::Wtnone => Some(kernels::eval_lsb_pair_win_lb),
        }
    }
}

/// The process's carveout state for the bounded 128-thread cached kernel. `Default` applies
/// the R6-measured hint 16 whenever the prepared configuration launches that kernel;
/// [`CarveoutHint::None`] is the pre-R7 state, in which nothing is set and nothing is echoed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum CarveoutHint {
    #[default]
    Default,
    None,
    Explicit(u32),
}

impl CarveoutHint {
    fn resolve(self, launches_cached_128_lb: bool) -> Option<u32> {
        match self {
            Self::Explicit(pct) => Some(pct),
            Self::None => None,
            Self::Default => launches_cached_128_lb.then_some(16),
        }
    }
}

impl std::str::FromStr for CarveoutHint {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "none" {
            return Ok(Self::None);
        }
        s.parse().map(Self::Explicit).map_err(|_| {
            format!("`{s}` is neither `none` nor a percent of the maximum shared memory")
        })
    }
}

/// The shape knobs of one pass. `lde_shape` applies to [`EvalMode::Unfused`] only,
/// `cell_map` to the fused modes only, and `compact_groups`/`bank_perm` to
/// [`EvalMode::LsbCompact`] only; `main` rejects the other combinations.
///
/// `Default` leaves `compact_groups` AND `block_threads` at 0, neither of which is legal —
/// construct through `main`'s `pass_config`, which fills both, or set them explicitly.
/// `Harness::new` substitutes a legal `compact_groups` for the modes that ignore it, so
/// only a hand-built `LsbCompact` config can reach that invalid state; `block_threads` has
/// no such substitution and an illegal value panics at kernel dispatch, like
/// `compact_groups` does for `LsbCompact`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PassConfig {
    pub mode: EvalMode,
    pub lde_shape: LdeShape,
    pub cell_map: CellMap,
    /// Groups a warp owns in [`EvalMode::LsbCompact`]; ignored elsewhere.
    pub compact_groups: u32,
    /// Staging tap permutation in [`EvalMode::LsbCompact`]; ignored elsewhere. `Identity`
    /// is the pre-fix layout, kept reachable so the bank-conflict A/B is re-runnable.
    pub bank_perm: BankPerm,
    /// v3 R3 arm of [`EvalMode::LsbPair`]; ignored elsewhere. `Control` is R2 exactly.
    pub pair_arm: PairArm,
    /// v3 R4 coset-cache arm of [`EvalMode::LsbPair`]; ignored elsewhere. `Control` is
    /// the uncached body; every other arm runs the cached one.
    pub cache_arm: CacheArm,
    /// v3 R7 carrier of a single-arm [`EvalMode::LsbPair`] run; ignored elsewhere.
    /// `Local` is the R4 per-thread frame — the absence of `--carrier`.
    pub carrier: LaneCarrier,
    /// Class the v3 R4 prologue produces first. A table-emission order only — the kernel
    /// walks what the host uploaded, so this costs no SASS.
    pub prologue_order: PrologueOrder,
    /// TEST-ONLY: corrupt the selected cached arm's records and upload them UNCHECKED.
    pub cache_mutate: Option<CacheMutation>,
    /// The pinned rotation this run executes, or `None` for a single-arm run. The harness
    /// then prepares every lane of that set instead of one arm, and owns BOTH block sizes
    /// internally. ONE field, so a run cannot be two factorials at once.
    pub lane_set: Option<LaneSet>,
    /// Whether the 128-thread NO-CACHE baseline runs the `__launch_bounds__(128, 7)`
    /// sibling. FALSE is the default and is the frozen control128; TRUE selects the bounded
    /// baseline, which is what makes the 128 cache contrast bound-to-bound.
    pub control_launch_bounds: bool,
    /// Whether the 128-thread cached arm runs the `__launch_bounds__(128, 7)` sibling.
    /// TRUE is the measurement arm: unbounded it takes 75 registers = 6 blocks/SM against
    /// control128's 7, and the contrast would carry an occupancy step. Ignored at 256,
    /// where the cached body already holds the control's 3 blocks.
    pub cache_launch_bounds: bool,
    /// Threads per eval block in [`EvalMode::LsbPair`]; ignored elsewhere. 256 is the R2
    /// shape, 128 is v3 R4's second block size — a distinct kernel, not a launch
    /// parameter, because the shared plane and the epilogue reduction are static.
    pub block_threads: u32,
    /// v3 R6: preferred shared-memory carveout set on the bounded 128-thread cached kernel
    /// before any launch. Per-function and process-sticky, so a run has exactly one hint
    /// state.
    pub carveout_hint: CarveoutHint,
}

impl PassConfig {
    /// Logical rows one eval block covers under this configuration.
    pub fn rows_per_block(&self) -> u32 {
        if self.mode == EvalMode::LsbPair && self.block_threads == UNISKIP_PAIR_THREADS_128 as u32 {
            return UNISKIP_PAIR_ROWS_PER_BLOCK_128 as u32;
        }
        self.mode.rows_per_block_with(self.compact_groups)
    }
}

/// The timed stages of one pass, in execution order.
pub const STAGES: [&str; 4] = ["lde", "eval", "finalize", "fold"];

/// Device time of one pass, from the CUDA events the pass records.
#[derive(Clone, Copy, Debug)]
pub struct StageTimes {
    pub stage_ms: [f32; STAGES.len()],
    pub total_ms: f32,
}

/// COMPULSORY traffic of one pass: every distinct byte a stage must read or write
/// at least once. Real DRAM traffic is never below this and is usually above it —
/// the eval kernel issues one load per operand reference, and the LDE re-reads its
/// input once per coset cell — so `bytes / time` is a LOWER bound on the bandwidth
/// a stage is achieving, not an upper one.
#[derive(Clone, Copy, Debug)]
pub struct PassBytes {
    pub stage: [u64; STAGES.len()],
    pub total: u64,
}

/// A class-pair LDE launch (`bf`, `e4`), or `None` in a mode with no LDE stage.
type LdeLaunch = fn(&UniskipVmDesc, &DeviceSlice<u16>, usize, &CudaStream) -> CudaResult<()>;
type EvalLaunch = fn(&UniskipVmDesc, u32, &CudaStream) -> CudaResult<()>;
/// A window arm's launch: the control descriptor plus the side descriptor.
type WindowLaunch = fn(&UniskipVmDesc, &UniskipWindowDesc, u32, &CudaStream) -> CudaResult<()>;
type CachedLaunch = fn(&UniskipVmDesc, &UniskipCacheDesc, u32, &CudaStream) -> CudaResult<()>;
/// Carrier S: the slab is the launch's own dynamic shared memory, so its size is a launch
/// parameter and the reduction plane aliases its head.
type SegSharedLaunch =
    fn(&UniskipVmDesc, &UniskipCacheDesc, &UniskipSegDesc, u32, u32, &CudaStream) -> CudaResult<()>;
/// Carrier G: the slab is device scratch the caller owns, so the plane is static shared.
type SegSlabLaunch =
    fn(&UniskipVmDesc, &UniskipCacheDesc, &UniskipSegDesc, u32, &CudaStream) -> CudaResult<()>;
/// The machinery floor: no slab and no prologue, hence no plan parameter at all.
type SegRecomputeLaunch = fn(&UniskipVmDesc, &UniskipSegDesc, u32, &CudaStream) -> CudaResult<()>;

/// Slab bytes and words one accounting unit occupies: a `bf` source's produced pair per
/// lane identity, 32 identities to a warp row.
const SEG_SLAB_UNIT_BYTES: u32 = UNISKIP_COSET_UNIT_BYTES as u32 * 32;
const SEG_SLAB_UNIT_WORDS: u32 = SEG_SLAB_UNIT_BYTES / size_of::<u32>() as u32;

/// The segmented launch of one carrier. ONE dispatch, shared by the factorial lanes and
/// the `--carrier` single-arm path, so a carrier cannot be wired two different ways.
#[derive(Clone, Copy)]
enum SegLaunch {
    Shared(SegSharedLaunch),
    Slab(SegSlabLaunch),
    Recompute(SegRecomputeLaunch),
}

impl SegLaunch {
    fn of(carrier: LaneCarrier) -> Option<Self> {
        Some(match carrier {
            LaneCarrier::Local => return None,
            LaneCarrier::SegS64 => Self::Shared(kernels::eval_lsb_seg_s_cv64),
            LaneCarrier::SegS100 => Self::Shared(kernels::eval_lsb_seg_s_cv100),
            LaneCarrier::SegSAcc => Self::Shared(kernels::eval_lsb_seg_s_acc),
            LaneCarrier::SegG => Self::Slab(kernels::eval_lsb_seg_g),
            LaneCarrier::SegRecompute => Self::Recompute(kernels::eval_lsb_seg_recompute),
        })
    }
}

/// One prepared segmented launch: everything a seg kernel needs beyond the control
/// descriptor. Built once, resident for the run — nothing here is rebuilt or re-uploaded
/// inside a timed rotation.
struct PreparedSeg {
    launch: SegLaunch,
    /// The owner-stamped prologue table; `UniskipCacheDesc::default()` on the machinery
    /// floor, whose kernel takes no plan.
    plan: UniskipCacheDesc,
    seg: UniskipSegDesc,
    /// Dynamic shared request of a carrier-S launch; 0 where the plane is static.
    shared_bytes: u32,
    /// The arm's footprint in accounting units — what `seg.slab_stride_words` is derived
    /// from, kept so the derivation is re-checked at every launch.
    units: u32,
    /// Carrier G's per-block scratch. The lane (or the harness) OWNS this allocation:
    /// `seg.slab_base` is a bare `u64`, so this field is the only thing keeping it alive.
    #[allow(dead_code)] // referenced by seg.slab_base
    slab: Option<DeviceAllocation<u32>>,
}

impl PreparedSeg {
    fn run(&self, desc: &UniskipVmDesc, blocks: u32, stream: &CudaStream) -> CudaResult<()> {
        match self.launch {
            SegLaunch::Shared(launch) => launch(
                desc,
                &self.plan,
                &self.seg,
                blocks,
                self.shared_bytes,
                stream,
            ),
            SegLaunch::Slab(launch) => {
                debug_assert!(
                    self.seg.slab_base != 0
                        && self.seg.slab_stride_words == self.units * SEG_SLAB_UNIT_WORDS,
                    "carrier G launched against slab base {:#x} stride {} words, not the \
                     {} units this arm plans",
                    self.seg.slab_base,
                    self.seg.slab_stride_words,
                    self.units
                );
                launch(desc, &self.plan, &self.seg, blocks, stream)
            }
            SegLaunch::Recompute(launch) => launch(desc, &self.seg, blocks, stream),
        }
    }
}

/// Build one carrier's launch state against one planned arm and the shared deal.
fn prepare_seg(
    carrier: LaneCarrier,
    state: &CacheArmState,
    deal: &SegPlan,
    blocks: u32,
) -> CudaResult<PreparedSeg> {
    let launch = SegLaunch::of(carrier).expect("a seg carrier names a seg kernel");
    let units = state.counts.c;
    let mut plan = UniskipCacheDesc::default();
    if carrier.uses_plan() {
        plan = state.descriptor(PrologueOrder::E4First);
        let owners = seg::stripe_prologue(state);
        seg::validate_owners(&owners, state)
            .unwrap_or_else(|e| panic!("the prologue owner stripe is invalid: {e}"));
        assert_eq!(
            owners.len(),
            plan.count as usize,
            "the stripe covers {} rows against the table's {}",
            owners.len(),
            plan.count
        );
        // Matched by SOURCE, never by position: the stripe and the table are two walks of
        // the same rows, and only the id says they are the same row.
        for &(source, owner) in &owners {
            let mut stamped = 0;
            for entry in plan.entry[..plan.count as usize]
                .iter_mut()
                .filter(|entry| entry.source == source)
            {
                entry.reserved = owner;
                stamped += 1;
            }
            assert_eq!(
                stamped, 1,
                "prologue source {source} matched {stamped} table rows, not exactly one"
            );
        }
    } else {
        // The machinery floor's carrier IS the reduction plane, so one live slot would be
        // a shared read ~21 KiB past a 2 KiB allocation rather than a wrong number.
        assert!(
            state
                .sources
                .iter()
                .all(|rec| rec.cache_slot == UNISKIP_CACHE_SLOT_NONE),
            "the {} carrier needs the all-sentinel record clone; arm {} carries live slots",
            carrier.as_str(),
            state.id
        );
    }

    let mut seg = UniskipSegDesc {
        list_offset: deal.list_offset,
        ..Default::default()
    };
    let mut shared_bytes = 0;
    let mut slab = None;
    if carrier.uses_slab() {
        // Exactly the region the kernel addresses: `blocks` per-block slabs of the arm's
        // own footprint. `cache0` plans nothing and never touches it, so the allocation
        // still takes one word rather than none — `alloc(0)` has no valid pointer.
        let words = blocks as usize * units as usize * SEG_SLAB_UNIT_WORDS as usize;
        let mut alloc = DeviceAllocation::<u32>::alloc(words.max(1))?;
        let base = alloc.as_mut_ptr() as u64;
        assert_eq!(
            base as usize % UNISKIP_COSET_E4_ALIGN,
            0,
            "the slab must be {UNISKIP_COSET_E4_ALIGN}-byte aligned for its uint4 halves"
        );
        seg.slab_base = base;
        seg.slab_stride_words = units * SEG_SLAB_UNIT_WORDS;
        slab = Some(alloc);
    } else if matches!(launch, SegLaunch::Shared(_)) {
        let plane = match carrier {
            LaneCarrier::SegSAcc => kernels::SEG_ACC_PLANE_BYTES,
            _ => kernels::SEG_FOLD_PLANE_BYTES,
        };
        shared_bytes = (units * SEG_SLAB_UNIT_BYTES).max(plane);
    }
    Ok(PreparedSeg {
        launch,
        plan,
        seg,
        shared_bytes,
        units,
        slab,
    })
}

/// Set one seg symbol's preferred shared-memory carveout. Per function and sticky for the
/// process, which is why `_cv64` and `_cv100` are two symbols over one body.
fn set_seg_carveout(carrier: LaneCarrier, percent: u32) -> CudaResult<()> {
    match carrier {
        LaneCarrier::Local => Ok(()),
        LaneCarrier::SegS64 => kernels::set_seg_s_cv64_carveout(percent),
        LaneCarrier::SegS100 => kernels::set_seg_s_cv100_carveout(percent),
        LaneCarrier::SegSAcc => kernels::set_seg_s_acc_carveout(percent),
        LaneCarrier::SegG => kernels::set_seg_g_carveout(percent),
        LaneCarrier::SegRecompute => kernels::set_seg_recompute_carveout(percent),
    }
}

/// Put the DEALT program on a descriptor. The deal is a permutation of the same records,
/// so nothing else about the descriptor moves — and a seg lane must never be composed with
/// a position-keyed side table (R3's window tags), which is why no such path exists.
fn upload_dealt_program(desc: &mut UniskipVmDesc, deal: &SegPlan) {
    assert_eq!(
        deal.program.len(),
        desc.record_count as usize,
        "the deal is not a permutation of this program"
    );
    desc.program[..deal.program.len()].copy_from_slice(&deal.program);
    desc.record_count = deal.program.len() as u32;
}

/// The plan-identity line: the deal's list boundaries, its predicted per-warp costs, the
/// owner census of the REFERENCE stripe (`hot16` — the arm the committed dealer oracle
/// pins and every seg rotation carries), and the dealt record stream's fingerprint.
fn seg_line(deal: &SegPlan, state: &CacheArmState) -> String {
    let mut e4 = [0u32; UNISKIP_SEG_K];
    let mut bf = [0u32; UNISKIP_SEG_K];
    for (source, owner) in seg::stripe_prologue(state) {
        let class = state.sources[source as usize].source_class;
        let counted = if component_width(class) == UNISKIP_COSET_E4_UNITS {
            &mut e4
        } else {
            &mut bf
        };
        counted[usize::from(owner)] += 1;
    }
    let list = |values: &[u64]| {
        values
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(",")
    };
    let counts = |values: &[u32]| list(&values.iter().map(|&v| u64::from(v)).collect::<Vec<_>>());
    format!(
        "SEG list_offset={} cost={} owners=e4:{};bf:{} hash={}",
        counts(&deal.list_offset.map(u32::from)),
        list(&deal.predicted_cost),
        counts(&e4),
        counts(&bf),
        seg::program_hash(&deal.program)
    )
}

/// One prepared factorial lane. The descriptors are kernel PARAMETERS (by value,
/// `__grid_constant__`), so every lane's own source array and prologue table are resident
/// at once with no device upload — nothing re-uploads inside a timed rotation.
pub struct PreparedLane {
    pub lane: CacheLane,
    desc: UniskipVmDesc,
    plan: UniskipCacheDesc,
    launch: LaneLaunch,
    /// The lane's own plan facts, so the log states what each lane IS rather than only
    /// what it is called — two lanes with identical admitted sets are one experiment under
    /// two labels, which is how R3's aliasing bug read as a zero effect.
    pub counts: coset_cache::CacheCounts,
    pub admitted: Vec<u16>,
    /// This lane's grid. The 128 lanes cover 16 rows per block, the 256 lanes 32, so the
    /// 128 grid is twice the 256 one over the same trace.
    pub blocks: u32,
}

enum LaneLaunch {
    Plain(EvalLaunch),
    Cached(CachedLaunch),
    /// v3 R7. The segmented state lives IN the variant, so a seg lane cannot be launched
    /// through a cached or a window entry point and a local lane cannot reach a slab.
    Seg(Box<PreparedSeg>),
}

pub struct Harness {
    pub layout: Layout,
    pub desc: UniskipVmDesc,
    geometry: Geometry,
    /// Eval grid and its partials count at this mode's row tile — NOT
    /// `geometry.blocks`, which is the warp-wide tile the v1/v2 modes use.
    eval_blocks: u32,
    eval_partials: u64,
    seed: u32,
    flat_eq: bool,
    config: PassConfig,
    /// The carveout percent this harness APPLIED, which under [`CarveoutHint::Default`] is
    /// not readable off the config.
    carveout: Option<u32>,
    lde: Option<[LdeLaunch; CLASSES]>,
    eval: EvalLaunch,
    /// The eval kernel this harness will launch, by name. Set at the SAME match that picks
    /// the launch function, so a config block quoting it cannot drift from what runs — a
    /// separate name-computing mirror is exactly how the unwired launch-bounds selector
    /// stayed invisible.
    eval_kernel: &'static str,
    /// Set only on a cached arm; when set it replaces `eval` and carries the prologue
    /// table. Its descriptor is the arm's own CLONED source array, uploaded at build, and
    /// the launch it holds already encodes the block size AND the launch-bounds choice —
    /// a timed run is attributable to exactly one kernel through this field.
    eval_cached: Option<(CachedLaunch, UniskipCacheDesc)>,
    /// Set only on a window arm; when set it replaces `eval` and carries the side
    /// descriptor. The control path never touches either field.
    eval_window: Option<(WindowLaunch, UniskipWindowDesc)>,
    /// Set only on a `--carrier` run; when set it replaces `eval` and carries the dealt
    /// lists, the owner-stamped table and (carrier G) the slab.
    eval_seg: Option<PreparedSeg>,
    /// The plan-identity line of the run's deal, printed by the runner; `None` unless the
    /// run is segmented. The anchor rotation deals nothing and must not carry one.
    seg_line: Option<String>,
    /// v3 R4 factorial lanes, prepared once and resident together; empty unless the run
    /// is a `--cache-factorial`.
    cache_lanes: Vec<PreparedLane>,
    /// v3 R4: every coset-cache arm's CLONED state, planned once and resident together
    /// so nothing re-plans or re-uploads inside a timed rotation. The selected arm's copy
    /// is what reaches `desc.source`; the rest exist so the planner and its always-on
    /// validator run on every `lsb-pair` run, control included.
    ///
    /// Each arm is INDEPENDENTLY fallible: a census can push an arm past the cache frame
    /// (`--sources 60` already does), and an arm this run never selects must not take the
    /// run down with it. Only the selected arm's failure is fatal, and `main` is where
    /// that is decided.
    cache_arms: Vec<(CacheArm, Result<CacheArmState, String>)>,
    /// Both window descriptors, resident together so the in-process factorial can switch
    /// arms per round without reallocating or re-uploading anything.
    window_tagged: UniskipWindowDesc,
    window_none: UniskipWindowDesc,
    taps: [DeviceAllocation<u32>; CLASSES],
    /// One unused word per class in a fused mode — see [`EvalMode::materializes_coset`].
    cosets: [DeviceAllocation<u32>; CLASSES],
    #[allow(dead_code)] // referenced by desc.eq_low
    eq_low: DeviceAllocation<u32>,
    partials: DeviceAllocation<u32>,
    q: DeviceAllocation<u32>,
    /// One `e4` per (source, row), at `source * rows + row`.
    folded: DeviceAllocation<u32>,
    jobs: [DeviceAllocation<u16>; CLASSES],
    job_counts: [usize; CLASSES],
    stream: CudaStream,
    /// `STAGES.len() + 1` markers: one before the first stage, one after each.
    events: Vec<CudaEvent>,
}

impl Harness {
    /// Allocate the backings, upload the program, the LDE matrix and the coefficient
    /// bank, and run the init kernels over the taps and the eq tables. `flat_eq`
    /// forces every eq entry to ONE — the `--validate-flat-eq` debug mode, which
    /// isolates the term VM from the eq composition on both sides. `config` picks the
    /// source-resolution mode and the grid shapes; none of them changes `q`. `plan` is
    /// the shared-memory assignment, applied to the wire only in a caching mode.
    pub fn new(
        program: &SynthProgram,
        geometry: &Geometry,
        seed: u32,
        flat_eq: bool,
        config: PassConfig,
        plan: &CachePlan,
        window: UniskipWindowDesc,
    ) -> CudaResult<Self> {
        let layout = Layout::new(program, geometry, config.mode.source_layout());
        // A mode that runs no compaction still uploads a well-formed schedule, so the
        // symbol never holds another run's plan.
        let compact_groups = if config.mode.uses_compact_groups() {
            config.compact_groups
        } else {
            UNISKIP_COMPACT_MAX_GROUPS as u32
        };
        let rows_per_block = PassConfig {
            compact_groups,
            ..config
        }
        .rows_per_block();
        let eval_blocks = geometry.eval_blocks(rows_per_block);
        let eval_partials = geometry.eval_partials(rows_per_block);
        let stream = CudaStream::create()?;

        // `alloc(0)` has no valid device pointer; a class with no columns still gets
        // a one-word backing so the base records stay dereferenceable-but-unused.
        let alloc_words =
            |class: usize| DeviceAllocation::<u32>::alloc(layout.class_words(class).max(1));
        let mut taps = [alloc_words(CLASS_BF)?, alloc_words(CLASS_E4)?];
        // A fused mode never reads a coset element, so it allocates no coset backing:
        // this is the 1x-backing memory saving the mode exists for. Its base records
        // are NULLED below rather than pointed at the placeholder, so a stray coset
        // read faults instead of returning garbage.
        let cosets = if config.mode.materializes_coset() {
            [alloc_words(CLASS_BF)?, alloc_words(CLASS_E4)?]
        } else {
            [
                DeviceAllocation::<u32>::alloc(1)?,
                DeviceAllocation::<u32>::alloc(1)?,
            ]
        };

        let mut job_ids: [Vec<u16>; CLASSES] = [Vec::new(), Vec::new()];
        for (id, rec) in program.sources.iter().enumerate() {
            job_ids[class_index(rec.source_class)].push(id as u16);
        }
        let job_counts = [job_ids[CLASS_BF].len(), job_ids[CLASS_E4].len()];
        // The job lists ARE the used-column map: one source per column of every
        // window, so the LDE covers each backing exactly once and no coset element
        // is left at its uninitialized value.
        let total_columns: u32 = layout.windows.iter().map(|w| w.columns).sum();
        assert_eq!(
            program.sources.len() as u32,
            total_columns,
            "the source table must cover every column of every window exactly once"
        );
        let mut jobs = [
            DeviceAllocation::<u16>::alloc(job_counts[CLASS_BF].max(1))?,
            DeviceAllocation::<u16>::alloc(job_counts[CLASS_E4].max(1))?,
        ];
        for class in 0..CLASSES {
            if job_counts[class] > 0 {
                memory_copy(&mut jobs[class][..job_counts[class]], &job_ids[class][..])?;
            }
        }

        // The allocation carries the whole derived-table init space; `eq_low` is its
        // tail slice, so no two derived tables hold identical data (see
        // `reference::UNISKIP_EQ_LOW_INIT_BASE`).
        let eq_low_offset = reference::UNISKIP_EQ_LOW_INIT_BASE as usize * CLASS_WORDS[CLASS_E4];
        let eq_low_words = eq_low_offset + geometry.eq_low_len() * CLASS_WORDS[CLASS_E4];
        let mut eq_low = DeviceAllocation::<u32>::alloc(eq_low_words)?;

        let mut partials =
            DeviceAllocation::<u32>::alloc(eval_partials as usize * CLASS_WORDS[CLASS_E4])?;
        let q = DeviceAllocation::<u32>::alloc(UNISKIP_CELLS * CLASS_WORDS[CLASS_E4])?;
        // A mode that runs no fold stage allocates no fold output: at the benchmark
        // geometry that buffer is ~1 GiB of device memory nothing would ever read.
        let folded = DeviceAllocation::<u32>::alloc(if config.mode.runs_fold() {
            program.sources.len() * geometry.logical_rows as usize * CLASS_WORDS[CLASS_E4]
        } else {
            1
        })?;

        let mut desc = UniskipVmDesc {
            record_count: program.program.len() as u32,
            num_sources: program.sources.len() as u32,
            log_rows: geometry.log_rows,
            eq_sizes: UniskipEqSizes {
                high: [geometry.eq_sizes.0, geometry.eq_sizes.1],
                low: geometry.eq_sizes.2,
            },
            eq_low: eq_low.as_ptr() as u64 + (eq_low_offset * size_of::<u32>()) as u64,
            partials: partials.as_mut_ptr() as u64,
            immediates: program.immediates_canonical.map(reference::to_device_bf),
            ..Default::default()
        };
        desc.program[..program.program.len()].copy_from_slice(&program.program);
        desc.source[..program.sources.len()].copy_from_slice(&program.sources);
        // The plan reaches the device on the wire (`cache_slot` per record) and as the
        // inverse unit -> source table below. A non-caching mode leaves every record at
        // the sentinel and uploads an empty table, so no kernel can read a stale slot.
        let fill = if config.mode.uses_cache() {
            assert_eq!(
                plan.source_slot.len(),
                program.sources.len(),
                "the cache plan was lowered from a different program"
            );
            for (rec, &slot) in desc.source[..program.sources.len()]
                .iter_mut()
                .zip(plan.source_slot.iter())
            {
                rec.cache_slot = slot;
            }
            plan.fill
        } else {
            [UNISKIP_CACHE_FILL_NONE; UNISKIP_CACHE_UNITS]
        };
        for window in 0..UNISKIP_WINDOWS {
            let class = layout.windows[window].class;
            let byte_offset = layout.window_byte_offset(window) as u64;
            desc.tap_bases[window] = UniskipBaseRecord {
                base: taps[class].as_ptr() as u64 + byte_offset,
            };
            desc.coset_bases[window] = UniskipBaseRecord {
                base: if config.mode.materializes_coset() {
                    cosets[class].as_ptr() as u64 + byte_offset
                } else {
                    0
                },
            };
        }

        kernels::upload_lde_matrix(&reference::flat_lde_matrix(&lde_matrix()))?;
        kernels::upload_ntt_twiddles(&reference::ntt_twiddle_words())?;
        kernels::upload_compact_perm(&compact::bank_perm_words(config.bank_perm))?;
        kernels::upload_compact_schedule(
            &compact::schedule_words(config.bank_perm, compact_groups as usize)
                .try_into()
                .expect("the compaction schedule is padded to the symbol size"),
        )?;
        kernels::upload_eq_high(&reference::eq_high_words(seed, flat_eq))?;
        kernels::upload_coeff_bank(&reference::coeff_bank_words(seed))?;
        kernels::upload_fold_weights(&reference::fold_weight_words(seed))?;
        kernels::upload_cache_fill(&fill)?;
        kernels::init_bf(&mut taps[CLASS_BF], seed, &stream)?;
        kernels::init_e4(&mut taps[CLASS_E4], seed, &stream)?;
        kernels::init_e4(&mut eq_low, seed, &stream)?;
        stream.synchronize()?;

        if flat_eq {
            let ones: Vec<u32> =
                std::iter::repeat_n(reference::e4_one_words(), geometry.eq_low_len())
                    .flatten()
                    .collect();
            memory_copy(
                &mut eq_low[eq_low_offset..eq_low_offset + ones.len()],
                &ones[..],
            )?;
        }

        let mut events = Vec::with_capacity(STAGES.len() + 1);
        for _ in 0..=STAGES.len() {
            events.push(CudaEvent::create()?);
        }

        // Mode dispatch is resolved ONCE, here: the pass itself is two function
        // pointers, so neither arm carries the other's branch.
        let lde = match config.mode {
            EvalMode::Unfused => Some(match config.lde_shape {
                LdeShape::Cell => [kernels::lde_bf as LdeLaunch, kernels::lde_e4 as LdeLaunch],
                LdeShape::Row => [
                    kernels::lde_bf_row as LdeLaunch,
                    kernels::lde_e4_row as LdeLaunch,
                ],
            }),
            EvalMode::FusedRecompute
            | EvalMode::FusedCached
            | EvalMode::LsbRecompute
            | EvalMode::LsbCompact
            | EvalMode::LsbPair => None,
        };
        // Name and launch are chosen together, once, so the config block cannot describe a
        // kernel the run did not use.
        let mut eval_kernel = "n/a";
        let eval: EvalLaunch = match (config.mode, config.cell_map) {
            (EvalMode::Unfused, _) => kernels::eval,
            (EvalMode::FusedRecompute, CellMap::Block) => kernels::eval_fused,
            (EvalMode::FusedRecompute, CellMap::Interleave) => kernels::eval_fused_interleave,
            (EvalMode::FusedCached, CellMap::Block) => kernels::eval_fused_cached,
            (EvalMode::FusedCached, CellMap::Interleave) => kernels::eval_fused_cached_interleave,
            (EvalMode::LsbRecompute, _) => kernels::eval_lsb_w0,
            (EvalMode::LsbPair, _) => match config.block_threads as usize {
                UNISKIP_PAIR_THREADS_128 if config.control_launch_bounds => {
                    eval_kernel = "eval_lsb_pair_128_lb";
                    kernels::eval_lsb_pair_128_lb
                }
                UNISKIP_PAIR_THREADS_128 => {
                    eval_kernel = "eval_lsb_pair_128";
                    kernels::eval_lsb_pair_128
                }
                UNISKIP_THREADS_PER_BLOCK => match config.pair_arm {
                    PairArm::T => {
                        eval_kernel = "eval_lsb_pair_lb";
                        kernels::eval_lsb_pair_lb
                    }
                    _ => {
                        eval_kernel = "eval_lsb_pair";
                        kernels::eval_lsb_pair
                    }
                },
                other => panic!("--block-threads {other} has no kernel"),
            },
            (EvalMode::LsbCompact, _) => match compact_groups {
                4 => kernels::eval_lsb_compact_g4,
                8 => kernels::eval_lsb_compact_g8,
                other => panic!("--compact-groups {other} has no kernel"),
            },
        };

        let cache_arms = match config.mode {
            EvalMode::LsbPair => coset_cache::plan_all(program),
            _ => Vec::new(),
        };

        // ONE deal per run — the lists are chosen CAPTURE-BLIND, so a single split serves
        // every arm and every carrier of the rotation. `main` runs the same dealer as a
        // pre-flight, so a program the dealer rejects exits there rather than here.
        let segmented = config.carrier.is_seg()
            || (config.mode == EvalMode::LsbPair && config.lane_set.is_some_and(LaneSet::is_seg));
        let deal = segmented.then(|| {
            let deal = seg::deal(program)
                .unwrap_or_else(|e| panic!("the seg dealer rejected this program: {e}"));
            seg::validate(&deal, program)
                .unwrap_or_else(|e| panic!("the seg deal is invalid: {e}"));
            deal
        });

        let eval_cached = match config.mode {
            EvalMode::LsbPair if config.cache_arm.uses_cache() && !config.carrier.is_seg() => {
                let state = cache_arms
                    .iter()
                    .find(|(a, _)| *a == config.cache_arm)
                    .and_then(|(_, s)| s.as_ref().ok())
                    .expect("main rejects an unplannable selected arm before device setup");
                // The BOUNDED 128 kernel is the default: unbounded it takes 75 registers
                // = 6 blocks/SM against control128's 7, which the occupancy gate forbids
                // accepting silently. `cache_launch_bounds = false` selects the stepped one
                // deliberately, to price what the bound costs.
                let (launch, name): (CachedLaunch, &'static str) =
                    match (config.block_threads as usize, config.cache_launch_bounds) {
                        (UNISKIP_PAIR_THREADS_128, true) => (
                            kernels::eval_lsb_pair_cached_128_lb,
                            "eval_lsb_pair_cached_128_lb",
                        ),
                        (UNISKIP_PAIR_THREADS_128, false) => (
                            kernels::eval_lsb_pair_cached_128,
                            "eval_lsb_pair_cached_128",
                        ),
                        _ => (kernels::eval_lsb_pair_cached, "eval_lsb_pair_cached"),
                    };
                eval_kernel = name;
                Some((launch, state.descriptor(config.prologue_order)))
            }
            _ => None,
        };

        // The arm's CLONED source array is what reaches the device — `cache_slot` written
        // on admitted records, sentinel elsewhere. The canonical program is never mutated;
        // this happens once at build, never inside a timed rotation.
        if eval_cached.is_some() {
            let mut state = cache_arms
                .iter()
                .find(|(a, _)| *a == config.cache_arm)
                .and_then(|(_, s)| s.as_ref().ok())
                .expect("checked above")
                .clone();
            if let Some(how) = config.cache_mutate {
                // UNCHECKED on purpose: `validate` would reject this, and the gate is that
                // the DEVICE notices.
                match coset_cache::mutate(&mut state, how) {
                    Some(what) => println!("  cache mutation      {what}"),
                    None => panic!(
                        "arm {} has no slot pair this mutation can use",
                        config.cache_arm.as_str()
                    ),
                }
            }
            desc.source[..state.sources.len()].copy_from_slice(&state.sources);
        }

        // FACTORIAL LANES. Built at the 128 row tile (see `rows_per_block`), so `partials`
        // is allocated for the larger grid and the 256 lanes use half of it. Each lane
        // carries its own by-value descriptors; no lane re-uploads anything.
        let mut cache_lanes: Vec<PreparedLane> = Vec::new();
        if let (Some(set), EvalMode::LsbPair) = (config.lane_set, config.mode) {
            for &lane in set.lanes() {
                let mut lane_desc = desc;
                let mut plan = UniskipCacheDesc::default();
                let mut counts = coset_cache::CacheCounts::default();
                let mut admitted: Vec<u16> = Vec::new();
                let mut state = None;
                if lane.arm.uses_cache() {
                    let planned = cache_arms
                        .iter()
                        .find(|(a, _)| *a == lane.arm)
                        .and_then(|(_, s)| s.as_ref().ok())
                        .unwrap_or_else(|| {
                            // UNREACHABLE by construction: `main` plans every lane and
                            // exits cleanly before building the harness, so reaching
                            // here means that check was removed.
                            panic!(
                                "factorial lane {} is unplannable and main did not \
                                 reject it — the pre-flight check is missing",
                                lane.label
                            )
                        });
                    lane_desc.source[..planned.sources.len()].copy_from_slice(&planned.sources);
                    plan = planned.descriptor(PrologueOrder::E4First);
                    counts = planned.counts;
                    admitted = planned.admitted.iter().map(|e| e.source).collect();
                    state = Some(planned);
                }
                // The harness is built at the 128 tile (`pass_config` forces it for the
                // factorial), so `eval_blocks` is the 16-row grid and the 256 lanes take
                // half of it.
                let blocks = if lane.block_threads as usize == UNISKIP_PAIR_THREADS_128 {
                    eval_blocks
                } else {
                    eval_blocks / 2
                };
                // ONE source of truth for which kernel: the lane picks a `LaneKernel`
                // and both the launcher and the printed name come from it. A seg lane
                // additionally takes the DEALT program — the same records permuted, so
                // `q` is unchanged — while every local lane keeps the ordered one.
                let launch = match lane.kernel() {
                    LaneKernel::Cached128Lb => {
                        LaneLaunch::Cached(kernels::eval_lsb_pair_cached_128_lb)
                    }
                    LaneKernel::Cached128 => LaneLaunch::Cached(kernels::eval_lsb_pair_cached_128),
                    LaneKernel::Cached => LaneLaunch::Cached(kernels::eval_lsb_pair_cached),
                    LaneKernel::Pair128Lb => LaneLaunch::Plain(kernels::eval_lsb_pair_128_lb),
                    LaneKernel::Pair128 => LaneLaunch::Plain(kernels::eval_lsb_pair_128),
                    LaneKernel::Pair => LaneLaunch::Plain(kernels::eval_lsb_pair),
                    LaneKernel::SegSCv64
                    | LaneKernel::SegSCv100
                    | LaneKernel::SegSAcc
                    | LaneKernel::SegG
                    | LaneKernel::SegRecompute => {
                        let deal = deal.as_ref().expect("a seg lane set deals its program");
                        let state = state.expect("a seg carrier runs a planned arm");
                        upload_dealt_program(&mut lane_desc, deal);
                        LaneLaunch::Seg(Box::new(prepare_seg(lane.carrier, state, deal, blocks)?))
                    }
                };
                // FULL-TRACE INVARIANT. The row map is fixed, not grid-stride, so a
                // short grid evaluates a PREFIX of the trace and finalize reduces the
                // same prefix — silently. Every lane must cover every logical row.
                assert_eq!(
                    u64::from(blocks) * u64::from(lane.rows_per_block()),
                    geometry.logical_rows,
                    "lane {} covers {} of {} logical rows",
                    lane.label,
                    u64::from(blocks) * u64::from(lane.rows_per_block()),
                    geometry.logical_rows
                );
                cache_lanes.push(PreparedLane {
                    lane,
                    desc: lane_desc,
                    plan,
                    launch,
                    blocks,
                    counts,
                    admitted,
                });
            }
        }

        // The single-arm segmented path. It replaces the cached one rather than joining
        // it: the arm's records still reach the device, but the walk bounds, the carrier
        // and the reduction all come from the seg descriptor.
        let eval_seg = match config.mode {
            EvalMode::LsbPair if config.carrier.is_seg() => {
                let state = cache_arms
                    .iter()
                    .find(|(a, _)| *a == config.cache_arm)
                    .and_then(|(_, s)| s.as_ref().ok())
                    .expect("main rejects an unplannable selected arm before device setup");
                let deal = deal.as_ref().expect("a seg carrier deals its program");
                desc.source[..state.sources.len()].copy_from_slice(&state.sources);
                upload_dealt_program(&mut desc, deal);
                eval_kernel = config
                    .carrier
                    .kernel()
                    .expect("a seg carrier names a seg kernel")
                    .name();
                Some(prepare_seg(config.carrier, state, deal, eval_blocks)?)
            }
            _ => None,
        };

        // The plan-identity line the runner prints, keyed to the REFERENCE stripe rather
        // than to whichever arm this run selects: the deal is capture-blind, so the line
        // fingerprints (program, term order) alone.
        let seg_line = deal.as_ref().map(|deal| {
            let state = cache_arms
                .iter()
                .find(|(a, _)| *a == CacheArm::Hot16)
                .and_then(|(_, s)| s.as_ref().ok())
                .expect("hot16 is the seg line's reference stripe and fits inside every frame");
            seg_line(deal, state)
        });

        let none = UniskipWindowDesc::default();
        let eval_window = match config.mode {
            EvalMode::LsbPair => config.pair_arm.kernel_for().map(|launch| {
                let desc = if config.pair_arm.uses_schedule() {
                    window
                } else {
                    none
                };
                (launch, desc)
            }),
            _ => None,
        };

        // v3 R6: one carveout state per process, applied before any launch. Only the
        // bounded cached body is steered; the uncached control is the probe's anchor.
        let launches_cached_128_lb = eval_kernel == LaneKernel::Cached128Lb.name()
            || cache_lanes
                .iter()
                .any(|prepared| prepared.lane.kernel() == LaneKernel::Cached128Lb);
        let carveout = config.carveout_hint.resolve(launches_cached_128_lb);
        if let Some(pct) = carveout {
            kernels::set_cached_128_lb_carveout(pct)?;
            println!("  carveout hint       {pct}% (eval_lsb_pair_cached_128_lb)");
        }
        // v3 R7: one hint per USED seg symbol, applied once before any launch and echoed
        // once each. Not steerable — the percent IS the carrier's configuration under
        // test, and an unhinted symbol would take the driver's own sizing (R6 measured
        // that at 64 KiB for a 128-thread kernel), which is a different arm.
        for carrier in LaneCarrier::SEG {
            let used = config.carrier == carrier
                || cache_lanes
                    .iter()
                    .any(|prepared| prepared.lane.carrier == carrier);
            if !used {
                continue;
            }
            let pct = carrier
                .carveout()
                .expect("a seg carrier states its carveout");
            set_seg_carveout(carrier, pct)?;
            println!(
                "  carveout hint       {pct}% ({})",
                carrier
                    .kernel()
                    .expect("a seg carrier names a seg kernel")
                    .name()
            );
        }

        Ok(Self {
            layout,
            desc,
            geometry: *geometry,
            eval_blocks,
            eval_partials,
            seed,
            flat_eq,
            config,
            carveout,
            lde,
            eval,
            eval_kernel,
            cache_lanes,
            eval_window,
            eval_cached,
            eval_seg,
            seg_line,
            cache_arms,
            window_tagged: window,
            window_none: none,
            taps,
            cosets,
            eq_low,
            partials,
            q,
            folded,
            jobs,
            job_counts,
            stream,
            events,
        })
    }

    /// One coset LDE pass over both field classes, in the configured grid shape —
    /// nothing at all in a fused mode, where the accessor absorbs it.
    pub fn run_lde(&self) -> CudaResult<()> {
        let Some([bf, e4]) = self.lde else {
            return Ok(());
        };
        bf(
            &self.desc,
            &self.jobs[CLASS_BF],
            self.job_counts[CLASS_BF],
            &self.stream,
        )?;
        e4(
            &self.desc,
            &self.jobs[CLASS_E4],
            self.job_counts[CLASS_E4],
            &self.stream,
        )
    }

    /// One fold pass over both field classes, at the round challenge the fold
    /// weights were uploaded for — nothing at all in a mode that does not run it.
    pub fn run_fold(&mut self) -> CudaResult<()> {
        if !self.config.mode.runs_fold() {
            return Ok(());
        }
        kernels::fold_bf(
            &self.desc,
            &self.jobs[CLASS_BF],
            self.job_counts[CLASS_BF],
            &mut self.folded,
            &self.stream,
        )?;
        kernels::fold_e4(
            &self.desc,
            &self.jobs[CLASS_E4],
            self.job_counts[CLASS_E4],
            &mut self.folded,
            &self.stream,
        )
    }

    /// One full uniskip pass: coset LDE, the 32-cell eval, the reduction of the
    /// block partials into `q`, then the fold at the round challenge. Every pass
    /// records the stage events, warmup included, so a timed pass and an untimed
    /// one are the same work.
    pub fn run_pass(&mut self) -> CudaResult<()> {
        self.events[0].record(&self.stream)?;
        self.run_lde()?;
        self.events[1].record(&self.stream)?;
        match (&self.eval_seg, &self.eval_cached, &self.eval_window) {
            (Some(seg), ..) => seg.run(&self.desc, self.eval_blocks, &self.stream)?,
            (None, Some((launch, plan)), _) => {
                launch(&self.desc, plan, self.eval_blocks, &self.stream)?
            }
            (None, None, Some((launch, win))) => {
                launch(&self.desc, win, self.eval_blocks, &self.stream)?
            }
            (None, None, None) => (self.eval)(&self.desc, self.eval_blocks, &self.stream)?,
        }
        self.events[2].record(&self.stream)?;
        kernels::finalize(&self.partials, self.eval_blocks, &mut self.q, &self.stream)?;
        self.events[3].record(&self.stream)?;
        self.run_fold()?;
        self.events[4].record(&self.stream)
    }

    /// One pass with the eval stage forced to `arm` — the in-process factorial's unit of
    /// work. Every arm shares this harness's backings, control descriptor and both window
    /// descriptors, so a round differs only in which kernel runs. `lde` and `fold` are
    /// absent in this mode, so the recorded stages are `eval` and `finalize` alone.
    pub fn run_pass_arm(&mut self, arm: PairArm) -> CudaResult<()> {
        self.events[0].record(&self.stream)?;
        self.events[1].record(&self.stream)?;
        match arm.kernel_for() {
            None if arm == PairArm::T => {
                kernels::eval_lsb_pair_lb(&self.desc, self.eval_blocks, &self.stream)?
            }
            None => kernels::eval_lsb_pair(&self.desc, self.eval_blocks, &self.stream)?,
            Some(launch) => {
                let win = if arm.uses_schedule() {
                    &self.window_tagged
                } else {
                    &self.window_none
                };
                launch(&self.desc, win, self.eval_blocks, &self.stream)?
            }
        }
        self.events[2].record(&self.stream)?;
        kernels::finalize(&self.partials, self.eval_blocks, &mut self.q, &self.stream)?;
        self.events[3].record(&self.stream)?;
        self.events[4].record(&self.stream)
    }

    /// One coset-cache arm's planned state — `None` outside `lsb-pair` or when this
    /// census puts the arm past the frame.
    pub fn cache_arm_state(&self, arm: CacheArm) -> Option<&CacheArmState> {
        self.cache_arms
            .iter()
            .find(|(a, _)| *a == arm)
            .and_then(|(_, s)| s.as_ref().ok())
    }

    /// The prepared factorial lanes, in rotation order.
    pub fn cache_lanes(&self) -> &[PreparedLane] {
        &self.cache_lanes
    }

    /// One pass on one factorial lane. Every lane shares this harness's backings and its
    /// partials buffer; a round differs only in which descriptor pair and kernel run, and
    /// in the grid the lane's block size implies. `lde` and `fold` are absent, so the
    /// recorded stages are `eval` and `finalize`.
    pub fn run_cache_lane(&mut self, index: usize) -> CudaResult<()> {
        let lane = &self.cache_lanes[index];
        self.events[0].record(&self.stream)?;
        self.events[1].record(&self.stream)?;
        match &lane.launch {
            LaneLaunch::Cached(launch) => {
                launch(&lane.desc, &lane.plan, lane.blocks, &self.stream)?
            }
            LaneLaunch::Plain(launch) => launch(&lane.desc, lane.blocks, &self.stream)?,
            LaneLaunch::Seg(seg) => seg.run(&lane.desc, lane.blocks, &self.stream)?,
        }
        self.events[2].record(&self.stream)?;
        kernels::finalize(&self.partials, lane.blocks, &mut self.q, &self.stream)?;
        self.events[3].record(&self.stream)?;
        self.events[4].record(&self.stream)
    }

    /// The eval kernel this harness launches, by name — bound to the dispatch, not
    /// recomputed. A window arm replaces `eval` after the name is set, so it reports its
    /// own placeholder rather than the control's.
    pub fn eval_kernel(&self) -> &'static str {
        if self.eval_cached.is_some() || self.eval_seg.is_some() {
            return self.eval_kernel;
        }
        match &self.eval_window {
            Some(_) => "eval_lsb_pair_win*",
            None => self.eval_kernel,
        }
    }

    /// The carveout percent this harness applied to the local incumbent's body, or `None`
    /// for the driver's own sizing. The seg symbols' hints are fixed per carrier.
    pub fn carveout(&self) -> Option<u32> {
        self.carveout
    }

    /// The run's plan-identity line, or `None` when nothing was dealt.
    pub fn seg_line(&self) -> Option<&str> {
        self.seg_line.as_deref()
    }

    /// Why an arm is unavailable at this census, if it is.
    pub fn cache_arm_error(&self, arm: CacheArm) -> Option<&str> {
        self.cache_arms
            .iter()
            .find(|(a, _)| *a == arm)
            .and_then(|(_, s)| s.as_ref().err())
            .map(String::as_str)
    }

    pub fn synchronize(&self) -> CudaResult<()> {
        self.stream.synchronize()
    }

    pub fn config(&self) -> PassConfig {
        self.config
    }

    /// Eval grid at this mode's row tile — the number `finalize` reduces over.
    pub fn eval_blocks(&self) -> u32 {
        self.eval_blocks
    }

    /// Device bytes the pass holds in its tap and coset backings.
    pub fn backing_bytes_resident(&self) -> u64 {
        let backing = self.layout.backing_bytes();
        backing + u64::from(self.config.mode.materializes_coset()) * backing
    }

    /// Device time of the last pass, in [`STAGES`] order. Only valid once the pass
    /// has completed — call [`Self::synchronize`] first.
    pub fn stage_times(&self) -> CudaResult<StageTimes> {
        let mut stage_ms = [0f32; STAGES.len()];
        for (stage, ms) in stage_ms.iter_mut().enumerate() {
            *ms = elapsed_time(&self.events[stage], &self.events[stage + 1])?;
        }
        Ok(StageTimes {
            stage_ms,
            total_ms: elapsed_time(&self.events[0], &self.events[STAGES.len()])?,
        })
    }

    /// Compulsory traffic of one pass, in [`STAGES`] order — see [`PassBytes`]. A
    /// fused mode has no LDE stage and its eval reads the tap backing only, so its
    /// floor is one backing lighter in each of the two stages.
    pub fn pass_bytes(&self) -> PassBytes {
        let e4_bytes = CLASS_WORDS[CLASS_E4] as u64 * size_of::<u32>() as u64;
        let backing = self.layout.backing_bytes();
        let partials = self.eval_partials * e4_bytes;
        let folded = u64::from(self.desc.num_sources) * self.layout.rows * e4_bytes;
        let coset = u64::from(self.config.mode.materializes_coset()) * backing;
        let fold = u64::from(self.config.mode.runs_fold()) * (backing + folded);
        let stage = [
            2 * coset,
            backing + coset + partials,
            partials + UNISKIP_CELLS as u64 * e4_bytes,
            fold,
        ];
        PassBytes {
            stage,
            total: stage.iter().sum(),
        }
    }

    /// The 32 evaluations the last pass produced, four `u32` limbs per cell.
    pub fn download_q(&self) -> CudaResult<Vec<u32>> {
        let mut host = vec![0u32; UNISKIP_CELLS * CLASS_WORDS[CLASS_E4]];
        memory_copy(&mut host[..], &self.q[..])?;
        Ok(host)
    }

    /// Compare all 32 cells against the full CPU oracle, bit-exact.
    pub fn validate_q(&self, program: &SynthProgram) -> CudaResult<Result<(), String>> {
        let actual = self.download_q()?;
        let expected = reference::eval_q(
            program,
            &self.geometry,
            self.seed,
            self.flat_eq,
            self.layout.source_layout,
        );
        Ok(reference::check_q(&expected, &actual))
    }

    fn download_column(
        &self,
        backing: &[DeviceAllocation<u32>; CLASSES],
        window: usize,
        column: usize,
    ) -> CudaResult<Vec<u32>> {
        let class = self.layout.windows[window].class;
        let words = CLASS_WORDS[class];
        let start = self.layout.column_base(window, column) as usize * words;
        let len = self.layout.column_elements() as usize * words;
        let mut host = vec![0u32; len];
        memory_copy(&mut host[..], &backing[class][start..start + len])?;
        Ok(host)
    }

    /// Compare the first and last used column of every window — taps and all 16
    /// coset cells — against the host reference, bit-exact. Only meaningful where the
    /// coset is materialized; a fused mode has no buffer to check and leans on the
    /// `q` oracle, which addresses all 32 cells.
    pub fn validate_lde(&self) -> CudaResult<Result<(), String>> {
        assert!(
            self.config.mode.materializes_coset(),
            "validate_lde needs a materialized coset"
        );
        for window in 0..UNISKIP_WINDOWS {
            let columns = self.layout.windows[window].columns as usize;
            let checked: Vec<usize> = match columns {
                0 => Vec::new(),
                1 => vec![0],
                _ => vec![0, columns - 1],
            };
            for column in checked {
                let rec = self.desc.source[..self.desc.num_sources as usize]
                    .iter()
                    .copied()
                    .find(|r| addr_window(r.addr) == window && addr_column(r.addr) == column)
                    .expect("every window column is a source record");
                let taps = self.download_column(&self.taps, window, column)?;
                let coset = self.download_column(&self.cosets, window, column)?;
                let label = format!("window {window} column {column}");
                if let Err(e) = reference::check_column(
                    &self.layout,
                    self.seed,
                    window,
                    rec,
                    &taps,
                    &coset,
                    &label,
                ) {
                    return Ok(Err(e));
                }
            }
        }
        Ok(Ok(()))
    }

    /// The first and last used column of a field class, in backing order. Fewer
    /// than two entries if the class holds fewer than two columns.
    fn class_edge_sources(&self, class: usize) -> Vec<(usize, UniskipSourceRecord)> {
        let mut of_class: Vec<(usize, UniskipSourceRecord)> = self.desc.source
            [..self.desc.num_sources as usize]
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, rec)| class_index(rec.source_class) == class)
            .collect();
        of_class.sort_by_key(|(_, rec)| {
            self.layout
                .column_base(addr_window(rec.addr), addr_column(rec.addr))
        });
        match of_class.len() {
            0 => Vec::new(),
            1 => vec![of_class[0]],
            n => vec![of_class[0], of_class[n - 1]],
        }
    }

    /// Rows the fold check samples: the two ends plus a few interior rows.
    fn sample_rows(&self) -> Vec<u64> {
        let rows = self.layout.rows;
        let mut sampled = vec![0, 1, rows / 3, rows / 2, rows - 1];
        sampled.sort_unstable();
        sampled.dedup();
        sampled
    }

    /// Compare the folded values of the first and last used column of both field
    /// classes, at sampled rows, against the host fold — bit-exact. Sampled rather
    /// than exhaustive: the fold output is one `e4` per (source, row), so a full
    /// download is the size of the whole tap backing.
    pub fn validate_fold(&self) -> CudaResult<Result<(), String>> {
        assert!(
            self.config.mode.runs_fold(),
            "validate_fold needs a mode that runs the fold stage"
        );
        let words = CLASS_WORDS[CLASS_E4];
        let rows = self.sample_rows();
        for class in 0..CLASSES {
            for (id, rec) in self.class_edge_sources(class) {
                let mut host = vec![0u32; rows.len() * words];
                for (i, &row) in rows.iter().enumerate() {
                    let start = (id as u64 * self.layout.rows + row) as usize * words;
                    memory_copy(
                        &mut host[i * words..(i + 1) * words],
                        &self.folded[start..start + words],
                    )?;
                }
                let label = format!(
                    "source {id} (window {} column {})",
                    addr_window(rec.addr),
                    addr_column(rec.addr)
                );
                if let Err(e) =
                    reference::fold_check(&self.layout, self.seed, rec, &rows, &host, &label)
                {
                    return Ok(Err(e));
                }
            }
        }
        Ok(Ok(()))
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::synth::{generate, Census, SYNTH_E4_WINDOW};

    /// The 128 branch and the constant pair the `.cuh` mirrors. `uniskip_lsb_pair.cuh`
    /// holds `UNISKIP_PAIR_WARPS_128 = 4` with `static_assert(ROWS_PER_BLOCK_128 == 16)`;
    /// if either side drifts the kernel and the grid disagree about rows per block, which
    /// is silent corruption rather than a build error.
    #[test]
    fn cpu_pass_config_rows_per_block_tracks_the_block_size() {
        assert_eq!(UNISKIP_PAIR_WARPS_128, 4);
        assert_eq!(UNISKIP_PAIR_THREADS_128, 128);
        assert_eq!(UNISKIP_PAIR_ROWS_PER_BLOCK_128, 16);
        let at = |threads: usize| {
            PassConfig {
                mode: EvalMode::LsbPair,
                block_threads: threads as u32,
                ..Default::default()
            }
            .rows_per_block()
        };
        assert_eq!(
            at(UNISKIP_THREADS_PER_BLOCK),
            UNISKIP_PAIR_ROWS_PER_BLOCK as u32
        );
        assert_eq!(
            at(UNISKIP_PAIR_THREADS_128),
            UNISKIP_PAIR_ROWS_PER_BLOCK_128 as u32
        );
        // The block axis is `lsb-pair`'s alone: no other mode reads it.
        assert_eq!(
            PassConfig {
                mode: EvalMode::Unfused,
                block_threads: UNISKIP_PAIR_THREADS_128 as u32,
                ..Default::default()
            }
            .rows_per_block(),
            UNISKIP_ROWS_PER_BLOCK as u32
        );
    }

    /// The three-state hint, resolved without a device. `Default` is the only state that
    /// reads the predicate, and it is the one a silent regression would turn into a
    /// baseline shift no log states.
    #[test]
    fn cpu_carveout_hint_resolves_three_states() {
        assert_eq!(CarveoutHint::default(), CarveoutHint::Default);
        assert_eq!(CarveoutHint::Default.resolve(true), Some(16));
        assert_eq!(CarveoutHint::Default.resolve(false), None);
        assert_eq!(CarveoutHint::None.resolve(true), None);
        assert_eq!(CarveoutHint::None.resolve(false), None);
        assert_eq!(CarveoutHint::Explicit(25).resolve(true), Some(25));
        assert_eq!(CarveoutHint::Explicit(25).resolve(false), Some(25));
    }

    /// The spelling every operator doc points at. `none` is the ONLY word the parser
    /// takes; anything else must be a bare percent, and a mistyped word must not fall
    /// through to a default that silently applies a hint.
    #[test]
    fn cpu_carveout_hint_parses_none_and_percent() {
        assert_eq!("none".parse::<CarveoutHint>(), Ok(CarveoutHint::None));
        assert_eq!("16".parse::<CarveoutHint>(), Ok(CarveoutHint::Explicit(16)));
        assert_eq!("0".parse::<CarveoutHint>(), Ok(CarveoutHint::Explicit(0)));
        assert!("None".parse::<CarveoutHint>().is_err());
        assert!("default".parse::<CarveoutHint>().is_err());
        assert!("-1".parse::<CarveoutHint>().is_err());
        assert!("16%".parse::<CarveoutHint>().is_err());
    }

    /// One leg of that predicate compares `eval_kernel` against this name, so a rename on
    /// either side would silently stop applying the default on the single-arm path.
    #[test]
    fn cpu_cached_128_lb_kernel_name_is_pinned() {
        assert_eq!(
            LaneKernel::Cached128Lb.name(),
            "eval_lsb_pair_cached_128_lb"
        );
    }

    #[test]
    fn cpu_layout_tiles_backings() {
        let geometry = Geometry::new(10).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let layout = Layout::new(&program, &geometry, SourceLayout::PlaneMajor);

        let mut expected = [0u64; CLASSES];
        for window in 0..UNISKIP_WINDOWS {
            let placement = layout.windows[window];
            assert_eq!(
                placement.class,
                class_index(program.windows[window].kind.source_class())
            );
            assert_eq!(placement.offset, expected[placement.class]);
            expected[placement.class] += u64::from(placement.columns) * layout.column_elements();
            // E4 alignment invariant: a `uint4` load needs a 16-byte-aligned base.
            if placement.class == CLASS_E4 {
                assert_eq!(layout.window_byte_offset(window) % 16, 0);
            }
        }
        assert_eq!(layout.class_elements, expected);
        assert_eq!(layout.windows[SYNTH_E4_WINDOW].class, CLASS_E4);

        // Column blocks tile their backing exactly once, with no gaps.
        let mut seen = std::collections::HashSet::new();
        for window in 0..UNISKIP_WINDOWS {
            let placement = layout.windows[window];
            for column in 0..placement.columns as usize {
                let base = layout.column_base(window, column);
                for element in base..base + layout.column_elements() {
                    assert!(seen.insert((placement.class, element)));
                }
            }
        }
        assert_eq!(seen.len() as u64, layout.class_elements.iter().sum::<u64>());
    }
}
