use std::ffi::CStr;

use clap::{CommandFactory, Parser};
use era_cudart::device::{get_device, get_device_properties};
use gpu_gkr_uniskip_bench::abi::{
    UNISKIP_CELLS, UNISKIP_COMPACT_DEFAULT_GROUPS, UNISKIP_LOG_TAPS, UNISKIP_PAIR_THREADS_128,
    UNISKIP_SEG_COHORTS, UNISKIP_SRC_E4_GLOBAL, UNISKIP_THREADS_PER_BLOCK,
};
use gpu_gkr_uniskip_bench::cache;
use gpu_gkr_uniskip_bench::compact::BankPerm;
use gpu_gkr_uniskip_bench::coset_cache::{
    self, CacheArm, CacheMutation, LaneCarrier, LaneSet, PrologueOrder,
};
use gpu_gkr_uniskip_bench::geometry::Geometry;
use gpu_gkr_uniskip_bench::harness::PairArm;
use gpu_gkr_uniskip_bench::harness::{
    CarveoutHint, CellMap, EvalMode, Harness, LdeShape, PassConfig, StageTimes, STAGES,
};
use gpu_gkr_uniskip_bench::kernels::NvtxRange;
use gpu_gkr_uniskip_bench::seg;
use gpu_gkr_uniskip_bench::synth::{generate, Census, TermOrder};
use gpu_gkr_uniskip_bench::window::{self, WindowMutation};

/// Standalone CUDA benchmark for one uniskip sumcheck pass (k = 4).
#[derive(Parser)]
#[command(name = "gpu_gkr_uniskip_bench", version, about, long_about = None)]
struct Cli {
    /// log2 of the trace length (k = 4, so log_rows = log_trace - 4).
    #[arg(long, default_value_t = 20)]
    log_trace: u32,

    /// Untimed iterations run before measurement. Default 3, or a factorial rotation's
    /// PREREGISTERED warmup when one is selected (`--frontier-factorial` 10,
    /// `--frontier-extension` 16, `--frontier-interior` 12 — a whole number of rotations
    /// in every case).
    #[arg(long)]
    warmup: Option<u32>,

    /// Timed iterations. Default 20, or a factorial rotation's PREREGISTERED round count
    /// when one is selected (`--frontier-factorial` 100, `--frontier-extension` 104,
    /// `--frontier-interior` 96). An explicit value is accepted only if it still balances
    /// the rotation.
    #[arg(long)]
    iterations: Option<u32>,

    /// Seed of the deterministic synthetic program and data generator.
    #[arg(long, default_value_t = 0)]
    seed: u32,

    /// Census: distinct source columns.
    #[arg(long, default_value_t = 59)]
    sources: u32,

    /// Census: semantic terms (ungrouped + grouped atoms).
    #[arg(long, default_value_t = 150)]
    semantic_terms: u32,

    /// Census: groups (each contributes one header record).
    #[arg(long, default_value_t = 25)]
    groups: u32,

    /// Census: semantic terms that live inside a group.
    #[arg(long, default_value_t = 72)]
    grouped_atoms: u32,

    /// Source resolution: `unfused` materializes the coset in its own LDE stage,
    /// `fused-recompute` extends the taps on read (no LDE launch, no coset backing),
    /// `fused-cached` adds the fixed shared-memory slab assignment on top,
    /// `lsb-recompute` is the v3 R0 arm — LSB group layout, lane = tap, one
    /// shuffle-NTT per reference, no window and no fold stage — and `lsb-compact` is
    /// v3 R1, which stages the group vectors in shared memory and packs only the real
    /// multiplies across lanes (measured slower; kept as a control arm). `lsb-pair` is
    /// v3 R2 and the recommended v3 arm: pair-resident radix-2, both halves of a
    /// butterfly in one lane, so the unity multiply is never written.
    #[arg(long, value_enum, default_value_t = EvalMode::Unfused)]
    mode: EvalMode,

    /// Record order: `census` = emission order, `locality` = the permutation that
    /// clusters records reading the same sources. Same records, same `q`.
    #[arg(long, value_enum, default_value_t = TermOrder::Census)]
    term_order: TermOrder,

    /// LDE grid shape: `cell` = one thread per coset cell (v1, 16x tap re-read),
    /// `row` = one thread per row emitting all 16 cells. Same output bytes.
    /// Unfused modes only.
    #[arg(long, value_enum)]
    lde_shape: Option<LdeShape>,

    /// Cells a warp owns: `block` = `4w..4w+3` (v1; warps 4-7 carry every coset
    /// recompute), `interleave` = `{w, w+8, w+16, w+24}`. Fused modes only.
    #[arg(long, value_enum)]
    cell_map: Option<CellMap>,

    /// Groups a warp owns in `--mode lsb-compact`: 4 or 8. A lane holds `groups / 2`
    /// elements, so one program walk serves `groups` rows. Compact mode only.
    #[arg(long)]
    compact_groups: Option<u32>,

    /// v3 R3 arm of `--mode lsb-pair`: `control` (R2 exactly — same kernel, same wire),
    /// `t` (`__launch_bounds__(256, 3)` alone — built to test the twiddle-remat lever and
    /// measured not to: bank-3 loads are byte-identical either way), `w` (coset-only
    /// top-4-BF register window), `wt` (both), `wnone` (the WØ diagnostic: window kernel
    /// with an all-`none` tag stream), or `wtnone` (the same at 3 blocks, which splits
    /// `wt - t` into machinery and removal). `lsb-pair` mode only.
    #[arg(long, value_enum)]
    pair_arm: Option<PairArm>,

    /// v3 R4/R5/R8 coset-cache arm of `--mode lsb-pair`: `control` (no cache — today's
    /// behavior), `cache0` (cached body, empty admitted set — the fixed-machinery
    /// diagnostic), a prefix of the canonical admission list (`hot4`, `hot16`, the R5/R8
    /// frontier points `k17 k18 k19 k20 k21 k22 k23 k24 k32 k40 k45 k46 k48 k49 k50 k51`,
    /// `allrepeat`), the E4-only set `e4rich`, or the `all59` capacity-stress diagnostic
    /// (every live source, refs = 1 included). Mutually exclusive with `--pair-arm` and
    /// with `--factorial`. The host plan for every arm is built and validated on any
    /// `lsb-pair` run, whichever arm is selected.
    #[arg(long, value_enum)]
    cache_arm: Option<CacheArm>,

    /// Run the 128-thread NO-CACHE baseline under `__launch_bounds__(128, 7)` — the
    /// bounded control, so the 128 cache contrast can be taken bound-to-bound instead of
    /// assuming a launch bound costs the same on two different bodies (R3's `t` measured
    /// +3.43 % on a body whose registers the bound did not change). The default is the
    /// FROZEN control128. 128 threads, `--cache-arm control` only.
    #[arg(long)]
    control_launch_bounds: bool,

    /// Run the 128-thread cached arm WITHOUT `__launch_bounds__(128, 7)`. Unbounded it
    /// takes 75 registers = 6 blocks/SM against control128's 7, so the cache-vs-control
    /// contrast would carry an occupancy step; the bounded sibling is the measurement arm
    /// and this flag prices what the bound costs. 128-thread cached arms only.
    #[arg(long)]
    no_cache_launch_bounds: bool,

    /// Run the v3 R4 primary factorial: 11 lanes (5 arms at 256, 6 at 128 including both
    /// no-cache baselines) in ONE process against shared allocations, in a generated cyclic
    /// rotation. Use `--iterations` a multiple of 11 (the record uses 110 per term order).
    /// The factorial owns both block sizes internally, so it takes neither --block-threads
    /// nor a single --cache-arm.
    #[arg(long)]
    cache_factorial: bool,

    /// Run the v3 R5 primary admission-frontier factorial: 10 lanes at 128 threads
    /// (`k24 k32 k40 k45 k46 k48 hot16 cache0 control_lb`) plus the shipping `control@256`
    /// anchor, in ONE process against shared allocations, in a generated cyclic rotation.
    /// 100 rounds / 10 warmup per term order unless overridden; an override must still be a
    /// multiple of 10. Mutually exclusive with every other rotation.
    #[arg(long)]
    frontier_factorial: bool,

    /// Run the v3 R5 conditional frontier extension: 8 lanes — the refs-2 E4 tail
    /// `k49 k50 k51` with `k48` riding along so the k48 -> k49 boundary is PAIRED
    /// in-session, plus the anchors both sessions share. 104 rounds / 16 warmup per term
    /// order unless overridden; an override must still be a multiple of 8.
    #[arg(long)]
    frontier_extension: bool,

    /// Run the v3 R8 frontier-interior sweep: 12 lanes — the seven unmeasured admission
    /// points `k17 k18 k19 k20 k21 k22 k23` with `k24` riding along so the whole
    /// `hot16 -> k24` walk is PAIRED in-session, plus the anchors every frontier session
    /// shares. 96 rounds / 12 warmup per term order unless overridden; an override must
    /// still be a multiple of 12.
    #[arg(long)]
    frontier_interior: bool,

    /// Run the v3 R6 carveout probe: 5 lanes — the R5 knee neighborhood `k24 k32 k40
    /// hot16` at 128 threads plus the shipping `control@256` anchor — in ONE process, one
    /// carveout state (the R7 default 16, or `--carveout-hint none` for the driver
    /// default) for the whole process.
    /// The whole contract is preregistered and PINNED: locality order only, exactly
    /// 100 rounds / 10 warmup, hint 16. Mutually exclusive with every other rotation.
    #[arg(long)]
    carveout_probe: bool,

    /// Run the v3 R7 shared-memory-carrier rotation: 10 lanes — the three local anchors
    /// (`control@256`, `control_lb@128`, the hinted `hot16@128` incumbent), the segmented
    /// machinery floor, and the carrier-S points `seg-cache0-s seg-hot16-s64
    /// seg-hot16-s100 seg-k24-s seg-k40-s seg-hot16-acc` — in ONE process, one deal shared
    /// by every seg lane. 100 rounds / 10 warmup unless overridden; an override must still
    /// be a multiple of 10.
    #[arg(long)]
    seg_smem_factorial: bool,

    /// Run the v3 R7 device-scratch-carrier rotation: 9 lanes — the same three local
    /// anchors and machinery floor, then carrier G at `cache0 hot16 k24 k40 allrepeat`.
    /// 99 rounds / 9 warmup unless overridden; an override must still be a multiple of 9.
    #[arg(long)]
    seg_gmem_factorial: bool,

    /// Run the v3 R7 anchor rotation: 2 lanes — the hinted `hot16@128` incumbent against
    /// the never-hinted shipping `control@256`. It deals no program and prints no SEG
    /// line. Two jobs: re-anchoring the seg sessions, and pricing the incumbent's carveout
    /// hint as a PAIRED per-round contrast when `--carveout-hint 32` or `100` is added —
    /// which is what a standalone log cannot carry under session drift.
    #[arg(long)]
    seg_anchor: bool,

    /// Run the v3 R7b transplant rotation: 8 lanes — the same three local anchors and
    /// machinery floor as the R7 sets, then the four-rows-per-block transplant at
    /// `cache0 hot16 k40` plus the slotted-slab variant of `hot16`. 96 rounds / 8 warmup
    /// unless overridden; an override must still be a multiple of 8.
    #[arg(long)]
    segb_factorial: bool,

    /// v3 R7 carrier of a single segmented arm: `seg-s` (carrier S at the 64 KiB carveout
    /// request), `seg-s100` (the same body at 100 KiB), `seg-s-acc` (the accumulator-first
    /// reduction diagnostic), `seg-g` (carrier G, a per-block device-scratch slab) or
    /// `seg-recompute` (the machinery floor: the cohort loop with no slab and no
    /// prologue). The v3 R7b transplants take the same surface: `segb-g`,
    /// `segb-recompute` and `segb-g-slotted` (the slab region claimed per resident block
    /// out of a software slot pool). Needs `--mode lsb-pair --block-threads 128` and a
    /// `--cache-arm` on that carrier's support matrix; composes with `--validate` /
    /// `--dump-q` / `--profile`.
    #[arg(long, value_enum)]
    carrier: Option<LaneCarrier>,

    /// v3 R6: preferred shared-memory carveout (percent of the maximum) set on the bounded
    /// 128-thread cached kernel before any launch; absent = the R7 default of 16 wherever
    /// that kernel runs, `none` = the driver's own sizing. A percent composes with
    /// `--carveout-probe`, with `--seg-anchor` (tiers 32 and 100 — the attribution
    /// contrast), with a single cached `--cache-arm` at 128 threads (the ncu gate surface),
    /// or with a `--carrier` arm — where it steers THAT carrier's symbol instead, which is
    /// how a dynamic-shared body's hint ladder is mapped (`--profile`, one round, no
    /// validation knob). Rejected everywhere else; `none` composes with everything except a
    /// carrier, which must state its configuration.
    #[arg(long, value_name = "none|0..=100")]
    carveout_hint: Option<CarveoutHint>,

    /// TEST-ONLY. Corrupt the selected cached arm's records and upload them UNCHECKED —
    /// the always-on validator would reject them, which is the point. `retarget` points a
    /// cached reference at a different LIVE same-width slot, so `q` must change.
    #[arg(long, value_enum)]
    cache_mutate: Option<CacheMutation>,

    /// Class the v3 R4 prologue produces FIRST. `e4first` is the spec's pinned production
    /// order; `bffirst` is the capacity-arm diagnostic — whichever class is produced last
    /// is the one still warm in L1 at walk entry. A table-emission order only: the kernel
    /// walks what the host uploads, so the two cost the same SASS.
    #[arg(long, value_enum)]
    prologue_order: Option<PrologueOrder>,

    /// Threads per eval block in `--mode lsb-pair`: 256 (the R2 shape) or 128 (v3 R4's
    /// second block size — 4 warps, 16 rows per block, doubled grid). 128 is a distinct
    /// kernel, not a launch parameter: the shared plane and the epilogue reduction are
    /// static. It is the no-cache BASELINE for the 128 axis, so it composes with
    /// `--pair-arm control` only.
    #[arg(long)]
    block_threads: Option<u32>,

    /// Staging tap permutation in `--mode lsb-compact`: `linear` (the shipped,
    /// bank-conflict-free layout) or `identity` (the pre-fix layout, kept so the
    /// bank-conflict A/B is re-runnable). Compact mode only.
    #[arg(long, value_enum)]
    bank_perm: Option<BankPerm>,

    /// Validation knob: rewrite this many same-class binary products into
    /// self-products (`x * x`), which is the only way to exercise the LSB mode's
    /// duplicate rule — the default census emits none. It changes `q`; the census
    /// and cache plan do not track it and go stale (see README), so a timing taken
    /// under it is not comparable with the recorded arms.
    #[arg(long, default_value_t = 0)]
    self_products: u32,

    /// Wrap the first timed iteration in the `gkr_uniskip_pass0` NVTX range.
    /// Needs `--iterations >= 1`.
    #[arg(long)]
    profile: bool,

    /// Run all six R3 arms in ONE process against shared allocations, executing them in
    /// a generated cyclic rotation each round so no arm keeps a fixed position in the
    /// order. Emits one `SAMPLE` line per (round, arm) for `tools/factorial_table.py`.
    /// Use a round count that is a multiple of 6 so every arm starts equally often.
    /// Requires `--mode lsb-pair`; mutually exclusive with `--pair-arm`.
    #[arg(long)]
    factorial: bool,

    /// TEST-ONLY. Corrupt the window schedule and upload it UNCHECKED — the always-on
    /// validator would reject these streams, which is the point: it proves the device
    /// reads the tag's slot number rather than deriving it. `retarget` points one reuse at
    /// a different already-filled slot. Requires a window arm.
    #[arg(long, value_enum)]
    window_mutate: Option<WindowMutation>,

    /// TEST-ONLY, diagnostic builds only (`GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1`): report
    /// the device chain-execution counter per warp-program walk, and optionally poison
    /// every slot's retained copy after its fill so a later reuse must change `q`.
    #[arg(long)]
    window_count: bool,

    /// TEST-ONLY, diagnostic builds only. See `--window-count`.
    #[arg(long)]
    window_poison: bool,

    /// Print the 32 evaluations as raw hex words, one cell per line. Two runs that
    /// claim the same `q` can then be compared device-to-device, without going through
    /// the host oracle — which is what pins `lsb-compact` against `lsb-recompute`.
    #[arg(long)]
    dump_q: bool,

    /// Check the GPU result against the host reference.
    #[arg(long)]
    validate: bool,

    /// Validate with all eq tables forced to ONE on both sides. Implies `--validate`.
    #[arg(long)]
    validate_flat_eq: bool,
}

/// The single-arm defaults of `--warmup` / `--iterations`; a factorial rotation supplies
/// its own preregistered pair instead.
const DEFAULT_WARMUP: u32 = 3;
const DEFAULT_ITERATIONS: u32 = 20;

impl Cli {
    /// Every rotation flag that is set. More than one is rejected before anything reads
    /// [`Cli::lane_set`], so the ambiguity never reaches a lane list.
    fn lane_sets(&self) -> Vec<LaneSet> {
        [
            (self.cache_factorial, LaneSet::CacheFactorial),
            (self.frontier_factorial, LaneSet::FrontierFactorial),
            (self.frontier_extension, LaneSet::FrontierExtension),
            (self.frontier_interior, LaneSet::FrontierInterior),
            (self.carveout_probe, LaneSet::CarveoutProbe),
            (self.seg_smem_factorial, LaneSet::SegSmem),
            (self.seg_gmem_factorial, LaneSet::SegGmem),
            (self.seg_anchor, LaneSet::SegAnchor),
            (self.segb_factorial, LaneSet::Segb),
        ]
        .into_iter()
        .filter_map(|(on, set)| on.then_some(set))
        .collect()
    }

    fn lane_set(&self) -> Option<LaneSet> {
        self.lane_sets().first().copied()
    }

    /// Timed rounds: the flag if given, else the selected rotation's preregistered count,
    /// else the single-arm default.
    fn rounds(&self) -> u32 {
        self.iterations.unwrap_or_else(|| {
            self.lane_set()
                .and_then(LaneSet::rounds_and_warmup)
                .map_or(DEFAULT_ITERATIONS, |(rounds, _)| rounds)
        })
    }

    fn warmup_rounds(&self) -> u32 {
        self.warmup.unwrap_or_else(|| {
            self.lane_set()
                .and_then(LaneSet::rounds_and_warmup)
                .map_or(DEFAULT_WARMUP, |(_, warmup)| warmup)
        })
    }
}

fn fail(message: String) -> ! {
    Cli::command()
        .error(clap::error::ErrorKind::InvalidValue, message)
        .exit()
}

/// `cudaDevAttrLocalL1CacheSupported`, recorded because "local hits are L1 hits" is an
/// ASSUMPTION on any part until this says otherwise — spec 7 requires it queried once.
fn local_l1_supported() -> String {
    let Ok(id) = get_device() else {
        return "unknown".into();
    };
    match get_device_properties(id) {
        Ok(props) => format!("{}", props.localL1CacheSupported != 0),
        Err(e) => format!("unknown ({e})"),
    }
}

fn device_name() -> String {
    let id = match get_device() {
        Ok(id) => id,
        Err(e) => return format!("unknown ({e})"),
    };
    match get_device_properties(id) {
        // CUDA fills `name` with a NUL-terminated ASCII string.
        Ok(props) => unsafe { CStr::from_ptr(props.name.as_ptr()) }
            .to_string_lossy()
            .into_owned(),
        Err(e) => format!("unknown ({e})"),
    }
}

/// The slotted carrier's claim mask, after every launch this process made: a set bit is a
/// region a block claimed and never released, which the next launch would hand to a second
/// owner. Outside every timed loop by construction — it runs once, after the rotation.
fn check_slot_masks(harness: &Harness) {
    match harness
        .validate_slot_masks()
        .unwrap_or_else(|e| fail(format!("slot mask download failed: {e}")))
    {
        Ok(0) => (),
        Ok(checked) => println!("slot mask: all clear ({checked} checked)"),
        Err(leak) => {
            eprintln!("slot mask: LEAKED — {leak}");
            std::process::exit(1);
        }
    }
}

fn gib(bytes: u64) -> f64 {
    bytes as f64 / (1u64 << 30) as f64
}

/// `(median, mean, min, max)` of a non-empty sample.
fn summarize(samples: &[f32]) -> (f64, f64, f64, f64) {
    let mut sorted: Vec<f64> = samples.iter().map(|&s| f64::from(s)).collect();
    sorted.sort_by(f64::total_cmp);
    let mid = sorted.len() / 2;
    let median = if sorted.len().is_multiple_of(2) {
        0.5 * (sorted[mid - 1] + sorted[mid])
    } else {
        sorted[mid]
    };
    let mean = sorted.iter().sum::<f64>() / sorted.len() as f64;
    (median, mean, sorted[0], sorted[sorted.len() - 1])
}

/// Compulsory bandwidth of a stage: its floor traffic over its median time.
fn gb_per_s(bytes: u64, median_ms: f64) -> f64 {
    if median_ms <= 0.0 {
        return 0.0;
    }
    bytes as f64 / (median_ms * 1e-3) / 1e9
}

/// The legal flag matrix: a grid-shape flag only applies to the mode that runs that
/// grid. Rejecting the combination is deliberate — silently ignoring it would let a
/// recorded measurement name a shape the run never used.
fn pass_config(cli: &Cli, geometry: &Geometry) -> PassConfig {
    // FIRST, before anything reads the selected rotation: each rotation pins its own lane
    // list, round count and log keyword, so two of them at once is not a configuration.
    if let [first, second, ..] = cli.lane_sets()[..] {
        fail(format!(
            "{} and {} each own the whole rotation — its lanes, its round count and its \
             log grammar; pick one",
            first.flag(),
            second.flag()
        ));
    }
    if !cli.mode.uses_lde_shape() && cli.lde_shape.is_some() {
        fail(format!(
            "--lde-shape applies to unfused modes only; --mode {} runs no LDE stage",
            cli.mode.as_str()
        ));
    }
    if !cli.mode.uses_cell_map() && cli.cell_map.is_some() {
        fail(match cli.mode {
            EvalMode::Unfused => format!(
                "--cell-map applies to fused modes only; --mode {} keeps the v1 block map",
                cli.mode.as_str()
            ),
            _ => format!(
                "--cell-map applies to fused modes only; --mode {} fixes its own lane map",
                cli.mode.as_str()
            ),
        });
    }
    if !cli.mode.uses_compact_groups() && cli.compact_groups.is_some() {
        fail(format!(
            "--compact-groups applies to --mode lsb-compact only; --mode {} has a fixed warp geometry",
            cli.mode.as_str()
        ));
    }
    if cli.factorial {
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "--factorial applies to --mode lsb-pair only; --mode {} has no R3 arms",
                cli.mode.as_str()
            ));
        }
        if cli.pair_arm.is_some() {
            fail("--factorial runs every arm; it is mutually exclusive with --pair-arm".into());
        }
        // The factorial rotates the R3 arms, which read the CONTROL descriptor. A cached
        // arm rewrites `desc.source`, so this would silently time R3 bodies against a
        // cache-cloned wire.
        if cli.cache_arm.is_some_and(|a| a.uses_cache()) {
            fail(
                "--factorial rotates the R3 --pair-arm bodies; a cached --cache-arm would \
                 change the uploaded source records under them"
                    .into(),
            );
        }
        // The factorial returns before the validation block, so accepting these would
        // print `validate true` and check nothing.
        if cli.window_count || cli.window_poison {
            fail(
                "--factorial is a timing run; --window-count and --window-poison are \
                 diagnostic probes that would contaminate it — use --pair-arm or \
                 tools/r3_gates.sh"
                    .into(),
            );
        }
        // `--profile` wraps the first timed iteration, which in a factorial belongs to
        // whichever arm the rotation put first — an NVTX range over one arbitrary arm.
        if cli.profile {
            fail(
                "--factorial rotates arms, so --profile would wrap whichever arm the \
                 rotation put first; profile one arm with --pair-arm"
                    .into(),
            );
        }
        if cli.validate || cli.validate_flat_eq || cli.dump_q {
            fail(
                "--factorial is a timing run; use --pair-arm or tools/r3_gates.sh for \
                 --validate / --dump-q"
                    .into(),
            );
        }
    }
    if !cli.mode.uses_pair_arm() && cli.pair_arm.is_some() {
        fail(format!(
            "--pair-arm applies to --mode lsb-pair only; --mode {} has no R3 arms",
            cli.mode.as_str()
        ));
    }
    let block_threads = cli
        .block_threads
        .unwrap_or(UNISKIP_THREADS_PER_BLOCK as u32);
    if cli.block_threads.is_some() {
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "--block-threads applies to --mode lsb-pair only; --mode {} has one block \
                 shape",
                cli.mode.as_str()
            ));
        }
        if block_threads as usize != UNISKIP_THREADS_PER_BLOCK
            && block_threads as usize != UNISKIP_PAIR_THREADS_128
        {
            fail(format!(
                "--block-threads {block_threads} is not one of {UNISKIP_THREADS_PER_BLOCK}, \
                 {UNISKIP_PAIR_THREADS_128}"
            ));
        }
    }
    if block_threads == UNISKIP_PAIR_THREADS_128 as u32 {
        // The R3 arms are 256-thread kernels; there is no 128-thread window body, and the
        // 128 kernel is the no-cache baseline of its own axis.
        if cli.pair_arm.is_some_and(|a| a != PairArm::Control) {
            fail(
                "--block-threads 128 is the no-cache baseline; the R3 --pair-arm bodies \
                  exist at 256 threads only"
                    .into(),
            );
        }
        if cli.factorial {
            fail(
                "--factorial rotates the R3 256-thread arms; --block-threads 128 has no \
                  place in it"
                    .into(),
            );
        }
    }
    if let Some(order) = cli.prologue_order {
        // Mode first: a wrong mode is the coarser error and must not be masked by the
        // arm-scope ones below.
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "--prologue-order applies to --mode lsb-pair only; --mode {} has no \
                 coset-cache prologue",
                cli.mode.as_str()
            ));
        }
        // The segmented prologue is STRIPED by owner warp against the pinned e4-first
        // production order; re-ordering the table would move rows between warps without
        // moving their owner bytes.
        if let Some(carrier) = cli.carrier {
            fail(format!(
                "--prologue-order is not part of the segmented surface; --carrier {} \
                 stripes the pinned e4first order by owner warp",
                carrier.as_str()
            ));
        }
        let arm = cli.cache_arm.unwrap_or_default();
        if !arm.uses_cache() {
            fail(format!(
                "--prologue-order {} is inert without a cached --cache-arm: there is no \
                 prologue to order",
                order.as_str()
            ));
        }
        // Spec 3.3: the alternate class order is a capacity-arm diagnostic, not a design
        // fork — it says nothing on an arm whose footprint fits comfortably.
        if order != PrologueOrder::E4First && !matches!(arm, CacheArm::AllRepeat | CacheArm::All59)
        {
            fail(format!(
                "--prologue-order {} is a capacity-arm diagnostic; it applies to \
                 --cache-arm allrepeat or all59, not {}",
                order.as_str(),
                arm.as_str()
            ));
        }
    }
    // ONE matrix for all three rotations: R4's primary and both R5 frontier sets face the
    // same exclusions, parameterized by the flag that selected the set. A per-mode copy is
    // how a knob ends up rejected under one rotation and silently accepted under another.
    if let Some(set) = cli.lane_set() {
        let flag = set.flag();
        // Everything the rotation must own itself, or that would contaminate it.
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "{flag} applies to --mode lsb-pair only; --mode {} has no {}",
                cli.mode.as_str(),
                set.arms_noun()
            ));
        }
        for (other, on) in [
            ("--pair-arm", cli.pair_arm.is_some()),
            ("--cache-arm", cli.cache_arm.is_some()),
            ("--carrier", cli.carrier.is_some()),
            ("--block-threads", cli.block_threads.is_some()),
            ("--prologue-order", cli.prologue_order.is_some()),
            ("--cache-mutate", cli.cache_mutate.is_some()),
            ("--factorial", cli.factorial),
            ("--control-launch-bounds", cli.control_launch_bounds),
            ("--no-cache-launch-bounds", cli.no_cache_launch_bounds),
        ] {
            if on {
                fail(format!(
                    "{flag} owns the arm set and both block sizes; {other} would \
                     change what the rotation runs"
                ));
            }
        }
        if cli.window_count || cli.window_poison || cli.window_mutate.is_some() {
            fail(format!(
                "{flag} is a timing run; the diagnostic probes would contaminate \
                  it — use {}",
                set.gates()
            ));
        }
        // The removals the emitter divides by are the DEFAULT census's. Any census knob
        // silently invalidates them, and a slope is worse than useless when its denominator
        // is wrong.
        let default = Census::default();
        for (knob, differs) in [
            ("--sources", cli.sources != default.sources),
            (
                "--semantic-terms",
                cli.semantic_terms != default.semantic_terms,
            ),
            ("--groups", cli.groups != default.groups),
            (
                "--grouped-atoms",
                cli.grouped_atoms != default.grouped_atoms,
            ),
            ("--self-products", cli.self_products != 0),
        ] {
            if differs {
                fail(format!(
                    "{flag} prices removals against the DEFAULT census; {knob} \
                     changes the program and invalidates every slope"
                ));
            }
        }
        // Balance is a GATE, not a note: an unbalanced rotation gives some lanes more
        // first-position rounds than others, and first position is the one that pays for
        // whatever the previous round left in cache.
        let lane_count = set.lanes().len() as u32;
        if !cli.rounds().is_multiple_of(lane_count) {
            fail(format!(
                "{flag} needs --iterations a multiple of {lane_count} so every \
                 lane starts equally often; got {}",
                cli.rounds()
            ));
        }
        if cli.profile {
            fail(format!(
                "{flag} rotates lanes, so --profile would wrap whichever lane \
                  the rotation put first; profile one arm with --cache-arm"
            ));
        }
        if cli.validate || cli.validate_flat_eq || cli.dump_q {
            fail(format!(
                "{flag} is a timing run; use --cache-arm or {} \
                  for --validate / --dump-q",
                set.gates()
            ));
        }
    }
    // The v3 R7 single-arm surface. A carrier names one kernel, one carveout and one
    // supported arm set; everything that would change what that kernel reads, or steer a
    // symbol it does not launch, is rejected rather than ignored.
    if let Some(carrier) = cli.carrier {
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "--carrier applies to --mode lsb-pair only; --mode {} has no R7 carriers",
                cli.mode.as_str()
            ));
        }
        if block_threads as usize != UNISKIP_PAIR_THREADS_128 {
            fail(format!(
                "--carrier {} is a {UNISKIP_PAIR_THREADS_128}-thread body; it needs \
                 --block-threads {UNISKIP_PAIR_THREADS_128}",
                carrier.as_str()
            ));
        }
        let Some(arm) = cli.cache_arm else {
            fail(format!(
                "--carrier {} needs --cache-arm; the carrier decides where a produced \
                 coset pair lives, the arm decides which ones are produced",
                carrier.as_str()
            ));
        };
        if !carrier.supports(arm) {
            fail(format!(
                "--carrier {} runs --cache-arm {}; {} is not on its support matrix",
                carrier.as_str(),
                carrier.supported_arms().join(" | "),
                arm.as_str()
            ));
        }
        for (other, on) in [
            ("--cache-mutate", cli.cache_mutate.is_some()),
            ("--control-launch-bounds", cli.control_launch_bounds),
            ("--no-cache-launch-bounds", cli.no_cache_launch_bounds),
        ] {
            if on {
                fail(format!(
                    "--carrier {} pins its own kernel, records and carveout; {other} would \
                     describe a configuration the run does not have",
                    carrier.as_str()
                ));
            }
        }
        // `none` is the one hint spelling that cannot compose with a carrier: it would leave
        // the symbol at the driver's own sizing, and an unhinted carrier is not the carrier
        // the design specifies (R6 measured the 128-thread default at 64 KiB).
        if cli.carveout_hint == Some(CarveoutHint::None) {
            fail(format!(
                "--carveout-hint none would leave {} at the driver's own sizing; a carrier \
                 states its configuration — pass a percent to probe another tier",
                carrier
                    .kernel()
                    .expect("a seg carrier names a seg kernel")
                    .name()
            ));
        }
    }
    if cli.cache_mutate.is_some() && !cli.cache_arm.is_some_and(|a| a.uses_cache()) {
        fail("--cache-mutate needs a cached --cache-arm to corrupt".into());
    }
    if cli.control_launch_bounds
        && !(block_threads as usize == UNISKIP_PAIR_THREADS_128
            && !cli.cache_arm.is_some_and(|a| a.uses_cache()))
    {
        fail(
            "--control-launch-bounds is the bounded 128-thread NO-CACHE baseline; it needs \
             --block-threads 128 and no cached --cache-arm"
                .into(),
        );
    }
    if cli.no_cache_launch_bounds
        && !(block_threads as usize == UNISKIP_PAIR_THREADS_128
            && cli.cache_arm.is_some_and(|a| a.uses_cache()))
    {
        fail(
            "--no-cache-launch-bounds applies to a 128-thread cached arm only; at 256 the \
             cached body already holds the control's block count"
                .into(),
        );
    }
    // The R6 rotation is preregistered whole: locality order (the shipping order), hint
    // 16 (the one empirically verified 32 KiB config), 100 rounds / 10 warmup. The emitter
    // pins the same contract on the analysis side; this keeps an off-contract log from
    // ever existing.
    if cli.lane_set() == Some(LaneSet::CarveoutProbe) {
        if cli.term_order != TermOrder::Locality {
            fail(
                "--carveout-probe is preregistered locality-only — the shipping order; \
                 the census bar question is closed"
                    .into(),
            );
        }
        if cli.iterations.is_some_and(|i| i != 100) || cli.warmup.is_some_and(|w| w != 10) {
            fail(
                "--carveout-probe is preregistered at 100 rounds / 10 warmup; other \
                 round counts are not part of its contract"
                    .into(),
            );
        }
        if matches!(cli.carveout_hint, Some(CarveoutHint::Explicit(p)) if p != 16) {
            fail(
                "--carveout-probe's preregistered hint is 16 — the one value the G0 \
                 ladder verified as the 32 KiB configuration"
                    .into(),
            );
        }
    }
    if let Some(CarveoutHint::Explicit(pct)) = cli.carveout_hint {
        if pct > 100 {
            fail(format!(
                "--carveout-hint {pct} is a percent of the maximum shared memory; 0..=100"
            ));
        }
        let probe = cli.lane_set() == Some(LaneSet::CarveoutProbe);
        // The R7 attribution surface: the anchor rotation's `hot16` lane is the SAME body
        // the probe steered, and `control@256` is a different symbol that never receives
        // a hint — so the contrast is paired per round and immune to session drift. Only
        // the two preregistered tiers, which are the seg carriers' own requests.
        let anchor = cli.lane_set() == Some(LaneSet::SegAnchor);
        if anchor && !matches!(pct, 32 | 100) {
            fail(format!(
                "--seg-anchor prices the {} attribution tiers 32 and 100 against its \
                 unhinted default; --carveout-hint {pct} is not part of that contract",
                LaneSet::SegAnchor.tag()
            ));
        }
        // The R7 LADDER-MAPPING surface: on a `--carrier` arm the percent steers that
        // carrier's OWN symbol, not the local incumbent's. It is a permanent probing
        // surface, and it has to be one — the hint -> configuration map is a property of
        // the body's shared-memory KIND, so a dynamic-shared symbol's ladder cannot be
        // read off the static-shared one (R7 G0 aborted on exactly that transplant).
        let carrier_probe = cli.carrier.is_some_and(LaneCarrier::is_seg);
        // The single-arm gate surface: the ncu configuration check profiles exactly the
        // body the hint steers, so the unbounded sibling is excluded with the rest. The
        // pct stays free HERE (this is how the ladder was mapped), but the surface is
        // profiling-only: it must carry --profile and no validation/dump knob.
        let single_cached_128 = cli.lane_set().is_none()
            && !carrier_probe
            && cli.cache_arm.is_some_and(|a| a.uses_cache())
            && block_threads as usize == UNISKIP_PAIR_THREADS_128
            && !cli.no_cache_launch_bounds;
        if !(probe || anchor || single_cached_128 || carrier_probe) {
            fail(
                "--carveout-hint steers the bounded 128-thread cached kernel; it composes \
                 with --carveout-probe, with --seg-anchor, with a single cached --cache-arm \
                 at --block-threads 128, or with a --carrier arm (whose own symbol it then \
                 steers), nothing else; the launcher default (hint 16) applies to \
                 cached@128lb lanes regardless — use --carveout-hint none for the unhinted \
                 state"
                    .into(),
            );
        }
        if carrier_probe {
            // Profiling-only, like the local surface: what this maps is a CONFIGURATION,
            // and a configuration is read off one launch with a profiler attached.
            if !cli.profile {
                fail(
                    "--carveout-hint on a --carrier arm is the ladder-mapping surface; \
                     add --profile"
                        .into(),
                );
            }
            if cli.validate || cli.validate_flat_eq || cli.dump_q {
                fail(
                    "--carveout-hint is a profiling knob; --validate / --dump-q have no \
                     hint contract"
                        .into(),
                );
            }
            // A probed tier is off the shipped configuration, so a timing taken under it is
            // not comparable with anything: one round, which is what a G0 capture takes.
            if cli.rounds() > 1 {
                fail(format!(
                    "--carveout-hint on a --carrier arm maps a configuration, not a time; \
                     --iterations 0 or 1, got {}",
                    cli.rounds()
                ));
            }
        }
        if single_cached_128 && !probe {
            if !cli.profile {
                fail(
                    "--carveout-hint on a single cached arm is the ncu gate surface; \
                     add --profile"
                        .into(),
                );
            }
            if cli.validate || cli.validate_flat_eq || cli.dump_q {
                fail(
                    "--carveout-hint is a profiling knob; --validate / --dump-q have no \
                     hint contract"
                        .into(),
                );
            }
        }
    }
    if cli.cache_arm.is_some() {
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "--cache-arm applies to --mode lsb-pair only; --mode {} has no R4 arms",
                cli.mode.as_str()
            ));
        }
        if cli.pair_arm.is_some() {
            fail(
                "--cache-arm and --pair-arm select different rungs' arms of the same \
                 kernel family; pick one"
                    .into(),
            );
        }
    }
    if !cli.mode.uses_compact_groups() && cli.bank_perm.is_some() {
        fail(format!(
            "--bank-perm applies to --mode lsb-compact only; --mode {} has no compaction \
             staging buffer to lay out",
            cli.mode.as_str()
        ));
    }
    let compact_groups = cli
        .compact_groups
        .unwrap_or(UNISKIP_COMPACT_DEFAULT_GROUPS as u32);
    if !matches!(compact_groups, 4 | 8) {
        fail(format!(
            "--compact-groups {compact_groups} is not one of 4, 8"
        ));
    }
    // C1: the factorial spans BOTH block sizes, so the harness must be built at the FINER
    // tile — `eval_blocks` is then the 16-row grid that covers the whole trace, and the
    // 256 lanes take half of it. Left at 256 every lane would launch a grid for half the
    // rows, and the row map is fixed rather than grid-stride, so the upper half would
    // simply never be evaluated.
    let block_threads = if cli.lane_set().is_some() {
        UNISKIP_PAIR_THREADS_128 as u32
    } else {
        block_threads
    };
    let config = PassConfig {
        mode: cli.mode,
        lde_shape: cli.lde_shape.unwrap_or_default(),
        cell_map: cli.cell_map.unwrap_or_default(),
        compact_groups,
        bank_perm: cli.bank_perm.unwrap_or_default(),
        pair_arm: cli.pair_arm.unwrap_or_default(),
        cache_arm: cli.cache_arm.unwrap_or_default(),
        carrier: cli.carrier.unwrap_or_default(),
        prologue_order: cli.prologue_order.unwrap_or_default(),
        cache_launch_bounds: !cli.no_cache_launch_bounds,
        control_launch_bounds: cli.control_launch_bounds,
        cache_mutate: cli.cache_mutate,
        lane_set: cli.lane_set(),
        block_threads,
        carveout_hint: cli.carveout_hint.unwrap_or_default(),
    };
    // The eval grid must tile the trace: a compact block is 8 warps x `groups` rows, so a
    // small --log-trace can leave fewer rows than one block covers. Rejected here rather
    // than through Geometry's bare assert, so it exits like every other illegal
    // combination.
    let rows_per_block = u64::from(config.rows_per_block());
    let rows = 1u64 << geometry.log_rows;
    if !rows.is_multiple_of(rows_per_block) {
        fail(format!(
            "--log-trace {} gives {rows} logical rows, which --mode {} at {rows_per_block} rows \
             per block does not tile; raise --log-trace to at least {}",
            geometry.log_trace,
            config.mode.as_str(),
            rows_per_block.trailing_zeros() + UNISKIP_LOG_TAPS
        ));
    }
    config
}

/// The in-process balanced factorial. One harness, one set of allocations, both window
/// descriptors resident; each round runs every arm once in a CYCLIC ROTATION of the arm
/// list, so no arm ever holds a fixed position and any per-round drift is shared. Warmup
/// rounds rotate identically. Every sample is emitted; nothing is summarized here.
/// The in-process balanced factorial of one PINNED rotation — R4's eleven-lane primary or
/// either R5 frontier set. Same shape as R3's: one process, shared allocations, a generated
/// cyclic rotation over warmup and timed rounds so no lane keeps a position. Differences
/// from R3: lanes spanning BOTH block sizes, and `eval`/`finalize` logged as separate raw
/// fields because the 128 grid doubles the partial count and finalize is not the same work
/// on the two sides.
///
/// The lane set decides the log keyword AND whether the ARM lines carry the ordered
/// admitted-id list; nothing else about the loop differs, so the two grammars cannot fork.
fn run_lane_factorial(harness: &mut Harness, cli: &Cli, set: LaneSet) {
    let lanes: Vec<_> = harness
        .cache_lanes()
        .iter()
        .map(|p| (p.lane, p.blocks, p.counts, p.admitted.clone()))
        .collect();
    if lanes.is_empty() {
        fail("the harness prepared no factorial lanes".into());
    }
    // The pre-flight validated the PINNED set; this is what ties that verdict to what the
    // harness actually prepared, so the structural gates cannot be passed by one list and
    // the rotation run on another.
    if !lanes
        .iter()
        .map(|(l, ..)| *l)
        .eq(set.lanes().iter().copied())
    {
        fail(format!(
            "the harness prepared a rotation {} does not name — the validated lane set and \
             the executed one are not the same list",
            set.flag()
        ));
    }
    let n = lanes.len();
    let rounds = cli.rounds();
    let warmup = cli.warmup_rounds();
    // The rotation about to be generated, checked before it runs: the CLI gate proves only
    // that the round count divides by the lane count, not that the schedule realizes it.
    let want_starts = rounds / n as u32;
    let mut starts = vec![0u32; n];
    for i in 0..rounds {
        starts[(warmup + i) as usize % n] += 1;
    }
    if !rounds.is_multiple_of(n as u32) || starts.iter().any(|&c| c != want_starts) {
        fail(format!(
            "the generated rotation starts lanes {starts:?} times over {rounds} timed \
             rounds; every lane must start exactly {want_starts}, or a lane keeps a \
             position and its median carries that position's clock state"
        ));
    }
    // Occupancy, kernel and geometry facts come from Rust so the emitter carries no
    // constants of its own — it reads the arm schema off these lines. The probe's hint
    // state rides IN the log (never inferred from a filename); the older tags keep their
    // grammar byte-stable.
    let hint = if set == LaneSet::CarveoutProbe {
        match harness.carveout() {
            Some(p) => format!(" carveout-hint={p}"),
            None => " carveout-hint=default".to_string(),
        }
    } else {
        String::new()
    };
    println!(
        "{} schedule order={} lanes={n} rounds={rounds} warmup={warmup}{hint}",
        set.tag(),
        cli.term_order.as_str()
    );
    // The dealt program's identity, right after the schedule line. A rotation that deals
    // nothing prints nothing — an anchor log carrying this line is a mislabelled log.
    if let Some(line) = harness.seg_line() {
        println!("{line}");
    }
    // Lane FACTS, not just labels: C, removals and the admitted set travel with the
    // occupancy so the emitter carries no constant and an aliased lane is visible. The
    // frontier sets carry the admitted ids IN ADMISSION ORDER as well — counts alone cannot
    // detect a reversal among equal-ref, equal-class sources, so the emitter gates the LIST.
    for (lane, blocks, counts, admitted) in &lanes {
        let ids = if !set.is_frontier() {
            String::new()
        } else if admitted.is_empty() {
            " -".into()
        } else {
            format!(
                " {}",
                admitted
                    .iter()
                    .map(u16::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            )
        };
        println!(
            "ARM {} {} {} {} {} {} {} {} {}{ids}",
            lane.label,
            lane.regs,
            lane.blocks_per_sm,
            lane.block_threads,
            blocks,
            lane.kernel().name(),
            counts.c,
            counts.removals,
            admitted.len()
        );
    }
    let round = |harness: &mut Harness, index: u32, timed: bool| {
        for offset in 0..n {
            let slot = (index as usize + offset) % n;
            harness
                .run_cache_lane(slot)
                .unwrap_or_else(|e| fail(format!("{} launch failed: {e}", lanes[slot].0.label)));
            harness
                .synchronize()
                .unwrap_or_else(|e| fail(format!("{} failed: {e}", lanes[slot].0.label)));
            if !timed {
                continue;
            }
            let t = harness
                .stage_times()
                .unwrap_or_else(|e| fail(format!("stage timing failed: {e}")));
            // eval and finalize RAW and separate: summing them would hide the block-size
            // effect on finalize, which is a different grid on the two sides.
            println!(
                "SAMPLE {} {index} {} {:.6} {:.6} {}",
                cli.term_order.as_str(),
                lanes[slot].0.label,
                t.stage_ms[1],
                t.stage_ms[2],
                lanes[slot].0.kernel().name()
            );
        }
    };
    for w in 0..warmup {
        round(harness, w, false);
    }
    for i in 0..rounds {
        round(harness, warmup + i, true);
    }
    println!(
        "{} done order={} warmup={warmup} rounds={rounds} lanes={n}",
        set.tag(),
        cli.term_order.as_str()
    );
}

fn run_factorial(harness: &mut Harness, cli: &Cli) {
    let arms = PairArm::FACTORIAL;
    // The emitter reads its occupancy labels from here, so the register/block facts live
    // in exactly one place.
    for arm in arms {
        let (regs, blocks) = arm.occupancy();
        println!("ARM {} {regs} {blocks}", arm.as_str());
    }
    let mut round = |harness: &mut Harness, index: u32, timed: bool| {
        for offset in 0..arms.len() {
            let arm = arms[(index as usize + offset) % arms.len()];
            harness
                .run_pass_arm(arm)
                .unwrap_or_else(|e| fail(format!("{} launch failed: {e}", arm.as_str())));
            harness
                .synchronize()
                .unwrap_or_else(|e| fail(format!("{} failed: {e}", arm.as_str())));
            if !timed {
                continue;
            }
            let t = harness
                .stage_times()
                .unwrap_or_else(|e| fail(format!("stage timing failed: {e}")));
            // `lde` and `fold` do not run in this mode; eval + finalize is the arm.
            println!(
                "SAMPLE {} {index} {} {:.6} {:.6}",
                cli.term_order.as_str(),
                arm.as_str(),
                t.stage_ms[1],
                t.stage_ms[2]
            );
        }
    };
    for i in 0..cli.warmup_rounds() {
        round(harness, i, false);
    }
    for i in 0..cli.rounds() {
        round(harness, cli.warmup_rounds() + i, true);
    }
    println!(
        "FACTORIAL done order={} warmup={} rounds={} arms={}",
        cli.term_order.as_str(),
        cli.warmup_rounds(),
        cli.rounds(),
        arms.len()
    );
}

fn main() {
    let cli = Cli::parse();
    let geometry = Geometry::new(cli.log_trace).unwrap_or_else(|e| fail(e));
    let config = pass_config(&cli, &geometry);
    // The knob the mode does not run reads `n/a`, so a recorded line never names a
    // shape that run never used.
    let lde_shape_label = if config.mode.uses_lde_shape() {
        config.lde_shape.as_str()
    } else {
        "n/a"
    };
    let cell_map_label = if config.mode.uses_cell_map() {
        config.cell_map.as_str()
    } else {
        "n/a"
    };
    let pair_arm_label = if config.mode.uses_pair_arm() {
        config.pair_arm.as_str()
    } else {
        "n/a"
    };
    let block_threads_label = if !config.mode.uses_pair_arm() {
        "n/a".to_string()
    } else if cli.lane_set().is_some() {
        "256 + 128 (both, per lane)".to_string()
    } else {
        config.block_threads.to_string()
    };
    let prologue_order_label = if config.mode.uses_pair_arm() && config.cache_arm.uses_cache() {
        config.prologue_order.as_str()
    } else {
        "n/a"
    };
    // The kernel a timed run actually launches, printed so a recorded number is
    // attributable to one body — an unwired selector is otherwise invisible.
    // A factorial run has no single arm or block size — printing one would name a
    // configuration the run never uses, which is how C1's half-trace grid hid behind a
    // "block_threads 256" line that was load-bearing and wrong.
    let cache_arm_label = match cli.lane_set() {
        _ if !config.mode.uses_pair_arm() => "n/a".to_string(),
        Some(set) => format!("{} ({} lanes)", set.noun(), set.lanes().len()),
        None => config.cache_arm.as_str().to_string(),
    };
    // A rotation names its carriers per lane; a single-arm run names the one it launches.
    let carrier_label = match cli.lane_set() {
        _ if !config.mode.uses_pair_arm() => "n/a",
        Some(set) if set.is_seg() => "per lane (see the ARM lines)",
        Some(_) => LaneCarrier::Local.as_str(),
        None => config.carrier.as_str(),
    };
    let (compact_groups_label, bank_perm_label) = if config.mode.uses_compact_groups() {
        (config.compact_groups.to_string(), config.bank_perm.as_str())
    } else {
        ("n/a".to_string(), "n/a")
    };

    let census = Census {
        sources: cli.sources,
        semantic_terms: cli.semantic_terms,
        groups: cli.groups,
        grouped_atoms: cli.grouped_atoms,
    };
    let mut program = generate(cli.seed, census).unwrap_or_else(|e| fail(e));
    let self_products = program.force_self_products(cli.self_products);
    if self_products != cli.self_products {
        fail(format!(
            "--self-products {}: this program has only {self_products} same-class binary products to rewrite",
            cli.self_products
        ));
    }
    program.apply_term_order(cli.term_order);
    // Order-invariant: the plan is ranked off the reference census, which is a property
    // of the record multiset.
    let plan = cache::plan(&program);
    // The window schedule is per (program, term order, census knobs), so it is built
    // AFTER `force_self_products` and `apply_term_order`. Built and validated even for
    // the control arm, which ships it as the all-`none` stream, so the machinery is
    // exercised on every run rather than only on the arms that read it.
    // The factorial runs `w`/`wt` itself, so it needs the PLANNED schedule even though
    // `--pair-arm` is absent (they are mutually exclusive). Getting this wrong is silent:
    // the window arms would run the all-`none` stream and read as identical to `wnone`.
    let window = if config.pair_arm.uses_schedule() || cli.factorial {
        window::plan(&program)
    } else {
        window::WindowSchedule::empty(&program)
    };
    if let Err(e) = window::validate(&program, &window) {
        fail(format!("window schedule is invalid: {e}"));
    }
    // TEST-ONLY unchecked path: the mutation is applied AFTER validation and deliberately
    // not re-validated, because every mutation here is exactly what the validator rejects.
    let window = match cli.window_mutate {
        None => window,
        Some(kind) => {
            if !config.pair_arm.uses_schedule() {
                fail("--window-mutate needs a window arm with a schedule (w or wt)".into());
            }
            let mutated = window::mutate(&program, &window, kind);
            println!("window mutation      {kind:?} applied UNCHECKED (test-only)");
            assert!(
                window::validate(&program, &mutated).is_err(),
                "a mutation the validator accepts is not a mutation"
            );
            mutated
        }
    };

    println!("gpu_gkr_uniskip_bench config");
    println!("  log_trace           {}", cli.log_trace);
    println!("  warmup              {}", cli.warmup_rounds());
    println!("  iterations          {}", cli.rounds());
    println!("  seed                {}", cli.seed);
    println!("  profile             {}", cli.profile);
    println!("  validate            {}", cli.validate);
    println!("  validate_flat_eq    {}", cli.validate_flat_eq);
    println!("  mode                {}", config.mode.as_str());
    println!("  lde_shape           {lde_shape_label}");
    println!("  cell_map            {cell_map_label}");
    println!("  compact_groups      {compact_groups_label}");
    println!("  bank_perm           {bank_perm_label}");
    println!("  pair_arm            {pair_arm_label}");
    println!("  cache_arm           {cache_arm_label}");
    println!("  carrier             {carrier_label}");
    println!("  block_threads       {block_threads_label}");
    println!("  prologue_order      {prologue_order_label}");
    println!("  term_order          {}", cli.term_order.as_str());
    println!("  self_products       {self_products}");
    if self_products > 0 {
        println!(
            "  census / plan       STALE (measured before --self-products rewrote the program)"
        );
    }
    println!("geometry");
    println!("  log_rows            {}", geometry.log_rows);
    println!("  logical rows        {}", geometry.logical_rows);
    println!(
        "  blocks              {} ({} rows per block)",
        geometry.eval_blocks(config.rows_per_block()),
        config.rows_per_block()
    );
    println!(
        "  eq sizes            high {} / {} low {}",
        geometry.eq_sizes.0, geometry.eq_sizes.1, geometry.eq_sizes.2
    );
    println!(
        "  partials            {} e4",
        UNISKIP_CELLS as u64 * u64::from(config.partial_slots(&geometry))
    );
    println!("census");
    println!("{}", program.census);
    println!(
        "  window columns      {:?}",
        program
            .windows
            .iter()
            .map(|w| w.columns)
            .collect::<Vec<_>>()
    );
    // Printed in every mode: the plan is a property of the program, and `C` / `Ru` /
    // the op split are what decide whether an all-cell fill producer is worth building.
    if config.mode.uses_pair_arm() && config.pair_arm.uses_window() {
        println!("window schedule");
        println!("  window sources      {:?}", window.slot_source);
        println!("  window refs         {:?}", window.slot_refs);
        println!(
            "  window reuses       {} ({} -> {} component passes per walk)",
            window.reuses, window.passes_without, window.passes_with
        );
    }
    if let Some(set) = cli.lane_set() {
        // PRE-FLIGHT, through the one shared validator: every lane plannable and inside the
        // frame before the harness exists (so an unplannable one exits cleanly here instead
        // of panicking inside device setup), no cached lane that removes nothing, and no two
        // lanes of one kernel admitting the same set.
        if let Err(e) = coset_cache::validate_lane_set(&program, set.lanes()) {
            fail(format!("{}: {e}", set.flag()));
        }
    }
    // The same pre-flight for the deal: a program that cannot fill four nonempty lists of
    // whole atoms exits here, not inside device setup.
    if config.carrier.is_seg() || cli.lane_set().is_some_and(LaneSet::is_seg) {
        match seg::deal(&program) {
            Ok(deal) => {
                if let Err(e) = seg::validate(&deal, &program) {
                    fail(format!("the seg deal is invalid: {e}"));
                }
            }
            Err(e) => fail(format!("the seg dealer rejected this program: {e}")),
        }
    }
    if config.mode.uses_pair_arm() {
        // Recomputed from the live resolver stream, so unlike the shared-memory cache
        // plan below it is never stale under --self-products.
        let canonical = coset_cache::canonical_admission(&program);
        let planned = coset_cache::plan_all(&program);
        println!("coset cache (v3 R4)");
        println!(
            "  admission           {} of {} live sources reused (refs >= 2); {} of them e4",
            canonical.len(),
            coset_cache::ranked_live(&program).len(),
            coset_cache::e4_rich(&canonical).len()
        );
        // A census can push an arm past the frame. Say which, rather than failing a run
        // that never selects it.
        let unavailable: Vec<&str> = planned
            .iter()
            .filter(|(_, s)| s.is_err())
            .map(|(a, _)| a.as_str())
            .collect();
        if !unavailable.is_empty() {
            println!(
                "  unavailable         {} (past the {}-unit frame at this census)",
                unavailable.join(", "),
                gpu_gkr_uniskip_bench::abi::UNISKIP_COSET_FRAME_UNITS
            );
        }
        // The SELECTED arm must be plannable — that failure is fatal, and it is a
        // different failure from "not implemented yet".
        let state = planned
            .iter()
            .find(|(a, _)| *a == config.cache_arm)
            .map(|(_, s)| s)
            .expect("every arm is planned");
        let state = match state {
            Ok(state) => state,
            Err(e) => fail(format!("--cache-arm {}: {e}", config.cache_arm.as_str())),
        };
        let c = state.counts;
        println!(
            "  arm {:<16}admitted {} ({} bf / {} e4), C = {} units / {} B per thread",
            state.id,
            state.admitted.len(),
            c.b,
            c.e,
            c.c,
            c.bytes
        );
        println!(
            "  per walk            {} chains ({} without), {} removals, {} stores, {} loads",
            c.chains, c.passes_without, c.removals, c.store_instrs, c.load_instrs
        );
        println!(
            "  local L1 supported  {} (cudaDevAttrLocalL1CacheSupported)",
            local_l1_supported()
        );
    }
    println!(
        "cache plan{}{}",
        if config.mode.uses_cache() {
            ""
        } else {
            " (not applied in this mode)"
        },
        if self_products > 0 { " (STALE)" } else { "" }
    );
    println!("{plan}");

    let validate = cli.validate || cli.validate_flat_eq;
    let mut harness = Harness::new(
        &program,
        &geometry,
        cli.seed,
        cli.validate_flat_eq,
        config,
        &plan,
        window.descriptor(),
    )
    .unwrap_or_else(|e| fail(format!("device setup failed: {e}")));

    let bytes = harness.pass_bytes();
    let columns: u32 = program.windows.iter().map(|w| w.columns).sum();
    let sources = program.sources.len();
    let e4_sources = program
        .sources
        .iter()
        .filter(|r| r.source_class == UNISKIP_SRC_E4_GLOBAL)
        .count();
    let device = device_name();
    // Read straight off the harness, so a recorded number is attributable to the kernel
    // that actually ran; it sits here because the harness does not exist any earlier.
    println!("work");
    // A factorial has no single kernel — naming one lane's body as THE kernel is the same
    // class of mistake as printing one block size for a two-size rotation.
    if cli.lane_set().is_some() {
        println!("  eval kernel         per lane (see the ARM lines)");
    } else {
        println!("  eval kernel         {}", harness.eval_kernel());
    }
    println!("  device              {device}");
    println!(
        "  sources             {sources} ({} bf / {e4_sources} e4)",
        sources - e4_sources
    );
    println!("  columns             {columns}");
    println!(
        "  tap backing         {:.2} GiB ({})",
        gib(harness.layout.backing_bytes()),
        if config.mode.materializes_coset() {
            "the coset backing matches"
        } else {
            "no coset backing"
        }
    );
    println!(
        "  resident backings   {:.2} GiB",
        gib(harness.backing_bytes_resident())
    );
    println!(
        "  compulsory traffic  {} B ({:.2} GiB) per pass",
        bytes.total,
        gib(bytes.total)
    );
    // The rotation path prints this after its schedule line instead, where the lanes it
    // describes are already named.
    if cli.lane_set().is_none() {
        if let Some(line) = harness.seg_line() {
            println!("{line}");
        }
    }

    if (cli.window_count || cli.window_poison || cli.window_mutate.is_some())
        && !gpu_gkr_uniskip_bench::kernels::window_diag_build()
    {
        fail(
            "--window-count / --window-poison / --window-mutate need a build with \
             GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1"
                .into(),
        );
    }
    if cli.window_poison {
        gpu_gkr_uniskip_bench::kernels::upload_poison_slots(true)
            .unwrap_or_else(|e| fail(format!("poison upload failed: {e}")));
    }

    if cli.factorial {
        // Recorded in the log so the emitted table can never be read without knowing which
        // schedule produced it.
        println!(
            "FACTORIAL schedule order={} slots={:?} refs={:?} reuses={} passes={}->{}",
            cli.term_order.as_str(),
            window.slot_source,
            window.slot_refs,
            window.reuses,
            window.passes_without,
            window.passes_with
        );
        assert!(
            window.reuses > 0,
            "the factorial needs a planned schedule; an empty one makes w indistinguishable from wnone"
        );
        run_factorial(&mut harness, &cli);
        return;
    }

    if let Some(set) = cli.lane_set() {
        run_lane_factorial(&mut harness, &cli, set);
        check_slot_masks(&harness);
        return;
    }

    for _ in 0..cli.warmup_rounds() {
        harness
            .run_pass()
            .unwrap_or_else(|e| fail(format!("pass launch failed: {e}")));
    }
    harness
        .synchronize()
        .unwrap_or_else(|e| fail(format!("warmup failed: {e}")));

    let mut samples: Vec<StageTimes> = Vec::with_capacity(cli.rounds() as usize);
    for iteration in 0..cli.rounds() {
        let range = (cli.profile && iteration == 0).then(|| NvtxRange::new(c"gkr_uniskip_pass0"));
        harness
            .run_pass()
            .unwrap_or_else(|e| fail(format!("pass launch failed: {e}")));
        harness
            .synchronize()
            .unwrap_or_else(|e| fail(format!("pass failed: {e}")));
        drop(range);
        samples.push(
            harness
                .stage_times()
                .unwrap_or_else(|e| fail(format!("stage timing failed: {e}"))),
        );
    }

    if cli.window_count {
        let calls = gpu_gkr_uniskip_bench::kernels::take_chain_calls()
            .unwrap_or_else(|e| fail(format!("chain-counter readback failed: {e}")));
        // One walk per warp; the counter ticks once per warp per chain execution. Every
        // pass runs every warp, so the total must divide exactly — a truncating division
        // would hide a deviation of up to `warps * passes - 1`, far larger than the
        // 47-execution signal this gate exists to see.
        // Warps per block follows the BLOCK SIZE, not the 256-thread constant: at
        // --block-threads 128 a block is 4 warps, and using 8 would silently halve the
        // reported per-walk figure.
        let warps = u64::from(harness.eval_blocks()) * u64::from(config.block_threads / 32);
        let passes = u64::from(cli.warmup_rounds()) + samples.len() as u64;
        assert!(passes > 0, "--window-count needs at least one pass");
        if config.carrier.is_seg() {
            // A seg block's four warps SPLIT one program between them, so the per-warp
            // walk is not the unit any more: the whole block executes the arm's chain
            // count once per cohort. `counts.chains` already includes the prologue. The
            // transplant covers ONE cohort per block, so its unit is the block itself.
            let blocks = u64::from(harness.eval_blocks());
            let cohorts = if config.carrier.is_segb() {
                1
            } else {
                u64::from(UNISKIP_SEG_COHORTS)
            };
            assert_eq!(
                calls % (blocks * cohorts * passes),
                0,
                "chain executions {calls} are not a whole multiple of {blocks} blocks x \
                 {cohorts} cohorts x {passes} passes"
            );
            let per_cohort = calls / (blocks * cohorts * passes);
            let chains = harness
                .cache_arm_state(config.cache_arm)
                .expect("the selected arm is planned")
                .counts
                .chains;
            assert_eq!(
                per_cohort,
                u64::from(chains),
                "a {} cohort executed {per_cohort} chains against the arm's {chains}",
                config.carrier.as_str()
            );
            if config.carrier.is_segb() {
                println!(
                    "chain executions     {calls} total / {blocks} blocks = {per_cohort} per block"
                );
            } else {
                println!(
                    "chain executions     {calls} total / {blocks} blocks / {cohorts} cohorts = {per_cohort} per cohort"
                );
            }
        } else {
            assert_eq!(
                calls % (warps * passes),
                0,
                "chain executions {calls} are not a whole multiple of {warps} warps x {passes} passes"
            );
            println!(
                "chain executions     {calls} total / {warps} warps / {passes} passes = {} per warp-program walk",
                calls / (warps * passes)
            );
        }
    }

    let mut total_median = 0.0;
    if samples.is_empty() {
        println!("timing: skipped (--iterations 0)");
    } else {
        println!("timing over {} iterations (ms)", samples.len());
        // "min GB/s": compulsory traffic / median, a LOWER bound on achieved bandwidth.
        println!("  stage        median      mean       min       max  min GB/s");
        let stage_series =
            |pick: &dyn Fn(&StageTimes) -> f32| -> Vec<f32> { samples.iter().map(pick).collect() };
        for (stage, name) in STAGES.iter().enumerate() {
            let series = stage_series(&|t: &StageTimes| t.stage_ms[stage]);
            let (median, mean, min, max) = summarize(&series);
            println!(
                "  {name:<10}{median:>9.3}{mean:>10.3}{min:>10.3}{max:>10.3}{:>10.1}",
                gb_per_s(bytes.stage[stage], median)
            );
        }
        let series = stage_series(&|t: &StageTimes| t.total_ms);
        let (median, mean, min, max) = summarize(&series);
        total_median = median;
        println!(
            "  {:<10}{median:>9.3}{mean:>10.3}{min:>10.3}{max:>10.3}{:>10.1}",
            "total",
            gb_per_s(bytes.total, median)
        );
    }

    if cli.dump_q {
        if samples.is_empty() {
            harness
                .run_pass()
                .unwrap_or_else(|e| fail(format!("pass launch failed: {e}")));
            harness
                .synchronize()
                .unwrap_or_else(|e| fail(format!("pass failed: {e}")));
        }
        let q = harness
            .download_q()
            .unwrap_or_else(|e| fail(format!("q download failed: {e}")));
        for (cell, limbs) in q.chunks(4).enumerate() {
            println!(
                "q[{cell:02}] {:08x} {:08x} {:08x} {:08x}",
                limbs[0], limbs[1], limbs[2], limbs[3]
            );
        }
    }

    // Validation compares device buffers, so it needs a pass to have run even when
    // the iteration count is zero.
    if validate {
        if samples.is_empty() {
            harness
                .run_pass()
                .unwrap_or_else(|e| fail(format!("pass launch failed: {e}")));
            harness
                .synchronize()
                .unwrap_or_else(|e| fail(format!("pass failed: {e}")));
        }
        let mut failed = false;
        if config.mode.materializes_coset() {
            match harness
                .validate_lde()
                .unwrap_or_else(|e| fail(format!("validation download failed: {e}")))
            {
                Ok(()) => println!("LDE validate: OK"),
                Err(mismatch) => {
                    eprintln!("LDE validate: FAILED — {mismatch}");
                    failed = true;
                }
            }
        } else {
            // No coset buffer exists; the q oracle addresses all 32 cells and covers
            // the recomputed ones.
            println!("LDE validate: n/a (no coset backing)");
        }
        match harness
            .validate_q(&program)
            .unwrap_or_else(|e| fail(format!("validation download failed: {e}")))
        {
            Ok(()) => println!("q validate: OK ({}/{})", UNISKIP_CELLS, UNISKIP_CELLS),
            Err(mismatch) => {
                eprintln!("q validate: FAILED — {mismatch}");
                failed = true;
            }
        }
        if config.mode.runs_fold() {
            match harness
                .validate_fold()
                .unwrap_or_else(|e| fail(format!("validation download failed: {e}")))
            {
                Ok(()) => println!("fold validate: OK"),
                Err(mismatch) => {
                    eprintln!("fold validate: FAILED — {mismatch}");
                    failed = true;
                }
            }
        } else {
            println!("fold validate: n/a (no fold stage in this mode)");
        }
        if failed {
            std::process::exit(1);
        }
    }
    check_slot_masks(&harness);

    println!(
        "summary: log_trace {} | mode {} | lde_shape {lde_shape_label} | cell_map {cell_map_label} | \
         compact_groups {compact_groups_label} | bank_perm {bank_perm_label} | pair_arm {pair_arm_label} | \
         cache_arm {cache_arm_label} | block_threads {block_threads_label} | \
         kernel {} | term_order {} | \
         C {} Ru {} | {sources} sources / \
         {columns} columns / {} B ({:.2} GiB) per pass | total median {total_median:.3} ms over \
         {} iterations | {device}",
        cli.log_trace,
        config.mode.as_str(),
        if cli.lane_set().is_some() { "per-lane" } else { harness.eval_kernel() },
        cli.term_order.as_str(),
        plan.cached_width,
        plan.uncached_refs,
        bytes.total,
        gib(bytes.total),
        samples.len()
    );
}
