use std::ffi::CStr;

use clap::{CommandFactory, Parser};
use era_cudart::device::{get_device, get_device_properties};
use gpu_gkr_uniskip_bench::abi::{
    UNISKIP_CELLS, UNISKIP_COMPACT_DEFAULT_GROUPS, UNISKIP_LOG_TAPS, UNISKIP_PAIR_THREADS_128,
    UNISKIP_SRC_E4_GLOBAL, UNISKIP_THREADS_PER_BLOCK,
};
use gpu_gkr_uniskip_bench::cache;
use gpu_gkr_uniskip_bench::compact::BankPerm;
use gpu_gkr_uniskip_bench::coset_cache::{self, CacheArm, CacheMutation, PrologueOrder};
use gpu_gkr_uniskip_bench::geometry::Geometry;
use gpu_gkr_uniskip_bench::harness::PairArm;
use gpu_gkr_uniskip_bench::harness::{
    CellMap, EvalMode, Harness, LdeShape, PassConfig, StageTimes, STAGES,
};
use gpu_gkr_uniskip_bench::kernels::NvtxRange;
use gpu_gkr_uniskip_bench::synth::{generate, Census, TermOrder};
use gpu_gkr_uniskip_bench::window::{self, WindowMutation};

/// Standalone CUDA benchmark for one uniskip sumcheck pass (k = 4).
#[derive(Parser)]
#[command(name = "gpu_gkr_uniskip_bench", version, about, long_about = None)]
struct Cli {
    /// log2 of the trace length (k = 4, so log_rows = log_trace - 4).
    #[arg(long, default_value_t = 20)]
    log_trace: u32,

    /// Untimed iterations run before measurement.
    #[arg(long, default_value_t = 3)]
    warmup: u32,

    /// Timed iterations.
    #[arg(long, default_value_t = 20)]
    iterations: u32,

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

    /// v3 R4 coset-cache arm of `--mode lsb-pair`: `control` (no cache — today's
    /// behavior), `cache0` (cached body, empty admitted set — the fixed-machinery
    /// diagnostic), a prefix of the canonical admission list (`hot4`, `hot16`,
    /// `allrepeat`), the E4-only set `e4rich`, or the `all59` capacity-stress
    /// diagnostic (every live source, refs = 1 included). Mutually
    /// exclusive with `--pair-arm` and with `--factorial`. The host plan for every arm is
    /// built and validated on any `lsb-pair` run, whichever arm is selected.
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
    /// rotation. Use `--iterations` a multiple of 11 (the record uses 99 per term order).
    /// The factorial owns both block sizes internally, so it takes neither --block-threads
    /// nor a single --cache-arm.
    #[arg(long)]
    cache_factorial: bool,

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
    if cli.cache_factorial {
        // Everything the rotation must own itself, or that would contaminate it.
        if !cli.mode.uses_pair_arm() {
            fail(format!(
                "--cache-factorial applies to --mode lsb-pair only; --mode {} has no R4 arms",
                cli.mode.as_str()
            ));
        }
        for (flag, set) in [
            ("--pair-arm", cli.pair_arm.is_some()),
            ("--cache-arm", cli.cache_arm.is_some()),
            ("--block-threads", cli.block_threads.is_some()),
            ("--prologue-order", cli.prologue_order.is_some()),
            ("--cache-mutate", cli.cache_mutate.is_some()),
            ("--factorial", cli.factorial),
            ("--control-launch-bounds", cli.control_launch_bounds),
            ("--no-cache-launch-bounds", cli.no_cache_launch_bounds),
        ] {
            if set {
                fail(format!(
                    "--cache-factorial owns the arm set and both block sizes; {flag} would \
                     change what the rotation runs"
                ));
            }
        }
        if cli.window_count || cli.window_poison || cli.window_mutate.is_some() {
            fail(
                "--cache-factorial is a timing run; the diagnostic probes would contaminate \
                  it — use tools/r4_gates.sh"
                    .into(),
            );
        }
        // The removals the emitter divides by are the DEFAULT census's. Any census knob
        // silently invalidates them, and a slope is worse than useless when its denominator
        // is wrong.
        let default = Census::default();
        for (flag, differs) in [
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
                    "--cache-factorial prices removals against the DEFAULT census; {flag} \
                     changes the program and invalidates every slope"
                ));
            }
        }
        // Balance is a GATE, not a note: an unbalanced rotation gives some lanes more
        // first-position rounds than others, and first position is the one that pays for
        // whatever the previous round left in cache.
        let lane_count = gpu_gkr_uniskip_bench::coset_cache::CACHE_FACTORIAL.len() as u32;
        if !cli.iterations.is_multiple_of(lane_count) {
            fail(format!(
                "--cache-factorial needs --iterations a multiple of {lane_count} so every \
                 lane starts equally often; got {}",
                cli.iterations
            ));
        }
        if cli.profile {
            fail(
                "--cache-factorial rotates lanes, so --profile would wrap whichever lane \
                  the rotation put first; profile one arm with --cache-arm"
                    .into(),
            );
        }
        if cli.validate || cli.validate_flat_eq || cli.dump_q {
            fail(
                "--cache-factorial is a timing run; use --cache-arm or tools/r4_gates.sh \
                  for --validate / --dump-q"
                    .into(),
            );
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
    let block_threads = if cli.cache_factorial {
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
        prologue_order: cli.prologue_order.unwrap_or_default(),
        cache_launch_bounds: !cli.no_cache_launch_bounds,
        control_launch_bounds: cli.control_launch_bounds,
        cache_mutate: cli.cache_mutate,
        cache_factorial: cli.cache_factorial,
        block_threads,
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
/// The v3 R4 primary factorial. Same shape as R3's: one process, shared allocations, a
/// generated cyclic rotation over warmup and timed rounds so no lane keeps a position.
/// Differences: eleven lanes spanning BOTH block sizes, and `eval`/`finalize` are logged as
/// separate raw fields because the 128 grid doubles the partial count and finalize is not
/// the same work on the two sides.
fn run_cache_factorial(harness: &mut Harness, cli: &Cli) {
    let lanes: Vec<_> = harness
        .cache_lanes()
        .iter()
        .map(|p| (p.lane, p.blocks, p.counts, p.admitted.clone()))
        .collect();
    if lanes.is_empty() {
        fail("the harness prepared no factorial lanes".into());
    }
    let n = lanes.len();
    // Occupancy, kernel and geometry facts come from Rust so the emitter carries no
    // constants of its own — it reads the arm schema off these lines.
    println!(
        "CACHE-FACTORIAL schedule order={} lanes={n} rounds={} warmup={}",
        cli.term_order.as_str(),
        cli.iterations,
        cli.warmup
    );
    // Lane FACTS, not just labels: C, removals and the admitted-set size travel with the
    // occupancy so the emitter carries no constant and an aliased lane is visible.
    let mut seen: Vec<(Vec<u16>, &str, u32)> = Vec::new();
    for (lane, blocks, counts, admitted) in &lanes {
        if lane.arm.uses_cache() && lane.arm != CacheArm::Cache0 {
            if counts.removals == 0 {
                fail(format!(
                    "lane {} is a cached arm that removes nothing — it is cache0 under \
                     another name, and the contrast would read as a zero effect",
                    lane.label
                ));
            }
            if let Some((_, other, _)) = seen
                .iter()
                .find(|(set, _, size)| set == admitted && *size == lane.block_threads)
            {
                fail(format!(
                    "lanes {} and {other} admit the SAME set — one experiment under two \
                     labels, which reads as +0.000 rather than as a bug",
                    lane.label
                ));
            }
            seen.push((admitted.clone(), lane.label, lane.block_threads));
        }
        println!(
            "ARM {} {} {} {} {} {} {} {} {}",
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
    for w in 0..cli.warmup {
        round(harness, w, false);
    }
    for i in 0..cli.iterations {
        round(harness, cli.warmup + i, true);
    }
    println!(
        "CACHE-FACTORIAL done order={} warmup={} rounds={} lanes={n}",
        cli.term_order.as_str(),
        cli.warmup,
        cli.iterations
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
    for i in 0..cli.warmup {
        round(harness, i, false);
    }
    for i in 0..cli.iterations {
        round(harness, cli.warmup + i, true);
    }
    println!(
        "FACTORIAL done order={} warmup={} rounds={} arms={}",
        cli.term_order.as_str(),
        cli.warmup,
        cli.iterations,
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
    } else if cli.cache_factorial {
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
    let cache_arm_label = if !config.mode.uses_pair_arm() {
        "n/a"
    } else if cli.cache_factorial {
        "factorial (11 lanes)"
    } else {
        config.cache_arm.as_str()
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
    println!("  warmup              {}", cli.warmup);
    println!("  iterations          {}", cli.iterations);
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
        geometry.eval_partials(config.rows_per_block())
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
            state.arm.as_str(),
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
    println!("  eval kernel         {}", harness.eval_kernel());
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

    if cli.cache_factorial {
        run_cache_factorial(&mut harness, &cli);
        return;
    }

    for _ in 0..cli.warmup {
        harness
            .run_pass()
            .unwrap_or_else(|e| fail(format!("pass launch failed: {e}")));
    }
    harness
        .synchronize()
        .unwrap_or_else(|e| fail(format!("warmup failed: {e}")));

    let mut samples: Vec<StageTimes> = Vec::with_capacity(cli.iterations as usize);
    for iteration in 0..cli.iterations {
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
        let passes = u64::from(cli.warmup) + samples.len() as u64;
        assert!(passes > 0, "--window-count needs at least one pass");
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
        harness.eval_kernel(),
        cli.term_order.as_str(),
        plan.cached_width,
        plan.uncached_refs,
        bytes.total,
        gib(bytes.total),
        samples.len()
    );
}
