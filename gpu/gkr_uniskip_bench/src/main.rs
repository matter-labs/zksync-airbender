use std::ffi::CStr;

use clap::{CommandFactory, Parser};
use era_cudart::device::{get_device, get_device_properties};
use gpu_gkr_uniskip_bench::abi::{UNISKIP_CELLS, UNISKIP_SRC_E4_GLOBAL};
use gpu_gkr_uniskip_bench::cache;
use gpu_gkr_uniskip_bench::geometry::Geometry;
use gpu_gkr_uniskip_bench::harness::{
    CellMap, EvalMode, Harness, LdeShape, PassConfig, StageTimes, STAGES,
};
use gpu_gkr_uniskip_bench::kernels::NvtxRange;
use gpu_gkr_uniskip_bench::synth::{generate, Census, TermOrder};

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
    /// shuffle-NTT per reference, no window and no fold stage.
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

    /// Validation knob: rewrite this many same-class binary products into
    /// self-products (`x * x`), which is the only way to exercise the LSB mode's
    /// duplicate rule — the default census emits none. It changes `q` and the
    /// per-source reference counts, so a timing taken under it is not comparable
    /// with the recorded arms.
    #[arg(long, default_value_t = 0)]
    self_products: u32,

    /// Wrap the first timed iteration in the `gkr_uniskip_pass0` NVTX range.
    /// Needs `--iterations >= 1`.
    #[arg(long)]
    profile: bool,

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
fn pass_config(cli: &Cli) -> PassConfig {
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
                "--cell-map applies to fused modes only; --mode {} fixes the lane map at \
                 lane = tap, two groups per warp",
                cli.mode.as_str()
            ),
        });
    }
    PassConfig {
        mode: cli.mode,
        lde_shape: cli.lde_shape.unwrap_or_default(),
        cell_map: cli.cell_map.unwrap_or_default(),
    }
}

fn main() {
    let cli = Cli::parse();
    let config = pass_config(&cli);
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

    let geometry = Geometry::new(cli.log_trace).unwrap_or_else(|e| fail(e));
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
            "--self-products {}: this census emits only {self_products} same-class binary products",
            cli.self_products
        ));
    }
    program.apply_term_order(cli.term_order);
    // Order-invariant: the plan is ranked off the reference census, which is a property
    // of the record multiset.
    let plan = cache::plan(&program);

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
    println!("  term_order          {}", cli.term_order.as_str());
    println!("  self_products       {self_products}");
    println!("geometry");
    println!("  log_rows            {}", geometry.log_rows);
    println!("  logical rows        {}", geometry.logical_rows);
    println!(
        "  blocks              {} ({} rows per block)",
        geometry.eval_blocks(config.mode.rows_per_block()),
        config.mode.rows_per_block()
    );
    println!(
        "  eq sizes            high {} / {} low {}",
        geometry.eq_sizes.0, geometry.eq_sizes.1, geometry.eq_sizes.2
    );
    println!(
        "  partials            {} e4",
        geometry.eval_partials(config.mode.rows_per_block())
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
    println!(
        "cache plan{}",
        if config.mode.uses_cache() {
            ""
        } else {
            " (not applied in this mode)"
        }
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
    println!("work");
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
         term_order {} | C {} Ru {} | {sources} sources / \
         {columns} columns / {} B ({:.2} GiB) per pass | total median {total_median:.3} ms over \
         {} iterations | {device}",
        cli.log_trace,
        config.mode.as_str(),
        cli.term_order.as_str(),
        plan.cached_width,
        plan.uncached_refs,
        bytes.total,
        gib(bytes.total),
        samples.len()
    );
}
