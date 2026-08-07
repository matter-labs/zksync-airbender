use std::ffi::CStr;

use clap::{CommandFactory, Parser};
use era_cudart::device::{get_device, get_device_properties};
use gpu_gkr_uniskip_bench::abi::{UNISKIP_CELLS, UNISKIP_SRC_E4_GLOBAL};
use gpu_gkr_uniskip_bench::geometry::Geometry;
use gpu_gkr_uniskip_bench::harness::{Harness, StageTimes, STAGES};
use gpu_gkr_uniskip_bench::kernels::NvtxRange;
use gpu_gkr_uniskip_bench::synth::{generate, Census};

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

fn main() {
    let cli = Cli::parse();

    let geometry = Geometry::new(cli.log_trace).unwrap_or_else(|e| fail(e));
    let census = Census {
        sources: cli.sources,
        semantic_terms: cli.semantic_terms,
        groups: cli.groups,
        grouped_atoms: cli.grouped_atoms,
    };
    let program = generate(cli.seed, census).unwrap_or_else(|e| fail(e));

    println!("gpu_gkr_uniskip_bench config");
    println!("  log_trace           {}", cli.log_trace);
    println!("  warmup              {}", cli.warmup);
    println!("  iterations          {}", cli.iterations);
    println!("  seed                {}", cli.seed);
    println!("  profile             {}", cli.profile);
    println!("  validate            {}", cli.validate);
    println!("  validate_flat_eq    {}", cli.validate_flat_eq);
    println!("geometry");
    println!("  log_rows            {}", geometry.log_rows);
    println!("  logical rows        {}", geometry.logical_rows);
    println!("  blocks              {}", geometry.blocks);
    println!(
        "  eq sizes            high {} / {} low {}",
        geometry.eq_sizes.0, geometry.eq_sizes.1, geometry.eq_sizes.2
    );
    println!("  partials            {} e4", geometry.partials);
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

    let validate = cli.validate || cli.validate_flat_eq;
    let mut harness = Harness::new(&program, &geometry, cli.seed, cli.validate_flat_eq)
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
        "  tap backing         {:.2} GiB (the coset backing matches)",
        gib(harness.layout.backing_bytes())
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
        println!("  stage        median      mean       min       max      GB/s");
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
        if failed {
            std::process::exit(1);
        }
    }

    println!(
        "summary: log_trace {} | {sources} sources / {columns} columns / {} B ({:.2} GiB) per pass \
         | total median {total_median:.3} ms over {} iterations | {device}",
        cli.log_trace,
        bytes.total,
        gib(bytes.total),
        samples.len()
    );
}
