use clap::{CommandFactory, Parser};

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

    /// Emit NVTX ranges / per-phase profiling output.
    #[arg(long)]
    profile: bool,

    /// Check the GPU result against the host reference.
    #[arg(long)]
    validate: bool,

    /// Validate with all eq tables forced to ONE on both sides.
    #[arg(long)]
    validate_flat_eq: bool,
}

fn main() {
    let cli = Cli::parse();

    let Some(ungrouped_terms) = cli.semantic_terms.checked_sub(cli.grouped_atoms) else {
        Cli::command()
            .error(
                clap::error::ErrorKind::InvalidValue,
                format!(
                    "--grouped-atoms ({}) exceeds --semantic-terms ({})",
                    cli.grouped_atoms, cli.semantic_terms
                ),
            )
            .exit();
    };
    let program_records = ungrouped_terms + cli.groups + cli.grouped_atoms;

    println!("gpu_gkr_uniskip_bench config");
    println!("  log_trace           {}", cli.log_trace);
    println!("  warmup              {}", cli.warmup);
    println!("  iterations          {}", cli.iterations);
    println!("  seed                {}", cli.seed);
    println!("  profile             {}", cli.profile);
    println!("  validate            {}", cli.validate);
    println!("  validate_flat_eq    {}", cli.validate_flat_eq);
    println!("census");
    println!("  sources             {}", cli.sources);
    println!("  semantic terms      {}", cli.semantic_terms);
    println!("  groups              {}", cli.groups);
    println!("  grouped atoms       {}", cli.grouped_atoms);
    println!("  ungrouped terms     {ungrouped_terms}");
    println!("  program records     {program_records}");
}
