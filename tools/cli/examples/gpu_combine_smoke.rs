//! GPU carried-chain combiner smoke test for CI.
//!
//! Combines the given recursion-unified proof artifacts several times through a
//! single [`CarriedChainCombiner`], which the one-shot `cli combine` command cannot
//! exercise: the first round builds and caches the prover's host state, and every
//! round re-creates (and drops) the CUDA contexts and the fixed-size device memory
//! pool, so a regression in host-state reuse or context recreation fails here even
//! when a single combine still passes. Each round's artifact is written to the
//! output directory as `combined_round_<n>.json` for external verification.

use clap::Parser;
use cli_lib::prover_utils::{
    deserialize_from_file, serialize_to_file, CarriedChainCombiner, GpuConfig, ProofArtifact,
    SecurityLevel,
};
use std::path::Path;

#[derive(Parser)]
struct Args {
    /// Paths to the recursion-unified proof artifacts to combine (at least two).
    #[arg(short, long, num_args = 2.., required = true)]
    proofs: Vec<String>,
    // Combination policy is part of the trust boundary and must be supplied
    // explicitly rather than inherited from prover-controlled artifact metadata.
    #[arg(long, value_enum)]
    security_level: SecurityLevel,
    #[arg(long, default_value = "output")]
    output_dir: String,
    /// Number of sequential combines through the same combiner.
    #[arg(long, default_value_t = 2)]
    rounds: usize,
    #[arg(long, default_value_t = 8)]
    gpu_replay_threads: usize,
}

fn main() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .init();

    let args = Args::parse();
    let artifacts: Vec<ProofArtifact> = args
        .proofs
        .iter()
        .map(|path| deserialize_from_file(path))
        .collect();

    let gpu = GpuConfig {
        replay_worker_threads_count: args.gpu_replay_threads,
        // The combiner ignores `memory_preset` and pins its own device pool.
        ..Default::default()
    };
    let mut combiner = CarriedChainCombiner::new_gpu(args.security_level, gpu);
    for round in 1..=args.rounds {
        let combined = combiner
            .combine(&artifacts)
            .unwrap_or_else(|e| panic!("carried-chain combine round {round} failed: {e}"));
        let output_path = Path::new(&args.output_dir).join(format!("combined_round_{round}.json"));
        if let Some(parent) = output_path.parent() {
            std::fs::create_dir_all(parent).expect("Failed to create output directory");
        }
        serialize_to_file(&combined, &output_path);
        println!(
            "Round {round}/{}: combined proof artifact written to {}",
            args.rounds,
            output_path.display()
        );
    }
}
