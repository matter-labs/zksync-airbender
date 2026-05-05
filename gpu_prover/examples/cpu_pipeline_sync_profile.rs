#![cfg_attr(not(feature = "sync_profiling"), allow(dead_code))]

#[cfg(not(feature = "sync_profiling"))]
compile_error!(
    "run with `cargo run -p gpu_prover --release --features sync_profiling --example cpu_pipeline_sync_profile`"
);

use gpu_prover::execution::cpu_pipeline_model::{
    CpuPipelineMode, CpuPipelineModel, CpuPipelineModelConfig, CpuPipelineModelInput,
};
use gpu_prover::execution::prover::ExecutionKind;
use gpu_prover::machine_type::MachineType;
use setups::read_binary;
use std::cmp::Reverse;
use std::env;
use std::path::PathBuf;
use tracing_subscriber::EnvFilter;

fn main() {
    init_tracing_subscriber();

    let artifacts_dir = env::var("ZKSYNC_ETHEREUM_ARTIFACTS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from("/home/popzxc/workspace/airbender/ethereum-prover/artifacts")
        });
    let witness_path = env::var("ZKSYNC_ETHEREUM_WITNESS")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("/home/popzxc/workspace/airbender/24232546_witness.bin"));
    let runs = env_usize("ZKSYNC_SYNC_PROFILE_RUNS", 1);
    let replay_threads = env_usize("ZKSYNC_REPLAY_THREADS", 4);
    let host_allocators = env_usize("ZKSYNC_HOST_ALLOCATORS", 384);
    let trace_chunks_count_override = env_optional_usize("ZKSYNC_TRACE_CHUNKS");
    let use_dedicated_pipeline_threads = env_bool("ZKSYNC_DEDICATED_PIPELINE_THREADS");
    let mode = env_mode();

    eprintln!("loading input from {}", artifacts_dir.display());
    let (_, binary_image) = read_binary(&artifacts_dir.join("app.bin"));
    let (_, text_section) = read_binary(&artifacts_dir.join("app.text"));
    eprintln!("loading witness from {}", witness_path.display());
    let witness_bytes = std::fs::read(&witness_path).expect("witness file should be readable");
    let nondeterminism: Vec<u32> =
        bincode::decode_from_slice(witness_bytes.as_slice(), bincode::config::standard())
            .expect("witness should decode as Vec<u32>")
            .0;

    eprintln!(
        "initializing CPU pipeline model: mode={mode:?}, replay_threads={replay_threads}, host_allocators={host_allocators}, trace_chunks={}, dedicated_pipeline_threads={use_dedicated_pipeline_threads}",
        trace_chunks_count_override
            .map(|value| value.to_string())
            .unwrap_or_else(|| "default".to_string())
    );
    let model = CpuPipelineModel::new(
        CpuPipelineModelConfig {
            execution_kind: ExecutionKind::Unrolled,
            machine_type: MachineType::FullUnsigned,
            mode,
            max_thread_pool_threads: None,
            replay_worker_threads_count: replay_threads,
            host_allocators_count: host_allocators,
            memory_holders_count: 1,
            trace_chunks_count_override,
            use_dedicated_pipeline_threads,
            ..Default::default()
        },
        CpuPipelineModelInput {
            binary_image,
            text_section,
        },
    );

    for run_index in 0..runs {
        eprintln!("starting profiled run {run_index}");
        let report = model.run(nondeterminism.clone());
        eprintln!("finished profiled run {run_index}");
        println!(
            "run={} mode={:?} replay_threads={} trace_chunks={} dedicated_pipeline_threads={} cycles={} snapshots={} finalized={} total={:.3}ms simulator={:.3}ms replay_cpu_sum={:.3}ms init_scan={:.3}ms init_partition={:.3}ms",
            run_index,
            report.mode,
            replay_threads,
            trace_chunks_count_override
                .map(|value| value.to_string())
                .unwrap_or_else(|| "default".to_string()),
            use_dedicated_pipeline_threads,
            report.cycles,
            report.snapshots_produced,
            report.snapshots_finalized,
            report.timings.total_wall.as_secs_f64() * 1000.0,
            report.timings.simulator_wall.as_secs_f64() * 1000.0,
            report.timings.replay_cpu.as_secs_f64() * 1000.0,
            report.timings.init_teardown_scan.as_secs_f64() * 1000.0,
            report.timings.init_teardown_partition.as_secs_f64() * 1000.0,
        );

        let mut rows = report.sync_profile;
        rows.sort_by_key(|row| Reverse(row.total.as_nanos()));
        for row in rows {
            println!("{row}");
        }
    }
}

fn init_tracing_subscriber() {
    let env_filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));

    // Existing prover diagnostics use the `log` crate. The tracing-log feature
    // on tracing-subscriber bridges those records, so RUST_LOG works here
    // without changing the code paths being profiled.
    tracing_subscriber::fmt()
        .with_env_filter(env_filter)
        .try_init()
        .expect("tracing subscriber should initialize once");
}

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .map(|value| {
            value
                .parse()
                .expect("numeric environment value should parse")
        })
        .unwrap_or(default)
}

fn env_optional_usize(name: &str) -> Option<usize> {
    env::var(name).ok().map(|value| {
        value
            .parse()
            .expect("numeric environment value should parse")
    })
}

fn env_bool(name: &str) -> bool {
    match env::var(name).as_deref() {
        Ok("1") | Ok("true") | Ok("yes") | Ok("on") => true,
        Ok("0") | Ok("false") | Ok("no") | Ok("off") | Err(_) => false,
        Ok(value) => panic!("unsupported boolean {name}={value}"),
    }
}

fn env_mode() -> CpuPipelineMode {
    match env::var("ZKSYNC_CPU_PIPELINE_MODE").as_deref() {
        Ok("simulation") | Ok("SimulationOnly") => CpuPipelineMode::SimulationOnly,
        Ok("full") | Ok("Full") => CpuPipelineMode::Full,
        Ok("full_without_delegation") | Ok("FullWithoutDelegationReplay") => {
            CpuPipelineMode::FullWithoutDelegationReplay
        }
        Ok(value) => panic!("unsupported ZKSYNC_CPU_PIPELINE_MODE={value}"),
        Err(_) => CpuPipelineMode::Full,
    }
}
