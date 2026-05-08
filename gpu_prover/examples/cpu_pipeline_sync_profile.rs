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
use std::time::Duration;
use tracing_subscriber::EnvFilter;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ProfileConfig {
    mode: CpuPipelineMode,
    replay_threads: usize,
    host_allocators: usize,
    trace_chunks_count_override: Option<usize>,
    use_dedicated_pipeline_threads: bool,
    replay_segment_cycle_limit: Option<usize>,
}

#[derive(Clone, Debug)]
struct AutocheckResult {
    config: ProfileConfig,
    runs: usize,
    total_wall: Duration,
    best_total_wall: Duration,
}

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
    let autocheck = env_bool("ZKSYNC_AUTOCHECK");
    let default_replay_threads = if autocheck {
        std::thread::available_parallelism()
            .map(|value| value.get())
            .unwrap_or(4)
    } else {
        4
    };
    let runs = env_usize("ZKSYNC_SYNC_PROFILE_RUNS", 1);
    let replay_threads = env_usize("ZKSYNC_REPLAY_THREADS", default_replay_threads);
    let autocheck_num_gpus = if autocheck {
        env_usize("ZKSYNC_NUM_GPUS", 1)
    } else {
        1
    };
    let autocheck_default_host_allocators = production_default_host_allocators(autocheck_num_gpus);
    let default_host_allocators = if autocheck {
        autocheck_default_host_allocators
    } else {
        384
    };
    let host_allocators = env_usize("ZKSYNC_HOST_ALLOCATORS", default_host_allocators);
    let trace_chunks_count_override = env_optional_usize("ZKSYNC_TRACE_CHUNKS");
    let use_dedicated_pipeline_threads = env_bool("ZKSYNC_DEDICATED_PIPELINE_THREADS");
    let replay_segment_cycle_limit = env_optional_usize("ZKSYNC_REPLAY_SEGMENT_CYCLES");
    let autocheck_n_configs = env_optional_usize("ZKSYNC_AUTOCHECK_N_CONFIGS");
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

    if autocheck {
        run_autocheck(
            mode,
            runs,
            replay_threads,
            host_allocators,
            autocheck_num_gpus,
            autocheck_default_host_allocators,
            trace_chunks_count_override,
            use_dedicated_pipeline_threads,
            replay_segment_cycle_limit,
            autocheck_n_configs,
            CpuPipelineModelInput {
                binary_image,
                text_section,
            },
            nondeterminism,
        );
        return;
    }

    eprintln!(
        "initializing CPU pipeline model: mode={mode:?}, replay_threads={replay_threads}, host_allocators={host_allocators}, trace_chunks={}, dedicated_pipeline_threads={use_dedicated_pipeline_threads}, replay_segment_cycles={}",
        trace_chunks_count_override
            .map(|value| value.to_string())
            .unwrap_or_else(|| "default".to_string()),
        replay_segment_cycle_limit
            .map(|value| value.to_string())
            .unwrap_or_else(|| "off".to_string()),
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
            replay_segment_cycle_limit,
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
            "run={} mode={:?} replay_threads={} trace_chunks={} dedicated_pipeline_threads={} replay_segment_cycles={} cycles={} snapshots={} finalized={} total={:.3}ms simulator={:.3}ms replay_cpu_sum={:.3}ms init_scan={:.3}ms init_partition={:.3}ms",
            run_index,
            report.mode,
            replay_threads,
            trace_chunks_count_override
                .map(|value| value.to_string())
                .unwrap_or_else(|| "default".to_string()),
            use_dedicated_pipeline_threads,
            replay_segment_cycle_limit
                .map(|value| value.to_string())
                .unwrap_or_else(|| "off".to_string()),
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

fn run_autocheck(
    mode: CpuPipelineMode,
    runs: usize,
    max_replay_threads: usize,
    max_host_allocators: usize,
    num_gpus: usize,
    default_host_allocators: usize,
    max_trace_chunks_count_override: Option<usize>,
    use_dedicated_pipeline_threads: bool,
    max_replay_segment_cycle_limit: Option<usize>,
    autocheck_n_configs: Option<usize>,
    input: CpuPipelineModelInput,
    nondeterminism: Vec<u32>,
) {
    let replay_threads_values = autocheck_replay_threads_values(max_replay_threads);
    assert!(
        max_host_allocators >= default_host_allocators,
        "ZKSYNC_HOST_ALLOCATORS must be at least {default_host_allocators} for ZKSYNC_NUM_GPUS={num_gpus}"
    );
    let host_allocators_values =
        autocheck_host_allocators_values(max_host_allocators, default_host_allocators);
    let trace_chunks_values = autocheck_trace_chunks_values(max_trace_chunks_count_override);
    let replay_segment_values = autocheck_replay_segment_values(max_replay_segment_cycle_limit);
    let default_config = default_profile_config(
        mode,
        use_dedicated_pipeline_threads,
        default_host_allocators,
    );
    let all_configs = build_autocheck_configs(
        mode,
        use_dedicated_pipeline_threads,
        &replay_threads_values,
        &host_allocators_values,
        &trace_chunks_values,
        &replay_segment_values,
    );
    let configs = select_autocheck_configs(all_configs, autocheck_n_configs, default_config);
    let full_configs_count = replay_threads_values.len()
        * host_allocators_values.len()
        * trace_chunks_values.len()
        * replay_segment_values.len();
    let configs_count = configs.len();

    eprintln!(
        "starting autocheck: configs={configs_count}/{full_configs_count}, runs_per_config={runs}, num_gpus={num_gpus}, default_host_allocators={default_host_allocators}, replay_threads={replay_threads_values:?}, host_allocators={host_allocators_values:?}, trace_chunks={}, replay_segment_cycles={}",
        format_option_list(&trace_chunks_values, "default"),
        format_option_list(&replay_segment_values, "off"),
    );

    let mut results = Vec::with_capacity(configs_count);
    let mut global_run_index = 0usize;
    for (config_index, config) in configs.into_iter().enumerate() {
        eprintln!(
            "autocheck config {}/{}: {config:?}",
            config_index + 1,
            configs_count
        );
        let model = CpuPipelineModel::new(
            CpuPipelineModelConfig {
                execution_kind: ExecutionKind::Unrolled,
                machine_type: MachineType::FullUnsigned,
                mode,
                max_thread_pool_threads: None,
                replay_worker_threads_count: config.replay_threads,
                host_allocators_count: config.host_allocators,
                memory_holders_count: 1,
                trace_chunks_count_override: config.trace_chunks_count_override,
                use_dedicated_pipeline_threads,
                replay_segment_cycle_limit: config.replay_segment_cycle_limit,
                ..Default::default()
            },
            CpuPipelineModelInput {
                binary_image: input.binary_image.clone(),
                text_section: input.text_section.clone(),
            },
        );

        let mut total_wall = Duration::default();
        let mut best_total_wall = Duration::MAX;
        for run_index in 0..runs {
            let report_run_index = global_run_index;
            global_run_index += 1;
            let report = model.run(nondeterminism.clone());
            total_wall += report.timings.total_wall;
            best_total_wall = best_total_wall.min(report.timings.total_wall);
            print_autocheck_report(report_run_index, run_index, config, &report);
        }
        results.push(AutocheckResult {
            config,
            runs,
            total_wall,
            best_total_wall,
        });
    }

    results.sort_by_key(|result| result.average_total_wall().as_nanos());
    println!("winners count={}", results.len().min(5));
    for (rank, result) in results.iter().take(5).enumerate() {
        print_winner(rank + 1, result);
    }
    let default_result = results
        .iter()
        .find(|result| result.config == default_config)
        .expect("autocheck matrix should include the default configuration");
    let best_result = results
        .first()
        .expect("autocheck should run at least one config");
    print_default_result(default_result, best_result);
}

impl AutocheckResult {
    fn average_total_wall(&self) -> Duration {
        self.total_wall / self.runs as u32
    }
}

fn print_autocheck_report(
    global_run_index: usize,
    run_index: usize,
    config: ProfileConfig,
    report: &gpu_prover::execution::cpu_pipeline_model::CpuPipelineModelReport,
) {
    println!("RUN {global_run_index}");
    println!(
        "configuration run={run_index} mode={:?} replay_threads={} trace_chunks={} host_allocators={} dedicated_pipeline_threads={} replay_segment_cycles={}",
        config.mode,
        config.replay_threads,
        format_option(config.trace_chunks_count_override, "default"),
        config.host_allocators,
        config.use_dedicated_pipeline_threads,
        format_option(config.replay_segment_cycle_limit, "off"),
    );
    println!(
        "metadata run={run_index} cycles={} snapshots={} finalized={} replayed_cycles={} host_payloads={} tracing_rows={} inits_and_teardowns={}",
        report.cycles,
        report.snapshots_produced,
        report.snapshots_finalized,
        report.replayed_cycles,
        report.host_payloads_produced,
        report.tracing_rows_by_circuit.values().sum::<usize>(),
        report.inits_and_teardowns,
    );
    println!(
        "timings run={run_index} total={:.3}ms simulator={:.3}ms replay_cpu_sum={:.3}ms init_scan={:.3}ms init_partition={:.3}ms",
        millis(report.timings.total_wall),
        millis(report.timings.simulator_wall),
        millis(report.timings.replay_cpu),
        millis(report.timings.init_teardown_scan),
        millis(report.timings.init_teardown_partition),
    );
    println!("-----------");
}

fn print_winner(rank: usize, result: &AutocheckResult) {
    let config = result.config;
    println!(
        "winner rank={rank} avg_total={:.3}ms best_total={:.3}ms runs={} mode={:?} replay_threads={} trace_chunks={} host_allocators={} dedicated_pipeline_threads={} replay_segment_cycles={}",
        millis(result.average_total_wall()),
        millis(result.best_total_wall),
        result.runs,
        config.mode,
        config.replay_threads,
        format_option(config.trace_chunks_count_override, "default"),
        config.host_allocators,
        config.use_dedicated_pipeline_threads,
        format_option(config.replay_segment_cycle_limit, "off"),
    );
}

fn print_default_result(default_result: &AutocheckResult, best_result: &AutocheckResult) {
    let config = default_result.config;
    let default_avg = millis(default_result.average_total_wall());
    let default_best = millis(default_result.best_total_wall);
    let best_avg = millis(best_result.average_total_wall());
    let best_best = millis(best_result.best_total_wall);
    let avg_delta_ms = default_avg - best_avg;
    let avg_delta_pct = percent_delta(default_avg, best_avg);
    let best_delta_ms = default_best - best_best;
    let best_delta_pct = percent_delta(default_best, best_best);
    println!(
        "default_config_timings avg_total={default_avg:.3}ms best_attempt_total={default_best:.3}ms runs={} mode={:?} replay_threads={} trace_chunks={} host_allocators={} dedicated_pipeline_threads={} replay_segment_cycles={}",
        default_result.runs,
        config.mode,
        config.replay_threads,
        format_option(config.trace_chunks_count_override, "default"),
        config.host_allocators,
        config.use_dedicated_pipeline_threads,
        format_option(config.replay_segment_cycle_limit, "off"),
    );
    let config = best_result.config;
    println!(
        "best_config_timings avg_total={best_avg:.3}ms best_attempt_total={best_best:.3}ms runs={} mode={:?} replay_threads={} trace_chunks={} host_allocators={} dedicated_pipeline_threads={} replay_segment_cycles={}",
        best_result.runs,
        config.mode,
        config.replay_threads,
        format_option(config.trace_chunks_count_override, "default"),
        config.host_allocators,
        config.use_dedicated_pipeline_threads,
        format_option(config.replay_segment_cycle_limit, "off"),
    );
    println!("delta_average_values total={avg_delta_ms:+.3}ms total_pct={avg_delta_pct:+.2}%");
    println!("delta_best_values total={best_delta_ms:+.3}ms total_pct={best_delta_pct:+.2}%");
}

fn default_profile_config(
    mode: CpuPipelineMode,
    use_dedicated_pipeline_threads: bool,
    default_host_allocators: usize,
) -> ProfileConfig {
    ProfileConfig {
        mode,
        replay_threads: 4,
        host_allocators: default_host_allocators,
        trace_chunks_count_override: None,
        use_dedicated_pipeline_threads,
        replay_segment_cycle_limit: None,
    }
}

fn build_autocheck_configs(
    mode: CpuPipelineMode,
    use_dedicated_pipeline_threads: bool,
    replay_threads_values: &[usize],
    host_allocators_values: &[usize],
    trace_chunks_values: &[Option<usize>],
    replay_segment_values: &[Option<usize>],
) -> Vec<ProfileConfig> {
    let mut configs = Vec::new();
    for replay_threads in replay_threads_values.iter().copied() {
        for host_allocators in host_allocators_values.iter().copied() {
            for trace_chunks_count_override in trace_chunks_values.iter().copied() {
                for replay_segment_cycle_limit in replay_segment_values.iter().copied() {
                    configs.push(ProfileConfig {
                        mode,
                        replay_threads,
                        host_allocators,
                        trace_chunks_count_override,
                        use_dedicated_pipeline_threads,
                        replay_segment_cycle_limit,
                    });
                }
            }
        }
    }
    configs.sort_by_key(|config| autocheck_config_sort_key(*config));
    dedup_preserving_order(configs)
}

fn select_autocheck_configs(
    configs: Vec<ProfileConfig>,
    n_configs: Option<usize>,
    default_config: ProfileConfig,
) -> Vec<ProfileConfig> {
    let Some(n_configs) = n_configs else {
        return configs;
    };
    assert_ne!(n_configs, 0, "ZKSYNC_AUTOCHECK_N_CONFIGS must be non-zero");
    if configs.len() <= n_configs {
        return configs;
    }
    assert!(
        configs.contains(&default_config),
        "autocheck matrix should include the default configuration"
    );
    if n_configs == 1 {
        return vec![default_config];
    }

    // Keep the default baseline in the selected set so the final delta is based on an actual
    // measured run. The remaining slots are spread across the sorted configuration space.
    let non_default_configs = configs
        .into_iter()
        .filter(|config| *config != default_config)
        .collect::<Vec<_>>();
    let mut selected = evenly_spaced_configs(&non_default_configs, n_configs - 1);
    selected.push(default_config);
    selected.sort_by_key(|config| autocheck_config_sort_key(*config));
    selected
}

fn evenly_spaced_configs(configs: &[ProfileConfig], count: usize) -> Vec<ProfileConfig> {
    if count == 0 {
        return Vec::new();
    }
    if configs.len() <= count {
        return configs.to_vec();
    }
    if count == 1 {
        return vec![configs[configs.len() - 1]];
    }

    let max_index = configs.len() - 1;
    let max_slot = count - 1;
    let mut selected = Vec::with_capacity(count);
    for slot in 0..count {
        let index = (slot * max_index + max_slot / 2) / max_slot;
        selected.push(configs[index]);
    }
    dedup_preserving_order(selected)
}

fn autocheck_config_sort_key(config: ProfileConfig) -> (usize, usize, usize, usize, u8, u8) {
    (
        config.replay_threads,
        option_sort_key(config.trace_chunks_count_override),
        config.host_allocators,
        option_sort_key(config.replay_segment_cycle_limit),
        config.use_dedicated_pipeline_threads as u8,
        mode_sort_key(config.mode),
    )
}

fn option_sort_key(value: Option<usize>) -> usize {
    value.unwrap_or(0)
}

fn mode_sort_key(mode: CpuPipelineMode) -> u8 {
    match mode {
        CpuPipelineMode::SimulationOnly => 0,
        CpuPipelineMode::FullWithoutDelegationReplay => 1,
        CpuPipelineMode::Full => 2,
    }
}

fn autocheck_replay_threads_values(max_replay_threads: usize) -> Vec<usize> {
    assert_ne!(
        max_replay_threads, 0,
        "ZKSYNC_REPLAY_THREADS must be non-zero"
    );
    assert!(
        max_replay_threads >= 4,
        "ZKSYNC_REPLAY_THREADS must be at least 4 in autocheck mode"
    );
    let mut values = vec![4];
    let mut powers = Vec::new();
    let mut value = 4usize;
    while value < max_replay_threads {
        powers.push(value);
        value *= 2;
    }
    values.extend(powers.into_iter().rev().take(2));
    values.push(max_replay_threads);
    values.sort_unstable();
    let values = dedup_preserving_order(values);
    if values.len() <= 4 {
        values
    } else {
        let start = values.len() - 4;
        let mut clipped = vec![4];
        clipped.extend_from_slice(&values[start + 1..]);
        dedup_preserving_order(clipped)
    }
}

fn autocheck_host_allocators_values(
    max_host_allocators: usize,
    default_host_allocators: usize,
) -> Vec<usize> {
    assert_ne!(
        max_host_allocators, 0,
        "ZKSYNC_HOST_ALLOCATORS must be non-zero"
    );
    assert_ne!(
        default_host_allocators, 0,
        "default host allocators must be non-zero"
    );
    let mut values = vec![default_host_allocators];
    for value in [384, 512, 768, 1024, 1536, 2048, 3072] {
        if value <= max_host_allocators {
            values.push(value);
        }
    }
    values.push(max_host_allocators);
    values.sort_unstable();
    dedup_preserving_order(values)
}

fn autocheck_trace_chunks_values(max_trace_chunks: Option<usize>) -> Vec<Option<usize>> {
    let mut values = vec![None];
    match max_trace_chunks {
        Some(max_trace_chunks) => {
            assert_ne!(max_trace_chunks, 0, "ZKSYNC_TRACE_CHUNKS must be non-zero");
            for value in [384, 512, 768, 1024, 1536, 2048, 3072] {
                if value <= max_trace_chunks {
                    values.push(Some(value));
                }
            }
            values.push(Some(max_trace_chunks));
        }
        None => {
            values.push(Some(384));
        }
    }
    dedup_preserving_order(values)
}

fn autocheck_replay_segment_values(max_replay_segment_cycles: Option<usize>) -> Vec<Option<usize>> {
    let max_replay_segment_cycles = max_replay_segment_cycles.unwrap_or(1_000_000);
    assert_ne!(
        max_replay_segment_cycles, 0,
        "ZKSYNC_REPLAY_SEGMENT_CYCLES must be non-zero"
    );
    let mut values = vec![None];
    for value in [250_000, 500_000, 1_000_000] {
        if value <= max_replay_segment_cycles {
            values.push(Some(value));
        }
    }
    values.push(Some(max_replay_segment_cycles));
    dedup_preserving_order(values)
}

fn dedup_preserving_order<T: Eq + Copy>(values: Vec<T>) -> Vec<T> {
    let mut deduped = Vec::with_capacity(values.len());
    for value in values {
        if !deduped.contains(&value) {
            deduped.push(value);
        }
    }
    deduped
}

fn format_option(value: Option<usize>, none: &str) -> String {
    value
        .map(|value| value.to_string())
        .unwrap_or_else(|| none.to_string())
}

fn format_option_list(values: &[Option<usize>], none: &str) -> String {
    let values = values
        .iter()
        .map(|value| format_option(*value, none))
        .collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn percent_delta(default_value: f64, best_value: f64) -> f64 {
    if best_value == 0.0 {
        0.0
    } else {
        (default_value - best_value) * 100.0 / best_value
    }
}

fn production_default_host_allocators(num_gpus: usize) -> usize {
    assert_ne!(num_gpus, 0, "ZKSYNC_NUM_GPUS must be non-zero");

    // Match the real prover defaults: one concurrent job gets a fixed pool,
    // then every GPU contributes the per-device host allocation reserve.
    256usize
        .checked_add(
            num_gpus
                .checked_mul(128)
                .expect("ZKSYNC_NUM_GPUS should fit allocator formula"),
        )
        .expect("default host allocator count should fit usize")
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
