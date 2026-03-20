#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use base64::Engine;
use clap::{Parser, Subcommand, ValueEnum};
use cli_lib::prover_utils::{
    default_backend_for_build, deserialize_from_file, serialize_to_file, u32_from_hex_string,
    CpuConfig, GpuConfig, ProgramProver, ProgramProverConfig, ProgramSource, ProofArtifact,
    ProofTarget, ProverBackend,
};
use execution_utils::setups::read_binary;
use reqwest::blocking::Client;
use riscv_transpiler::ir::{
    preprocess_bytecode, DecodingOptions, FullUnsignedMachineDecoderConfig,
    ReducedMachineDecoderConfig,
};
use riscv_transpiler::vm::{DelegationsCounters, RamWithRomRegion, SimpleTape, State, VM};
use serde::Serialize;
use serde_json::Value;
use std::path::Path;
use std::{fs, iter};

use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

const DEFAULT_CYCLES: usize = 32_000_000;
const DEFAULT_RUN_RAM_BOUND_BYTES: usize = 1 << 30;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Clone, Debug, ValueEnum, Parser)]
enum InputType {
    Hex,
    ProverInputJson,
}

impl Default for InputType {
    fn default() -> Self {
        InputType::Hex
    }
}

#[derive(Clone, Debug, Parser, Default)]
struct InputConfig {
    #[arg(long)]
    input_file: Option<String>,

    #[arg(long, value_enum, default_value = "hex")]
    input_type: InputType,

    #[arg(long)]
    input_rpc: Option<String>,
    #[arg(long)]
    input_batch: Option<u64>,
}

#[derive(Clone, Debug, ValueEnum)]
enum RunMachine {
    FullUnsigned,
    Reduced,
}

#[derive(Subcommand)]
enum Commands {
    /// Generate proof artifact for a single input.
    Prove {
        #[arg(short, long)]
        bin: String,
        #[arg(long)]
        text: Option<String>,
        #[clap(flatten)]
        input: InputConfig,
        #[arg(long, default_value = "output")]
        output_dir: String,
        #[arg(long, default_value = "proof.json")]
        output_file: String,
        #[arg(long, value_enum, default_value = "recursion-unified")]
        target: ProofTarget,
        #[arg(long, value_enum)]
        backend: Option<ProverBackend>,
        #[arg(long, default_value_t = 0)]
        batch_id: u64,

        #[arg(long, default_value_t = 1 << 31)]
        cpu_cycles_bound: usize,
        #[arg(long, default_value_t = 1 << 30)]
        cpu_ram_bound: usize,
        #[arg(long)]
        cpu_worker_threads: Option<usize>,

        #[arg(long, default_value_t = 8)]
        gpu_replay_threads: usize,
    },
    /// Generate proof artifacts for many input files.
    ProveBatch {
        #[arg(short, long)]
        bin: String,
        #[arg(long)]
        text: Option<String>,
        #[arg(long)]
        input_file: Vec<String>,
        #[arg(long, value_enum, default_value = "hex")]
        input_type: InputType,
        #[arg(long, default_value = "output")]
        output_dir: String,
        #[arg(long, value_enum, default_value = "recursion-unified")]
        target: ProofTarget,
        #[arg(long, value_enum)]
        backend: Option<ProverBackend>,
        #[arg(long, default_value_t = 0)]
        batch_id_base: u64,

        #[arg(long, default_value_t = 1 << 31)]
        cpu_cycles_bound: usize,
        #[arg(long, default_value_t = 1 << 30)]
        cpu_ram_bound: usize,
        #[arg(long)]
        cpu_worker_threads: Option<usize>,

        #[arg(long, default_value_t = 8)]
        gpu_replay_threads: usize,
    },
    /// Continue staged proving from an existing proof artifact.
    ContinueProof {
        #[arg(short, long)]
        proof: String,
        #[arg(short, long)]
        bin: String,
        #[arg(long)]
        text: Option<String>,
        #[arg(long, default_value = "output")]
        output_dir: String,
        #[arg(long, default_value = "proof.json")]
        output_file: String,
        #[arg(long, value_enum, default_value = "recursion-unified")]
        target: ProofTarget,
        #[arg(long, default_value_t = 1 << 31)]
        cpu_cycles_bound: usize,
        #[arg(long, default_value_t = 1 << 30)]
        cpu_ram_bound: usize,
        #[arg(long)]
        cpu_worker_threads: Option<usize>,
    },
    /// Verify a single proof artifact.
    Verify {
        #[arg(short, long)]
        proof: String,
        #[arg(short, long)]
        bin: String,
        #[arg(long)]
        text: Option<String>,
    },
    /// Run binary via the transpiler VM.
    Run {
        #[arg(short, long)]
        bin: String,
        #[arg(long)]
        text: Option<String>,
        #[clap(flatten)]
        input: InputConfig,
        #[arg(long)]
        cycles: Option<usize>,
        #[arg(long, num_args = 1.., value_delimiter = ',')]
        expected_results: Option<Vec<u32>>,
        #[arg(long, value_enum, default_value = "full-unsigned")]
        machine: RunMachine,
    },
}

#[derive(Debug, Serialize)]
struct BatchSummary {
    items: Vec<BatchSummaryItem>,
}

#[derive(Debug, Serialize)]
struct BatchSummaryItem {
    input_file: String,
    output_file: String,
    batch_id: u64,
    total_ms: u64,
}

fn fetch_data_from_json_rpc(url: &str) -> Result<Option<String>, reqwest::Error> {
    let client = Client::new();
    let response = client.post(url).send()?.json::<Value>()?;

    match &response["result"] {
        Value::String(data) => {
            let tmp_data = data.strip_prefix("0x").unwrap_or(data);
            Ok(Some(tmp_data.to_string()))
        }
        _ => Ok(None),
    }
}

fn fetch_input_data(input: &InputConfig) -> Result<Option<Vec<u32>>, reqwest::Error> {
    let (data, input_type) = if let Some(input_file) = &input.input_file {
        (
            Some(fs::read_to_string(input_file).unwrap().trim().to_string()),
            input.input_type.clone(),
        )
    } else if let Some(url) = &input.input_rpc {
        (fetch_data_from_json_rpc(url)?, InputType::ProverInputJson)
    } else {
        return Ok(None);
    };

    parse_input_data(data, input_type)
}

fn parse_input_data(
    data: Option<String>,
    input_type: InputType,
) -> Result<Option<Vec<u32>>, reqwest::Error> {
    match input_type {
        InputType::Hex => Ok(data.map(|d| u32_from_hex_string(&d))),
        InputType::ProverInputJson => {
            if let Some(data) = data {
                let json: Value = serde_json::from_str(&data).expect("Failed to parse JSON");
                let prover_input = json["prover_input"].as_str().unwrap_or_default();

                let decoded = base64::engine::general_purpose::STANDARD
                    .decode(prover_input)
                    .expect("Failed to decode base64 input");

                let prover_input: Vec<u32> = decoded
                    .chunks_exact(4)
                    .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
                    .collect();
                Ok(Some(prover_input))
            } else {
                Ok(None)
            }
        }
    }
}

fn make_prover_config(
    target: ProofTarget,
    backend: Option<ProverBackend>,
    cpu_cycles_bound: usize,
    cpu_ram_bound: usize,
    cpu_worker_threads: Option<usize>,
    gpu_replay_threads: usize,
) -> ProgramProverConfig {
    ProgramProverConfig {
        target,
        backend: backend.unwrap_or_else(default_backend_for_build),
        cpu: CpuConfig {
            cycles_bound: cpu_cycles_bound,
            ram_bound: cpu_ram_bound,
            worker_threads: cpu_worker_threads,
        },
        gpu: GpuConfig {
            replay_worker_threads_count: gpu_replay_threads,
        },
    }
}

fn write_artifact(artifact: &ProofArtifact, output_dir: &str, output_file: &str) {
    let output_path = Path::new(output_dir).join(output_file);
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).expect("Failed to create output directory");
    }
    serialize_to_file(artifact, &output_path);
    println!("Proof artifact written to {}", output_path.display());
}

fn main() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .init();

    let cli = Cli::parse();

    match cli.command {
        Commands::Prove {
            bin,
            text,
            input,
            output_dir,
            output_file,
            target,
            backend,
            batch_id,
            cpu_cycles_bound,
            cpu_ram_bound,
            cpu_worker_threads,
            gpu_replay_threads,
        } => {
            let input_words = fetch_input_data(&input)
                .expect("Failed to fetch input")
                .unwrap_or_default();

            let source = ProgramSource::from_paths(bin, text);
            let prover_config = make_prover_config(
                target,
                backend,
                cpu_cycles_bound,
                cpu_ram_bound,
                cpu_worker_threads,
                gpu_replay_threads,
            );

            let prover = ProgramProver::new(source, prover_config)
                .unwrap_or_else(|e| panic!("Failed to create prover: {}", e));
            let artifact = prover
                .prove_words(batch_id, input_words)
                .unwrap_or_else(|e| panic!("Proving failed: {}", e));

            write_artifact(&artifact, &output_dir, &output_file);
        }
        Commands::ProveBatch {
            bin,
            text,
            input_file,
            input_type,
            output_dir,
            target,
            backend,
            batch_id_base,
            cpu_cycles_bound,
            cpu_ram_bound,
            cpu_worker_threads,
            gpu_replay_threads,
        } => {
            let source = ProgramSource::from_paths(bin, text);
            let prover_config = make_prover_config(
                target,
                backend,
                cpu_cycles_bound,
                cpu_ram_bound,
                cpu_worker_threads,
                gpu_replay_threads,
            );

            let prover = ProgramProver::new(source, prover_config)
                .unwrap_or_else(|e| panic!("Failed to create prover: {}", e));

            fs::create_dir_all(&output_dir).expect("Failed to create output directory");

            let mut summary = BatchSummary { items: Vec::new() };

            for (idx, input_path) in input_file.iter().enumerate() {
                let input_data = fs::read_to_string(input_path)
                    .unwrap_or_else(|e| panic!("Failed to read {}: {}", input_path, e));

                let parsed_words =
                    parse_input_data(Some(input_data.trim().to_string()), input_type.clone())
                        .expect("Failed to parse input")
                        .unwrap_or_default();

                let batch_id = batch_id_base + idx as u64;
                let artifact = prover
                    .prove_words(batch_id, parsed_words)
                    .unwrap_or_else(|e| panic!("Proving failed for {}: {}", input_path, e));

                let output_file = format!("proof_{}.json", idx);
                let output_path = Path::new(&output_dir).join(&output_file);
                serialize_to_file(&artifact, &output_path);

                summary.items.push(BatchSummaryItem {
                    input_file: input_path.clone(),
                    output_file,
                    batch_id,
                    total_ms: artifact.timings_ms.total_ms,
                });
            }

            let summary_path = Path::new(&output_dir).join("batch_summary.json");
            serialize_to_file(&summary, &summary_path);
            println!("Batch summary written to {}", summary_path.display());
        }
        Commands::ContinueProof {
            proof,
            bin,
            text,
            output_dir,
            output_file,
            target,
            cpu_cycles_bound,
            cpu_ram_bound,
            cpu_worker_threads,
        } => {
            let input_artifact: ProofArtifact = deserialize_from_file(&proof);
            let source = ProgramSource::from_paths(bin, text);
            let prover_config = make_prover_config(
                target,
                Some(ProverBackend::Cpu),
                cpu_cycles_bound,
                cpu_ram_bound,
                cpu_worker_threads,
                8,
            );

            let prover = ProgramProver::new(source, prover_config)
                .unwrap_or_else(|e| panic!("Failed to create prover: {}", e));
            let artifact = prover
                .continue_artifact(input_artifact)
                .unwrap_or_else(|e| panic!("Continuation failed: {}", e));

            write_artifact(&artifact, &output_dir, &output_file);
        }
        Commands::Verify { proof, bin, text } => {
            let artifact: ProofArtifact = deserialize_from_file(&proof);
            let source = ProgramSource::from_paths(bin, text);
            let output = cli_lib::prover_utils::verify_artifact(&artifact, &source)
                .unwrap_or_else(|e| panic!("Verification failed: {}", e));
            println!("PROOF IS VALID. output={:?}", output);
        }
        Commands::Run {
            bin,
            text,
            input,
            cycles,
            expected_results,
            machine,
        } => {
            let input_words = fetch_input_data(&input)
                .expect("Failed to fetch input")
                .unwrap_or_default();
            let source = ProgramSource::from_paths(bin, text);
            run_binary(
                &source,
                cycles.unwrap_or(DEFAULT_CYCLES),
                input_words,
                expected_results,
                machine,
            );
        }
    }
}

fn run_binary(
    source: &ProgramSource,
    cycles: usize,
    input_data: Vec<u32>,
    expected_results: Option<Vec<u32>>,
    machine: RunMachine,
) {
    let (_, binary_image) = read_binary(Path::new(&source.bin_path));
    let (_, text_section) = read_binary(Path::new(&source.text_path));

    let (registers, finished) = match machine {
        RunMachine::FullUnsigned => run_binary_with_decoder::<FullUnsignedMachineDecoderConfig>(
            &binary_image,
            &text_section,
            cycles,
            input_data,
        ),
        RunMachine::Reduced => run_binary_with_decoder::<ReducedMachineDecoderConfig>(
            &binary_image,
            &text_section,
            cycles,
            input_data,
        ),
    };

    if !finished {
        println!(
            "Program did not finish within {} cycles; reporting current register state",
            cycles
        );
    }

    let result = registers[10..26]
        .iter()
        .map(|x| format!("{}", x))
        .collect::<Vec<_>>()
        .join(", ");
    println!("Result: {}", result);

    if let Some(expected_results) = expected_results {
        for (i, (a, b)) in registers[10..18]
            .iter()
            .zip(expected_results.iter().chain(iter::repeat(&0)))
            .enumerate()
        {
            if a != b {
                panic!(
                    "Expected result mismatch at x{}: got {}, expected {}",
                    10 + i,
                    a,
                    b
                );
            }
        }
    }
}

fn run_binary_with_decoder<D: DecodingOptions>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles: usize,
    input_data: Vec<u32>,
) -> ([u32; 32], bool) {
    // The CLI now mirrors the active proving path: ROM comes from `.bin`, while
    // instruction decoding comes from the paired `.text` section.
    let instructions = preprocess_bytecode::<D>(text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ prover::common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            binary_image,
            DEFAULT_RUN_RAM_BOUND_BYTES,
        );

    // We only need final registers for `cli run`, so counters are enough and
    // the no-op snapshotter keeps the execution path lightweight.
    let mut state = State::initial_with_counters(DelegationsCounters::default());
    let mut non_determinism_source = QuasiUARTSource::new_with_reads(input_data);
    let finished = VM::<DelegationsCounters>::run_basic_unrolled(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        cycles,
        &mut non_determinism_source,
    );

    (state.registers.map(|register| register.value), finished)
}
