use base64::Engine;
use clap::{Parser, Subcommand, ValueEnum};
use prover_pipeline::{
    default_backend_for_build, deserialize_from_file, load_program_words, serialize_to_file,
    u32_from_hex_string, ProgramProver, ProgramProverConfig, ProgramSource, ProofArtifact,
    ProofTarget, ProverBackend, RamSize, SoundnessMode,
};
use reqwest::blocking::Client;
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::{
    DecodingOptions, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
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

#[derive(Clone, Debug, Default, ValueEnum, Parser)]
enum InputType {
    #[default]
    Hex,
    ProverInputJson,
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

#[derive(Clone, Debug, Parser)]
struct BackendSettings {
    /// Cycle limit for the proved program; unlimited when absent.
    #[arg(long)]
    cycles_bound: Option<u32>,
    #[arg(long, value_enum, default_value = "1gib")]
    ram_size: RamSize,
    /// Proving thread pool size; every core when absent.
    #[arg(long)]
    worker_threads: Option<usize>,
    /// Replay threads; the backend's default when absent.
    #[arg(long)]
    replay_threads: Option<usize>,
}

/// `--soundness-mode` values: the [`SoundnessMode::cli_name`] spellings.
fn soundness_mode_parser() -> impl clap::builder::TypedValueParser<Value = SoundnessMode> {
    use clap::builder::TypedValueParser;
    clap::builder::PossibleValuesParser::new(SoundnessMode::ALL.iter().map(|mode| mode.cli_name()))
        .map(|name: String| SoundnessMode::from_cli_name(&name).expect("a possible value"))
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
        /// Flat ROM image (`objcopy -O binary`); pair with `--text`, or use `--elf` instead.
        #[arg(short, long, required_unless_present = "elf", conflicts_with = "elf")]
        bin: Option<String>,
        /// Text section dump; derived from `--bin` when omitted.
        #[arg(long, conflicts_with = "elf")]
        text: Option<String>,
        /// The linked ELF file, replacing `--bin`/`--text`.
        #[arg(long)]
        elf: Option<String>,
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
        /// Soundness accounting of every proof layer and of its verifier. A mode the backend
        /// cannot prove is rejected before the input is read.
        #[arg(
            long,
            value_parser = soundness_mode_parser(),
            default_value = SoundnessMode::DEFAULT.cli_name()
        )]
        soundness_mode: SoundnessMode,

        #[clap(flatten)]
        settings: BackendSettings,
    },
    /// Generate proof artifacts for many input files.
    ProveBatch {
        /// Flat ROM image (`objcopy -O binary`); pair with `--text`, or use `--elf` instead.
        #[arg(short, long, required_unless_present = "elf", conflicts_with = "elf")]
        bin: Option<String>,
        /// Text section dump; derived from `--bin` when omitted.
        #[arg(long, conflicts_with = "elf")]
        text: Option<String>,
        /// The linked ELF file, replacing `--bin`/`--text`.
        #[arg(long)]
        elf: Option<String>,
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
        /// Soundness accounting of every proof layer and of its verifier, recorded in every
        /// artifact and in the batch summary. A mode the backend cannot prove is rejected before
        /// any input is read.
        #[arg(
            long,
            value_parser = soundness_mode_parser(),
            default_value = SoundnessMode::DEFAULT.cli_name()
        )]
        soundness_mode: SoundnessMode,

        #[clap(flatten)]
        settings: BackendSettings,
    },
    /// Continue staged proving from an existing proof artifact.
    ContinueProof {
        #[arg(short, long)]
        proof: String,
        /// Flat ROM image (`objcopy -O binary`); pair with `--text`, or use `--elf` instead.
        #[arg(short, long, required_unless_present = "elf", conflicts_with = "elf")]
        bin: Option<String>,
        /// Text section dump; derived from `--bin` when omitted.
        #[arg(long, conflicts_with = "elf")]
        text: Option<String>,
        /// The linked ELF file, replacing `--bin`/`--text`.
        #[arg(long)]
        elf: Option<String>,
        #[arg(long, default_value = "output")]
        output_dir: String,
        #[arg(long, default_value = "proof.json")]
        output_file: String,
        #[arg(long, value_enum, default_value = "recursion-unified")]
        target: ProofTarget,
        #[arg(long, value_enum)]
        backend: Option<ProverBackend>,
        /// Expected soundness mode of the input artifact, also used for the new layers. An artifact
        /// in another mode is rejected before any proving; there is no conversion between modes.
        #[arg(
            long,
            value_parser = soundness_mode_parser(),
            default_value = SoundnessMode::DEFAULT.cli_name()
        )]
        soundness_mode: SoundnessMode,
        #[clap(flatten)]
        settings: BackendSettings,
    },
    /// Verify a single proof artifact.
    Verify {
        #[arg(short, long)]
        proof: String,
        /// Flat ROM image (`objcopy -O binary`); pair with `--text`, or use `--elf` instead.
        #[arg(short, long, required_unless_present = "elf", conflicts_with = "elf")]
        bin: Option<String>,
        /// Text section dump; derived from `--bin` when omitted.
        #[arg(long, conflicts_with = "elf")]
        text: Option<String>,
        /// The linked ELF file, replacing `--bin`/`--text`.
        #[arg(long)]
        elf: Option<String>,
        /// Expected soundness mode of the artifact: the proof is checked with this mode's verifiers,
        /// and an artifact claiming another mode is rejected.
        #[arg(
            long,
            value_parser = soundness_mode_parser(),
            default_value = SoundnessMode::DEFAULT.cli_name()
        )]
        soundness_mode: SoundnessMode,
    },
    /// Run binary via the transpiler VM.
    Run {
        /// Flat ROM image (`objcopy -O binary`); pair with `--text`, or use `--elf` instead.
        #[arg(short, long, required_unless_present = "elf", conflicts_with = "elf")]
        bin: Option<String>,
        /// Text section dump; derived from `--bin` when omitted.
        #[arg(long, conflicts_with = "elf")]
        text: Option<String>,
        /// The linked ELF file, replacing `--bin`/`--text`.
        #[arg(long)]
        elf: Option<String>,
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
    soundness_mode: &'static str,
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
                    .as_chunks::<4>()
                    .0
                    .iter()
                    .map(|chunk| u32::from_le_bytes(*chunk))
                    .collect();
                Ok(Some(prover_input))
            } else {
                Ok(None)
            }
        }
    }
}

/// The L1 targets exist only in `pessimistic-conjecture` (deferred product scope); reject the
/// prover's own selection before any input is read.
fn admit_target(config: &ProgramProverConfig) -> Result<(), String> {
    prover_pipeline::validate_target_selection(config.target, config.selection())
        .map_err(|error| error.to_string())
}

fn make_prover_config(
    soundness_mode: SoundnessMode,
    target: ProofTarget,
    backend: Option<ProverBackend>,
    settings: BackendSettings,
) -> ProgramProverConfig {
    ProgramProverConfig {
        soundness_mode,
        target,
        backend: backend.unwrap_or_else(default_backend_for_build),
        cycles_bound: settings.cycles_bound,
        ram_size: settings.ram_size,
        worker_threads: settings.worker_threads,
        replay_threads: settings.replay_threads,
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

    // Proving (and the embedded verifiers) needs a much bigger stack than the
    // default main-thread stack; run all commands on a big-stack thread
    // (equivalent to RUST_MIN_STACK=1GiB for spawned threads).
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(run_cli)
        .expect("failed to spawn main worker thread")
        .join()
        .expect("main worker thread panicked");
}

fn run_cli() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Prove {
            bin,
            text,
            elf,
            input,
            output_dir,
            output_file,
            target,
            backend,
            batch_id,
            soundness_mode,
            settings,
        } => {
            let source = program_source(bin, text, elf);
            let prover_config = make_prover_config(soundness_mode, target, backend, settings);

            let mut prover = ProgramProver::new(source, prover_config)
                .unwrap_or_else(|e| panic!("Failed to create prover: {}", e));
            let input_words = fetch_input_data(&input)
                .expect("Failed to fetch input")
                .unwrap_or_default();
            let artifact = prover
                .prove_words(batch_id, input_words)
                .unwrap_or_else(|e| panic!("Proving failed: {}", e));

            write_artifact(&artifact, &output_dir, &output_file);
        }
        Commands::ProveBatch {
            bin,
            text,
            elf,
            input_file,
            input_type,
            output_dir,
            target,
            backend,
            batch_id_base,
            soundness_mode,
            settings,
        } => {
            let source = program_source(bin, text, elf);
            let prover_config = make_prover_config(soundness_mode, target, backend, settings);

            let mut prover = ProgramProver::new(source, prover_config)
                .unwrap_or_else(|e| panic!("Failed to create prover: {}", e));

            fs::create_dir_all(&output_dir).expect("Failed to create output directory");

            let mut summary = BatchSummary {
                soundness_mode: soundness_mode.cli_name(),
                items: Vec::new(),
            };

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
            elf,
            output_dir,
            output_file,
            target,
            backend,
            soundness_mode,
            settings,
        } => {
            let prover_config = make_prover_config(soundness_mode, target, backend, settings);
            admit_target(&prover_config).unwrap_or_else(|e| panic!("Continuation rejected: {}", e));
            let input_artifact: ProofArtifact = deserialize_from_file(&proof);
            input_artifact
                .validate_expected_mode(soundness_mode)
                .unwrap_or_else(|e| panic!("Continuation rejected: {}", e));
            let source = program_source(bin, text, elf);

            let mut prover =
                ProgramProver::for_continuation(source, prover_config, &input_artifact)
                    .unwrap_or_else(|e| panic!("Failed to create prover: {}", e));
            let artifact = prover
                .continue_artifact(input_artifact)
                .unwrap_or_else(|e| panic!("Continuation failed: {}", e));

            write_artifact(&artifact, &output_dir, &output_file);
        }
        Commands::Verify {
            proof,
            bin,
            text,
            elf,
            soundness_mode,
        } => {
            let artifact: ProofArtifact = deserialize_from_file(&proof);
            let source = program_source(bin, text, elf);
            let output =
                prover_pipeline::verify_artifact_in_mode(&artifact, &source, soundness_mode)
                    .unwrap_or_else(|e| panic!("Verification failed: {}", e));
            if artifact.target == ProofTarget::L1 {
                println!(
                    "FEEDER SIDECAR AND CHAIN ARE VALID. Proth proof was not verified. output={:?}",
                    output
                );
            } else {
                println!("PROOF IS VALID. output={:?}", output);
            }
        }
        Commands::Run {
            bin,
            text,
            elf,
            input,
            cycles,
            expected_results,
            machine,
        } => {
            let input_words = fetch_input_data(&input)
                .expect("Failed to fetch input")
                .unwrap_or_default();
            let source = program_source(bin, text, elf);
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

fn program_source(bin: Option<String>, text: Option<String>, elf: Option<String>) -> ProgramSource {
    match (bin, text, elf) {
        (Some(bin), Some(text), None) => ProgramSource::legacy_binaries(bin, text),
        (Some(bin), None, None) => ProgramSource::legacy_binaries_from_bin(bin),
        (None, None, Some(elf)) => ProgramSource::elf(elf),
        _ => unreachable!("clap enforces exactly one of --bin / --elf"),
    }
}

fn run_binary(
    source: &ProgramSource,
    cycles: usize,
    input_data: Vec<u32>,
    expected_results: Option<Vec<u32>>,
    machine: RunMachine,
) {
    let (binary_image, text_section) =
        load_program_words(source).unwrap_or_else(|e| panic!("Failed to load program: {}", e));

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
    let instructions = preprocess_bytecode::<D, true>(text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
        binary_image,
        DEFAULT_RUN_RAM_BOUND_BYTES,
    );

    // We only need final registers for `cli run`, so counters are enough and
    // the no-op snapshotter keeps the execution path lightweight.
    let mut state = State::initial_with_counters(DelegationsCounters::default());
    let mut non_determinism_source = QuasiUARTSource::new_with_reads(input_data);
    let finished = VM::<DelegationsCounters>::run_basic_unrolled::<
        _,
        _,
        _,
        prover::field::baby_bear::base::BabyBearField,
    >(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        cycles,
        &mut non_determinism_source,
    );

    (state.registers.map(|register| register.value), finished)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    const MODE_COMMANDS: [&[&str]; 4] = [
        &["prove", "--bin", "app.bin"],
        &["prove-batch", "--bin", "app.bin"],
        &[
            "continue-proof",
            "--proof",
            "proof.json",
            "--bin",
            "app.bin",
        ],
        &["verify", "--proof", "proof.json", "--bin", "app.bin"],
    ];

    fn parse(args: &[&str]) -> Result<Cli, clap::Error> {
        Cli::try_parse_from(iter::once("cli").chain(args.iter().copied()))
    }

    fn with_mode<'a>(command: &[&'a str], mode: &'a str) -> Vec<&'a str> {
        command
            .iter()
            .copied()
            .chain(["--soundness-mode", mode])
            .collect()
    }

    fn mode_of(command: Commands) -> SoundnessMode {
        match command {
            Commands::Prove { soundness_mode, .. }
            | Commands::ProveBatch { soundness_mode, .. }
            | Commands::ContinueProof { soundness_mode, .. }
            | Commands::Verify { soundness_mode, .. } => soundness_mode,
            Commands::Run { .. } => panic!("run takes no soundness mode"),
        }
    }

    /// The prover config that `continue-proof` builds from its own arguments.
    fn continuation_config(target: ProofTarget, mode: SoundnessMode) -> ProgramProverConfig {
        let target = target.to_possible_value().unwrap();
        let args = with_mode(MODE_COMMANDS[2], mode.cli_name());
        let args: Vec<&str> = args
            .into_iter()
            .chain(["--target", target.get_name()])
            .collect();
        match parse(&args).unwrap().command {
            Commands::ContinueProof {
                target,
                backend,
                soundness_mode,
                settings,
                ..
            } => make_prover_config(soundness_mode, target, backend, settings),
            _ => unreachable!(),
        }
    }

    #[test]
    fn ethproofs_l1_targets_are_rejected_before_any_input() {
        for target in [ProofTarget::L1Feeder, ProofTarget::L1] {
            let config = continuation_config(target, SoundnessMode::EthproofsSoundnessCalc);
            assert_eq!(
                (config.target, config.selection().soundness_mode),
                (target, SoundnessMode::EthproofsSoundnessCalc)
            );
            assert_eq!(
                admit_target(&config).unwrap_err(),
                "UnsupportedSpecialConfigMode: ethproofs soundness mode is not implemented for the L1 feeder/wrap/EVM profile (deferred product scope); requested L1Feeder"
            );
            admit_target(&continuation_config(
                target,
                SoundnessMode::PessimisticConjecture,
            ))
            .unwrap();
        }
        for target in [
            ProofTarget::Base,
            ProofTarget::RecursionUnrolled,
            ProofTarget::RecursionUnified,
        ] {
            for &mode in SoundnessMode::ALL {
                admit_target(&continuation_config(target, mode)).unwrap();
            }
        }
    }

    #[test]
    fn soundness_mode_defaults_to_pessimistic_conjecture() {
        assert_eq!(SoundnessMode::DEFAULT, SoundnessMode::PessimisticConjecture);
        for command in MODE_COMMANDS {
            let parsed = parse(command).unwrap();
            assert_eq!(
                mode_of(parsed.command),
                SoundnessMode::PessimisticConjecture,
                "{command:?}"
            );
        }
    }

    #[test]
    fn every_mode_is_accepted_by_its_cli_name() {
        for command in MODE_COMMANDS {
            for mode in SoundnessMode::ALL {
                let parsed = parse(&with_mode(command, mode.cli_name())).unwrap();
                assert_eq!(mode_of(parsed.command), *mode, "{command:?}");
            }
        }
    }

    #[test]
    fn other_spellings_are_rejected() {
        for command in MODE_COMMANDS {
            for spelling in ["ethproofs", "EthproofsSoundnessCalc", "ethproofs_soundcalc"] {
                let err = parse(&with_mode(command, spelling)).err().unwrap();
                assert_eq!(err.kind(), clap::error::ErrorKind::InvalidValue);
            }
        }
    }

    #[test]
    fn run_takes_no_soundness_mode() {
        let err = parse(&with_mode(
            &["run", "--bin", "app.bin"],
            SoundnessMode::DEFAULT.cli_name(),
        ))
        .err()
        .unwrap();
        assert_eq!(err.kind(), clap::error::ErrorKind::UnknownArgument);
    }

    #[test]
    fn prover_config_carries_the_selected_mode() {
        for mode in SoundnessMode::ALL {
            let parsed = parse(&with_mode(MODE_COMMANDS[0], mode.cli_name())).unwrap();
            let Commands::Prove {
                soundness_mode,
                target,
                backend,
                settings,
                ..
            } = parsed.command
            else {
                unreachable!("parsed a prove command")
            };
            let config = make_prover_config(soundness_mode, target, backend, settings);
            assert_eq!(config.soundness_mode, *mode);
        }
    }

    #[test]
    fn help_lists_every_mode() {
        let mut cli = Cli::command();
        for name in ["prove", "prove-batch", "continue-proof", "verify"] {
            let help = cli
                .find_subcommand_mut(name)
                .unwrap()
                .render_long_help()
                .to_string();
            for mode in SoundnessMode::ALL {
                assert!(help.contains(mode.cli_name()), "{name}: {help}");
            }
        }
    }
}
