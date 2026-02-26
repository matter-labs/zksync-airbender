use anyhow::Context;
use std::borrow::Cow;
use std::fs;
use std::io;
use std::path::PathBuf;

use clap::Args;
use clap::Parser;
use clap::Subcommand;
use rand::rngs::StdRng;
use rand::SeedableRng;

mod circuits;
mod crashes;
mod mutations;
mod seeds;
mod state;
mod triage;

use circuits::CircuitKind;
use circuits::CircuitRegistry;
use circuits::ProverAttempt;
use crashes::BugReport;
use crashes::ExecutionOutcome;
use rand::seq::IndexedRandom as _;
use state::FuzzerState;

use crate::prover::crashes::BugType;
use crate::prover::mutations::MutatedInput;
use crate::prover::mutations::MutatorRegistry;
use crate::prover::seeds::SeedCase;
pub use crate::prover::triage::TriageCli;

/// Command-line arguments for the prover fuzzer scaffold and crash triage.
#[derive(Debug, Parser)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Option<Command>,
    #[command(flatten)]
    pub fuzz: FuzzCli,
}

#[derive(Debug, Subcommand)]
pub enum Command {
    Triage(TriageCli),
}

/// Command-line arguments for the prover fuzzing loop.
#[derive(Debug, Clone, Args, Default)]
pub struct FuzzCli {
    /// Directory containing `.bin`/`.text` seed program pairs.
    #[arg(short = 'i', long)]
    pub input_dir: Option<PathBuf>,
    /// Directory used to store fuzzer state such as cache entries and crashes.
    #[arg(short = 'o', long)]
    pub output_dir: Option<PathBuf>,
    /// Number of fuzz-loop iterations to execute.
    #[arg(long)]
    pub iterations: Option<usize>,
    /// RNG seed used to make scaffold behavior reproducible.
    #[arg(long)]
    pub seed: Option<u64>,
    #[arg(long, default_value_t = false)]
    pub skip_validation: bool,
}

/// Resolved runtime configuration derived from the CLI.
#[derive(Debug, Clone)]
pub struct FuzzerConfig {
    /// Input corpus directory passed by the user.
    pub input_dir: PathBuf,
    /// Root output directory passed by the user.
    pub output_dir: PathBuf,
    /// Cache directory nested under [`FuzzerConfig::output_dir`].
    pub cache_dir: PathBuf,
    /// Crash directory nested under [`FuzzerConfig::output_dir`].
    pub crash_dir: PathBuf,
    /// Number of fuzz-loop iterations to execute.
    pub iterations: Option<usize>,
    /// RNG seed used by the fuzzer.
    pub seed: u64,
}

/// Top-level prover fuzzer orchestrator.
pub struct Fuzzer {
    /// Static runtime configuration.
    config: FuzzerConfig,
    /// Mutable runtime state.
    state: FuzzerState,
    /// Deterministic RNG used for seed selection and mutation.
    rng: StdRng,
    /// Registry of circuit adapters used by the scaffold.
    registry: CircuitRegistry,
}

/// Identifies the original seed/circuit pair from which a mutation was derived.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SeedCaseRef {
    /// Name of the seed program used as the mutation base.
    pub seed_program: String,
    /// Circuit family targeted by the mutated input.
    pub circuit: CircuitKind,
}

/// Runs the prover fuzzer scaffold from parsed CLI arguments.
pub fn run(cli: Cli) -> anyhow::Result<()> {
    if let Some(Command::Triage(triage)) = cli.command {
        return triage::run(triage);
    }

    let skip_validation = cli.fuzz.skip_validation;
    let config = cli.fuzz.try_into()?;
    let mut fuzzer = Fuzzer::new(config);

    fuzzer.initialize()?;
    if !skip_validation {
        fuzzer.validate_seeds();
    }
    fuzzer.run_loop()?;

    Ok(())
}

fn current_timestamp() -> u64 {
    use std::time::SystemTime;

    match SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
        Ok(n) => n.as_secs(),
        Err(_) => panic!("SystemTime before UNIX EPOCH!"),
    }
}

impl TryFrom<FuzzCli> for FuzzerConfig {
    type Error = anyhow::Error;

    /// Expands CLI arguments into the runtime configuration shape used by the fuzzer.
    fn try_from(cli: FuzzCli) -> Result<Self, Self::Error> {
        let input_dir = cli
            .input_dir
            .context("`--input-dir` is required unless running `triage`")?;
        let output_dir = cli
            .output_dir
            .context("`--output-dir` is required unless running `triage`")?;

        Ok(FuzzerConfig {
            cache_dir: output_dir.join("cache"),
            crash_dir: output_dir.join("crashes"),
            input_dir,
            output_dir,
            iterations: cli.iterations,
            seed: cli.seed.unwrap_or_else(current_timestamp),
        })
    }
}

impl Fuzzer {
    /// Constructs a new fuzzer with deterministic RNG state and an empty runtime state.
    fn new(config: FuzzerConfig) -> Self {
        Self {
            rng: StdRng::seed_from_u64(config.seed),
            config,
            state: FuzzerState::default(),
            registry: CircuitRegistry::new(),
        }
    }

    /// Prepares directories, loads seed programs, and materializes the in-memory seed database.
    fn initialize(&mut self) -> io::Result<()> {
        log::info!("Seed: {}", self.config.seed);
        prepare_output_dirs(&self.config)?;
        self.state = FuzzerState::new(&self.config, &self.registry)?;

        Ok(())
    }

    /// Executes the main fuzz loop for the configured number of iterations.
    fn run_loop(&mut self) -> io::Result<()> {
        let m = MutatorRegistry::new();
        {
            let seed_cases = self.state.seed_cases();
            log::info!(
                "Loaded {} seed{}",
                seed_cases.len(),
                if seed_cases.len() == 1 { "" } else { "s" }
            );
        }

        let (range, iterations_str) = match self.config.iterations {
            Some(iterations) => {
                log::info!(
                    "Fuzzing for {iterations} iteration{}",
                    if iterations == 1 { "" } else { "s" }
                );
                (1..=iterations, Cow::<str>::Owned(format!("{iterations}")))
            }
            // To keep the ranges the same type the iterator is not actually infinite but until the
            // maximum possible usize.
            None => (1..=usize::MAX, Cow::<str>::Borrowed("?")),
        };

        for n in range {
            let seed_case = self.state.seed_cases().choose(&mut self.rng).unwrap();
            log::info!("[{}/{iterations_str}] Picked {seed_case}", n);
            let Some(mutated) = mutate_until_different(seed_case, &m, &mut self.rng) else {
                log::warn!("[{}/{iterations_str}] Ignoring {seed_case} because we could not mutate it into a different input", n);
                continue;
            };
            let outcome = self.run_one_iteration(mutated);
            if let ExecutionOutcome::Interesting(report) = outcome {
                log::info!("[{}/{iterations_str}] Found crash!", n);
                self.state.save_bug(*report, &self.config.crash_dir)?;
            }
        }
        Ok(())
    }

    /// Runs each seed e2e to check that they are valid.
    fn validate_seeds(&mut self) {
        let registry = &self.registry;
        let seed_cases = self.state.seed_cases_mut();
        let seed_count = seed_cases.len();
        log::info!(
            "Validating {seed_count} seed{}",
            if seed_count == 1 { "" } else { "s" }
        );
        let mut removed_count = 0;
        let mut n = 0;
        seed_cases.retain(|seed| {
            n += 1;
            let ProverAttempt::Success(proof) = registry.prove(&seed.base_input) else {
                log::warn!("[{n}/{seed_count}] Seed {seed} failed during proof generation",);
                removed_count += 1;
                return false;
            };
            let BugType::ValidationBug = registry.validate(&seed.base_input, &proof) else {
                log::warn!("[{n}/{seed_count}] Seed {seed} failed during proof validation",);
                removed_count += 1;
                return false;
            };
            log::info!("[{n}/{seed_count}] Seed {seed} validated successfuly",);
            true
        });

        if removed_count > 0 {
            log::warn!("Removed {removed_count} seeds from the set");
        }
    }

    /// Runs one fuzz iteration: given a mutated seed, attempt proving, and classify the result.
    fn run_one_iteration(&self, mutated: MutatedInput) -> ExecutionOutcome {
        match self.registry.prove(&mutated.mutated_input) {
            ProverAttempt::Crash => {
                log::info!("Prover crashed (that's good)");
                ExecutionOutcome::DiscardedProverCrash
            }
            ProverAttempt::Success(proof) => {
                log::info!("Prover generated a proof from the mutated input!");
                let bug_type = self.registry.validate(&mutated.mutated_input, &proof);
                log::info!("Proof validation outcome: {bug_type}");
                ExecutionOutcome::Interesting(Box::new(BugReport::new(mutated, bug_type)))
            }
        }
    }
}

/// Mutates the input seed, trying again if the mutated input is equal to
/// the original seed.
///
/// Gives up after a 1000 mutations attemps.
fn mutate_until_different(
    seed_case: &SeedCase,
    m: &MutatorRegistry,
    rng: &mut StdRng,
) -> Option<MutatedInput> {
    use similar::ChangeTag;
    use similar::TextDiff;
    const MAX_ATTEMPS: usize = 1000;
    let mut attemps = 0;

    let mut mutated_input;
    loop {
        log::debug!("[mutate_until_different] attempt #{attemps}");
        if attemps >= MAX_ATTEMPS {
            return None;
        }
        attemps += 1;
        mutated_input = m.apply_mutations(seed_case, rng);
        if mutated_input != seed_case {
            log::debug!("[mutate_until_different]    produced a different input");

            let old = format!("{:#?}", seed_case.base_input);
            let new = format!("{:#?}", mutated_input.mutated_input);
            let diff = TextDiff::from_lines(&old, &new);

            for change in diff.iter_all_changes() {
                let sign = match change.tag() {
                    ChangeTag::Delete => "-",
                    ChangeTag::Insert => "+",
                    ChangeTag::Equal => continue,
                };
                log::debug!("{}{}", sign, change);
            }

            break;
        }
    }
    Some(mutated_input)
}

/// Ensures the fuzzer output root and its required subdirectories exist.
fn prepare_output_dirs(config: &FuzzerConfig) -> io::Result<()> {
    fs::create_dir_all(&config.output_dir)?;
    fs::create_dir_all(&config.cache_dir)?;
    fs::create_dir_all(&config.crash_dir)?;
    Ok(())
}
