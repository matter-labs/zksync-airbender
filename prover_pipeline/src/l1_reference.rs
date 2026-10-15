use super::*;
use serde::de::DeserializeOwned;
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};
use std::sync::atomic::{AtomicU64, Ordering};

const REGENERATE: &str = "RUST_MIN_STACK=1073741824 cargo test -p prover_pipeline --release --lib l1_reference::generate_l1_reference -- --exact --ignored --nocapture --test-threads=1";
static MAX_STAGE_VMHWM: AtomicU64 = AtomicU64::new(0);

fn fixture_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/l1_reference_2p21"))
}

fn feeder_checkpoint_name(layer: u8) -> String {
    format!("feeder_layer_{layer}.json")
}

fn feeder_report_name(layer: u8) -> String {
    format!("feeder_layer_{layer}_report.json")
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum CheckpointStep {
    Feeder { layer: u8 },
}

const CHECKPOINT_SCHEMA_VERSION: u32 = 2;

/// A feeder-layer checkpoint: the state after feeder layer `layer`
/// (zero-based), so `feeder_layers = layer + 1`. Resuming it continues the
/// feeder loop at layer `layer + 1` (or only validates the wrap fit when the
/// checkpoint proof already has one instance).
#[derive(Clone, Debug, Serialize, Deserialize)]
struct StepCheckpoint {
    fixture_schema_version: u32,
    step: CheckpointStep,
    feeder_layers: u32,
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    input_is_base: bool,
    program_cycles: u64,
}

impl StepCheckpoint {
    fn from_state(layer: u8, state: &RecursionState) -> Self {
        Self {
            fixture_schema_version: CHECKPOINT_SCHEMA_VERSION,
            step: CheckpointStep::Feeder { layer },
            feeder_layers: state.feeder_layers,
            proof: state.proof.clone(),
            setups: state.setups.clone(),
            chain_end_params: state.chain_end_params.clone(),
            input_is_base: state.input_is_base,
            program_cycles: state.program_cycles,
        }
    }

    fn into_state(self) -> Result<RecursionState, String> {
        let CheckpointStep::Feeder { layer } = self.step;
        if self.fixture_schema_version != CHECKPOINT_SCHEMA_VERSION
            || self.feeder_layers != u32::from(layer) + 1
            || !(1..=MAX_FEEDER_LAYERS).contains(&self.feeder_layers)
            || self.input_is_base
            || self.chain_end_params.len() < 3 + self.feeder_layers as usize
        {
            return Err("invalid feeder checkpoint".into());
        }
        rebuild_chain(&self.chain_end_params)?;
        Ok(RecursionState {
            stage: ProofTarget::RecursionUnified,
            l1: None,
            proof: self.proof,
            setups: self.setups,
            chain_end_params: self.chain_end_params,
            input_is_base: self.input_is_base,
            timings: ProofTimingsMs::default(),
            program_cycles: self.program_cycles,
            feeder_layers: self.feeder_layers,
        })
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct ProgramIdentity {
    bin_keccak256: String,
    text_keccak256: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct ReferenceConfiguration {
    security_level: SecurityLevel,
    backend: ProverBackend,
    worker_threads: usize,
    batch_id: u64,
    blake_unrolled: String,
    blake_bridge: String,
    blake_final: String,
    user_nd_words: Vec<u32>,
}

#[derive(Debug, Serialize, Deserialize)]
struct FileIdentity {
    name: String,
    bytes: u64,
    keccak256: String,
}

type Inventory = Vec<FileIdentity>;

#[derive(Debug, Serialize, Deserialize)]
struct ProofManifest {
    format_version: u32,
    program: ProgramIdentity,
    fsv: Vec<FsvIdentity>,
    configuration: ReferenceConfiguration,
    files: Inventory,
}

fn hex_digest(bytes: &[u8]) -> String {
    keccak256(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn read_bytes(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path).map_err(|error| format!("L1 reference read {}: {error}", path.display()))
}

fn read_typed<T: DeserializeOwned>(path: &Path) -> Result<T, String> {
    let file = File::open(path)
        .map_err(|error| format!("L1 reference open {}: {error}", path.display()))?;
    serde_json::from_reader(BufReader::new(file))
        .map_err(|error| format!("L1 reference deserialize {}: {error}", path.display()))
}

fn write_compact<T: Serialize>(path: &Path, value: &T) -> Result<(), String> {
    let temporary = path.with_extension("json.part");
    let file = File::create(&temporary)
        .map_err(|error| format!("L1 reference create {}: {error}", temporary.display()))?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, value)
        .map_err(|error| format!("L1 reference serialize {}: {error}", path.display()))?;
    writer
        .flush()
        .map_err(|error| format!("L1 reference flush: {error}"))?;
    drop(writer);
    fs::rename(&temporary, path)
        .map_err(|error| format!("L1 reference rename {}: {error}", path.display()))
}

fn file_identity(dir: &Path, name: &str) -> Result<FileIdentity, String> {
    let bytes = read_bytes(&dir.join(name))?;
    Ok(FileIdentity {
        name: name.into(),
        bytes: bytes.len() as u64,
        keccak256: hex_digest(&bytes),
    })
}

fn fsv_identities(blake: PipelineBlakeModes) -> Result<Vec<FsvIdentity>, String> {
    [
        (
            "unrolled_base",
            FsvProgram::UnrolledBaseLayer,
            blake.unrolled,
        ),
        (
            "unrolled_recursion",
            FsvProgram::UnrolledRecursionLayer,
            blake.unrolled,
        ),
        ("bridge_base", FsvProgram::UnrolledBaseLayer, blake.bridge),
        (
            "bridge_recursion",
            FsvProgram::UnrolledRecursionLayer,
            blake.bridge,
        ),
        (
            "unified",
            FsvProgram::UnifiedRecursionLayer,
            blake.final_layer,
        ),
        (
            "feeder_first",
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        ),
        (
            "feeder",
            FsvProgram::UnifiedRecursionLayerL1Feeder,
            BlakeMode::BlakeSpecialOpcodes,
        ),
        (
            "feeder_wrap",
            FsvProgram::UnifiedRecursionLayerL1FeederWrap,
            BlakeMode::BlakeSpecialOpcodes,
        ),
    ]
    .into_iter()
    .map(|(role, program, mode)| {
        let stem = program.file_stem(mode);
        Ok(FsvIdentity {
            role: role.into(),
            bin_keccak256: hex_digest(&read_bytes(&fsv_dir().join(format!("{stem}.bin")))?),
            text_keccak256: hex_digest(&read_bytes(&fsv_dir().join(format!("{stem}.text")))?),
            stem,
        })
    })
    .collect()
}

fn source() -> ProgramSource {
    ProgramSource::from_paths(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../examples/basic_fibonacci/app.bin")
            .to_string_lossy()
            .into_owned(),
        None,
    )
}

fn config(target: ProofTarget) -> ProgramProverConfig {
    ProgramProverConfig {
        target,
        backend: ProverBackend::Cpu,
        worker_threads: Some(24),
        cycles_bound: None,
        ..ProgramProverConfig::default()
    }
}

fn deterministic_pow_required() {
    if !cfg!(feature = "deterministic_pow") {
        panic!("L1 reference requires deterministic_pow");
    }
}

fn preflight(stage: &str, required_gib: u64) {
    let meminfo =
        fs::read_to_string("/proc/meminfo").expect("L1 reference preflight reads /proc/meminfo");
    let available = meminfo
        .lines()
        .find_map(|line| {
            line.strip_prefix("MemAvailable:")?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
        .expect("L1 reference preflight finds MemAvailable");
    println!("preflight stage={stage} memavailable_kib={available} required_gib={required_gib}");
    assert!(
        available >= required_gib * 1024 * 1024,
        "L1 reference preflight {stage}: MemAvailable {available} KiB is below {required_gib} GiB"
    );
}

fn start_stage() -> Instant {
    fs::write("/proc/self/clear_refs", "5").expect("L1 reference resets VmHWM before each stage");
    Instant::now()
}

fn vmhwm_kib() -> u64 {
    let process_status =
        fs::read_to_string("/proc/self/status").expect("L1 reference reads /proc/self/status");
    process_status
        .lines()
        .find_map(|line| {
            line.strip_prefix("VmHWM:")?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
        .expect("L1 reference finds VmHWM")
}

fn log_stage_with_peak(stage: &str, start: Instant, vmhwm: u64) {
    MAX_STAGE_VMHWM.fetch_max(vmhwm, Ordering::Relaxed);
    println!(
        "stage={stage} wall_ms={} vmhwm_kib={vmhwm} vmhwm_scope=stage worker_threads=24",
        elapsed_ms(start)
    );
}

fn log_stage(stage: &str, start: Instant) -> u64 {
    let vmhwm = vmhwm_kib();
    log_stage_with_peak(stage, start, vmhwm);
    vmhwm
}

struct FixtureObserver<'a> {
    sink: &'a Path,
    layers: Vec<u8>,
    started: Instant,
    peak_vmhwm_kib: u64,
}

impl FeederObserver for FixtureObserver<'_> {
    fn feeder_layer(
        &mut self,
        layer: u8,
        state: &RecursionState,
        report: &FsvRunReport,
    ) -> Result<(), String> {
        if layer as usize != self.layers.len() {
            return Err("L1 reference feeder observer layer order".into());
        }
        self.layers.push(layer);
        write_compact(
            &self.sink.join(feeder_checkpoint_name(layer)),
            &StepCheckpoint::from_state(layer, state),
        )?;
        write_compact(&self.sink.join(feeder_report_name(layer)), report)?;
        self.peak_vmhwm_kib = self
            .peak_vmhwm_kib
            .max(log_stage(&format!("feeder_layer_{layer}"), self.started));
        self.started = start_stage();
        Ok(())
    }
}

enum GenerateFrom<'a> {
    Program,
    RecursionUnified(&'a Path),
    /// A feeder-layer checkpoint: the rest of the feeder chain.
    FeederLayer(&'a Path),
    L1Feeder(&'a Path),
}

fn generate_into(sink: &Path, from: GenerateFrom<'_>) -> Result<Inventory, String> {
    deterministic_pow_required();
    fs::create_dir_all(sink).map_err(|error| format!("L1 reference sink: {error}"))?;
    let source = source();
    let names = match from {
        GenerateFrom::Program => {
            preflight("program", 125);
            let loaded = load_program(&source)?;
            let blake = PipelineBlakeModes::from_env();
            let identities = fsv_identities(blake)?;
            let start = start_stage();
            let base = {
                let mut prover = ProgramProver::new(source.clone(), config(ProofTarget::Base))?;
                prover.prove_words(0, vec![])?
            };
            log_stage("base", start);
            let start = start_stage();
            let mut artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::RecursionUnified),
                    &base,
                )?;
                prover.continue_artifact(base)?
            };
            log_stage("recursion_unified", start);
            artifact.timings_ms = ProofTimingsMs::default();
            write_compact(&sink.join("recursion_unified.json"), &artifact)?;
            drop(artifact);
            let feeder = generate_into(
                sink,
                GenerateFrom::RecursionUnified(&sink.join("recursion_unified.json")),
            )?;
            let wrap = generate_into(sink, GenerateFrom::L1Feeder(&sink.join("l1_feeder.json")))?;
            let files: Inventory = std::iter::once(file_identity(sink, "recursion_unified.json")?)
                .chain(feeder)
                .chain(wrap)
                .collect();
            let mut names: Vec<String> = files.iter().map(|file| file.name.clone()).collect();
            write_compact(
                &sink.join("manifest.json"),
                &ProofManifest {
                    format_version: 1,
                    program: ProgramIdentity {
                        bin_keccak256: hex_digest(&loaded.bin_bytes),
                        text_keccak256: hex_digest(&loaded.text_bytes),
                    },
                    fsv: identities,
                    configuration: ReferenceConfiguration {
                        security_level: COMPILED_SECURITY_LEVEL,
                        backend: ProverBackend::Cpu,
                        worker_threads: 24,
                        batch_id: 0,
                        blake_unrolled: blake.unrolled.tag().into(),
                        blake_bridge: blake.bridge.tag().into(),
                        blake_final: blake.final_layer.tag().into(),
                        user_nd_words: vec![],
                    },
                    files,
                },
            )?;
            names.push("manifest.json".into());
            names
        }
        GenerateFrom::RecursionUnified(input) => {
            preflight("feeder", 75);
            let artifact: ProofArtifact = read_typed(input)?;
            if artifact.target != ProofTarget::RecursionUnified
                || artifact.batch_id != 0
                || artifact.backend != ProverBackend::Cpu
            {
                return Err(
                    "L1 reference requires the CPU recursion-unified checkpoint at batch_id 0"
                        .into(),
                );
            }
            let start = start_stage();
            let mut observer = FixtureObserver {
                sink,
                layers: vec![],
                started: start,
                peak_vmhwm_kib: 0,
            };
            let mut artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::L1Feeder),
                    &artifact,
                )?;
                prover.continue_artifact_observed(artifact, &mut observer)?
            };
            if observer.layers.is_empty()
                || observer.layers.len() != artifact.feeder_layers as usize
            {
                return Err(format!(
                    "L1 reference observed feeder layers {:?} for a {}-layer chain",
                    observer.layers, artifact.feeder_layers
                ));
            }
            log_stage_with_peak("feeder", start, observer.peak_vmhwm_kib.max(vmhwm_kib()));
            artifact.timings_ms = ProofTimingsMs::default();
            write_compact(&sink.join("l1_feeder.json"), &artifact)?;
            observer
                .layers
                .iter()
                .flat_map(|&layer| [feeder_checkpoint_name(layer), feeder_report_name(layer)])
                .chain(["l1_feeder.json".to_string()])
                .collect()
        }
        GenerateFrom::FeederLayer(input) => {
            preflight("feeder_resume", 75);
            let manifest: ProofManifest = read_typed(
                &input
                    .parent()
                    .ok_or("L1 reference checkpoint parent")?
                    .join("manifest.json"),
            )?;
            let loaded = load_program(&source)?;
            if manifest.format_version != 1
                || manifest.configuration.security_level != COMPILED_SECURITY_LEVEL
                || manifest.configuration.backend != ProverBackend::Cpu
                || manifest.configuration.batch_id != 0
                || manifest.configuration.worker_threads != 24
                || !manifest.configuration.user_nd_words.is_empty()
                || manifest.program.bin_keccak256 != hex_digest(&loaded.bin_bytes)
                || manifest.program.text_keccak256 != hex_digest(&loaded.text_bytes)
            {
                return Err(
                    "L1 reference feeder checkpoint manifest configuration or program mismatch"
                        .into(),
                );
            }
            let blake = PipelineBlakeModes {
                unrolled: parse_blake_tag(
                    &manifest.configuration.blake_unrolled,
                    FsvProgram::UnrolledBaseLayer,
                )?,
                bridge: parse_blake_tag(
                    &manifest.configuration.blake_bridge,
                    FsvProgram::UnrolledBaseLayer,
                )?,
                final_layer: parse_blake_tag(
                    &manifest.configuration.blake_final,
                    FsvProgram::UnifiedRecursionLayer,
                )?,
            };
            if serde_json::to_vec(&fsv_identities(blake)?).unwrap()
                != serde_json::to_vec(&manifest.fsv).unwrap()
            {
                return Err("L1 reference feeder checkpoint fsv identity mismatch".into());
            }
            let checkpoint: StepCheckpoint = read_typed(input)?;
            let mut state = checkpoint.into_state()?;
            let start = start_stage();
            let fsv = FsvPrograms::load(ProofTarget::L1Feeder, blake);
            {
                let mut backend = PipelineBackend::<cpu_execution_prover::CpuBackend>::new(
                    &config(ProofTarget::L1Feeder),
                );
                let spec = feeder_stage(FeederRole::Recurrent);
                let (bin, text) = fsv.feeder_program(FeederRole::Recurrent);
                backend.register(
                    spec.kind,
                    MachineType::Reduced,
                    bin,
                    text,
                    None,
                    &[spec.profile],
                );
                state = run_feeder_layers(
                    &mut backend,
                    &fsv,
                    state,
                    0,
                    &mut NoopObserver,
                    &build_unified_stream,
                    &ProductionFeederVerifier,
                )?;
                state = check_feeder_fit(
                    &fsv,
                    state,
                    &build_unified_stream,
                    &ProductionFeederVerifier,
                )?;
            }
            log_stage("feeder_resume", start);
            let mut artifact = finalize_artifact(
                &fsv,
                ProofTarget::L1Feeder,
                ProverBackend::Cpu,
                0,
                &loaded,
                state,
            );
            artifact.timings_ms = ProofTimingsMs::default();
            write_compact(&sink.join("l1_feeder.json"), &artifact)?;
            vec!["l1_feeder.json".to_string()]
        }
        GenerateFrom::L1Feeder(input) => {
            preflight("wrap", 60);
            let artifact: ProofArtifact = read_typed(input)?;
            if artifact.target != ProofTarget::L1Feeder
                || artifact.batch_id != 0
                || artifact.backend != ProverBackend::Cpu
            {
                return Err(
                    "L1 reference requires the CPU L1-feeder checkpoint at batch_id 0".into(),
                );
            }
            let start = start_stage();
            let artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::L1),
                    &artifact,
                )?;
                prover.continue_artifact(artifact)?
            };
            verify_artifact(&artifact, &source)?;
            log_stage("wrap", start);
            write_compact(
                &sink.join("l1_bundle.json"),
                artifact
                    .l1
                    .as_ref()
                    .ok_or("L1 reference missing wrap bundle")?,
            )?;
            vec!["l1_bundle.json".to_string()]
        }
    };
    let inventory: Inventory = names
        .into_iter()
        .map(|name| file_identity(sink, &name))
        .collect::<Result<_, _>>()?;
    for file in &inventory {
        println!(
            "fixture={} bytes={} keccak256={}",
            file.name, file.bytes, file.keccak256
        );
    }
    println!(
        "reference_max_stage_vmhwm_kib={} gnu_time_maxrss_scope=affected_by_stage_resets",
        MAX_STAGE_VMHWM.load(Ordering::Relaxed)
    );
    Ok(inventory)
}

fn disposable_dir(purpose: &str) -> PathBuf {
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../target"));
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("L1 reference staging clock")
        .as_nanos();
    target
        .join("l1_reference_staging")
        .join(format!("{purpose}-{}-{nonce}", std::process::id()))
}

fn typed_first_difference(name: &str, expected: &[u8], actual: &[u8]) -> Option<String> {
    macro_rules! fields {
        ($ty:ty; $($field:ident),+ $(,)?) => {{
            let expected: $ty = serde_json::from_slice(expected).ok()?;
            let actual: $ty = serde_json::from_slice(actual).ok()?;
            $(if serde_json::to_vec(&expected.$field).ok()? != serde_json::to_vec(&actual.$field).ok()? {
                return Some(stringify!($field).into());
            })+
            Some("serialized encoding".into())
        }};
    }
    match name {
        "recursion_unified.json" | "l1_feeder.json" => fields!(ProofArtifact;
            schema_version, security_level, target, backend, batch_id, cycles, program_cycles,
            program_bin_keccak, program_text_keccak, timings_ms, proof_counts, chain_end_params,
            chain_hash, chain_preimage, blake_unrolled, blake_bridge, blake_final, l1, proof, setups),
        name if name.starts_with("feeder_layer_") && name.ends_with("_report.json") => {
            fields!(FsvRunReport; cycles, output, nd_words_remaining, touched_windows,
            max_touched_address)
        }
        name if name.starts_with("feeder_layer_") => {
            fields!(StepCheckpoint; fixture_schema_version, step, proof, setups,
            chain_end_params, input_is_base, program_cycles)
        }
        "l1_bundle.json" => fields!(L1Bundle; wrap, commitment_mode, proof),
        "manifest.json" => {
            fields!(ProofManifest; format_version, program, fsv, configuration, files)
        }
        _ => None,
    }
}

fn compare_files(reference: &Path, sink: &Path, inventory: &Inventory) -> Result<(), String> {
    for file in inventory {
        let expected = read_bytes(&reference.join(&file.name))?;
        let actual = read_bytes(&sink.join(&file.name))?;
        if expected != actual {
            let offset = expected
                .iter()
                .zip(&actual)
                .position(|(a, b)| a != b)
                .unwrap_or(expected.len().min(actual.len()));
            let context = |bytes: &[u8]| {
                let start = offset.saturating_sub(40).min(bytes.len());
                String::from_utf8_lossy(&bytes[start..(start + 80).min(bytes.len())]).into_owned()
            };
            return Err(format!("L1 reference mismatch {} at byte {offset}, field {}; expected {:?}, actual {:?}; regenerate: {REGENERATE}",
                file.name, typed_first_difference(&file.name, &expected, &actual).unwrap_or_else(|| "unavailable (deserialize failed)".into()),
                context(&expected), context(&actual)));
        }
    }
    Ok(())
}

fn guard(from: GenerateFrom<'_>) {
    let reference = fixture_dir();
    let sink = disposable_dir("guard");
    let inventory = generate_into(&sink, from).expect("L1 reference guard regeneration");
    compare_files(&reference, &sink, &inventory).unwrap_or_else(|message| panic!("{message}"));
    fs::remove_dir_all(sink).expect("L1 reference guard removes disposable sink");
}

#[test]
#[ignore = "regenerates the committed L1 reference: ~35 min CPU (historical), up to ~110 GiB"]
fn generate_l1_reference() {
    let sink = disposable_dir("generate");
    let inventory = generate_into(&sink, GenerateFrom::Program).expect("L1 reference generation");
    let reference = fixture_dir();
    fs::create_dir_all(&reference).expect("L1 reference creates fixture directory");
    for file in &inventory {
        fs::rename(sink.join(&file.name), reference.join(&file.name))
            .expect("L1 reference promotes complete fixture set");
    }
    fs::remove_dir_all(sink).expect("L1 reference removes staging directory");
}

#[test]
#[ignore = "regenerates the full CPU L1 reference chain"]
fn committed_l1_reference_is_current() {
    guard(GenerateFrom::Program);
}

#[test]
#[ignore = "regenerates both CPU feeder layers"]
fn committed_l1_feeder_reference_is_current() {
    guard(GenerateFrom::RecursionUnified(
        &fixture_dir().join("recursion_unified.json"),
    ));
}

/// Resumes the feeder chain from the first committed checkpoint whose proof
/// still has more than one instance and regenerates the rest of it.
#[test]
#[ignore = "regenerates the CPU feeder layers after the first multi-instance checkpoint"]
fn committed_l1_feeder_mid_chain_resume_is_current() {
    let reference = fixture_dir();
    let checkpoint = (0..MAX_FEEDER_LAYERS as u8)
        .map(|layer| reference.join(feeder_checkpoint_name(layer)))
        .take_while(|path| path.exists())
        .find(|path| {
            let checkpoint: StepCheckpoint = read_typed(path).expect("feeder checkpoint");
            feeder_proof_instances(&checkpoint.proof, None).expect("feeder checkpoint proof") > 1
        })
        .expect("the L1 reference has a multi-instance feeder checkpoint");
    println!("resuming from {}", checkpoint.display());
    guard(GenerateFrom::FeederLayer(&checkpoint));
}

#[test]
#[ignore = "regenerates the CPU L1 wrap"]
fn committed_l1_wrap_reference_is_current() {
    guard(GenerateFrom::L1Feeder(
        &fixture_dir().join("l1_feeder.json"),
    ));
}

/// The proof and commitment-mode fixtures verifier_evm's 2p21 version
/// reads: the committed reference wrap bundle, serialized as the prover's
/// fixture writer does.
fn evm_fixtures() -> [(PathBuf, Vec<u8>); 2] {
    let bundle: L1Bundle =
        read_typed(&fixture_dir().join("l1_bundle.json")).expect("committed L1 wrap bundle");
    bundle.validate().expect("committed L1 wrap bundle");
    assert_eq!(bundle.wrap, L1WrapVersion::Wrap2p21);
    let prover = Path::new(env!("CARGO_MANIFEST_DIR")).join("../prover");
    [
        (
            prover.join("unified_circuit_proof_proth120_2p21.json"),
            serde_json::to_vec_pretty(&bundle.proof).unwrap(),
        ),
        (
            prover.join("unified_circuit_proof_proth120_2p21_commitment_mod_aux_data.json"),
            serde_json::to_vec_pretty(&bundle.commitment_mode).unwrap(),
        ),
    ]
}

#[test]
#[ignore = "writes the verifier_evm 2p21 proof fixtures from the committed L1 reference"]
fn export_l1_wrap_evm_fixtures() {
    for (path, bytes) in evm_fixtures() {
        fs::write(&path, bytes).expect("writes the EVM proof fixture");
        println!("wrote {}", path.display());
    }
}

#[test]
#[ignore = "reads the committed L1 reference"]
fn committed_l1_wrap_evm_fixtures_are_current() {
    for (path, bytes) in evm_fixtures() {
        assert!(
            read_bytes(&path).expect("committed EVM proof fixture") == bytes,
            "{} differs from the L1 reference bundle; regenerate: cargo test -p prover_pipeline --release --lib l1_reference::export_l1_wrap_evm_fixtures -- --exact --ignored",
            path.display()
        );
    }
}

fn empty_proof(final_pc: u32) -> ProgramProof {
    ProgramProof {
        riscv_proofs: BTreeMap::new(),
        compiled_riscv_circuits: BTreeMap::new(),
        inits_and_teardown_proofs: vec![],
        inits_and_teardowns_circuit: None,
        delegation_proofs: BTreeMap::new(),
        compiled_delegation_circuits: BTreeMap::new(),
        register_final_values: vec![],
        final_pc,
        final_timestamp: prover::common_constants::INITIAL_TIMESTAMP,
        end_params: [0; 8],
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
        pow_challenge: 0,
        num_it_circuits: None,
    }
}

fn test_state() -> RecursionState {
    let mut proof = empty_proof(0);
    let chain = rebuild_chain(&[[1; 8], [2; 8], [3; 8]]).unwrap();
    proof.set_recursion_chain(&chain);
    RecursionState {
        stage: ProofTarget::RecursionUnified,
        l1: None,
        proof,
        setups: BTreeMap::new(),
        chain_end_params: vec![[1; 8], [2; 8], [3; 8]],
        input_is_base: false,
        timings: ProofTimingsMs::default(),
        program_cycles: 123,
        feeder_layers: 0,
    }
}

/// The first fake feeder layer (program word 1) verifies into two
/// instances, the second (program word 2) into one: the loop runs F1 then
/// one recurrent layer. Proofs are verified against the chain their own
/// preimage records, extended by their end params ([`fake_nd`]).
struct FakeVerifier;

impl FeederVerifier for FakeVerifier {
    fn native_verify_standard(&self, nd_words: Vec<u32>) -> Result<[u32; 16], String> {
        self.native_verify(nd_words)
    }

    fn predict(&self, program: &ProgramWords, nd_words: Vec<u32>) -> Result<FsvRunReport, String> {
        let mut report = fake_report(fake_instances(program.0[0]));
        report.output = self.native_verify(nd_words)?;
        Ok(report)
    }

    fn native_verify(&self, nd_words: Vec<u32>) -> Result<[u32; 16], String> {
        let mut output = [0u32; 16];
        output[8..].copy_from_slice(&nd_words[..8]);
        Ok(output)
    }

    fn wrap_run(&self, _: &ProgramWords, _: Vec<u32>) -> Result<FsvRunReport, String> {
        panic!("feeder seam tests must not run the wrap program");
    }
}

fn fake_instances(program_word: u32) -> u64 {
    match program_word {
        1 => 2,
        2 => 1,
        other => panic!("unknown fake feeder program {other}"),
    }
}

fn fake_report(instances: u64) -> FsvRunReport {
    FsvRunReport {
        cycles: instances * UnrolledCircuitType::Unified22.get_domain_size() as u64 - 1,
        output: [0; 16],
        nd_words_remaining: 0,
        counters: riscv_transpiler::vm::DelegationsAndUnifiedCounters {
            cycles: (instances * UnrolledCircuitType::Unified22.get_domain_size() as u64 - 1)
                as usize,
            ..Default::default()
        },
        touched_windows: vec![0, 1],
        max_touched_address: 0,
        min_sp: 0x87f000,
        success_pc: 0,
        final_pc: 0,
    }
}

/// The stream of a fake proof: the hash of the chain it extends (the fake
/// verifier returns it as the proven chain).
fn fake_nd(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
    let preimage = proof.recursion_chain_preimage.expect("fake proof chain");
    let mut chain = FsvRecursionChain::resume(preimage);
    chain.extend(&compute_end_params(setups, proof.final_pc));
    chain.hash().to_vec()
}

fn test_fsv() -> FsvPrograms {
    let mut fsv = FsvPrograms::load(
        ProofTarget::Base,
        PipelineBlakeModes {
            unrolled: BlakeMode::Compression,
            bridge: BlakeMode::Compression,
            final_layer: BlakeMode::Compression,
        },
    );
    fsv.feeder_first = (vec![1], vec![1]);
    fsv.feeder = (vec![2], vec![2]);
    fsv.feeder_wrap = (vec![3], vec![3]);
    fsv
}

struct FakeBackend;

impl ProveBackend for FakeBackend {
    fn register(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: Option<u32>,
        _: &[ProofProfile],
    ) {
        panic!("feeder seam tests must not register");
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        assert_eq!(request.batch_id, 0);
        assert_eq!(request.kind, ExecutionKind::Unified22);
        assert_eq!(request.machine, MachineType::Reduced);
        assert_eq!(request.profile, ProofProfile::L1Feeder);
        assert_eq!(request.nd_words.len(), 8);
        let program = request.bin[0];
        Ok((
            crate::l1_feeder_tests::fake_feeder_proof(program, fake_instances(program) as usize),
            BTreeMap::new(),
        ))
    }

    fn prove_l1_wrap(&mut self, _: L1WrapRequest<'_>) -> Result<L1WrapResult, String> {
        panic!("feeder seam tests must not wrap");
    }

    fn setups(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: ProofProfile,
    ) -> Option<Setups> {
        panic!("feeder seam tests must not read setups");
    }
}

#[derive(Default)]
struct RecordingObserver {
    checkpoints: Vec<StepCheckpoint>,
}

impl FeederObserver for RecordingObserver {
    fn feeder_layer(
        &mut self,
        layer: u8,
        state: &RecursionState,
        _: &FsvRunReport,
    ) -> Result<(), String> {
        self.checkpoints
            .push(StepCheckpoint::from_state(layer, state));
        Ok(())
    }
}

fn normalized_state(state: RecursionState) -> Vec<u8> {
    serde_json::to_vec(&(
        state.stage,
        state.l1,
        state.proof,
        state.setups,
        state.chain_end_params,
        state.input_is_base,
        ProofTimingsMs::default(),
        state.program_cycles,
        state.feeder_layers,
    ))
    .unwrap()
}

#[test]
fn feeder_observer_sees_first_then_second() {
    let mut observer = RecordingObserver::default();
    run_feeder_layers(
        &mut FakeBackend,
        &test_fsv(),
        test_state(),
        0,
        &mut observer,
        &fake_nd,
        &FakeVerifier,
    )
    .unwrap();
    assert_eq!(observer.checkpoints.len(), 2);
    for (layer, checkpoint) in observer.checkpoints.iter().enumerate() {
        assert!(
            matches!(checkpoint.step, CheckpointStep::Feeder { layer: actual } if actual == layer as u8)
        );
        assert_eq!(checkpoint.feeder_layers, layer as u32 + 1);
        assert_eq!(checkpoint.chain_end_params.len(), layer + 4);
        assert_eq!(checkpoint.proof.final_pc, layer as u32 + 1);
        let prior = rebuild_chain(&checkpoint.chain_end_params[..layer + 3]).unwrap();
        assert_eq!(checkpoint.proof.recursion_chain_hash, Some(prior.hash()));
        assert_eq!(
            checkpoint.proof.recursion_chain_preimage,
            Some(prior.preimage())
        );
    }
}

#[test]
fn noop_observer_matches_unobserved_result() {
    let observed = run_feeder_layers(
        &mut FakeBackend,
        &test_fsv(),
        test_state(),
        0,
        &mut RecordingObserver::default(),
        &fake_nd,
        &FakeVerifier,
    )
    .unwrap();
    let noop = run_feeder_layers(
        &mut FakeBackend,
        &test_fsv(),
        test_state(),
        0,
        &mut NoopObserver,
        &fake_nd,
        &FakeVerifier,
    )
    .unwrap();
    let mut unobserved = test_state();
    let mut chain = rebuild_chain(&unobserved.chain_end_params).unwrap();
    for program in [&test_fsv().feeder_first, &test_fsv().feeder] {
        unobserved = advance_feeder_stage(
            &mut FakeBackend,
            program,
            &mut chain,
            unobserved,
            0,
            &fake_nd,
        )
        .unwrap();
    }
    unobserved.feeder_layers = 2;
    let noop = normalized_state(noop);
    assert_eq!(normalized_state(observed), noop);
    assert_eq!(normalized_state(unobserved), noop);
}

#[test]
fn observer_error_propagates() {
    struct Reject;
    impl FeederObserver for Reject {
        fn feeder_layer(
            &mut self,
            _: u8,
            _: &RecursionState,
            _: &FsvRunReport,
        ) -> Result<(), String> {
            Err("feeder observer rejection".into())
        }
    }
    let result = run_feeder_layers(
        &mut FakeBackend,
        &test_fsv(),
        test_state(),
        0,
        &mut Reject,
        &fake_nd,
        &FakeVerifier,
    );
    assert_eq!(result.err().as_deref(), Some("feeder observer rejection"));
}

#[test]
fn second_layer_helper_matches_loop() {
    let mut observer = RecordingObserver::default();
    let expected = run_feeder_layers(
        &mut FakeBackend,
        &test_fsv(),
        test_state(),
        0,
        &mut observer,
        &fake_nd,
        &FakeVerifier,
    )
    .unwrap();
    let state = observer.checkpoints.remove(0).into_state().unwrap();
    let resumed = run_feeder_layers(
        &mut FakeBackend,
        &test_fsv(),
        state,
        0,
        &mut NoopObserver,
        &fake_nd,
        &FakeVerifier,
    )
    .unwrap();
    assert_eq!(normalized_state(expected), normalized_state(resumed));
}

#[test]
fn guard_reports_first_differing_file() {
    let root = disposable_dir("comparison-test");
    let reference = root.join("reference");
    let sink = root.join("sink");
    fs::create_dir_all(&reference).unwrap();
    fs::create_dir_all(&sink).unwrap();
    let checkpoint = StepCheckpoint::from_state(0, &test_state());
    write_compact(&reference.join("feeder_layer_0.json"), &checkpoint).unwrap();
    let expected = read_bytes(&reference.join("feeder_layer_0.json")).unwrap();
    let mut actual = expected.clone();
    let offset = expected
        .windows(b"\"program_cycles\":123".len())
        .position(|window| window == b"\"program_cycles\":123")
        .unwrap()
        + b"\"program_cycles\":".len();
    actual[offset] = b'2';
    fs::write(sink.join("feeder_layer_0.json"), actual).unwrap();
    let inventory = vec![file_identity(&sink, "feeder_layer_0.json").unwrap()];
    let error = compare_files(&reference, &sink, &inventory).unwrap_err();
    assert!(
        error.contains(&format!("feeder_layer_0.json at byte {offset}")),
        "{error}"
    );
    assert!(error.contains("field program_cycles"), "{error}");
    assert!(error.contains(REGENERATE), "{error}");
    fs::remove_dir_all(root).unwrap();
}
