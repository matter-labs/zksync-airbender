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
/// checkpoint proof is terminal C).
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
            "feeder_a",
            FsvProgram::UnifiedRecursionLayerL1FeederA,
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

// CPU stages keep 40 GiB above the historical 110 GiB program peak
// and the feeder's 96 GiB planning budget.
// The 2026-10-19 run measured 72.80 GiB for Base and 88.79 GiB for RecUnified.
const CPU_PROGRAM_HOST_WINDOW_GIB: u64 = 150;
pub(super) const CPU_FEEDER_HOST_WINDOW_GIB: u64 = 136;
// The measured wrap peak was 37.57 GiB; round to 40 GiB plus the host reserve.
const CPU_WRAP_HOST_WINDOW_GIB: u64 = 80;

/// The CPU execution used by the reference producer.
#[derive(Clone, Copy)]
struct Execution {
    backend: ProverBackend,
}

impl Execution {
    const CPU: Self = Self {
        backend: ProverBackend::Cpu,
    };

    fn admits_input(self, input: ProverBackend) -> bool {
        input == ProverBackend::Cpu || input == self.backend
    }

    fn host_window_gib(self, cpu_gib: u64) -> u64 {
        cpu_gib
    }
}

fn config(target: ProofTarget, execution: Execution) -> ProgramProverConfig {
    ProgramProverConfig {
        target,
        backend: execution.backend,
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
    first_layer: u8,
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
        if layer as usize != self.first_layer as usize + self.layers.len() {
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

fn write_reference_manifest(
    sink: &Path,
    execution: Execution,
    files: Inventory,
    program: ProgramIdentity,
    fsv: Vec<FsvIdentity>,
    blake: PipelineBlakeModes,
) -> Result<Vec<String>, String> {
    let mut names: Vec<String> = files.iter().map(|file| file.name.clone()).collect();
    write_compact(
        &sink.join("manifest.json"),
        &ProofManifest {
            format_version: 1,
            program,
            fsv,
            configuration: ReferenceConfiguration {
                security_level: COMPILED_SECURITY_LEVEL,
                backend: execution.backend,
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
    Ok(names)
}

fn generate_into(
    sink: &Path,
    from: GenerateFrom<'_>,
    execution: Execution,
) -> Result<Inventory, String> {
    deterministic_pow_required();
    fs::create_dir_all(sink).map_err(|error| format!("L1 reference sink: {error}"))?;
    let source = source();
    let names = match from {
        GenerateFrom::Program => {
            preflight(
                "program",
                execution.host_window_gib(CPU_PROGRAM_HOST_WINDOW_GIB),
            );
            let loaded = load_program(&source)?;
            let blake = PipelineBlakeModes::from_env();
            let identities = fsv_identities(blake)?;
            let start = start_stage();
            let base = {
                let mut prover =
                    ProgramProver::new(source.clone(), config(ProofTarget::Base, execution))?;
                prover.prove_words(0, vec![])?
            };
            log_stage("base", start);
            let start = start_stage();
            let mut artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::RecursionUnified, execution),
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
                execution,
            )?;
            let wrap = generate_into(
                sink,
                GenerateFrom::L1Feeder(&sink.join("l1_feeder.json")),
                execution,
            )?;
            let files: Inventory = std::iter::once(file_identity(sink, "recursion_unified.json")?)
                .chain(feeder)
                .chain(wrap)
                .collect();
            write_reference_manifest(
                sink,
                execution,
                files,
                ProgramIdentity {
                    bin_keccak256: hex_digest(&loaded.bin_bytes),
                    text_keccak256: hex_digest(&loaded.text_bytes),
                },
                identities,
                blake,
            )?
        }
        GenerateFrom::RecursionUnified(input) => {
            preflight(
                "feeder",
                execution.host_window_gib(CPU_FEEDER_HOST_WINDOW_GIB),
            );
            let artifact: ProofArtifact = read_typed(input)?;
            if artifact.target != ProofTarget::RecursionUnified
                || artifact.batch_id != 0
                || !execution.admits_input(artifact.backend)
            {
                return Err(
                    "L1 reference requires a CPU or same-backend recursion-unified checkpoint at batch_id 0"
                        .into(),
                );
            }
            let start = start_stage();
            let mut observer = FixtureObserver {
                sink,
                first_layer: 0,
                layers: vec![],
                started: start,
                peak_vmhwm_kib: 0,
            };
            let mut artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::L1Feeder, execution),
                    &artifact,
                )?;
                prover.continue_artifact_observed(artifact, &mut observer)?
            };
            if observer.layers != [0, 1, 2] {
                return Err(
                    "L1 reference requires exactly three feeder observations [0, 1, 2]".into(),
                );
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
            preflight(
                "feeder_resume",
                execution.host_window_gib(CPU_FEEDER_HOST_WINDOW_GIB),
            );
            let manifest: ProofManifest = read_typed(
                &input
                    .parent()
                    .ok_or("L1 reference checkpoint parent")?
                    .join("manifest.json"),
            )?;
            let loaded = load_program(&source)?;
            if manifest.format_version != 1
                || manifest.configuration.security_level != COMPILED_SECURITY_LEVEL
                || !execution.admits_input(manifest.configuration.backend)
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
            let CheckpointStep::Feeder { layer } = &checkpoint.step;
            let first_layer = layer + 1;
            let state = checkpoint.into_state()?;
            let start = start_stage();
            let mut observer = FixtureObserver {
                sink,
                first_layer,
                layers: vec![],
                started: start,
                peak_vmhwm_kib: 0,
            };
            let mut prover = ProgramProver::for_feeder_checkpoint(
                source.clone(),
                config(ProofTarget::L1Feeder, execution),
                blake,
            )?;
            let state = prover.resume_feeder_checkpoint(state, 0, &mut observer)?;
            let state = check_feeder_fit(
                &prover.fsv,
                state,
                &build_unified_stream,
                &ProductionFeederVerifier,
            )?;
            log_stage_with_peak(
                "feeder_resume",
                start,
                observer.peak_vmhwm_kib.max(vmhwm_kib()),
            );
            let mut artifact = prover.finalize_state(&loaded, state, 0);
            artifact.timings_ms = ProofTimingsMs::default();
            write_compact(&sink.join("l1_feeder.json"), &artifact)?;
            observer
                .layers
                .iter()
                .flat_map(|&layer| [feeder_checkpoint_name(layer), feeder_report_name(layer)])
                .chain(["l1_feeder.json".to_string()])
                .collect()
        }
        GenerateFrom::L1Feeder(input) => {
            preflight("wrap", execution.host_window_gib(CPU_WRAP_HOST_WINDOW_GIB));
            let artifact: ProofArtifact = read_typed(input)?;
            if artifact.target != ProofTarget::L1Feeder
                || artifact.batch_id != 0
                || !execution.admits_input(artifact.backend)
            {
                return Err(
                    "L1 reference requires a CPU or same-backend L1-feeder checkpoint at batch_id 0"
                        .into(),
                );
            }
            let start = start_stage();
            let artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::L1, execution),
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
        "l1_bundle.json" => fields!(L1Bundle; wrap, operation_mode, proof),
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

/// `dir`'s manifest, with every listed file's length and hash checked
/// against `dir`'s own copy.
fn validated_manifest(dir: &Path) -> Result<ProofManifest, String> {
    let manifest: ProofManifest = read_typed(&dir.join("manifest.json"))?;
    for file in &manifest.files {
        let actual = file_identity(dir, &file.name)?;
        if actual.bytes != file.bytes || actual.keccak256 != file.keccak256 {
            return Err(format!(
                "L1 reference manifest of {} lists {} with another length or hash",
                dir.display(),
                file.name
            ));
        }
    }
    Ok(manifest)
}

/// Compares a reproduced L1 reference file with the reference's copy as
/// typed values: the whole serialized value after normalizing the fields a
/// GPU reproduction legitimately changes (an artifact's backend and timings),
/// naming the first differing field. Serialized bytes, never
/// `serde_json::Value`: the wrap proof holds integers beyond `u64`.
fn compare_reproduced_file(name: &str, expected: &[u8], actual: &[u8]) -> Result<(), String> {
    fn typed<T: DeserializeOwned>(name: &str, bytes: &[u8]) -> Result<T, String> {
        serde_json::from_slice(bytes)
            .map_err(|error| format!("L1 reference deserialize {name}: {error}"))
    }
    fn json<T: Serialize + ?Sized>(value: &T) -> Vec<u8> {
        serde_json::to_vec(value).expect("L1 reference serializes")
    }
    macro_rules! compare {
        ($ty:ty, [$expected:ident, $actual:ident] => $normalize:block; $($field:ident),+ $(,)?) => {{
            let $expected: $ty = typed(name, expected)?;
            #[allow(unused_mut)]
            let mut $actual: $ty = typed(name, actual)?;
            $normalize
            if json(&$expected) == json(&$actual) {
                return Ok(());
            }
            $(if json(&$expected.$field) != json(&$actual.$field) {
                return Err(format!(
                    "{name} differs from the L1 reference in field {}",
                    stringify!($field)
                ));
            })+
            Err(format!("{name} differs from the L1 reference in its serialized encoding"))
        }};
    }
    match name {
        "recursion_unified.json" | "l1_feeder.json" => compare!(ProofArtifact,
            [expected_artifact, actual_artifact] => {
                actual_artifact.backend = expected_artifact.backend;
                actual_artifact.timings_ms = expected_artifact.timings_ms.clone();
            };
            schema_version, security_level, target, batch_id, cycles, program_cycles,
            program_bin_keccak, program_text_keccak, proof_counts, chain_end_params,
            feeder_layers, chain_hash, chain_preimage, blake_unrolled, blake_bridge, blake_final,
            l1, proof, setups),
        name if name.starts_with("feeder_layer_") && name.ends_with("_report.json") => {
            if typed::<FsvRunReport>(name, expected)?.counters
                != typed::<FsvRunReport>(name, actual)?.counters
            {
                return Err(format!(
                    "{name} differs from the L1 reference in field counters"
                ));
            }
            compare!(FsvRunReport, [expected_report, actual_report] => {};
                cycles, output, nd_words_remaining, touched_windows, max_touched_address, min_sp,
                success_pc, final_pc)
        }
        name if name.starts_with("feeder_layer_") => {
            compare!(StepCheckpoint, [expected_checkpoint, actual_checkpoint] => {};
                fixture_schema_version, step, feeder_layers, proof, setups, chain_end_params,
                input_is_base, program_cycles)
        }
        "l1_bundle.json" => compare!(L1Bundle, [expected_bundle, actual_bundle] => {};
            wrap, operation_mode, proof),
        _ => Err(format!("L1 reference has no typed comparison for {name}")),
    }
}

fn guard(from: GenerateFrom<'_>) {
    let reference = fixture_dir();
    let sink = disposable_dir("guard");
    let inventory =
        generate_into(&sink, from, Execution::CPU).expect("L1 reference guard regeneration");
    compare_files(&reference, &sink, &inventory).unwrap_or_else(|message| panic!("{message}"));
    fs::remove_dir_all(sink).expect("L1 reference guard removes disposable sink");
}

#[test]
#[ignore = "requires 150 GiB for Program, then 136 GiB free in the same process; does not fit this host: use generate_l1_reference_from_recursion_unified"]
fn generate_l1_reference() {
    let sink = disposable_dir("generate");
    let inventory = generate_into(&sink, GenerateFrom::Program, Execution::CPU)
        .expect("L1 reference generation");
    let reference = fixture_dir();
    fs::create_dir_all(&reference).expect("L1 reference creates fixture directory");
    for file in &inventory {
        fs::rename(sink.join(&file.name), reference.join(&file.name))
            .expect("L1 reference promotes complete fixture set");
    }
    fs::remove_dir_all(sink).expect("L1 reference removes staging directory");
}

/// Run in a fresh process after independently reproducing the committed standard seed.
/// The full Program path still needs 136 GiB free after upstream retained state;
/// its single-process regeneration does not fit this host with the 40 GiB reserve.
#[test]
#[ignore = "regenerates CPU feeder+wrap from the committed standard seed; requires a fresh process and 136 GiB"]
fn generate_l1_reference_from_recursion_unified() {
    deterministic_pow_required();
    let reference = fixture_dir();
    let previous = validated_manifest(&reference).expect("committed reference identity");
    assert_eq!(previous.format_version, 1);
    let loaded = load_program(&source()).expect("L1 reference program");
    let program = ProgramIdentity {
        bin_keccak256: hex_digest(&loaded.bin_bytes),
        text_keccak256: hex_digest(&loaded.text_bytes),
    };
    assert_eq!(previous.program.bin_keccak256, program.bin_keccak256);
    assert_eq!(previous.program.text_keccak256, program.text_keccak256);
    let blake = PipelineBlakeModes::from_env();
    assert_eq!(previous.configuration.backend, ProverBackend::Cpu);
    assert_eq!(
        previous.configuration.security_level,
        COMPILED_SECURITY_LEVEL
    );
    assert_eq!(previous.configuration.worker_threads, 24);
    assert_eq!(previous.configuration.batch_id, 0);
    assert!(previous.configuration.user_nd_words.is_empty());
    assert_eq!(previous.configuration.blake_unrolled, blake.unrolled.tag());
    assert_eq!(previous.configuration.blake_bridge, blake.bridge.tag());
    assert_eq!(previous.configuration.blake_final, blake.final_layer.tag());
    let identities = fsv_identities(blake).expect("L1 reference FSV identities");
    let seed = file_identity(&reference, "recursion_unified.json").expect("committed seed");
    let sink = disposable_dir("generate-feeder");
    fs::create_dir_all(&sink).expect("L1 reference staging directory");
    fs::copy(reference.join(&seed.name), sink.join(&seed.name)).expect("stage committed seed");
    let feeder = generate_into(
        &sink,
        GenerateFrom::RecursionUnified(&sink.join(&seed.name)),
        Execution::CPU,
    )
    .expect("L1 reference feeder generation");
    let wrap = generate_into(
        &sink,
        GenerateFrom::L1Feeder(&sink.join("l1_feeder.json")),
        Execution::CPU,
    )
    .expect("L1 reference wrap generation");
    let files = std::iter::once(seed).chain(feeder).chain(wrap).collect();
    let names = write_reference_manifest(&sink, Execution::CPU, files, program, identities, blake)
        .expect("L1 reference manifest");
    for name in names {
        fs::rename(sink.join(&name), reference.join(&name))
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
#[ignore = "regenerates the CPU feeder chain"]
fn committed_l1_feeder_reference_is_current() {
    guard(GenerateFrom::RecursionUnified(
        &fixture_dir().join("recursion_unified.json"),
    ));
}

/// Every nonterminal A checkpoint, including a single A instance.
fn nonterminal_feeder_checkpoints() -> Vec<(PathBuf, u8)> {
    let reference = fixture_dir();
    let checkpoints: Vec<_> = (0..MAX_FEEDER_LAYERS as u8)
        .map(|layer| (reference.join(feeder_checkpoint_name(layer)), layer))
        .take_while(|(path, _)| path.exists())
        .filter(|(path, _)| {
            let checkpoint: StepCheckpoint = read_typed(path).expect("feeder checkpoint");
            validate_feeder_proof(&checkpoint.proof, None).expect("feeder checkpoint profile")
                == FeederProfile::A
        })
        .collect();
    assert!(
        !checkpoints.is_empty(),
        "the L1 reference has no A checkpoint"
    );
    checkpoints
}

#[test]
#[ignore = "regenerates the CPU feeder suffix from every nonterminal A checkpoint"]
fn committed_l1_feeder_mid_chain_resume_is_current() {
    for (checkpoint, _) in nonterminal_feeder_checkpoints() {
        println!("resuming from {}", checkpoint.display());
        guard(GenerateFrom::FeederLayer(&checkpoint));
    }
}

#[derive(Deserialize)]
struct FeederSeedManifest {
    files: Vec<(String, u64, String)>,
}

/// The BabyBear regression guard: the reference's regular recursion output
/// equals the accepted W2/W4 feeder seed of the same program.
#[test]
#[ignore = "reads the W2/W4 feeder seed of basic_fibonacci (AB_F3_REFERENCE_DIR)"]
fn cpu_recursion_unified_matches_feeder_seed() {
    let seed_dir = std::env::var_os("AB_F3_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/l1_feeder_reference")
        })
        .join("basic_fibonacci");
    let name = "recursion_unified.json";
    let seed_manifest: FeederSeedManifest = read_typed(&seed_dir.join("manifest.json"))
        .unwrap_or_else(|error| {
            panic!(
                "feeder seed manifest: {error}; the feeder reference is not committed, generate it: {}",
                super::l1_feeder_reference::REGENERATE
            )
        });
    let (_, bytes, keccak256) = seed_manifest
        .files
        .iter()
        .find(|(file, _, _)| file == name)
        .expect("the feeder seed manifest lists recursion_unified.json");
    let seed = read_bytes(&seed_dir.join(name)).expect("feeder seed");
    assert!(
        seed.len() as u64 == *bytes && hex_digest(&seed) == *keccak256,
        "the feeder seed differs from its manifest"
    );
    validated_manifest(&fixture_dir()).expect("L1 reference manifest");
    let reference = read_bytes(&fixture_dir().join(name)).expect("L1 reference");
    compare_reproduced_file(name, &seed, &reference).unwrap_or_else(|message| panic!("{message}"));
    println!(
        "recursion_unified.json raw bytes equal: {}",
        seed == reference
    );
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
    evm_fixtures_of(
        &bundle,
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../prover"),
    )
}

fn evm_fixtures_of(bundle: &L1Bundle, dir: &Path) -> [(PathBuf, Vec<u8>); 2] {
    bundle.validate().expect("L1 wrap bundle");
    assert_eq!(bundle.wrap, L1WrapVersion::Wrap2p21);
    [
        (
            dir.join("unified_circuit_proof_proth120_2p21.json"),
            serde_json::to_vec_pretty(&bundle.proof).unwrap(),
        ),
        (
            dir.join("unified_circuit_proof_proth120_2p21_commitment_mod_aux_data.json"),
            serde_json::to_vec_pretty(&bundle.operation_mode).unwrap(),
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

/// The same proof and commitment-mode fixtures for another L1 artifact (e.g. a
/// second program's `cli prove --target l1` output), written into a directory
/// of the caller's choice.
#[test]
#[ignore = "writes the 2p21 proof fixtures of the L1 artifact at AB_ALT_L1_ARTIFACT into AB_ALT_L1_OUT_DIR"]
fn export_alt_l1_wrap_evm_fixtures() {
    let artifact = std::env::var_os("AB_ALT_L1_ARTIFACT").expect("AB_ALT_L1_ARTIFACT");
    let out = PathBuf::from(std::env::var_os("AB_ALT_L1_OUT_DIR").expect("AB_ALT_L1_OUT_DIR"));
    let artifact: ProofArtifact = read_typed(Path::new(&artifact)).expect("L1 artifact");
    let bundle = artifact.l1.expect("the artifact carries an L1 bundle");
    fs::create_dir_all(&out).expect("creates the output directory");
    for (path, bytes) in evm_fixtures_of(&bundle, &out) {
        fs::write(&path, bytes).expect("writes the EVM proof fixture");
        println!("wrote {}", path.display());
    }
}

/// Setup-tree level the verifier's pinned setup frontier holds (the cap is level 3).
const SETUP_FRONTIER_LEVEL: usize = 9;

/// Recommits the L1 wrap setup (setup only, no proof), checks its cap against the committed
/// reference wrap proof, and writes the `2^SETUP_FRONTIER_LEVEL` setup-tree nodes at that
/// level, in physical order, for the verifier_evm setup frontier.
#[test]
#[ignore = "recommits the L1 wrap setup (about a minute of CPU) and writes the verifier_evm setup frontier"]
fn export_l1_wrap_setup_frontier() {
    use ::prover::field::Proth120;
    use ::prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
    use ::prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
    use ::prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
    use ::prover::merkle_trees::PathQueryable;
    use ::prover::worker::Worker;

    let bundle: L1Bundle =
        read_typed(&fixture_dir().join("l1_bundle.json")).expect("committed L1 wrap bundle");
    bundle.validate().expect("committed L1 wrap bundle");
    let setup_commitment = &bundle.proof.whir_proof.setup_commitment;

    let circuit_type = CircuitType::L1Wrap21;
    let (mut binary, mut text) = full_statement_verifier::host_utils::load_fsv_program(
        fsv_dir(),
        FsvProgram::UnifiedRecursionLayerL1FeederWrap,
        BlakeMode::BlakeSpecialOpcodes,
    );
    setups::pad_bytecode_for_proving_with_rom(&mut binary, circuit_type.rom());
    setups::pad_bytecode_for_proving_with_rom(&mut text, circuit_type.rom());
    let setup = unified_reduced_machine_proth120::l1_wrap_2p21::l1_wrap_setup(&binary, &text);
    let config = execution_prover::config::prover_config(
        circuit_type,
        ProofProfile::L1Wrap,
        ::prover::definitions::SecurityLevel::Sec100,
    );
    let pack_log2 = config.pack_log2;
    let worker = Worker::new();
    let twiddles = ::prover::fft::Twiddles::new(1 << (config.trace_len_log2 + pack_log2), &worker);
    let inputs: Vec<&[Proth120]> = setup
        .setup
        .hypercube_evals
        .iter()
        .map(|column| &column[..])
        .collect();
    let (commitment, frontier) =
        CosetByCosetBaseCommitment::<Proth120, Keccak256MerkleTreeWithCap>::commit_packed_with_level_nodes(
            &inputs,
            &twiddles,
            config.lde_factor,
            config.base_oracles_values_per_leaf.trailing_zeros() as usize,
            config.cap_size,
            config.trace_len_log2,
            pack_log2,
            SETUP_FRONTIER_LEVEL,
            &worker,
        );
    let cap = setup_commitment.commitment.cap.cap.clone();
    assert_eq!(
        commitment.get_cap().cap,
        cap,
        "recommitted setup differs from the reference proof's setup cap"
    );
    assert_eq!(
        <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<Proth120>>::build_over_leaf_hashes(
            frontier.clone(),
            config.cap_size,
            &worker,
        )
            .get_cap()
            .cap,
        cap,
        "the frontier does not reduce to the setup cap"
    );
    // every opened setup path reaches the frontier: hash the leaf (BE16 values, column-major)
    // and walk its lower siblings to the frontier level, where its node and sibling must be
    // frontier entries
    let digest_bytes =
        <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<Proth120>>::DIGEST_BYTES;
    let hash = |bytes: &[u8]| -> [u32; 8] {
        let mut out: [u8; 32] = Keccak256::digest(bytes).into();
        out[digest_bytes..].fill(0);
        std::array::from_fn(|i| u32::from_be_bytes(out[4 * i..4 * i + 4].try_into().unwrap()))
    };
    let be = |d: &[u32; 8]| -> Vec<u8> { d.iter().flat_map(|w| w.to_be_bytes()).collect() };
    let cap_log2 = config.cap_size.trailing_zeros() as usize;
    let height = setup_commitment.queries[0].path.len() - (SETUP_FRONTIER_LEVEL - cap_log2);
    let columns = setup_commitment.num_columns;
    for query in setup_commitment.queries.iter() {
        assert_eq!(query.path.len(), height + SETUP_FRONTIER_LEVEL - cap_log2);
        let values = &query.leaf_values_concatenated;
        let per_column = values.len() / columns;
        let leaf: Vec<u8> = (0..columns)
            .flat_map(|c| (0..per_column).map(move |o| values[o * columns + c]))
            .flat_map(|v| v.to_u128().to_be_bytes())
            .collect();
        let mut node = hash(&leaf);
        let mut index = query.index;
        for sibling in &query.path[..height] {
            let (left, right) = if index & 1 == 0 {
                (node, *sibling)
            } else {
                (*sibling, node)
            };
            node = hash(&[be(&left), be(&right)].concat());
            index >>= 1;
        }
        assert_eq!(
            node, frontier[index],
            "setup query {} does not reach its frontier node",
            query.index
        );
        assert_eq!(
            query.path[height],
            frontier[index ^ 1],
            "setup query {} misses the frontier sibling",
            query.index
        );
    }
    let digests: Vec<String> = frontier
        .iter()
        .map(|d| d.iter().map(|w| format!("{w:08x}")).collect())
        .collect();
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../verifier_evm/debug_data/l1_wrap_2p21/setup_frontier.json");
    fs::write(
        &path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&serde_json::json!({
                "level": SETUP_FRONTIER_LEVEL,
                "cap_size": config.cap_size,
                "digests": digests,
            }))
            .unwrap()
        ),
    )
    .expect("writes the setup frontier");
    println!("wrote {} ({} digests)", path.display(), frontier.len());
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

/// The first fake feeder layer (program word 1) needs one A instance;
/// the second (program word 2) fits one C instance. The loop runs F1 then
/// one recurrent layer. Proofs are verified against the chain their own
/// preimage records, extended by their end params ([`fake_nd`]).
struct FakeVerifier;

impl FeederVerifier for FakeVerifier {
    fn native_verify_standard(&self, nd_words: Vec<u32>) -> Result<[u32; 16], String> {
        self.native_verify(FeederProfile::C, nd_words)
    }

    fn predict(&self, program: &ProgramWords, nd_words: Vec<u32>) -> Result<FsvRunReport, String> {
        let mut report = fake_report(fake_instances(program.0[0]));
        report.output = self.native_verify(FeederProfile::C, nd_words)?;
        Ok(report)
    }

    fn native_verify(&self, _: FeederProfile, nd_words: Vec<u32>) -> Result<[u32; 16], String> {
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
    fsv.feeder_a = (vec![2], vec![2]);
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
        let program = request.bin[0];
        let profile = if program == 1 {
            FeederProfile::A
        } else {
            FeederProfile::C
        };
        assert_eq!(request.kind, profile.kind());
        assert_eq!(request.machine, MachineType::Reduced);
        assert_eq!(request.profile, profile.proof_profile());
        assert_eq!(request.nd_words.len(), 8);
        Ok((
            crate::l1_feeder_tests::fake_feeder_proof_for_profile(program, 1, profile),
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
    for (program, profile) in [
        (&test_fsv().feeder_first, FeederProfile::A),
        (&test_fsv().feeder_a, FeederProfile::C),
    ] {
        unobserved = advance_feeder_stage(
            &mut FakeBackend,
            program,
            profile,
            &mut chain,
            unobserved,
            0,
            &fake_nd,
        )
        .unwrap()
        .0;
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

#[test]
fn cpu_l1_feeder_profiles_and_capacity_margins() {
    let reference = fixture_dir();
    validated_manifest(&reference).expect("L1 reference manifest");
    for (layer, profile, instances, cycles, spare) in [
        (0, FeederProfile::A, 2, 16_100_762, 676_454),
        (1, FeederProfile::A, 1, 5_896_748, 2_491_860),
        (2, FeederProfile::C, 1, 2_959_131, 1_235_173),
    ] {
        let checkpoint: StepCheckpoint =
            read_typed(&reference.join(feeder_checkpoint_name(layer))).expect("feeder checkpoint");
        assert_eq!(
            validate_feeder_proof(&checkpoint.proof, Some(instances)).unwrap(),
            profile
        );
        setups::validate_setups_cap_size(&checkpoint.setups, profile.cap_size()).unwrap();
        let report: FsvRunReport = read_typed(&reference.join(feeder_report_name(layer)))
            .expect("feeder prediction report");
        assert_eq!(report.cycles, cycles, "feeder layer {layer} cycles");
        assert_eq!(report.nd_words_remaining, 0);
        assert_eq!(
            predicted_feeder_shape(&report).unwrap(),
            (profile, instances)
        );
        assert_eq!(
            instances as u64 * profile.circuit().get_domain_size() as u64 - report.cycles,
            spare
        );
    }
    assert_eq!(
        nonterminal_feeder_checkpoints()
            .iter()
            .map(|(_, layer)| *layer)
            .collect::<Vec<_>>(),
        [0, 1]
    );
    let artifact: ProofArtifact =
        read_typed(&reference.join("l1_feeder.json")).expect("terminal feeder artifact");
    assert_eq!(artifact.feeder_layers, 3);
    let stream = build_unified_stream(&artifact.setups, &artifact.proof);
    let output = FeederProfile::C.native_verify(stream.clone()).unwrap();
    let program = load_fsv_program(
        fsv_dir(),
        FsvProgram::UnifiedRecursionLayerL1FeederWrap,
        BlakeMode::BlakeSpecialOpcodes,
    );
    let report = observe_wrap_program(&program, stream).unwrap();
    validate_wrap_report(&report, &output).unwrap();
    assert_eq!(report.cycles, 2_042_763);
    assert_eq!(L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - report.cycles, 54_389);
}

#[test]
fn cpu_native_feeder_a_accepts_a_valid_stream_and_rejects_trailing_words() {
    let checkpoint: StepCheckpoint =
        read_typed(&fixture_dir().join(feeder_checkpoint_name(0))).expect("profile-A checkpoint");
    assert_eq!(
        validate_feeder_proof(&checkpoint.proof, Some(2)).unwrap(),
        FeederProfile::A
    );
    let mut stream = build_unified_stream(&checkpoint.setups, &checkpoint.proof);
    let output = FeederProfile::A
        .native_verify(stream.clone())
        .expect("valid A stream");
    ensure_recursion_chain_binds_program(
        &output,
        &rebuild_chain(&checkpoint.chain_end_params).unwrap().hash(),
    )
    .expect("A proof authenticates its checkpoint history");
    stream.push(0);
    let error = FeederProfile::A.native_verify(stream).unwrap_err();
    assert!(error.contains("1 trailing words"), "{error}");
}

#[test]
#[ignore = "measures trusted feeder continuation admission on the committed reference"]
fn cpu_l1_feeder_continuation_admission_cost() {
    preflight("continuation_admission", 64);
    validated_manifest(&fixture_dir()).expect("L1 reference manifest");
    let artifact: ProofArtifact =
        read_typed(&fixture_dir().join("l1_feeder.json")).expect("terminal feeder artifact");
    let source = source();
    let start = Instant::now();
    admit_continuation(&artifact, &source, ProofTarget::L1).expect("trusted continuation");
    println!(
        "s9-continuation-admission wall_us={} vmhwm_kib={}",
        start.elapsed().as_micros(),
        vmhwm_kib()
    );
}

/// The wrap bundle's proof integers exceed `u64`: a one-unit change in one of
/// them is a proof difference, not a lossy-equal value.
#[test]
fn cpu_typed_comparator_compares_wrap_proof_integers_exactly() {
    let name = "l1_bundle.json";
    let bundle = read_bytes(&fixture_dir().join(name)).expect("L1 reference bundle");
    compare_reproduced_file(name, &bundle, &bundle).unwrap();
    let text = String::from_utf8(bundle.clone()).unwrap();
    let start = text
        .char_indices()
        .find(|&(index, _)| {
            text[index..]
                .split(|c: char| !c.is_ascii_digit())
                .next()
                .is_some_and(|digits| {
                    digits.len() >= 21 && digits.parse::<u128>().is_ok_and(|v| v > u64::MAX.into())
                })
                && !text[..index].ends_with(|c: char| c.is_ascii_digit())
        })
        .map(|(index, _)| index)
        .expect("the wrap proof holds an integer beyond u64");
    let digits = text[start..]
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .unwrap();
    let changed = (digits.parse::<u128>().unwrap() - 1).to_string();
    let mutated = format!(
        "{}{changed}{}",
        &text[..start],
        &text[start + digits.len()..]
    );
    assert_eq!(
        compare_reproduced_file(name, &bundle, mutated.as_bytes()),
        Err(format!(
            "{name} differs from the L1 reference in field proof"
        ))
    );
}

#[test]
fn cpu_typed_comparator_ignores_backend_and_timings() {
    let expected = crate::l1_feeder_tests::artifact(ProofTarget::RecursionUnified, 1);
    let mut actual = expected.clone();
    actual.backend = ProverBackend::Gpu;
    actual.timings_ms.total_ms += 1;
    compare_reproduced_file(
        "recursion_unified.json",
        &serde_json::to_vec(&expected).unwrap(),
        &serde_json::to_vec(&actual).unwrap(),
    )
    .unwrap();
}

#[test]
fn cpu_typed_comparator_rejects_field_differences() {
    let expected = StepCheckpoint::from_state(0, &test_state());
    let mut actual = expected.clone();
    actual.program_cycles += 1;
    let error = compare_reproduced_file(
        "feeder_layer_0.json",
        &serde_json::to_vec(&expected).unwrap(),
        &serde_json::to_vec(&actual).unwrap(),
    )
    .unwrap_err();
    assert_eq!(
        error,
        "feeder_layer_0.json differs from the L1 reference in field program_cycles"
    );
}
