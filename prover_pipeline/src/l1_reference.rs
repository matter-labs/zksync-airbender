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

/// The host window a GPU reference run needs (decision O8).
const GPU_HOST_WINDOW_GIB: u64 = 64;

/// The backend the reference producer proves on. Reference inputs keep their
/// CPU provenance: a CPU-produced seed, checkpoint or manifest is valid input
/// for a GPU execution, and what the GPU run produces carries GPU provenance.
#[derive(Clone, Copy)]
struct Execution {
    backend: ProverBackend,
    #[cfg(feature = "gpu")]
    gpu_memory_preset: MemoryPreset,
}

impl Execution {
    const CPU: Self = Self {
        backend: ProverBackend::Cpu,
        #[cfg(feature = "gpu")]
        gpu_memory_preset: MemoryPreset::Auto,
    };

    #[cfg(feature = "gpu")]
    fn gpu(gpu_memory_preset: MemoryPreset) -> Self {
        Self {
            backend: ProverBackend::Gpu,
            gpu_memory_preset,
        }
    }

    fn admits_input(self, input: ProverBackend) -> bool {
        input == ProverBackend::Cpu || input == self.backend
    }

    fn host_window_gib(self, cpu_gib: u64) -> u64 {
        match self.backend {
            ProverBackend::Cpu => cpu_gib,
            ProverBackend::Gpu => GPU_HOST_WINDOW_GIB,
        }
    }
}

fn config(target: ProofTarget, execution: Execution) -> ProgramProverConfig {
    ProgramProverConfig {
        target,
        backend: execution.backend,
        worker_threads: Some(24),
        cycles_bound: None,
        #[cfg(feature = "gpu")]
        gpu_memory_preset: execution.gpu_memory_preset,
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
            preflight("program", execution.host_window_gib(125));
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
            names
        }
        GenerateFrom::RecursionUnified(input) => {
            preflight("feeder", execution.host_window_gib(75));
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
            preflight("feeder_resume", execution.host_window_gib(75));
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
            preflight("wrap", execution.host_window_gib(60));
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
            wrap, commitment_mode, proof),
        _ => Err(format!("L1 reference has no typed comparison for {name}")),
    }
}

/// The reproduction's manifest identity: the reference's except the backend,
/// and the same file names in order (their hashes are not compared).
fn compare_reproduced_manifest(
    expected: &ProofManifest,
    actual: &ProofManifest,
) -> Result<(), String> {
    let configuration = |manifest: &ProofManifest| {
        let mut value = serde_json::to_value(&manifest.configuration).unwrap();
        value.as_object_mut().unwrap().remove("backend");
        value
    };
    let names = |manifest: &ProofManifest| -> Vec<String> {
        manifest
            .files
            .iter()
            .map(|file| file.name.clone())
            .collect()
    };
    let json = |value: serde_json::Result<serde_json::Value>| value.unwrap();
    for (field, same) in [
        (
            "format_version",
            expected.format_version == actual.format_version,
        ),
        (
            "program",
            json(serde_json::to_value(&expected.program))
                == json(serde_json::to_value(&actual.program)),
        ),
        (
            "fsv",
            json(serde_json::to_value(&expected.fsv)) == json(serde_json::to_value(&actual.fsv)),
        ),
        (
            "configuration",
            configuration(expected) == configuration(actual),
        ),
        ("files", names(expected) == names(actual)),
    ] {
        if !same {
            return Err(format!(
                "GPU reproduction manifest differs from the L1 reference in {field}"
            ));
        }
    }
    Ok(())
}

/// What a GPU reproduction of the L1 reference produced.
#[derive(Clone, Copy, Debug)]
enum Reproduction {
    /// The whole chain from source, with its manifest.
    Complete,
    /// The chain resumed after feeder checkpoint `layer`: every reference file
    /// after that checkpoint's report.
    ResumedAfter(u8),
    /// The chain resumed from the recursion-unified checkpoint: every reference
    /// file after `recursion_unified.json`.
    ResumedAfterRecursionUnified,
}

/// The typed comparator of a GPU reproduction of the L1 reference: each
/// directory's manifest is checked against its own files, the reproduction
/// has exactly the reference files `reproduction` implies, in order, and
/// every typed field of every file equals the reference except the
/// artifacts' backend and timings. Raw hashes are never compared across the
/// two directories; [`compare_files`] stays the CPU regeneration oracle.
fn compare_gpu_reproduction(
    reference: &Path,
    sink: &Path,
    inventory: &Inventory,
    reproduction: Reproduction,
) -> Result<(), String> {
    let expected = validated_manifest(reference)?;
    let expected_names: Vec<&str> = expected
        .files
        .iter()
        .map(|file| file.name.as_str())
        .collect();
    let required: Vec<&str> = match reproduction {
        Reproduction::Complete => {
            compare_reproduced_manifest(&expected, &validated_manifest(sink)?)?;
            expected_names
                .iter()
                .copied()
                .chain(["manifest.json"])
                .collect()
        }
        Reproduction::ResumedAfter(layer) => {
            let report = feeder_report_name(layer);
            let position = expected_names
                .iter()
                .position(|name| *name == report)
                .ok_or_else(|| format!("the L1 reference has no {report}"))?;
            expected_names[position + 1..].to_vec()
        }
        Reproduction::ResumedAfterRecursionUnified => {
            let position = expected_names
                .iter()
                .position(|name| *name == "recursion_unified.json")
                .ok_or("the L1 reference has no recursion_unified.json")?;
            expected_names[position + 1..].to_vec()
        }
    };
    let names: Vec<&str> = inventory.iter().map(|file| file.name.as_str()).collect();
    if names != required {
        return Err(format!(
            "GPU reproduction files {names:?} differ from the expected {required:?} ({reproduction:?})"
        ));
    }
    for name in names.into_iter().filter(|name| *name != "manifest.json") {
        compare_reproduced_file(
            name,
            &read_bytes(&reference.join(name))?,
            &read_bytes(&sink.join(name))?,
        )?;
    }
    Ok(())
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
#[ignore = "regenerates the committed L1 reference: ~35 min CPU (historical), up to ~110 GiB"]
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
fn first_multi_instance_checkpoint() -> (PathBuf, u8) {
    let reference = fixture_dir();
    let (checkpoint, layer) = (0..MAX_FEEDER_LAYERS as u8)
        .map(|layer| (reference.join(feeder_checkpoint_name(layer)), layer))
        .take_while(|(path, _)| path.exists())
        .find(|(path, _)| {
            let checkpoint: StepCheckpoint = read_typed(path).expect("feeder checkpoint");
            feeder_proof_instances(&checkpoint.proof, None).expect("feeder checkpoint proof") > 1
        })
        .expect("the L1 reference has a multi-instance feeder checkpoint");
    println!("resuming from {}", checkpoint.display());
    (checkpoint, layer)
}

#[test]
#[ignore = "regenerates the CPU feeder layers after the first multi-instance checkpoint"]
fn committed_l1_feeder_mid_chain_resume_is_current() {
    guard(GenerateFrom::FeederLayer(
        &first_multi_instance_checkpoint().0,
    ));
}

#[cfg(feature = "gpu")]
fn gpu_reproduction(name: &str, reproduction: Reproduction, from: impl FnOnce(&Path) -> Inventory) {
    let _ = env_logger::builder()
        .is_test(true)
        .format_timestamp_millis()
        .try_init();
    let sink = disposable_dir(name);
    let inventory = from(&sink);
    compare_gpu_reproduction(&fixture_dir(), &sink, &inventory, reproduction)
        .unwrap_or_else(|message| panic!("{message}"));
    fs::remove_dir_all(sink).expect("L1 reference GPU reproduction removes its sink");
}

/// The whole reference chain from source on the GPU at the 30 GiB preset.
#[cfg(feature = "gpu")]
#[test]
#[ignore = "reproduces the L1 reference chain on the GPU"]
fn gpu_l1_reference_matches_committed() {
    gpu_reproduction("gpu", Reproduction::Complete, |sink| {
        generate_into(
            sink,
            GenerateFrom::Program,
            Execution::gpu(MemoryPreset::GiB30),
        )
        .expect("L1 reference GPU reproduction")
    });
}

/// The CPU reference's first multi-instance feeder checkpoint resumed on the
/// GPU at the 30 GiB preset: the remaining feeder layers, `l1_feeder.json`
/// and the wrap.
#[cfg(feature = "gpu")]
#[test]
#[ignore = "resumes the L1 reference feeder chain and wraps it on the GPU"]
fn gpu_l1_feeder_mid_chain_resume_matches_committed() {
    let (checkpoint, layer) = first_multi_instance_checkpoint();
    gpu_reproduction("gpu-resume", Reproduction::ResumedAfter(layer), |sink| {
        let execution = Execution::gpu(MemoryPreset::GiB30);
        let mut inventory = generate_into(sink, GenerateFrom::FeederLayer(&checkpoint), execution)
            .expect("L1 reference GPU feeder resume");
        inventory.extend(
            generate_into(
                sink,
                GenerateFrom::L1Feeder(&sink.join("l1_feeder.json")),
                execution,
            )
            .expect("L1 reference GPU wrap"),
        );
        inventory
    });
}

/// The CPU reference's recursion-unified checkpoint proved on the GPU at the
/// 30 GiB preset: every feeder layer, `l1_feeder.json` and the wrap.
#[cfg(feature = "gpu")]
#[test]
#[ignore = "proves the L1 reference feeder chain and wraps it on the GPU"]
fn gpu_l1_feeder_chain_matches_committed() {
    gpu_reproduction(
        "gpu-feeder-chain",
        Reproduction::ResumedAfterRecursionUnified,
        |sink| {
            let execution = Execution::gpu(MemoryPreset::GiB30);
            let mut inventory = generate_into(
                sink,
                GenerateFrom::RecursionUnified(&fixture_dir().join("recursion_unified.json")),
                execution,
            )
            .expect("L1 reference GPU feeder chain");
            inventory.extend(
                generate_into(
                    sink,
                    GenerateFrom::L1Feeder(&sink.join("l1_feeder.json")),
                    execution,
                )
                .expect("L1 reference GPU wrap"),
            );
            inventory
        },
    );
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
    let (pack_log2, _) = execution_prover::config::l1_wrap_packing(circuit_type);
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

/// A typed-comparator directory: a recursion-unified artifact, one feeder
/// layer with its report, the last-feeder artifact and the manifest.
fn typed_comparator_fixture(dir: &Path, backend: ProverBackend) -> Inventory {
    fs::create_dir_all(dir).unwrap();
    let loaded = LoadedProgram {
        bin_bytes: vec![1, 2, 3, 4],
        text_bytes: vec![5, 6, 7, 8],
        bin_u32: vec![0x13],
        text_u32: vec![0x13],
    };
    let state = || {
        let mut state = test_state();
        state.setups.insert(
            1,
            setups::UnrolledCircuitSetupParams {
                family_idx: 1,
                capacity: 2,
                setup_caps: prover::merkle_trees::MerkleTreeCapVarLength { cap: vec![[7; 8]] },
            },
        );
        state
    };
    let fsv = test_fsv();
    let mut artifact = finalize_artifact(
        &fsv,
        ProofTarget::RecursionUnified,
        backend,
        0,
        &loaded,
        state(),
    );
    artifact.timings_ms = ProofTimingsMs::default();
    write_compact(&dir.join("recursion_unified.json"), &artifact).unwrap();
    let mut state = state();
    state.chain_end_params.push([4; 8]);
    state.feeder_layers = 1;
    write_compact(
        &dir.join(feeder_checkpoint_name(0)),
        &StepCheckpoint::from_state(0, &state),
    )
    .unwrap();
    write_compact(&dir.join(feeder_report_name(0)), &fake_report(2)).unwrap();
    state.chain_end_params.push([5; 8]);
    state.feeder_layers = 2;
    write_compact(
        &dir.join(feeder_checkpoint_name(1)),
        &StepCheckpoint::from_state(1, &state),
    )
    .unwrap();
    write_compact(&dir.join(feeder_report_name(1)), &fake_report(1)).unwrap();
    state.stage = ProofTarget::L1Feeder;
    let mut artifact = finalize_artifact(&fsv, ProofTarget::L1Feeder, backend, 0, &loaded, state);
    artifact.timings_ms.total_ms = if backend == ProverBackend::Gpu { 1 } else { 2 };
    write_compact(&dir.join("l1_feeder.json"), &artifact).unwrap();
    rewrite_typed_manifest(dir, backend)
}

/// Writes `dir`'s manifest over its current files and returns its inventory.
fn rewrite_typed_manifest(dir: &Path, backend: ProverBackend) -> Inventory {
    let names = [
        "recursion_unified.json".to_string(),
        feeder_checkpoint_name(0),
        feeder_report_name(0),
        feeder_checkpoint_name(1),
        feeder_report_name(1),
        "l1_feeder.json".to_string(),
    ];
    let files: Inventory = names
        .iter()
        .map(|name| file_identity(dir, name).unwrap())
        .collect();
    write_compact(
        &dir.join("manifest.json"),
        &ProofManifest {
            format_version: 1,
            program: ProgramIdentity {
                bin_keccak256: "bin".into(),
                text_keccak256: "text".into(),
            },
            fsv: vec![FsvIdentity {
                role: "feeder_wrap".into(),
                stem: "stem".into(),
                bin_keccak256: "bin".into(),
                text_keccak256: "text".into(),
            }],
            configuration: ReferenceConfiguration {
                security_level: COMPILED_SECURITY_LEVEL,
                backend,
                worker_threads: 24,
                batch_id: 0,
                blake_unrolled: "u".into(),
                blake_bridge: "b".into(),
                blake_final: "f".into(),
                user_nd_words: vec![],
            },
            files,
        },
    )
    .unwrap();
    names
        .iter()
        .chain(std::iter::once(&"manifest.json".to_string()))
        .map(|name| file_identity(dir, name).unwrap())
        .collect()
}

fn mutate_json(path: &Path, mutate: impl FnOnce(&mut serde_json::Value)) {
    let mut value: serde_json::Value = read_typed(path).unwrap();
    mutate(&mut value);
    write_compact(path, &value).unwrap();
}

/// Runs the comparator on a CPU reference and a GPU reproduction to which
/// `mutate` was applied (the reproduction's manifest is rewritten after it
/// when `remanifest`).
fn typed_comparison(
    reproduction: Reproduction,
    mutate: impl FnOnce(&Path, &mut Inventory),
    remanifest: bool,
) -> Result<(), String> {
    let root = disposable_dir("typed");
    let (reference, sink) = (root.join("reference"), root.join("gpu"));
    typed_comparator_fixture(&reference, ProverBackend::Cpu);
    let mut inventory = typed_comparator_fixture(&sink, ProverBackend::Gpu);
    mutate(&sink, &mut inventory);
    if remanifest {
        let order: Vec<String> = inventory.iter().map(|file| file.name.clone()).collect();
        let rewritten = rewrite_typed_manifest(&sink, ProverBackend::Gpu);
        inventory = order
            .iter()
            .map(|name| {
                rewritten
                    .iter()
                    .find(|file| &file.name == name)
                    .map(|file| file_identity(&sink, &file.name).unwrap())
                    .unwrap()
            })
            .collect();
    }
    let result = compare_gpu_reproduction(&reference, &sink, &inventory, reproduction);
    fs::remove_dir_all(root).unwrap();
    result
}

#[test]
fn cpu_typed_comparator_ignores_backend_and_timings() {
    typed_comparison(Reproduction::Complete, |_, _| {}, false).unwrap();
}

#[test]
fn cpu_typed_comparator_accepts_a_resumed_suffix() {
    typed_comparison(
        Reproduction::ResumedAfter(0),
        |_, inventory| {
            inventory.retain(|file| {
                ![
                    "recursion_unified.json",
                    "feeder_layer_0.json",
                    "feeder_layer_0_report.json",
                    "manifest.json",
                ]
                .contains(&file.name.as_str())
            })
        },
        false,
    )
    .unwrap();
    typed_comparison(
        Reproduction::ResumedAfter(0),
        |_, inventory| inventory.retain(|file| file.name != "manifest.json"),
        false,
    )
    .unwrap_err();
}

#[test]
fn cpu_typed_comparator_rejects_a_shortened_reproduction() {
    for (reproduction, keep) in [
        (Reproduction::ResumedAfter(0), &["l1_feeder.json"][..]),
        (
            Reproduction::ResumedAfter(0),
            &["feeder_layer_1.json", "feeder_layer_1_report.json"],
        ),
        (Reproduction::Complete, &["l1_feeder.json", "manifest.json"]),
    ] {
        let err = typed_comparison(
            reproduction,
            |_, inventory| inventory.retain(|file| keep.contains(&file.name.as_str())),
            false,
        )
        .unwrap_err();
        assert!(err.contains("differ from the expected"), "{err}");
    }
}

#[test]
fn cpu_typed_comparator_rejects_field_differences() {
    for (name, field, mutate) in [
        (
            "l1_feeder.json",
            "proof",
            (|value: &mut serde_json::Value| value["proof"]["final_pc"] = 4.into())
                as fn(&mut serde_json::Value),
        ),
        ("recursion_unified.json", "setups", |value| {
            value["setups"]["1"]["capacity"] = 3.into()
        }),
        ("l1_feeder.json", "chain_hash", |value| {
            value["chain_hash"][0] = 9.into()
        }),
        ("feeder_layer_0.json", "chain_end_params", |value| {
            value["chain_end_params"][3][0] = 9.into()
        }),
        ("l1_feeder.json", "feeder_layers", |value| {
            value["feeder_layers"] = 3.into()
        }),
        ("feeder_layer_0_report.json", "cycles", |value| {
            value["cycles"] = 1.into()
        }),
        ("feeder_layer_0_report.json", "counters", |value| {
            value["counters"]["cycles"] = 1.into()
        }),
    ] {
        let err = typed_comparison(
            Reproduction::Complete,
            |sink, _| mutate_json(&sink.join(name), mutate),
            true,
        )
        .unwrap_err();
        assert_eq!(
            err,
            format!("{name} differs from the L1 reference in field {field}")
        );
    }
}

#[test]
fn cpu_typed_comparator_rejects_a_manifest_hash_mismatch() {
    let err = typed_comparison(
        Reproduction::Complete,
        |sink, _| {
            mutate_json(&sink.join("l1_feeder.json"), |value| {
                value["feeder_layers"] = 3.into()
            })
        },
        false,
    )
    .unwrap_err();
    assert!(
        err.contains("lists l1_feeder.json with another length or hash"),
        "{err}"
    );
}

#[test]
fn cpu_typed_comparator_rejects_a_reordered_inventory() {
    let err = typed_comparison(
        Reproduction::Complete,
        |_, inventory| inventory.swap(1, 2),
        false,
    )
    .unwrap_err();
    assert!(err.contains("differ from the expected"), "{err}");
}

#[test]
fn cpu_typed_comparator_rejects_another_manifest_identity() {
    let err = typed_comparison(
        Reproduction::Complete,
        |sink, _| {
            mutate_json(&sink.join("manifest.json"), |value| {
                value["configuration"]["worker_threads"] = 12.into()
            })
        },
        false,
    )
    .unwrap_err();
    assert_eq!(
        err,
        "GPU reproduction manifest differs from the L1 reference in configuration"
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
