use super::*;
use serde::de::DeserializeOwned;
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};

const REGENERATE: &str = concat!(
    "RUST_MIN_STACK=1073741824 cargo test -p prover_pipeline --release --lib l1_reference::generate_l1_reference_seed -- --exact --ignored --nocapture --test-threads=1 && ",
    "RUST_MIN_STACK=1073741824 cargo test -p prover_pipeline --release --lib l1_reference::generate_l1_reference_from_recursion_unified -- --exact --ignored --nocapture --test-threads=1"
);

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

/// The observed state after a nonterminal A layer (zero-based).
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
}

#[derive(Debug, Serialize, Deserialize)]
struct ProgramIdentity {
    bin_keccak256: String,
    text_keccak256: String,
}

/// A guest's identity is its registry `fsv-rom-digest-v1`, the one `load_fsv_exact` checks.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    fsv_rom_digest_v1: String,
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
    let standard = |program, mode| {
        FsvDescriptor::new(
            ::prover::definitions::SecurityLevel::Sec100,
            SoundnessMode::PessimisticConjecture,
            program,
            mode,
        )
    };
    [
        (
            "unrolled_base",
            standard(FsvProgram::UnrolledBaseLayer, blake.unrolled),
        ),
        (
            "unrolled_recursion",
            standard(FsvProgram::UnrolledRecursionLayer, blake.unrolled),
        ),
        (
            "bridge_base",
            standard(FsvProgram::UnrolledBaseLayer, blake.bridge),
        ),
        (
            "bridge_recursion",
            standard(FsvProgram::UnrolledRecursionLayer, blake.bridge),
        ),
        (
            "unified",
            standard(FsvProgram::UnifiedRecursionLayer, blake.final_layer),
        ),
        (
            "feeder_first",
            standard(
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::BlakeSpecialOpcodes,
            ),
        ),
        ("feeder_a", FsvDescriptor::l1_feeder(FsvProfile::L1FeederA)),
        (
            "feeder_wrap",
            FsvDescriptor::l1_feeder(FsvProfile::L1FeederWrap),
        ),
    ]
    .into_iter()
    .map(|(role, descriptor)| {
        let guest = load_fsv_exact(fsv_dir(), &descriptor)
            .map_err(|error| format!("FSV identity {role}: {error}"))?;
        let stem = descriptor
            .registry_entry()
            .map_err(|error| error.to_string())?
            .relative_path
            .trim_end_matches(".elf")
            .to_owned();
        Ok(FsvIdentity {
            role: role.into(),
            stem,
            fsv_rom_digest_v1: guest.digest().to_string(),
        })
    })
    .collect()
}

fn source() -> ProgramSource {
    ProgramSource::legacy_binaries_from_bin(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/basic_fibonacci/app.bin"),
    )
}

#[test]
fn cpu_fsv_identities_cover_the_l1_chain() {
    let identities =
        fsv_identities(PipelineBlakeModes::from_env()).expect("FSV images and identities");
    for role in ["unified", "feeder_first", "feeder_a", "feeder_wrap"] {
        assert!(
            identities.iter().any(|identity| identity.role == role),
            "missing L1 FSV role {role}"
        );
    }
    for identity in identities {
        println!("FSV identity role={} stem={}", identity.role, identity.stem);
    }
}

// CPU stages keep 40 GiB above the historical 110 GiB program peak
// and the feeder's 96 GiB planning budget.
// The 2026-10-19 run measured 72.80 GiB for Base and 88.79 GiB for RecUnified.
const CPU_PROGRAM_HOST_WINDOW_GIB: u64 = 150;
const CPU_FEEDER_HOST_WINDOW_GIB: u64 = 136;
// The measured wrap peak was 37.57 GiB; round to 40 GiB plus the host reserve.
const CPU_WRAP_HOST_WINDOW_GIB: u64 = 80;

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

struct FixtureObserver<'a> {
    sink: &'a Path,
    layers: Vec<u8>,
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
        if validate_feeder_proof(&state.proof, None)? != FeederProfile::C {
            write_compact(
                &self.sink.join(feeder_checkpoint_name(layer)),
                &StepCheckpoint::from_state(layer, state),
            )?;
        }
        write_compact(&self.sink.join(feeder_report_name(layer)), report)?;
        Ok(())
    }
}

enum GenerateFrom<'a> {
    ProgramSeed,
    RecursionUnified(&'a Path),
    L1Feeder(&'a Path),
}

fn write_reference_manifest(
    sink: &Path,
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
    Ok(names)
}

fn generate_into(sink: &Path, from: GenerateFrom<'_>) -> Result<Inventory, String> {
    deterministic_pow_required();
    fs::create_dir_all(sink).map_err(|error| format!("L1 reference sink: {error}"))?;
    let source = source();
    let names = match from {
        GenerateFrom::ProgramSeed => {
            preflight("program", CPU_PROGRAM_HOST_WINDOW_GIB);
            let loaded = load_program(&source)?;
            let blake = PipelineBlakeModes::from_env();
            let identities = fsv_identities(blake)?;
            let base = {
                let mut prover = ProgramProver::new(source.clone(), config(ProofTarget::Base))?;
                prover.prove_words(0, vec![])?
            };
            let mut artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::RecursionUnified),
                    &base,
                )?;
                prover.continue_artifact(base)?
            };
            artifact.timings_ms = ProofTimingsMs::default();
            write_compact(&sink.join("recursion_unified.json"), &artifact)?;
            drop(artifact);
            let files = vec![file_identity(sink, "recursion_unified.json")?];
            write_reference_manifest(
                sink,
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
            preflight("feeder", CPU_FEEDER_HOST_WINDOW_GIB);
            let artifact: ProofArtifact = read_typed(input)?;
            if artifact.target != ProofTarget::RecursionUnified
                || artifact.batch_id != 0
                || artifact.backend != ProverBackend::Cpu
            {
                return Err(
                    "L1 reference requires a CPU recursion-unified checkpoint at batch_id 0".into(),
                );
            }
            let mut observer = FixtureObserver {
                sink,
                layers: vec![],
            };
            let mut artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::L1Feeder),
                    &artifact,
                )?;
                prover
                    .continue_artifact_observed(artifact, &mut observer)
                    .map_err(|error| error.to_string())?
            };
            if observer.layers != [0, 1, 2] {
                return Err(
                    "L1 reference requires exactly three feeder observations [0, 1, 2]".into(),
                );
            }
            artifact.timings_ms = ProofTimingsMs::default();
            write_compact(&sink.join("l1_feeder.json"), &artifact)?;
            observer
                .layers
                .iter()
                .flat_map(|&layer| {
                    let mut names = vec![feeder_report_name(layer)];
                    if layer < 2 {
                        names.insert(0, feeder_checkpoint_name(layer));
                    }
                    names
                })
                .chain(["l1_feeder.json".to_string()])
                .collect()
        }
        GenerateFrom::L1Feeder(input) => {
            preflight("wrap", CPU_WRAP_HOST_WINDOW_GIB);
            let artifact: ProofArtifact = read_typed(input)?;
            if artifact.target != ProofTarget::L1Feeder
                || artifact.batch_id != 0
                || artifact.backend != ProverBackend::Cpu
            {
                return Err(
                    "L1 reference requires a CPU L1-feeder checkpoint at batch_id 0".into(),
                );
            }
            let artifact = {
                let mut prover = ProgramProver::for_continuation(
                    source.clone(),
                    config(ProofTarget::L1),
                    &artifact,
                )?;
                prover.continue_artifact(artifact)?
            };
            verify_artifact(&artifact, &source)?;
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

fn compare_files(reference: &Path, sink: &Path, inventory: &Inventory) -> Result<(), String> {
    for file in inventory {
        let expected = read_bytes(&reference.join(&file.name))?;
        let actual = read_bytes(&sink.join(&file.name))?;
        if expected != actual {
            return Err(format!(
                "L1 reference mismatch {}; regenerate: {REGENERATE}",
                file.name
            ));
        }
    }
    Ok(())
}

/// `dir`'s manifest, with every listed file's length and hash checked
/// against `dir`'s own copy.
/// The manifest's file inventory, checked against the files. It reads a manifest of any FSV
/// identity format, so a regeneration can replace an older one.
fn validated_inventory(dir: &Path) -> Result<Inventory, String> {
    #[derive(Deserialize)]
    struct Files {
        files: Inventory,
    }
    let Files { files } = read_typed(&dir.join("manifest.json"))?;
    for file in &files {
        let actual = file_identity(dir, &file.name)?;
        if actual.bytes != file.bytes || actual.keccak256 != file.keccak256 {
            return Err(format!(
                "L1 reference manifest of {} lists {} with another length or hash",
                dir.display(),
                file.name
            ));
        }
    }
    Ok(files)
}

/// The full manifest: its files are intact and its FSV identities are the registry's.
fn validated_manifest(dir: &Path) -> Result<ProofManifest, String> {
    validated_inventory(dir)?;
    let manifest: ProofManifest = read_typed(&dir.join("manifest.json"))?;
    let registry = fsv_identities(PipelineBlakeModes::from_env())?;
    if manifest.fsv != registry {
        return Err(format!(
            "L1 reference manifest of {} records FSV identities {:?}; the registry has {:?}",
            dir.display(),
            manifest.fsv,
            registry
        ));
    }
    Ok(manifest)
}

fn guard(from: GenerateFrom<'_>) {
    let reference = fixture_dir();
    let sink = disposable_dir("guard");
    let inventory = generate_into(&sink, from).expect("L1 reference guard regeneration");
    compare_files(&reference, &sink, &inventory).unwrap_or_else(|message| panic!("{message}"));
    fs::remove_dir_all(sink).expect("L1 reference guard removes disposable sink");
}

/// Produce the Standard recursion-unified seed in its own process before the feeder and wrap.
#[test]
#[ignore = "regenerates the CPU Standard seed; requires 150 GiB MemAvailable"]
fn generate_l1_reference_seed() {
    let reference = fixture_dir();
    let mut managed = BTreeSet::new();
    if reference.join("manifest.json").exists() {
        managed.extend(
            validated_inventory(&reference)
                .expect("previous L1 reference manifest")
                .into_iter()
                .map(|file| file.name),
        );
    }
    let sink = disposable_dir("generate-seed");
    let inventory =
        generate_into(&sink, GenerateFrom::ProgramSeed).expect("L1 reference seed generation");
    assert_eq!(
        inventory
            .iter()
            .map(|file| file.name.as_str())
            .collect::<Vec<_>>(),
        ["recursion_unified.json", "manifest.json"]
    );
    fs::create_dir_all(&reference).expect("L1 reference creates fixture directory");
    for name in managed {
        assert_eq!(
            Path::new(&name).file_name().and_then(|name| name.to_str()),
            Some(name.as_str())
        );
        if name != "recursion_unified.json" && name != "manifest.json" {
            fs::remove_file(reference.join(name))
                .expect("L1 seed removes the previous managed fixture");
        }
    }
    for file in &inventory {
        fs::rename(sink.join(&file.name), reference.join(&file.name))
            .expect("L1 reference promotes the seed and its manifest");
    }
    fs::remove_dir_all(sink).expect("L1 reference removes seed staging directory");
    let seeded = validated_manifest(&reference).expect("seed-only manifest validates");
    assert_eq!(
        seeded
            .files
            .iter()
            .map(|file| file.name.as_str())
            .collect::<Vec<_>>(),
        ["recursion_unified.json"]
    );
}

/// Run in a fresh process after independently reproducing the committed standard seed.
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
    )
    .expect("L1 reference feeder generation");
    let wrap = generate_into(&sink, GenerateFrom::L1Feeder(&sink.join("l1_feeder.json")))
        .expect("L1 reference wrap generation");
    let files = std::iter::once(seed).chain(feeder).chain(wrap).collect();
    let names = write_reference_manifest(&sink, files, program, identities, blake)
        .expect("L1 reference manifest");
    for name in names {
        fs::rename(sink.join(&name), reference.join(&name))
            .expect("L1 reference promotes complete fixture set");
    }
    fs::remove_dir_all(sink).expect("L1 reference removes staging directory");
}

#[test]
#[ignore = "regenerates the CPU feeder chain"]
fn committed_l1_feeder_reference_is_current() {
    guard(GenerateFrom::RecursionUnified(
        &fixture_dir().join("recursion_unified.json"),
    ));
}

#[test]
#[ignore = "regenerates the CPU L1 wrap"]
fn committed_l1_wrap_reference_is_current() {
    guard(GenerateFrom::L1Feeder(
        &fixture_dir().join("l1_feeder.json"),
    ));
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
    use ::prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, PathQueryable};
    use ::prover::worker::Worker;

    let bundle: L1Bundle =
        read_typed(&fixture_dir().join("l1_bundle.json")).expect("committed L1 wrap bundle");
    bundle.validate().expect("committed L1 wrap bundle");
    let setup_commitment = &bundle.proof.whir_proof.setup_commitment;

    let circuit_type = CircuitType::L1Wrap21;
    let (mut binary, mut text) = load_fsv_exact(
        fsv_dir(),
        &FsvDescriptor::l1_feeder(FsvProfile::L1FeederWrap),
    )
    .expect("pinned L1 wrap guest")
    .into_words();
    setups::pad_bytecode_for_proving_with_rom(&mut binary, circuit_type.rom());
    setups::pad_bytecode_for_proving_with_rom(&mut text, circuit_type.rom());
    let setup = unified_reduced_machine_proth120::l1_wrap_2p21::l1_wrap_setup(&binary, &text);
    let config = execution_prover::config::prover_config(
        circuit_type,
        ProofProfile::L1Wrap,
        ::prover::definitions::SecurityLevel::Sec100,
    );
    let pack_log2 = config.pack_log2();
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
            config.lde_factor(),
            config.base_oracles_values_per_leaf().trailing_zeros() as usize,
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
    let digest_bytes = ::prover::merkle_trees::keccak256_hash_leafs::KECCAK256_MERKLE_DIGEST_BYTES;
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
fn cpu_l1_feeder_profiles_and_capacity_margins() {
    let reference = fixture_dir();
    validated_manifest(&reference).expect("L1 reference manifest");
    for (layer, profile, instances) in [
        (0, FeederProfile::A, 2),
        (1, FeederProfile::A, 1),
        (2, FeederProfile::C, 1),
    ] {
        let (proof, setups) = if layer < 2 {
            let checkpoint: StepCheckpoint =
                read_typed(&reference.join(feeder_checkpoint_name(layer)))
                    .expect("feeder checkpoint");
            (checkpoint.proof, checkpoint.setups)
        } else {
            let artifact: ProofArtifact =
                read_typed(&reference.join("l1_feeder.json")).expect("terminal feeder artifact");
            (artifact.proof, artifact.setups)
        };
        assert_eq!(
            validate_feeder_proof(&proof, Some(instances)).unwrap(),
            profile
        );
        setups::validate_setups_cap_size(&setups, profile.cap_size()).unwrap();
        let report: FsvRunReport = read_typed(&reference.join(feeder_report_name(layer)))
            .expect("feeder prediction report");
        assert_eq!(report.nd_words_remaining, 0);
        assert_eq!(
            predicted_feeder_shape(&report).unwrap(),
            (profile, instances)
        );
        let capacity = instances as u64 * profile.circuit().get_domain_size() as u64;
        assert!(
            report.cycles <= capacity,
            "feeder layer {layer}: {} cycles exceed capacity {capacity}",
            report.cycles
        );
    }
    let artifact: ProofArtifact =
        read_typed(&reference.join("l1_feeder.json")).expect("terminal feeder artifact");
    assert_eq!(artifact.feeder_layers, 3);
    let stream = build_unified_stream(
        &artifact.setups,
        &artifact.proof,
        BlakeMode::BlakeSpecialOpcodes,
    );
    let output = FeederProfile::C.native_verify(stream.clone()).unwrap();
    let program = load_fsv_exact(
        fsv_dir(),
        &FsvDescriptor::l1_feeder(FsvProfile::L1FeederWrap),
    )
    .expect("pinned L1 wrap guest")
    .into_words();
    let report = ProductionFeederVerifier
        .wrap_run(&program, stream.clone())
        .unwrap();
    validate_wrap_report(&report, &output).unwrap();
    assert!(
        report.cycles <= L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - 16_384,
        "wrap must leave at least 16,384 cycles of capacity"
    );
    println!(
        "wrap_cycles={} margin_to_2p21={} margin_to_reserved_limit={}",
        report.cycles,
        L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - report.cycles,
        L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - 16_384 - report.cycles,
    );
    let count_end = stream.len() - 2 - 16;
    let count_start = count_end - full_statement_verifier::definitions::DELEGATION_TYPES.len();
    for offset in count_start..count_end {
        let mut bad = stream.clone();
        assert_eq!(bad[offset], 0);
        bad[offset] = 1;
        assert!(FeederProfile::C
            .native_verify(bad.clone())
            .unwrap_err()
            .contains("no delegation proofs"));
        assert!(ProductionFeederVerifier.wrap_run(&program, bad).is_err());
    }
    let mut trailing = stream.clone();
    trailing.push(7);
    assert!(FeederProfile::C
        .native_verify(trailing.clone())
        .unwrap_err()
        .contains("trailing"));
    let report = ProductionFeederVerifier
        .wrap_run(&program, trailing)
        .unwrap();
    assert_eq!(report.nd_words_remaining, 1);
    assert!(validate_wrap_report(&report, &output).is_err());
    let truncated = stream[..stream.len() - 1].to_vec();
    assert!(FeederProfile::C.native_verify(truncated.clone()).is_err());
    assert!(ProductionFeederVerifier
        .wrap_run(&program, truncated)
        .is_err());
    let mut flipped = stream;
    flipped[(FeederProfile::C.cap_size() - 1) * 8] ^= 1;
    assert!(FeederProfile::C.native_verify(flipped.clone()).is_err());
    assert!(ProductionFeederVerifier
        .wrap_run(&program, flipped)
        .is_err());
}

#[test]
fn cpu_native_feeder_a_accepts_a_valid_stream_and_rejects_trailing_words() {
    let checkpoint: StepCheckpoint =
        read_typed(&fixture_dir().join(feeder_checkpoint_name(0))).expect("profile-A checkpoint");
    assert_eq!(
        validate_feeder_proof(&checkpoint.proof, Some(2)).unwrap(),
        FeederProfile::A
    );
    let mut stream = build_unified_stream(
        &checkpoint.setups,
        &checkpoint.proof,
        BlakeMode::BlakeSpecialOpcodes,
    );
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

#[cfg(feature = "gpu")]
pub(super) mod gpu;
