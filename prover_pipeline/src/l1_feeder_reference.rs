//! The L1 feeder-chain fixtures and the production cycle gates (W2).
//!
//! For each input program the chain `RecursionUnified -> F1 -> .. -> Fk`
//! is produced on the CPU with deterministic PoW and every layer is
//! recorded: proof, setups, chain history, native 16-word output and the
//! verifier run that predicted it. The gates run on these fixtures: the
//! merge margin (a two-instance feeder proof verifies inside one 2^22
//! chunk), the wrap program over the last proof (within 2^21), fresh versus
//! resumed production, and the negative controls.

use super::*;
use prover::gkr::prover_config::example_configs::L1_FEEDER_QUERIES_AND_POW;
use serde::de::DeserializeOwned;
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};

const FIXTURE_SCHEMA_VERSION: u32 = 1;
const REGENERATE: &str = "RUST_MIN_STACK=1073741824 cargo test -p prover_pipeline --release --lib l1_feeder_reference::generate_feeder_reference -- --exact --ignored --nocapture --test-threads=1";

fn fixture_dir() -> PathBuf {
    std::env::var_os("AB_F3_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/l1_feeder_reference")
        })
}

/// The chain inputs: the program and its non-determinism words.
struct Input {
    name: &'static str,
    program: &'static str,
    nd_words: Vec<u32>,
}

fn inputs() -> Vec<Input> {
    vec![
        Input {
            name: "basic_fibonacci",
            program: "basic_fibonacci",
            nd_words: vec![],
        },
        Input {
            name: "dynamic_fibonacci_1000",
            program: "dynamic_fibonacci",
            nd_words: vec![1000],
        },
        Input {
            name: "dynamic_fibonacci_4321",
            program: "dynamic_fibonacci",
            nd_words: vec![4321],
        },
    ]
}

fn source(input: &Input) -> ProgramSource {
    ProgramSource::from_paths(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(format!("../examples/{}/app.bin", input.program))
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

fn hex_digest(bytes: &[u8]) -> String {
    keccak256(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn read_bytes(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path).map_err(|error| format!("feeder reference read {}: {error}", path.display()))
}

fn read_typed<T: DeserializeOwned>(path: &Path) -> Result<T, String> {
    let file = File::open(path)
        .map_err(|error| format!("feeder reference open {}: {error}", path.display()))?;
    serde_json::from_reader(BufReader::new(file))
        .map_err(|error| format!("feeder reference deserialize {}: {error}", path.display()))
}

fn write_compact<T: Serialize>(path: &Path, value: &T) -> Result<(), String> {
    let temporary = path.with_extension("json.part");
    let file = File::create(&temporary)
        .map_err(|error| format!("feeder reference create {}: {error}", temporary.display()))?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, value)
        .map_err(|error| format!("feeder reference serialize {}: {error}", path.display()))?;
    writer
        .flush()
        .map_err(|error| format!("feeder reference flush: {error}"))?;
    drop(writer);
    fs::rename(&temporary, path)
        .map_err(|error| format!("feeder reference rename {}: {error}", path.display()))
}

fn preflight(stage: &str, required_gib: u64) {
    let meminfo =
        fs::read_to_string("/proc/meminfo").expect("feeder reference reads /proc/meminfo");
    let available = meminfo
        .lines()
        .find_map(|line| {
            line.strip_prefix("MemAvailable:")?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
        .expect("feeder reference preflight finds MemAvailable");
    println!("preflight stage={stage} memavailable_kib={available} required_gib={required_gib}");
    assert!(
        available >= required_gib * 1024 * 1024,
        "feeder reference preflight {stage}: MemAvailable {available} KiB is below {required_gib} GiB"
    );
}

fn deterministic_pow_required() {
    if !cfg!(feature = "deterministic_pow") {
        panic!("the feeder reference requires deterministic_pow");
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
    bin_words: usize,
    rom_bytes: usize,
}

fn fsv_identities() -> Result<Vec<FsvIdentity>, String> {
    [
        ("feeder_first", FsvProgram::UnifiedRecursionLayer),
        ("feeder", FsvProgram::UnifiedRecursionLayerL1Feeder),
        ("feeder_wrap", FsvProgram::UnifiedRecursionLayerL1FeederWrap),
    ]
    .into_iter()
    .map(|(role, program)| {
        let stem = program.file_stem(BlakeMode::BlakeSpecialOpcodes);
        let bin = read_bytes(&fsv_dir().join(format!("{stem}.bin")))?;
        Ok(FsvIdentity {
            role: role.into(),
            bin_keccak256: hex_digest(&bin),
            text_keccak256: hex_digest(&read_bytes(&fsv_dir().join(format!("{stem}.text")))?),
            bin_words: bin.len() / 4,
            rom_bytes: program.rom().byte_size(),
            stem,
        })
    })
    .collect()
}

/// One proven feeder layer.
#[derive(Serialize, Deserialize)]
struct LayerFixture {
    fixture_schema_version: u32,
    layer: u8,
    role: String,
    feeder_layers: u32,
    /// The prediction run of this layer's program over its input.
    prediction: FsvRunReport,
    predicted_instances: usize,
    instances: usize,
    /// Cycles below the next 2^22 chunk boundary of the prediction run.
    chunk_margin_cycles: u64,
    native_output: [u32; 16],
    chain_hash: [u32; 8],
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    program_cycles: u64,
}

#[derive(Serialize, Deserialize)]
struct WrapRunFixture {
    fixture_schema_version: u32,
    report: FsvRunReport,
    native_output: [u32; 16],
    cycle_limit: u64,
    /// `None` when the run satisfies every wrap requirement.
    rejection: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct Manifest {
    fixture_schema_version: u32,
    input: String,
    nd_words: Vec<u32>,
    program_bin_keccak256: String,
    program_text_keccak256: String,
    fsv: Vec<FsvIdentity>,
    feeder_queries_and_pow: Vec<(usize, u32)>,
    blake_unrolled: String,
    blake_bridge: String,
    blake_final: String,
    layers: Vec<LayerSummary>,
    wrap_cycles: u64,
    wrap_rejection: Option<String>,
    files: Vec<(String, u64, String)>,
}

#[derive(Serialize, Deserialize, Clone)]
struct LayerSummary {
    layer: u8,
    role: String,
    prediction_cycles: u64,
    predicted_instances: usize,
    instances: usize,
    chunk_margin_cycles: u64,
}

struct Recorder<'a> {
    sink: &'a Path,
    layers: Vec<LayerSummary>,
}

impl FeederObserver for Recorder<'_> {
    fn feeder_layer(
        &mut self,
        layer: u8,
        state: &RecursionState,
        report: &FsvRunReport,
    ) -> Result<(), String> {
        if layer as usize != self.layers.len() {
            return Err("feeder reference observer layer order".into());
        }
        let instances = feeder_proof_instances(&state.proof, None)?;
        let predicted_instances = predicted_feeder_instances(report)?;
        let chunk = UnrolledCircuitType::Unified22.get_domain_size() as u64;
        let chunk_margin_cycles = predicted_instances as u64 * chunk - report.cycles;
        let native_output =
            native_verify_unified_l1_feeder(build_unified_stream(&state.setups, &state.proof))?;
        let chain = rebuild_chain(&state.chain_end_params)?;
        let role = if layer == 0 { "first" } else { "recurrent" };
        let fixture = LayerFixture {
            fixture_schema_version: FIXTURE_SCHEMA_VERSION,
            layer,
            role: role.into(),
            feeder_layers: state.feeder_layers,
            prediction: report.clone(),
            predicted_instances,
            instances,
            chunk_margin_cycles,
            native_output,
            chain_hash: chain.hash(),
            proof: state.proof.clone(),
            setups: state.setups.clone(),
            chain_end_params: state.chain_end_params.clone(),
            program_cycles: state.program_cycles,
        };
        write_compact(&self.sink.join(format!("layer_{layer}.json")), &fixture)?;
        println!(
            "feeder layer {layer} ({role}): prediction {} cycles, predicted {predicted_instances}, proven {instances} instance(s), chunk margin {chunk_margin_cycles}",
            report.cycles
        );
        self.layers.push(LayerSummary {
            layer,
            role: role.into(),
            prediction_cycles: report.cycles,
            predicted_instances,
            instances,
            chunk_margin_cycles,
        });
        Ok(())
    }
}

fn seed_path(dir: &Path) -> PathBuf {
    dir.join("recursion_unified.json")
}

/// The `RecursionUnified` artifact of `input`, proven from the program when
/// the sink holds none.
fn seed(sink: &Path, input: &Input) -> Result<ProofArtifact, String> {
    let path = seed_path(sink);
    if path.exists() {
        return read_typed(&path);
    }
    preflight("seed", 125);
    let source = source(input);
    let base = {
        let mut prover = ProgramProver::new(source.clone(), config(ProofTarget::Base))?;
        prover.prove_words(0, input.nd_words.clone())?
    };
    let mut artifact = {
        let mut prover =
            ProgramProver::for_continuation(source, config(ProofTarget::RecursionUnified), &base)?;
        prover.continue_artifact(base)?
    };
    artifact.timings_ms = ProofTimingsMs::default();
    write_compact(&path, &artifact)?;
    Ok(artifact)
}

/// Produce the feeder chain of `input` into `sink`: every layer, the final
/// `L1Feeder` artifact, the wrap-program run and the manifest.
fn generate_input(sink: &Path, input: &Input) -> Result<Vec<String>, String> {
    deterministic_pow_required();
    fs::create_dir_all(sink).map_err(|error| format!("feeder reference sink: {error}"))?;
    let seed = seed(sink, input)?;
    preflight("feeder", 75);
    let source = source(input);
    let loaded = load_program(&source)?;
    let mut prover = ProgramProver::for_continuation(source, config(ProofTarget::L1Feeder), &seed)?;
    let mut recorder = Recorder {
        sink,
        layers: vec![],
    };
    let (state, _) = prover.feeder_layers_observed(seed, &mut recorder)?;
    let (report, native_output) = prover.wrap_program_run(&state)?;
    let rejection = validate_wrap_report(&report, &native_output).err();
    println!(
        "wrap program over the last feeder proof: {} cycles (limit {L1_WRAP_PROGRAM_CYCLE_LIMIT}), windows {:?}, min sp 0x{:08x}, rejection {rejection:?}",
        report.cycles, report.touched_windows, report.min_sp
    );
    write_compact(
        &sink.join("wrap_run.json"),
        &WrapRunFixture {
            fixture_schema_version: FIXTURE_SCHEMA_VERSION,
            report: report.clone(),
            native_output,
            cycle_limit: L1_WRAP_PROGRAM_CYCLE_LIMIT as u64,
            rejection: rejection.clone(),
        },
    )?;
    let mut artifact = prover.finalize_state(&loaded, state, seed_batch_id());
    artifact.timings_ms = ProofTimingsMs::default();
    write_compact(&sink.join("l1_feeder.json"), &artifact)?;
    let blake = prover.fsv.modes();
    let mut names: Vec<String> = (0..recorder.layers.len())
        .map(|layer| format!("layer_{layer}.json"))
        .collect();
    names.extend([
        "recursion_unified.json".into(),
        "l1_feeder.json".into(),
        "wrap_run.json".into(),
    ]);
    let files = names
        .iter()
        .map(|name| {
            let bytes = read_bytes(&sink.join(name))?;
            Ok((name.clone(), bytes.len() as u64, hex_digest(&bytes)))
        })
        .collect::<Result<Vec<_>, String>>()?;
    write_compact(
        &sink.join("manifest.json"),
        &Manifest {
            fixture_schema_version: FIXTURE_SCHEMA_VERSION,
            input: input.name.into(),
            nd_words: input.nd_words.clone(),
            program_bin_keccak256: hex_digest(&loaded.bin_bytes),
            program_text_keccak256: hex_digest(&loaded.text_bytes),
            fsv: fsv_identities()?,
            feeder_queries_and_pow: L1_FEEDER_QUERIES_AND_POW.to_vec(),
            blake_unrolled: blake.unrolled.tag().into(),
            blake_bridge: blake.bridge.tag().into(),
            blake_final: blake.final_layer.tag().into(),
            layers: recorder.layers.clone(),
            wrap_cycles: report.cycles,
            wrap_rejection: rejection,
            files,
        },
    )?;
    names.push("manifest.json".into());
    Ok(names)
}

const fn seed_batch_id() -> u64 {
    0
}

fn load_manifest(dir: &Path) -> Result<Manifest, String> {
    read_typed(&dir.join("manifest.json"))
}

fn load_layer(dir: &Path, layer: usize) -> Result<LayerFixture, String> {
    read_typed(&dir.join(format!("layer_{layer}.json")))
}

fn stream_of(fixture: &LayerFixture) -> Vec<u32> {
    build_unified_stream(&fixture.setups, &fixture.proof)
}

fn feeder_program(program: FsvProgram) -> ProgramWords {
    load_fsv_program(fsv_dir(), program, BlakeMode::BlakeSpecialOpcodes)
}

/// Every input's fixtures, verified: file identities, every layer natively
/// verified and chained, the final artifact against the trusted chain.
fn verify_input(dir: &Path, input: &Input) -> Result<Manifest, String> {
    let manifest = load_manifest(dir)?;
    if manifest.input != input.name || manifest.nd_words != input.nd_words {
        return Err(format!(
            "feeder reference {} manifest names another input",
            input.name
        ));
    }
    if manifest.feeder_queries_and_pow != L1_FEEDER_QUERIES_AND_POW.to_vec() {
        return Err(format!(
            "feeder reference {} was produced under another feeder config: {:?}",
            input.name, manifest.feeder_queries_and_pow
        ));
    }
    if serde_json::to_vec(&manifest.fsv).unwrap() != serde_json::to_vec(&fsv_identities()?).unwrap()
    {
        return Err(format!(
            "feeder reference {} fsv identity mismatch",
            input.name
        ));
    }
    for (name, bytes, digest) in &manifest.files {
        let actual = read_bytes(&dir.join(name))?;
        if actual.len() as u64 != *bytes || hex_digest(&actual) != *digest {
            return Err(format!(
                "feeder reference {} file {name} differs from its manifest",
                input.name
            ));
        }
    }
    let source = source(input);
    let seed: ProofArtifact = read_typed(&seed_path(dir))?;
    verify_artifact(&seed, &source)?;
    let mut previous_instances = None;
    let mut previous_history = seed.chain_end_params.clone();
    for (layer, summary) in manifest.layers.iter().enumerate() {
        let fixture = load_layer(dir, layer)?;
        if fixture.layer as usize != layer
            || fixture.feeder_layers as usize != layer + 1
            || fixture.instances != summary.instances
            || fixture.predicted_instances != summary.predicted_instances
            || fixture.prediction.cycles != summary.prediction_cycles
        {
            return Err(format!(
                "feeder reference {} layer {layer} disagrees with its manifest",
                input.name
            ));
        }
        let instances = feeder_proof_instances(&fixture.proof, Some(fixture.predicted_instances))?;
        if let Some(previous) = previous_instances {
            if instances >= previous {
                return Err(format!(
                    "feeder reference {} layer {layer} did not converge",
                    input.name
                ));
            }
        }
        if fixture.chain_end_params.len() != previous_history.len() + 1
            || fixture.chain_end_params[..previous_history.len()] != previous_history[..]
        {
            return Err(format!(
                "feeder reference {} layer {layer} history does not extend the previous layer",
                input.name
            ));
        }
        let chain = rebuild_chain(&fixture.chain_end_params)?;
        if chain.hash() != fixture.chain_hash {
            return Err(format!(
                "feeder reference {} layer {layer} chain hash mismatch",
                input.name
            ));
        }
        let output = native_verify_unified_l1_feeder(stream_of(&fixture))?;
        if output != fixture.native_output {
            return Err(format!(
                "feeder reference {} layer {layer} native output mismatch",
                input.name
            ));
        }
        ensure_recursion_chain_binds_program(&output, &chain.hash())?;
        previous_instances = Some(instances);
        previous_history = fixture.chain_end_params.clone();
    }
    if previous_instances != Some(1) {
        return Err(format!(
            "feeder reference {} does not end at one instance",
            input.name
        ));
    }
    let artifact: ProofArtifact = read_typed(&dir.join("l1_feeder.json"))?;
    if artifact.target != ProofTarget::L1Feeder
        || artifact.feeder_layers as usize != manifest.layers.len()
        || artifact.chain_end_params != previous_history
    {
        return Err(format!(
            "feeder reference {} final artifact disagrees with its layers",
            input.name
        ));
    }
    verify_artifact(&artifact, &source)?;
    Ok(manifest)
}

fn disposable_dir(purpose: &str) -> PathBuf {
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../target"));
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("feeder reference staging clock")
        .as_nanos();
    target
        .join("l1_feeder_reference_staging")
        .join(format!("{purpose}-{}-{nonce}", std::process::id()))
}

/// Produce the fixtures of every input into the fixture directory (seeds are
/// reused when present).
#[test]
#[ignore = "produces the CPU feeder chains of three inputs: hours, up to ~125 GiB"]
fn generate_feeder_reference() {
    let reference = fixture_dir();
    for input in inputs() {
        let dir = reference.join(input.name);
        let sink = disposable_dir(input.name);
        fs::create_dir_all(&sink).unwrap();
        if seed_path(&dir).exists() {
            fs::copy(seed_path(&dir), seed_path(&sink)).unwrap();
        }
        let names = generate_input(&sink, &input).expect("feeder reference generation");
        fs::create_dir_all(&dir).unwrap();
        for name in names {
            fs::rename(sink.join(&name), dir.join(&name))
                .expect("feeder reference promotes the fixture set");
        }
        fs::remove_dir_all(sink).ok();
        println!(
            "feeder reference {} written to {}",
            input.name,
            dir.display()
        );
    }
}

#[test]
#[ignore = "natively verifies the committed feeder chains and recomputes their trusted setups"]
fn verify_feeder_reference() {
    for input in inputs() {
        let manifest = verify_input(&fixture_dir().join(input.name), &input).unwrap();
        println!(
            "feeder reference {}: layers {:?}, wrap {} cycles, rejection {:?}",
            input.name,
            manifest
                .layers
                .iter()
                .map(|layer| (
                    layer.predicted_instances,
                    layer.instances,
                    layer.prediction_cycles
                ))
                .collect::<Vec<_>>(),
            manifest.wrap_cycles,
            manifest.wrap_rejection
        );
    }
}

/// Fresh production versus resumption from the `RecursionUnified` seed and
/// from a multi-instance mid-chain layer: identical proofs, setups, chain
/// and outputs (timing excluded).
#[test]
#[ignore = "reproves the basic_fibonacci feeder chain twice: ~1 h CPU"]
fn resumed_feeder_chains_match_the_fresh_chain() {
    let input = inputs().remove(0);
    let dir = fixture_dir().join(input.name);
    let manifest = load_manifest(&dir).unwrap();
    let fresh: ProofArtifact = read_typed(&dir.join("l1_feeder.json")).unwrap();
    let source = source(&input);
    // from the seed
    let sink = disposable_dir("resume-seed");
    fs::create_dir_all(&sink).unwrap();
    fs::copy(seed_path(&dir), seed_path(&sink)).unwrap();
    generate_input(&sink, &input).unwrap();
    let from_seed: ProofArtifact = read_typed(&sink.join("l1_feeder.json")).unwrap();
    assert_eq!(
        serde_json::to_vec(&from_seed).unwrap(),
        serde_json::to_vec(&fresh).unwrap()
    );
    // from the first multi-instance layer
    let mid = manifest
        .layers
        .iter()
        .find(|layer| layer.instances > 1)
        .expect("a multi-instance layer to resume from");
    let fixture = load_layer(&dir, mid.layer as usize).unwrap();
    let checkpoint = ProofArtifact {
        target: ProofTarget::RecursionUnified,
        feeder_layers: fixture.feeder_layers,
        chain_end_params: fixture.chain_end_params.clone(),
        chain_hash: rebuild_chain(&fixture.chain_end_params).unwrap().hash(),
        chain_preimage: rebuild_chain(&fixture.chain_end_params).unwrap().preimage(),
        proof: fixture.proof.clone(),
        setups: fixture.setups.clone(),
        proof_counts: ProofCounts::from_proof(&fixture.proof),
        cycles: fixture.proof.executed_cycles(),
        ..fresh.clone()
    };
    let loaded = load_program(&source).unwrap();
    let mut prover =
        ProgramProver::for_continuation(source.clone(), config(ProofTarget::L1Feeder), &checkpoint)
            .unwrap();
    let (state, _) = prover
        .feeder_layers_observed(checkpoint, &mut NoopObserver)
        .unwrap();
    let mut resumed = prover.finalize_state(&loaded, state, seed_batch_id());
    resumed.timings_ms = ProofTimingsMs::default();
    assert_eq!(
        serde_json::to_vec(&resumed.proof).unwrap(),
        serde_json::to_vec(&fresh.proof).unwrap()
    );
    assert_eq!(resumed.setups, fresh.setups);
    assert_eq!(resumed.chain_end_params, fresh.chain_end_params);
    assert_eq!(resumed.feeder_layers, fresh.feeder_layers);
    verify_artifact(&resumed, &source).unwrap();
    fs::remove_dir_all(sink).ok();
}

/// The merge-margin gate: the production regular-link feeder verifies a
/// two-instance feeder proof inside one 2^22 chunk, and the fixture's next
/// layer is one instance.
#[test]
#[ignore = "runs the production feeder verifier over the two-instance fixtures"]
fn production_feeder_merge_gate() {
    let program = feeder_program(FsvProgram::UnifiedRecursionLayerL1Feeder);
    let chunk = UnrolledCircuitType::Unified22.get_domain_size() as u64;
    let mut found = false;
    for input in inputs() {
        let dir = fixture_dir().join(input.name);
        let manifest = load_manifest(&dir).unwrap();
        for (layer, summary) in manifest.layers.iter().enumerate() {
            if summary.instances != 2 {
                continue;
            }
            found = true;
            let fixture = load_layer(&dir, layer).unwrap();
            let next = load_layer(&dir, layer + 1).unwrap();
            assert_eq!(
                next.instances,
                1,
                "{}: layer {} after the two-instance layer",
                input.name,
                layer + 1
            );
            let report = ProductionFeederVerifier
                .predict(&program, stream_of(&fixture))
                .unwrap();
            assert_eq!(
                report.output, fixture.native_output,
                "{}: native output",
                input.name
            );
            assert_eq!(
                report.nd_words_remaining, 0,
                "{}: input exhausted",
                input.name
            );
            assert_eq!(
                delegation_calls(&report.counters),
                0,
                "{}: delegation calls",
                input.name
            );
            assert!(
                report.cycles < chunk,
                "{}: {} cycles is not below one chunk",
                input.name,
                report.cycles
            );
            println!(
                "merge gate {}: layer {layer} two-instance proof verifies in {} cycles, margin {} ({:.2}%), windows {:?}, min sp 0x{:08x}",
                input.name,
                report.cycles,
                chunk - report.cycles,
                (chunk - report.cycles) as f64 * 100.0 / chunk as f64,
                report.touched_windows,
                report.min_sp
            );
        }
    }
    assert!(
        found,
        "no two-instance feeder proof among the fixtures: the merge gate is unsatisfied"
    );
}

/// The wrap gate: the canonical 512 KiB-link wrap program over every
/// input's last feeder proof, within 2^21 cycles with every requirement.
#[test]
#[ignore = "runs the canonical wrap program over the last feeder proofs"]
fn production_wrap_program_gate() {
    let program = feeder_program(FsvProgram::UnifiedRecursionLayerL1FeederWrap);
    let mut min_margin = u64::MAX;
    for input in inputs() {
        let dir = fixture_dir().join(input.name);
        let manifest = load_manifest(&dir).unwrap();
        let fixture = load_layer(&dir, manifest.layers.len() - 1).unwrap();
        assert_eq!(fixture.instances, 1);
        let report = ProductionFeederVerifier
            .wrap_run(&program, stream_of(&fixture))
            .unwrap();
        validate_wrap_report(&report, &fixture.native_output).unwrap();
        let margin = L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - report.cycles;
        min_margin = min_margin.min(margin);
        println!(
            "wrap gate {}: {} cycles, margin {margin} ({:.2}%), windows {:?}, max address 0x{:08x}, min sp 0x{:08x}",
            input.name,
            report.cycles,
            margin as f64 * 100.0 / L1_WRAP_PROGRAM_CYCLE_LIMIT as f64,
            report.touched_windows,
            report.max_touched_address,
            report.min_sp
        );
    }
    println!("wrap gate minimum margin over the inputs: {min_margin} cycles");
}

/// The delegation count words of a feeder stream: one per
/// `DELEGATION_TYPES` entry, right before the PoW words and the chain
/// preimage.
fn delegation_count_offsets(stream: &[u32]) -> std::ops::Range<usize> {
    let tail = 2 + 16;
    let types = full_statement_verifier::definitions::DELEGATION_TYPES.len();
    stream.len() - tail - types..stream.len() - tail
}

#[test]
#[ignore = "runs the native and VM feeder verifiers over mutated fixtures"]
fn feeder_negative_controls() {
    let input = inputs().remove(0);
    let dir = fixture_dir().join(input.name);
    let manifest = load_manifest(&dir).unwrap();
    let last = load_layer(&dir, manifest.layers.len() - 1).unwrap();
    let stream = stream_of(&last);
    let feeder = feeder_program(FsvProgram::UnifiedRecursionLayerL1Feeder);
    let wrap = feeder_program(FsvProgram::UnifiedRecursionLayerL1FeederWrap);
    // the valid stream verifies natively and on both guest builds
    let native = native_verify_unified_l1_feeder(stream.clone()).unwrap();
    assert_eq!(native, last.native_output);
    assert_eq!(
        ProductionFeederVerifier
            .predict(&feeder, stream.clone())
            .unwrap()
            .output,
        native
    );
    assert_eq!(
        ProductionFeederVerifier
            .wrap_run(&wrap, stream.clone())
            .unwrap()
            .output,
        native
    );
    // every delegation count slot set to 1: rejected at the read
    for offset in delegation_count_offsets(&stream) {
        let mut mutated = stream.clone();
        assert_eq!(mutated[offset], 0);
        mutated[offset] = 1;
        let error = native_verify_unified_l1_feeder(mutated.clone()).unwrap_err();
        assert!(
            error.contains("no delegation proofs"),
            "slot {offset}: {error}"
        );
        assert!(
            ProductionFeederVerifier
                .predict(&feeder, mutated.clone())
                .is_err(),
            "regular guest slot {offset}"
        );
        assert!(
            ProductionFeederVerifier.wrap_run(&wrap, mutated).is_err(),
            "wrap guest slot {offset}"
        );
    }
    // trailing words and truncation
    let mut trailing = stream.clone();
    trailing.push(7);
    assert!(native_verify_unified_l1_feeder(trailing.clone())
        .unwrap_err()
        .contains("trailing"));
    assert!(
        ProductionFeederVerifier
            .predict(&feeder, trailing)
            .unwrap()
            .nd_words_remaining
            == 1
    );
    let truncated = stream[..stream.len() - 1].to_vec();
    assert!(native_verify_unified_l1_feeder(truncated.clone()).is_err());
    assert!(ProductionFeederVerifier
        .predict(&feeder, truncated)
        .is_err());
    // setup cap leaf 31, one bit
    let mut leaf_flip = stream.clone();
    leaf_flip[31 * 8] ^= 1;
    assert!(native_verify_unified_l1_feeder(leaf_flip.clone()).is_err());
    assert!(ProductionFeederVerifier
        .predict(&feeder, leaf_flip)
        .is_err());
    // artifact-level rejections
    let artifact: ProofArtifact = read_typed(&dir.join("l1_feeder.json")).unwrap();
    let source = source(&input);
    verify_artifact(&artifact, &source).unwrap();
    let mut stale = artifact.clone();
    stale.schema_version = LEGACY_ARTIFACT_SCHEMA_VERSION;
    assert!(verify_artifact(&stale, &source)
        .unwrap_err()
        .contains("stale"));
    let mut off_by_one = artifact.clone();
    off_by_one.feeder_layers += 1;
    assert!(verify_artifact(&off_by_one, &source).is_err());
    let mut off_by_one = artifact.clone();
    off_by_one.feeder_layers -= 1;
    assert!(verify_artifact(&off_by_one, &source).is_err());
    let mut stale_chain = artifact.clone();
    stale_chain.chain_hash[0] ^= 1;
    assert!(verify_artifact(&stale_chain, &source).is_err());
    let mut dropped_entry = artifact.clone();
    dropped_entry.chain_end_params.pop();
    assert!(verify_artifact(&dropped_entry, &source).is_err());
    // a multi-instance layer presented as the last feeder
    if let Some(mid) = manifest.layers.iter().find(|layer| layer.instances > 1) {
        let fixture = load_layer(&dir, mid.layer as usize).unwrap();
        let mut wrong_shape = artifact.clone();
        wrong_shape.proof = fixture.proof;
        wrong_shape.setups = fixture.setups;
        assert!(verify_artifact(&wrong_shape, &source)
            .unwrap_err()
            .contains("instance"));
    }
    // repeated equal recurrent entries keep the chain hash
    if artifact.feeder_layers >= 2 {
        let n = artifact.chain_end_params.len();
        let mut repeated = artifact.chain_end_params.clone();
        repeated.push(artifact.chain_end_params[n - 1]);
        assert_eq!(
            rebuild_chain(&repeated).unwrap().hash(),
            rebuild_chain(&artifact.chain_end_params).unwrap().hash()
        );
    }
}
