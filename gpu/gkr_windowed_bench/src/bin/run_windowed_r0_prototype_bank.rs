use std::env;
use std::ffi::CStr;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use era_cudart::device::{get_device, get_device_properties};
use era_cudart::result::CudaResultWrap;
use era_cudart_sys::CudaError;
use serde::Serialize;

use gpu_gkr_windowed_bench::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
use gpu_gkr_windowed_bench::r0_harness::{
    production_memory_preflight, r0_cells_sha256, R0TimingConfig,
};
use gpu_gkr_windowed_bench::r0_input::{build_prepared_r0_production_input, build_r0_input};
use gpu_gkr_windowed_bench::r0_prototype_harness::{
    R0PrototypeDeviceCapacity, R0PrototypeHarness, R0PrototypeLaunchability,
    R0PrototypePayloadCache, R0PrototypeRunConfig,
};
use gpu_gkr_windowed_bench::r0_prototype_kernels::{
    r0_prototype_link_proof_summary, r0_sectioned_manifest_sha256, r0_sectioned_shape_merge_policy,
    R0SectionedShapePolicy,
};
use gpu_gkr_windowed_bench::r0_prototype_manifest::{
    build_r0_sectioned_manifest_v4_for_merge_policy, r0_sectioned_compatible_compiled_shapes,
    resolve_r0_sectioned_compiled_shape, R0Lineage, R0PrototypeManifestV1, R0SectionedManifestV1,
    R0SectionedSymbolV1,
};
use gpu_gkr_windowed_bench::r0_prototype_report::{
    parse_nvidia_smi_clock_policy, validate_device_capacity_identity,
    validate_launchability_against_identity, R0PrototypeDeviceIdentityV2, R0PrototypeObservationV2,
    R0PrototypeTimingPhaseV2, R0PrototypeTimingSampleV2, R0_PROTOTYPE_REPORT_VERSION,
};

unsafe extern "C" {
    fn cudaDriverGetVersion(version: *mut i32) -> CudaError;
    fn cudaRuntimeGetVersion(version: *mut i32) -> CudaError;
}

const RETAINED_ADD_SUB_LOG3_CHECKSUM: &str =
    "73d6ebcb2515e42e761928222437a43932be9ec940276acdd7775d33b2508721";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    LinkProof,
    DeviceInfo,
    ReferenceSmoke,
    Correctness,
    SectionedCorrectness,
    SectionedMatrix,
    SectionedScreen,
    Screen,
}

impl Mode {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "link-proof" => Ok(Self::LinkProof),
            "device-info" => Ok(Self::DeviceInfo),
            "reference-smoke" => Ok(Self::ReferenceSmoke),
            "correctness" => Ok(Self::Correctness),
            "sectioned-correctness" => Ok(Self::SectionedCorrectness),
            "sectioned-matrix" => Ok(Self::SectionedMatrix),
            "sectioned-screen" => Ok(Self::SectionedScreen),
            "screen" => Ok(Self::Screen),
            _ => Err(format!("invalid prototype mode {value}")),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RuntimeOptions {
    repo_root: PathBuf,
    corpus: PathBuf,
    artifact_root: PathBuf,
    output_root: PathBuf,
    candidates: Vec<String>,
    coordinates: Vec<String>,
    mode: Mode,
    log_trace: Option<u32>,
    seed: u64,
    sectioned_shape: R0SectionedShapePolicy,
}

impl RuntimeOptions {
    fn parse() -> Result<Self, String> {
        let args = env::args().skip(1).collect::<Vec<_>>();
        Self::parse_with(&args, |name| env::var(name).ok())
    }

    fn parse_with<F>(args: &[String], env_value: F) -> Result<Self, String>
    where
        F: Fn(&str) -> Option<String>,
    {
        let cwd = env::current_dir().map_err(|error| format!("read current directory: {error}"))?;
        let executable =
            env::current_exe().map_err(|error| format!("read current executable: {error}"))?;
        Self::parse_with_context(args, env_value, &cwd, &executable)
    }

    fn parse_with_context<F>(
        args: &[String],
        env_value: F,
        cwd: &Path,
        executable: &Path,
    ) -> Result<Self, String>
    where
        F: Fn(&str) -> Option<String>,
    {
        let mut repo = env_value("AB_R0_PROTOTYPE_REPO_ROOT").map(PathBuf::from);
        let mut corpus = env_value("AB_R0_PROTOTYPE_CORPUS").map(PathBuf::from);
        let mut artifact_root = env_value("AB_R0_PROTOTYPE_ARTIFACT_ROOT").map(PathBuf::from);
        let mut output_root = env_value("AB_R0_PROTOTYPE_OUTPUT_ROOT").map(PathBuf::from);
        let mut candidates = split_list(env_value("AB_R0_PROTOTYPE_CANDIDATES"));
        let mut coordinates = split_list(env_value("AB_R0_PROTOTYPE_COORDINATES"));
        let mut mode = Mode::parse(
            env_value("AB_R0_PROTOTYPE_MODE")
                .as_deref()
                .unwrap_or("link-proof"),
        )?;
        let mut log_trace = None;
        let mut seed = 0u64;
        let mut sectioned_shape = R0SectionedShapePolicy::Exact;
        let mut sectioned_shape_explicit = false;

        let mut index = 0usize;
        while index < args.len() {
            let option = &args[index];
            let value = |index: &mut usize| -> Result<&str, String> {
                *index += 1;
                args.get(*index)
                    .map(String::as_str)
                    .ok_or_else(|| format!("{option} requires a value"))
            };
            match option.as_str() {
                "--repo-root" => repo = Some(PathBuf::from(value(&mut index)?)),
                "--corpus" => corpus = Some(PathBuf::from(value(&mut index)?)),
                "--artifact-root" => artifact_root = Some(PathBuf::from(value(&mut index)?)),
                "--output-root" => output_root = Some(PathBuf::from(value(&mut index)?)),
                "--candidate" => candidates = split_csv(value(&mut index)?),
                "--coordinate" => coordinates = split_csv(value(&mut index)?),
                "--mode" => mode = Mode::parse(value(&mut index)?)?,
                "--log" => {
                    log_trace = Some(
                        value(&mut index)?
                            .parse()
                            .map_err(|error| format!("invalid --log: {error}"))?,
                    )
                }
                "--seed" => {
                    seed = value(&mut index)?
                        .parse()
                        .map_err(|error| format!("invalid --seed: {error}"))?
                }
                "--sectioned-shape" => {
                    sectioned_shape = match value(&mut index)? {
                        "exact" => R0SectionedShapePolicy::Exact,
                        "compatible" => R0SectionedShapePolicy::Compatible,
                        "universal" => R0SectionedShapePolicy::Universal,
                        value => return Err(format!("invalid --sectioned-shape {value}")),
                    };
                    sectioned_shape_explicit = true;
                }
                "--help" => return Err(usage().to_owned()),
                _ => return Err(format!("unknown option {option}\n{}", usage())),
            }
            index += 1;
        }
        let repo = match repo {
            Some(path) => validate_repository_root(&path)?,
            None => discover_repository_root(cwd, executable)?,
        };
        let corpus = resolve_runtime_path(
            corpus,
            &repo,
            "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.bin",
        );
        let artifact_root =
            resolve_runtime_path(artifact_root, &repo, "gpu/gkr_windowed_bench/artifacts");
        let output_root = resolve_runtime_path(
            output_root,
            &repo,
            "target/windowed-gkr-r0-prototype-bank/runtime",
        );
        if sectioned_shape_explicit && mode != Mode::SectionedCorrectness {
            return Err("--sectioned-shape is valid only for sectioned-correctness".to_owned());
        }
        Ok(Self {
            repo_root: repo,
            corpus,
            artifact_root,
            output_root,
            candidates,
            coordinates,
            mode,
            log_trace,
            seed,
            sectioned_shape,
        })
    }
}

fn resolve_runtime_path(path: Option<PathBuf>, repo: &Path, default: &str) -> PathBuf {
    match path {
        Some(path) if path.is_absolute() => path,
        Some(path) => repo.join(path),
        None => repo.join(default),
    }
}

fn validate_repository_root(path: &Path) -> Result<PathBuf, String> {
    let path = path
        .canonicalize()
        .map_err(|error| format!("resolve repository root {}: {error}", path.display()))?;
    if !path.join("Cargo.toml").is_file()
        || !path.join("gpu/gkr_windowed_bench/Cargo.toml").is_file()
    {
        return Err(format!(
            "repository root {} lacks Cargo.toml and gpu/gkr_windowed_bench/Cargo.toml",
            path.display()
        ));
    }
    Ok(path)
}

fn discover_repository_root(cwd: &Path, executable: &Path) -> Result<PathBuf, String> {
    for start in [Some(cwd), executable.parent()].into_iter().flatten() {
        for candidate in start.ancestors() {
            if candidate.join("Cargo.toml").is_file()
                && candidate
                    .join("gpu/gkr_windowed_bench/Cargo.toml")
                    .is_file()
            {
                return validate_repository_root(candidate);
            }
        }
    }
    Err(format!(
        "discover repository root from cwd={} or executable={}; pass --repo-root or AB_R0_PROTOTYPE_REPO_ROOT",
        cwd.display(),
        executable.display()
    ))
}

fn usage() -> &'static str {
    "run_windowed_r0_prototype_bank [--mode link-proof|device-info|reference-smoke|correctness|sectioned-correctness|sectioned-matrix|sectioned-screen|screen] [--repo-root PATH] [--corpus PATH] [--artifact-root PATH] [--output-root PATH] [--candidate ID,...] [--coordinate CIRCUIT:LAYER,...] [--sectioned-shape exact|compatible|universal] [--log N] [--seed N]"
}

fn ensure_sectioned_runtime_available() -> Result<(), String> {
    #[cfg(r0_prototype_bank_full)]
    {
        Ok(())
    }
    #[cfg(not(r0_prototype_bank_full))]
    {
        Err(
            "sectioned execution requires GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE=full and CUDAARCHS=120"
                .to_owned(),
        )
    }
}

fn split_list(value: Option<String>) -> Vec<String> {
    value.as_deref().map(split_csv).unwrap_or_default()
}

fn split_csv(value: &str) -> Vec<String> {
    value
        .split(',')
        .map(str::trim)
        .filter(|item| !item.is_empty())
        .map(str::to_owned)
        .collect()
}

fn cuda_uuid(bytes: &[std::os::raw::c_char; 16]) -> String {
    let bytes = bytes.map(|byte| byte as u8);
    format!(
        "GPU-{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        bytes[0],
        bytes[1],
        bytes[2],
        bytes[3],
        bytes[4],
        bytes[5],
        bytes[6],
        bytes[7],
        bytes[8],
        bytes[9],
        bytes[10],
        bytes[11],
        bytes[12],
        bytes[13],
        bytes[14],
        bytes[15]
    )
}

fn query_device_identity() -> Result<R0PrototypeDeviceIdentityV2, Box<dyn std::error::Error>> {
    let cuda_device_index = get_device()?;
    let properties = get_device_properties(cuda_device_index)?;
    let capacity = R0PrototypeDeviceCapacity::query()?;
    let name = unsafe { CStr::from_ptr(properties.name.as_ptr()) }
        .to_str()?
        .to_owned();
    let uuid = cuda_uuid(&properties.uuid.bytes);
    let mut cuda_driver_version = 0i32;
    let mut cuda_runtime_version = 0i32;
    unsafe {
        cudaDriverGetVersion(&mut cuda_driver_version).wrap()?;
        cudaRuntimeGetVersion(&mut cuda_runtime_version).wrap()?;
    }
    let query = [
        "uuid",
        "name",
        "compute_cap",
        "driver_version",
        "pstate",
        "persistence_mode",
        "clocks.current.graphics",
        "clocks.current.memory",
        "clocks.max.graphics",
        "clocks.max.memory",
        "clocks.applications.graphics",
        "clocks.applications.memory",
        "clocks_event_reasons.active",
    ]
    .join(",");
    let output = Command::new("nvidia-smi")
        .args([
            "-i",
            &uuid,
            &format!("--query-gpu={query}"),
            "--format=csv,noheader",
        ])
        .output()?;
    if !output.status.success() {
        return Err(format!(
            "nvidia-smi clock-policy query failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        )
        .into());
    }
    let clock_policy = parse_nvidia_smi_clock_policy(std::str::from_utf8(&output.stdout)?)?;
    if !clock_policy.uuid.eq_ignore_ascii_case(&uuid)
        || clock_policy.name != name
        || clock_policy.compute_capability != format!("{}.{}", properties.major, properties.minor)
    {
        return Err("CUDA and nvidia-smi device identity disagree".into());
    }
    let identity = R0PrototypeDeviceIdentityV2 {
        cuda_device_index,
        uuid,
        name,
        compute_capability_major: properties.major,
        compute_capability_minor: properties.minor,
        cuda_driver_version,
        cuda_runtime_version,
        cuda_toolkit_version: env!("GPU_GKR_CUDA_TOOLKIT_VERSION").to_owned(),
        default_shared_memory_bytes: usize::try_from(capacity.default_shared_bytes)?,
        opt_in_shared_memory_bytes: usize::try_from(capacity.opt_in_shared_bytes)?,
        clock_policy,
    };
    if properties.sharedMemPerBlock != identity.default_shared_memory_bytes
        || properties.sharedMemPerBlockOptin != identity.opt_in_shared_memory_bytes
    {
        return Err(
            "CUDA properties and launch attributes disagree on shared-memory capacity".into(),
        );
    }
    validate_device_capacity_identity(&identity, capacity)?;
    Ok(identity)
}

fn checked_inputs(
    options: &RuntimeOptions,
) -> Result<
    (
        gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
        R0PrototypeManifestV1,
    ),
    Box<dyn std::error::Error>,
> {
    let corpus = fs::read(&options.corpus)?;
    if corpus != R0_CORPUS_BYTES {
        return Err(format!(
            "runtime corpus {} differs from the embedded checked bundle",
            options.corpus.display()
        )
        .into());
    }
    let bundle = decode_r0_bundle(&corpus)?;
    let manifest_bytes = fs::read(
        options
            .artifact_root
            .join("windowed_r0_prototype_manifest_v1.json"),
    )?;
    let manifest: R0PrototypeManifestV1 = serde_json::from_slice(&manifest_bytes)?;
    let expected = R0PrototypeHarness::manifest()?;
    if manifest != expected {
        return Err("runtime prototype manifest differs from the compiled manifest".into());
    }
    Ok((bundle, manifest))
}

fn checked_sectioned_manifest(
    options: &RuntimeOptions,
) -> Result<R0SectionedManifestV1, Box<dyn std::error::Error>> {
    let bytes = fs::read(
        options
            .artifact_root
            .join("windowed_r0_sectioned_manifest_v4.json"),
    )?;
    let observed: R0SectionedManifestV1 = serde_json::from_slice(&bytes)?;
    if observed
        != build_r0_sectioned_manifest_v4_for_merge_policy(r0_sectioned_shape_merge_policy())?
    {
        return Err("runtime sectioned manifest differs from the compiled manifest".into());
    }
    Ok(observed)
}

fn selected_coordinates<'a>(
    options: &RuntimeOptions,
    bundle: &'a gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
) -> Result<Vec<&'a gpu_gkr_windowed_bench::r0_artifact::FrozenR0Coordinate>, String> {
    let mut selected = Vec::new();
    for coordinate in &bundle.coordinates {
        let key = format!("{}:{}", coordinate.circuit, coordinate.layer);
        if options.coordinates.is_empty() || options.coordinates.contains(&key) {
            selected.push(coordinate);
        }
    }
    for requested in &options.coordinates {
        if !selected
            .iter()
            .any(|coordinate| format!("{}:{}", coordinate.circuit, coordinate.layer) == *requested)
        {
            return Err(format!("unknown prototype coordinate {requested}"));
        }
    }
    Ok(selected)
}

fn selected_configs(
    options: &RuntimeOptions,
    manifest: &R0PrototypeManifestV1,
) -> Result<Vec<R0PrototypeRunConfig>, Box<dyn std::error::Error>> {
    let manifest_order = || {
        manifest
            .configurations
            .iter()
            .map(|measurement| {
                R0PrototypeRunConfig::resolve(manifest, &measurement.configuration_id)
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let rows = if options.mode == Mode::ReferenceSmoke {
        manifest_order()?
            .into_iter()
            .filter(|row| row.candidate.lineage == R0Lineage::Reference)
            .collect()
    } else if options.candidates.is_empty() {
        manifest_order()?
    } else {
        let mut rows = Vec::new();
        for requested in &options.candidates {
            let matches = manifest
                .configurations
                .iter()
                .filter(|measurement| {
                    measurement.configuration_id == *requested
                        || measurement.candidate_id == *requested
                })
                .collect::<Vec<_>>();
            if matches.is_empty() {
                return Err(
                    format!("unknown prototype candidate/configuration {requested}").into(),
                );
            }
            for measurement in matches {
                if rows.iter().any(|row: &R0PrototypeRunConfig| {
                    row.measurement.configuration_id == measurement.configuration_id
                }) {
                    continue;
                }
                rows.push(R0PrototypeRunConfig::resolve(
                    manifest,
                    &measurement.configuration_id,
                )?);
            }
        }
        rows
    };
    if rows.is_empty() {
        return Err("prototype selection is empty".into());
    }
    Ok(rows)
}

fn observation(
    harness: &R0PrototypeHarness,
    config: &R0PrototypeRunConfig,
    coordinate: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0Coordinate,
    log_trace: u32,
    seed: u64,
    expected_checksum: &str,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<R0PrototypeObservationV2, Box<dyn std::error::Error>> {
    let descriptor = harness.descriptor(config)?;
    Ok(R0PrototypeObservationV2 {
        version: R0_PROTOTYPE_REPORT_VERSION,
        configuration_id: config.measurement.configuration_id.clone(),
        candidate_id: config.candidate.candidate_id.clone(),
        circuit: coordinate.circuit.clone(),
        layer: coordinate.layer,
        log_trace,
        seed,
        input_sha256: harness.base().hashes().input_sha256.clone(),
        program_sha256: descriptor.program_sha256.clone(),
        tile_sha256: descriptor.tile_sha256.clone(),
        descriptor_bytes: descriptor.payload_size,
        launchability: {
            let launchability = harness.launchability(config)?;
            validate_launchability_against_identity(device_identity, launchability)?;
            launchability
        },
        launch: None,
        cells: None,
        checksum: None,
        expected_checksum: Some(expected_checksum.to_owned()),
        passing: false,
        failure: None,
        device_identity: device_identity.clone(),
    })
}

fn sectioned_observation(
    harness: &R0PrototypeHarness,
    candidate: &R0SectionedSymbolV1,
    coordinate: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0Coordinate,
    log_trace: u32,
    seed: u64,
    expected_checksum: &str,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<R0PrototypeObservationV2, Box<dyn std::error::Error>> {
    let descriptor = harness.sectioned_descriptor();
    let launchability = harness.device_capacity().classify(0);
    validate_launchability_against_identity(device_identity, launchability)?;
    Ok(R0PrototypeObservationV2 {
        version: R0_PROTOTYPE_REPORT_VERSION,
        configuration_id: candidate.candidate_id.clone(),
        candidate_id: candidate.candidate_id.clone(),
        circuit: coordinate.circuit.clone(),
        layer: coordinate.layer,
        log_trace,
        seed,
        input_sha256: harness.base().hashes().input_sha256.clone(),
        program_sha256: descriptor.program_sha256.clone(),
        tile_sha256: None,
        descriptor_bytes: descriptor.payload_size,
        launchability,
        launch: None,
        cells: None,
        checksum: None,
        expected_checksum: Some(expected_checksum.to_owned()),
        passing: false,
        failure: None,
        device_identity: device_identity.clone(),
    })
}

fn run_correctness(
    options: &RuntimeOptions,
    bundle: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
    manifest: &R0PrototypeManifestV1,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<(), Box<dyn std::error::Error>> {
    let configs = selected_configs(options, manifest)?;
    let coordinates = selected_coordinates(options, bundle)?;
    let mut output = io::BufWriter::new(io::stdout().lock());
    for coordinate in coordinates {
        let log_trace = options.log_trace.unwrap_or(3);
        let input = build_r0_input(coordinate, log_trace, options.seed)?;
        let expected_cells = R0PrototypePayloadCache::canonical_expected(coordinate, &input)?;
        let expected_checksum = r0_cells_sha256(&expected_cells)?;
        if options.mode == Mode::ReferenceSmoke
            && (coordinate.circuit != "add_sub_lui_auipc_mop"
                || coordinate.layer != 0
                || log_trace != 3
                || options.seed != 0
                || expected_checksum != RETAINED_ADD_SUB_LOG3_CHECKSUM)
        {
            return Err("reference smoke must match retained add/sub layer0 log3 seed0".into());
        }
        let mut harness = R0PrototypeHarness::new_correctness(coordinate, &input)?;
        validate_device_capacity_identity(device_identity, harness.device_capacity())?;
        for config in &configs {
            let mut row = observation(
                &harness,
                config,
                coordinate,
                log_trace,
                options.seed,
                &expected_checksum,
                device_identity,
            )?;
            match row.launchability {
                R0PrototypeLaunchability::UnlaunchableCapacity { .. } => {
                    row.failure = Some("unlaunchable_capacity".to_owned());
                }
                R0PrototypeLaunchability::Launchable { .. } => {
                    match harness.run_configuration(config) {
                        Ok(observed) => {
                            row.passing = observed.cells == expected_cells;
                            row.cells = Some(observed.cells);
                            row.checksum = Some(observed.checksum);
                            row.launch = Some(observed.launch);
                            if !row.passing {
                                row.failure = Some("canonical_mismatch".to_owned());
                            }
                        }
                        Err(error) => row.failure = Some(error.to_string()),
                    }
                }
            }
            serde_json::to_writer(&mut output, &row)?;
            output.write_all(b"\n")?;
        }
    }
    output.flush()?;
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SectionedCorrectnessPlanRow {
    circuit: String,
    layer: u32,
    log_trace: u32,
    candidate_id: String,
}

fn plan_sectioned_correctness(
    coordinates: &[(String, u32, u16)],
    logs: [u32; 2],
    policy: R0SectionedShapePolicy,
) -> Result<Vec<SectionedCorrectnessPlanRow>, String> {
    let manifest =
        build_r0_sectioned_manifest_v4_for_merge_policy(r0_sectioned_shape_merge_policy())
            .map_err(|error| error.to_string())?;
    let mut rows = Vec::with_capacity(coordinates.len() * logs.len() * 2);
    for (circuit, layer, shape_bits) in coordinates {
        let requested_shapes = match policy {
            R0SectionedShapePolicy::Exact => vec![Some(
                resolve_r0_sectioned_compiled_shape(&manifest, *shape_bits)
                    .map_err(|error| error.to_string())?,
            )],
            R0SectionedShapePolicy::Compatible => {
                r0_sectioned_compatible_compiled_shapes(&manifest, *shape_bits)
                    .map_err(|error| error.to_string())?
                    .into_iter()
                    .map(Some)
                    .collect()
            }
            R0SectionedShapePolicy::Universal => vec![None],
        };
        let candidates = manifest
            .symbols
            .iter()
            .filter(|candidate| requested_shapes.contains(&candidate.shape_bits))
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Err(format!(
                "sectioned plan for {circuit}:{layer} shapes {requested_shapes:?} has {} candidates",
                candidates.len()
            ));
        }
        for log_trace in logs {
            rows.extend(
                candidates
                    .iter()
                    .map(|candidate| SectionedCorrectnessPlanRow {
                        circuit: circuit.clone(),
                        layer: *layer,
                        log_trace,
                        candidate_id: candidate.candidate_id.clone(),
                    }),
            );
        }
    }
    Ok(rows)
}

#[derive(Serialize)]
struct SectionedCorrectnessRow {
    version: u32,
    candidate_id: String,
    symbol: String,
    geometry: String,
    lowered_shape_bits: u16,
    compiled_shape_bits: Option<u16>,
    shape_policy: String,
    min_blocks: Option<u32>,
    manifest_sha256: String,
    executable_sha256: String,
    circuit: String,
    layer: u32,
    log_trace: u32,
    seed: u64,
    input_sha256: String,
    program_sha256: String,
    descriptor_bytes: usize,
    expected_checksum: String,
    checksum: Option<String>,
    cells: Option<[gpu_gkr_windowed_bench::r0_input::FrozenE4; 27]>,
    launch: Option<gpu_gkr_windowed_bench::r0_geometry::R0LaunchMetadata>,
    passing: bool,
    failure: Option<String>,
    device_identity: R0PrototypeDeviceIdentityV2,
}

fn run_sectioned_correctness(
    options: &RuntimeOptions,
    bundle: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
    manifest: &R0SectionedManifestV1,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<(), Box<dyn std::error::Error>> {
    let coordinates = selected_coordinates(options, bundle)?;
    let mut output = io::BufWriter::new(io::stdout().lock());
    for coordinate in coordinates {
        let log_trace = options.log_trace.unwrap_or(3);
        let input = build_r0_input(coordinate, log_trace, options.seed)?;
        let expected_cells = R0PrototypePayloadCache::canonical_expected(coordinate, &input)?;
        let expected_checksum = r0_cells_sha256(&expected_cells)?;
        let (mut harness, lowered_shape_bits, mut candidates) =
            R0PrototypeHarness::new_sectioned_correctness(
                coordinate,
                &input,
                manifest,
                options.sectioned_shape,
            )?;
        validate_device_capacity_identity(device_identity, harness.device_capacity())?;
        if !options.candidates.is_empty() {
            let requested = &options.candidates;
            candidates.retain(|candidate| {
                requested.iter().any(|value| {
                    value == &candidate.candidate_id
                        || value == &candidate.symbol
                        || value == candidate.geometry.as_str()
                })
            });
            for value in requested {
                if !candidates.iter().any(|candidate| {
                    value == &candidate.candidate_id
                        || value == &candidate.symbol
                        || value == candidate.geometry.as_str()
                }) {
                    return Err(format!(
                        "unknown sectioned candidate/geometry {value} for {}:{} shape {lowered_shape_bits:#05x}",
                        coordinate.circuit, coordinate.layer
                    )
                    .into());
                }
            }
        }
        if candidates.is_empty() {
            return Err("sectioned candidate selection is empty".into());
        }
        for candidate in candidates {
            let (program_sha256, descriptor_bytes) = {
                let descriptor = harness.sectioned_descriptor();
                (descriptor.program_sha256.clone(), descriptor.payload_size)
            };
            let mut row = SectionedCorrectnessRow {
                version: 2,
                candidate_id: candidate.candidate_id.clone(),
                symbol: candidate.symbol.clone(),
                geometry: candidate.geometry.as_str().to_owned(),
                lowered_shape_bits,
                compiled_shape_bits: candidate.shape_bits,
                shape_policy: match options.sectioned_shape {
                    R0SectionedShapePolicy::Exact => "exact",
                    R0SectionedShapePolicy::Compatible => "compatible",
                    R0SectionedShapePolicy::Universal => "universal",
                }
                .to_owned(),
                min_blocks: candidate.min_blocks,
                manifest_sha256: r0_sectioned_manifest_sha256().to_owned(),
                executable_sha256: harness.base().hashes().executable_sha256.clone(),
                circuit: coordinate.circuit.clone(),
                layer: coordinate.layer,
                log_trace,
                seed: options.seed,
                input_sha256: harness.base().hashes().input_sha256.clone(),
                program_sha256,
                descriptor_bytes,
                expected_checksum: expected_checksum.clone(),
                checksum: None,
                cells: None,
                launch: None,
                passing: false,
                failure: None,
                device_identity: device_identity.clone(),
            };
            match harness.run_sectioned_candidate(&candidate) {
                Ok(observed) => {
                    row.passing =
                        observed.cells == expected_cells && observed.checksum == expected_checksum;
                    row.cells = Some(observed.cells);
                    row.checksum = Some(observed.checksum);
                    row.launch = Some(observed.launch);
                    if !row.passing {
                        row.failure = Some("canonical_mismatch".to_owned());
                    }
                }
                Err(error) => row.failure = Some(error.to_string()),
            }
            serde_json::to_writer(&mut output, &row)?;
            output.write_all(b"\n")?;
        }
    }
    output.flush()?;
    Ok(())
}

#[derive(Serialize)]
struct ScreenRow {
    observation: R0PrototypeObservationV2,
    #[serde(skip_serializing_if = "Option::is_none")]
    shape_bits: Option<u16>,
    #[serde(skip_serializing_if = "Option::is_none")]
    geometry: Option<gpu_gkr_windowed_bench::r0_prototype_manifest::R0SectionedGeometry>,
    pilot_median_ms: Option<f64>,
    retained_samples: u32,
    pilot_correctness_checksum: Option<String>,
    pilot_post_session_checksum: Option<String>,
    retained_correctness_checksum: Option<String>,
    retained_post_session_checksum: Option<String>,
    pilot_samples: Vec<R0PrototypeTimingSampleV2>,
    samples: Vec<R0PrototypeTimingSampleV2>,
    candidate_wall_seconds: f64,
    coordinate_cpu_setup_seconds: f64,
    coordinate_harness_setup_seconds: f64,
    reference_wall_seconds: f64,
    coordinate_execution_wall_seconds: f64,
}

fn median(mut values: Vec<f64>) -> Result<f64, Box<dyn std::error::Error>> {
    if values.is_empty()
        || values
            .iter()
            .any(|value| !value.is_finite() || *value <= 0.0)
    {
        return Err("screen median requires finite positive samples".into());
    }
    values.sort_by(f64::total_cmp);
    Ok(values[values.len() / 2])
}

fn screen_pass_orders(
    candidate_count: usize,
    circuit: &str,
    layer: u32,
) -> Result<(Vec<usize>, Vec<usize>), String> {
    if candidate_count == 0 {
        return Err("screen pass requires at least one candidate".to_owned());
    }
    let pilot = (0..candidate_count).collect::<Vec<_>>();
    if candidate_count == 1 {
        return Ok((pilot.clone(), pilot));
    }
    let circuit_key = circuit.bytes().fold(0usize, |sum, byte| {
        sum.wrapping_mul(131).wrapping_add(usize::from(byte))
    });
    let rotation = (circuit_key.wrapping_add(layer as usize) % (candidate_count - 1)) + 1;
    let retained = pilot[rotation..]
        .iter()
        .chain(&pilot[..rotation])
        .copied()
        .collect();
    Ok((pilot, retained))
}

const ACTIVE_SECTIONED_CANDIDATES: usize = 2;
const SECTIONED_RETAINED_ROUNDS: usize = 5;

fn sectioned_coordinate_hash(coordinate_key: &str) -> usize {
    coordinate_key
        .bytes()
        .fold(0xcbf2_9ce4_8422_2325usize, |hash, byte| {
            hash.wrapping_mul(0x100_0000_01b3) ^ usize::from(byte)
        })
}

fn sectioned_round_order(
    candidate_count: usize,
    coordinate_key: &str,
    round: usize,
) -> Result<Vec<usize>, String> {
    if candidate_count != ACTIVE_SECTIONED_CANDIDATES || round >= SECTIONED_RETAINED_ROUNDS {
        return Err("sectioned round schedule requires 2 candidates and rounds 0..5".to_owned());
    }
    let start = (sectioned_coordinate_hash(coordinate_key) + round) % candidate_count;
    Ok((0..candidate_count)
        .map(|position| (start + position) % candidate_count)
        .collect())
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SectionedChunk {
    Candidate,
    ReferenceBefore,
    ReferenceAfter,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SectionedLayoutSample {
    arm: String,
    round_index: u32,
    chunk: SectionedChunk,
    sample_index: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SectionedRetainedLayout {
    chunks: Vec<(u32, SectionedChunk, u32)>,
    chunk_positions: std::collections::BTreeSet<u32>,
    samples: Vec<SectionedLayoutSample>,
}

fn sectioned_retained_layout(coordinate_key: &str) -> Result<SectionedRetainedLayout, String> {
    let mut chunks = Vec::with_capacity(20);
    let mut chunk_positions = std::collections::BTreeSet::new();
    let mut samples = Vec::with_capacity(150);
    for round in 0..SECTIONED_RETAINED_ROUNDS {
        chunks.push((round as u32, SectionedChunk::ReferenceBefore, 0));
        chunk_positions.insert(0);
        for sample_index in 0..5 {
            samples.push(SectionedLayoutSample {
                arm: "generic".to_owned(),
                round_index: round as u32,
                chunk: SectionedChunk::ReferenceBefore,
                sample_index,
            });
        }
        for (position, candidate) in
            sectioned_round_order(ACTIVE_SECTIONED_CANDIDATES, coordinate_key, round)?
                .into_iter()
                .enumerate()
        {
            let chunk_position = u32::try_from(position + 1)
                .map_err(|_| "sectioned chunk position overflow".to_owned())?;
            chunks.push((round as u32, SectionedChunk::Candidate, chunk_position));
            chunk_positions.insert(chunk_position);
            for sample_index in 0..10 {
                samples.push(SectionedLayoutSample {
                    arm: candidate.to_string(),
                    round_index: round as u32,
                    chunk: SectionedChunk::Candidate,
                    sample_index,
                });
            }
        }
        let reference_after_position = u32::try_from(ACTIVE_SECTIONED_CANDIDATES + 1)
            .map_err(|_| "sectioned reference position overflow".to_owned())?;
        chunks.push((
            round as u32,
            SectionedChunk::ReferenceAfter,
            reference_after_position,
        ));
        chunk_positions.insert(reference_after_position);
        for sample_index in 0..5 {
            samples.push(SectionedLayoutSample {
                arm: "generic".to_owned(),
                round_index: round as u32,
                chunk: SectionedChunk::ReferenceAfter,
                sample_index,
            });
        }
    }
    Ok(SectionedRetainedLayout {
        chunks,
        chunk_positions,
        samples,
    })
}

fn sectioned_matrix_round_order(
    candidate_count: usize,
    coordinate_key: &str,
    round: usize,
) -> Result<Vec<usize>, String> {
    if candidate_count == 0 || round >= SECTIONED_RETAINED_ROUNDS {
        return Err(
            "sectioned matrix schedule requires at least one candidate and rounds 0..5".to_owned(),
        );
    }
    let start = (sectioned_coordinate_hash(coordinate_key) + round) % candidate_count;
    Ok((0..candidate_count)
        .map(|position| (start + position) % candidate_count)
        .collect())
}

fn sectioned_matrix_retained_layout(
    candidate_count: usize,
    coordinate_key: &str,
) -> Result<SectionedRetainedLayout, String> {
    let mut chunks = Vec::with_capacity(candidate_count * SECTIONED_RETAINED_ROUNDS);
    let mut chunk_positions = std::collections::BTreeSet::new();
    let mut samples = Vec::with_capacity(candidate_count * SECTIONED_RETAINED_ROUNDS * 10);
    for round in 0..SECTIONED_RETAINED_ROUNDS {
        for (position, candidate) in
            sectioned_matrix_round_order(candidate_count, coordinate_key, round)?
                .into_iter()
                .enumerate()
        {
            let chunk_position = u32::try_from(position)
                .map_err(|_| "sectioned matrix chunk position overflow".to_owned())?;
            chunks.push((round as u32, SectionedChunk::Candidate, chunk_position));
            chunk_positions.insert(chunk_position);
            for sample_index in 0..10 {
                samples.push(SectionedLayoutSample {
                    arm: candidate.to_string(),
                    round_index: round as u32,
                    chunk: SectionedChunk::Candidate,
                    sample_index,
                });
            }
        }
    }
    Ok(SectionedRetainedLayout {
        chunks,
        chunk_positions,
        samples,
    })
}

fn sectioned_correctness_allows_timing<T: PartialEq>(
    expected_cells: &T,
    observed_cells: &T,
    expected_checksum: &str,
    observed_checksum: &str,
) -> bool {
    expected_cells == observed_cells && expected_checksum == observed_checksum
}

fn run_screen(
    options: &RuntimeOptions,
    bundle: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
    manifest: &R0PrototypeManifestV1,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<(), Box<dyn std::error::Error>> {
    let configs = selected_configs(options, manifest)?;
    let coordinates = selected_coordinates(options, bundle)?;
    let mut output = io::BufWriter::new(io::stdout().lock());
    for coordinate in coordinates {
        let coordinate_started = Instant::now();
        if !coordinate.trace_len.is_power_of_two() {
            return Err("production trace length is not a power of two".into());
        }
        let log_trace = coordinate.trace_len.ilog2();
        if options
            .log_trace
            .is_some_and(|requested| requested != log_trace)
        {
            return Err(format!(
                "screen log {} differs from production log {log_trace}",
                options.log_trace.unwrap()
            )
            .into());
        }
        let cpu_setup_started = Instant::now();
        let preflight = production_memory_preflight(coordinate, 0)?;
        let prepared = build_prepared_r0_production_input(coordinate, log_trace, options.seed)?;
        let coordinate_cpu_setup_seconds = cpu_setup_started.elapsed().as_secs_f64();
        let harness_setup_started = Instant::now();
        let mut harness =
            R0PrototypeHarness::new_prepared_production(coordinate, prepared, preflight)?;
        validate_device_capacity_identity(device_identity, harness.device_capacity())?;
        let coordinate_harness_setup_seconds = harness_setup_started.elapsed().as_secs_f64();
        let reference_id = manifest
            .configurations
            .iter()
            .find(|measurement| {
                manifest.symbols.iter().any(|candidate| {
                    candidate.candidate_id == measurement.candidate_id
                        && candidate.lineage == R0Lineage::Reference
                        && candidate.geometry
                            == gpu_gkr_windowed_bench::r0_geometry::R0Geometry::Cta288Pair
                })
            })
            .ok_or("missing cta288 reference configuration")?
            .configuration_id
            .clone();
        let reference = R0PrototypeRunConfig::resolve(manifest, &reference_id)?;
        let reference_started = Instant::now();
        let expected = harness.run_configuration(&reference)?;
        let reference_wall_seconds = reference_started.elapsed().as_secs_f64();
        let mut screens = configs
            .iter()
            .map(|config| {
                let mut row = observation(
                    &harness,
                    config,
                    coordinate,
                    log_trace,
                    options.seed,
                    &expected.checksum,
                    device_identity,
                )?;
                if matches!(
                    row.launchability,
                    R0PrototypeLaunchability::UnlaunchableCapacity { .. }
                ) {
                    row.failure = Some("unlaunchable_capacity".to_owned());
                }
                Ok(ScreenRow {
                    observation: row,
                    shape_bits: None,
                    geometry: None,
                    pilot_median_ms: None,
                    retained_samples: 0,
                    pilot_correctness_checksum: None,
                    pilot_post_session_checksum: None,
                    retained_correctness_checksum: None,
                    retained_post_session_checksum: None,
                    pilot_samples: Vec::new(),
                    samples: Vec::new(),
                    candidate_wall_seconds: 0.0,
                    coordinate_cpu_setup_seconds,
                    coordinate_harness_setup_seconds,
                    reference_wall_seconds,
                    coordinate_execution_wall_seconds: 0.0,
                })
            })
            .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;

        for (index, config) in configs.iter().enumerate() {
            if !matches!(
                screens[index].observation.launchability,
                R0PrototypeLaunchability::Launchable { .. }
            ) {
                continue;
            }
            let started = Instant::now();
            let observed = harness.run_configuration(config)?;
            let row = &mut screens[index].observation;
            row.launch = Some(observed.launch);
            row.cells = Some(observed.cells);
            row.checksum = Some(observed.checksum.clone());
            row.passing = observed.checksum == expected.checksum;
            if !row.passing {
                row.failure = Some("reference_mismatch".to_owned());
            }
            screens[index].candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        let (pilot_order, retained_order) =
            screen_pass_orders(configs.len(), &coordinate.circuit, coordinate.layer)?;
        let pilot_config = R0TimingConfig::screen(2, 3)?;
        for (position, index) in pilot_order.into_iter().enumerate() {
            if !screens[index].observation.passing {
                continue;
            }
            let started = Instant::now();
            let pilot = harness.measure_configuration(&configs[index], pilot_config)?;
            if pilot.correctness_checksum != expected.checksum
                || pilot.post_session_checksum != expected.checksum
            {
                return Err(format!(
                    "pilot checksum drift for {}",
                    configs[index].measurement.configuration_id
                )
                .into());
            }
            let pilot_median_ms = median(
                pilot
                    .samples
                    .iter()
                    .filter(|sample| !sample.warmup)
                    .map(|sample| sample.milliseconds)
                    .collect(),
            )?;
            let retained_samples = ((100.0 / pilot_median_ms).ceil() as u32).clamp(5, 50);
            let screen = &mut screens[index];
            screen.pilot_samples = R0PrototypeTimingSampleV2::from_session(
                &configs[index].measurement.configuration_id,
                &coordinate.circuit,
                coordinate.layer,
                log_trace,
                options.seed,
                R0PrototypeTimingPhaseV2::Pilot,
                0,
                u32::try_from(position)?,
                pilot_config,
                &pilot.samples,
            )?;
            screen.pilot_median_ms = Some(pilot_median_ms);
            screen.retained_samples = retained_samples;
            screen.pilot_correctness_checksum = Some(pilot.correctness_checksum);
            screen.pilot_post_session_checksum = Some(pilot.post_session_checksum);
            screen.candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        for (position, index) in retained_order.into_iter().enumerate() {
            if !screens[index].observation.passing {
                continue;
            }
            let started = Instant::now();
            let timing_config = R0TimingConfig::screen(2, screens[index].retained_samples)?;
            let timed = harness.measure_configuration(&configs[index], timing_config)?;
            if timed.correctness_checksum != expected.checksum
                || timed.post_session_checksum != expected.checksum
            {
                return Err(format!(
                    "retained checksum drift for {}",
                    configs[index].measurement.configuration_id
                )
                .into());
            }
            let screen = &mut screens[index];
            screen.samples = R0PrototypeTimingSampleV2::from_session(
                &configs[index].measurement.configuration_id,
                &coordinate.circuit,
                coordinate.layer,
                log_trace,
                options.seed,
                R0PrototypeTimingPhaseV2::Retained,
                1,
                u32::try_from(position)?,
                timing_config,
                &timed.samples,
            )?;
            screen.retained_correctness_checksum = Some(timed.correctness_checksum);
            screen.retained_post_session_checksum = Some(timed.post_session_checksum);
            screen.candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        let coordinate_execution_wall_seconds = coordinate_started.elapsed().as_secs_f64();
        for screen in &mut screens {
            screen.coordinate_execution_wall_seconds = coordinate_execution_wall_seconds;
            serde_json::to_writer(&mut output, screen)?;
            output.write_all(b"\n")?;
        }
        output.flush()?;
    }
    Ok(())
}

#[derive(Clone, Debug)]
enum SectionedScreenArm {
    Generic(R0PrototypeRunConfig),
    Sectioned(R0SectionedSymbolV1),
}

impl SectionedScreenArm {
    fn candidate_id(&self) -> &str {
        match self {
            Self::Generic(config) => &config.candidate.candidate_id,
            Self::Sectioned(candidate) => &candidate.candidate_id,
        }
    }

    fn symbol(&self) -> &str {
        match self {
            Self::Generic(config) => &config.candidate.symbol,
            Self::Sectioned(candidate) => &candidate.symbol,
        }
    }

    fn min_blocks(&self) -> Option<u32> {
        match self {
            Self::Generic(_) => None,
            Self::Sectioned(candidate) => candidate.min_blocks,
        }
    }

    fn compiled_shape_bits(&self) -> Option<u16> {
        match self {
            Self::Generic(_) => None,
            Self::Sectioned(candidate) => candidate.shape_bits,
        }
    }

    fn run(
        &self,
        harness: &mut R0PrototypeHarness,
    ) -> Result<gpu_gkr_windowed_bench::r0_harness::R0Observed, Box<dyn std::error::Error>> {
        Ok(match self {
            Self::Generic(config) => harness.run_configuration(config)?,
            Self::Sectioned(candidate) => harness.run_sectioned_candidate(candidate)?,
        })
    }

    fn measure(
        &self,
        harness: &mut R0PrototypeHarness,
        timing: R0TimingConfig,
    ) -> Result<gpu_gkr_windowed_bench::r0_harness::R0TimedSession, Box<dyn std::error::Error>>
    {
        Ok(match self {
            Self::Generic(config) => harness.measure_configuration(config, timing)?,
            Self::Sectioned(candidate) => harness.measure_sectioned_candidate(candidate, timing)?,
        })
    }
}

#[derive(Clone, Debug, Serialize)]
struct SectionedTimingSample {
    #[serde(flatten)]
    sample: R0PrototypeTimingSampleV2,
    round_index: u32,
    chunk: String,
    symbol: String,
    min_blocks: Option<u32>,
    compiled_shape_bits: Option<u16>,
    manifest_sha256: String,
    executable_sha256: String,
    input_sha256: String,
    program_sha256: String,
    device_identity: R0PrototypeDeviceIdentityV2,
}

#[derive(Serialize)]
struct SectionedScreenRow {
    observation: R0PrototypeObservationV2,
    arm_kind: String,
    lowered_shape_bits: u16,
    compiled_shape_bits: Option<u16>,
    geometry: String,
    min_blocks: Option<u32>,
    manifest_sha256: String,
    executable_sha256: String,
    pilot_median_ms: f64,
    retained_samples: u32,
    pilot_samples: Vec<SectionedTimingSample>,
    samples: Vec<SectionedTimingSample>,
    candidate_wall_seconds: f64,
    coordinate_cpu_setup_seconds: f64,
    coordinate_harness_setup_seconds: f64,
    coordinate_execution_wall_seconds: f64,
}

fn append_sectioned_timing_samples(
    row: &mut SectionedScreenRow,
    arm: &SectionedScreenArm,
    coordinate: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0Coordinate,
    log_trace: u32,
    seed: u64,
    phase: R0PrototypeTimingPhaseV2,
    round_index: u32,
    chunk: &str,
    chunk_position: u32,
    config: R0TimingConfig,
    timed: &gpu_gkr_windowed_bench::r0_harness::R0TimedSession,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<(), Box<dyn std::error::Error>> {
    let samples = R0PrototypeTimingSampleV2::from_session(
        arm.candidate_id(),
        &coordinate.circuit,
        coordinate.layer,
        log_trace,
        seed,
        phase.clone(),
        round_index,
        chunk_position,
        config,
        &timed.samples,
    )?
    .into_iter()
    .map(|sample| SectionedTimingSample {
        sample,
        round_index,
        chunk: chunk.to_owned(),
        symbol: arm.symbol().to_owned(),
        min_blocks: arm.min_blocks(),
        compiled_shape_bits: arm.compiled_shape_bits(),
        manifest_sha256: row.manifest_sha256.clone(),
        executable_sha256: row.executable_sha256.clone(),
        input_sha256: row.observation.input_sha256.clone(),
        program_sha256: row.observation.program_sha256.clone(),
        device_identity: device_identity.clone(),
    })
    .collect::<Vec<_>>();
    match phase {
        R0PrototypeTimingPhaseV2::Pilot => row.pilot_samples.extend(samples),
        R0PrototypeTimingPhaseV2::Retained => row.samples.extend(samples),
    }
    Ok(())
}

fn run_sectioned_screen(
    options: &RuntimeOptions,
    bundle: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
    prototype_manifest: &R0PrototypeManifestV1,
    sectioned_manifest: &R0SectionedManifestV1,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<(), Box<dyn std::error::Error>> {
    if !options.candidates.is_empty() {
        return Err("sectioned screen measures the exact generated 2+1 arm domain".into());
    }
    let coordinates = selected_coordinates(options, bundle)?;
    let reference_id = prototype_manifest
        .configurations
        .iter()
        .find(|measurement| {
            prototype_manifest.symbols.iter().any(|candidate| {
                candidate.candidate_id == measurement.candidate_id
                    && candidate.lineage == R0Lineage::Reference
                    && candidate.geometry
                        == gpu_gkr_windowed_bench::r0_geometry::R0Geometry::Cta288Pair
            })
        })
        .ok_or("missing cta288 reference configuration")?
        .configuration_id
        .clone();
    let reference = R0PrototypeRunConfig::resolve(prototype_manifest, &reference_id)?;
    let mut output = io::BufWriter::new(io::stdout().lock());

    for coordinate in coordinates {
        let coordinate_started = Instant::now();
        if !coordinate.trace_len.is_power_of_two() {
            return Err("production trace length is not a power of two".into());
        }
        let log_trace = coordinate.trace_len.ilog2();
        if options
            .log_trace
            .is_some_and(|requested| requested != log_trace)
        {
            return Err(format!(
                "sectioned screen log {} differs from production log {log_trace}",
                options.log_trace.unwrap()
            )
            .into());
        }

        let cpu_setup_started = Instant::now();
        let preflight = production_memory_preflight(coordinate, 0)?;
        let prepared = build_prepared_r0_production_input(coordinate, log_trace, options.seed)?;
        let coordinate_cpu_setup_seconds = cpu_setup_started.elapsed().as_secs_f64();

        let harness_setup_started = Instant::now();
        let (mut harness, shape_bits, candidates) =
            R0PrototypeHarness::new_prepared_sectioned_production(
                coordinate,
                prepared,
                preflight,
                sectioned_manifest,
            )?;
        validate_device_capacity_identity(device_identity, harness.device_capacity())?;
        let coordinate_harness_setup_seconds = harness_setup_started.elapsed().as_secs_f64();
        if candidates.len() != ACTIVE_SECTIONED_CANDIDATES {
            return Err(format!(
                "sectioned screen expected 2 candidates, got {}",
                candidates.len()
            )
            .into());
        }
        let mut arms = Vec::with_capacity(ACTIVE_SECTIONED_CANDIDATES + 1);
        arms.push(SectionedScreenArm::Generic(reference.clone()));
        arms.extend(candidates.into_iter().map(SectionedScreenArm::Sectioned));

        let reference_started = Instant::now();
        let expected = arms[0].run(&mut harness)?;
        let reference_wall_seconds = reference_started.elapsed().as_secs_f64();
        let expected_cells = expected.cells;
        let expected_checksum = expected.checksum;
        let executable_sha256 = harness.base().hashes().executable_sha256.clone();
        let manifest_sha256 = r0_sectioned_manifest_sha256().to_owned();

        let mut screens = arms
            .iter()
            .map(|arm| {
                let observation = match arm {
                    SectionedScreenArm::Generic(config) => observation(
                        &harness,
                        config,
                        coordinate,
                        log_trace,
                        options.seed,
                        &expected_checksum,
                        device_identity,
                    )?,
                    SectionedScreenArm::Sectioned(candidate) => sectioned_observation(
                        &harness,
                        candidate,
                        coordinate,
                        log_trace,
                        options.seed,
                        &expected_checksum,
                        device_identity,
                    )?,
                };
                Ok(SectionedScreenRow {
                    observation,
                    arm_kind: match arm {
                        SectionedScreenArm::Generic(_) => "generic",
                        SectionedScreenArm::Sectioned(_) => "sectioned",
                    }
                    .to_owned(),
                    lowered_shape_bits: shape_bits,
                    compiled_shape_bits: arm.compiled_shape_bits(),
                    geometry: match arm {
                        SectionedScreenArm::Generic(config) => {
                            config.candidate.geometry.as_str().to_owned()
                        }
                        SectionedScreenArm::Sectioned(candidate) => {
                            candidate.geometry.as_str().to_owned()
                        }
                    },
                    min_blocks: arm.min_blocks(),
                    manifest_sha256: manifest_sha256.clone(),
                    executable_sha256: executable_sha256.clone(),
                    pilot_median_ms: 0.0,
                    retained_samples: 0,
                    pilot_samples: Vec::new(),
                    samples: Vec::new(),
                    candidate_wall_seconds: 0.0,
                    coordinate_cpu_setup_seconds,
                    coordinate_harness_setup_seconds,
                    coordinate_execution_wall_seconds: 0.0,
                })
            })
            .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;

        screens[0].observation.launch = Some(expected.launch);
        screens[0].observation.cells = Some(expected_cells.clone());
        screens[0].observation.checksum = Some(expected_checksum.clone());
        screens[0].observation.passing = true;
        screens[0].candidate_wall_seconds += reference_wall_seconds;

        for index in 1..arms.len() {
            let started = Instant::now();
            let observed = arms[index].run(&mut harness)?;
            if !sectioned_correctness_allows_timing(
                &expected_cells,
                &observed.cells,
                &expected_checksum,
                &observed.checksum,
            ) {
                return Err(format!(
                    "sectioned correctness mismatch before timing for {}",
                    arms[index].candidate_id()
                )
                .into());
            }
            screens[index].observation.launch = Some(observed.launch);
            screens[index].observation.cells = Some(observed.cells);
            screens[index].observation.checksum = Some(observed.checksum);
            screens[index].observation.passing = true;
            screens[index].candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        let pilot_config = R0TimingConfig::screen(0, 3)?;
        for index in 0..arms.len() {
            let started = Instant::now();
            let pilot = arms[index].measure(&mut harness, pilot_config)?;
            if pilot.correctness_checksum != expected_checksum
                || pilot.post_session_checksum != expected_checksum
            {
                return Err(format!(
                    "sectioned pilot checksum drift for {}",
                    arms[index].candidate_id()
                )
                .into());
            }
            screens[index].pilot_median_ms = median(
                pilot
                    .samples
                    .iter()
                    .map(|sample| sample.milliseconds)
                    .collect(),
            )?;
            append_sectioned_timing_samples(
                &mut screens[index],
                &arms[index],
                coordinate,
                log_trace,
                options.seed,
                R0PrototypeTimingPhaseV2::Pilot,
                0,
                "pilot",
                u32::try_from(index)?,
                pilot_config,
                &pilot,
                device_identity,
            )?;
            screens[index].candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        let coordinate_key = format!("{}:{}", coordinate.circuit, coordinate.layer);
        let generic_config = R0TimingConfig::screen(0, 5)?;
        let candidate_config = R0TimingConfig::screen(0, 10)?;
        for round in 0..5usize {
            for (chunk, chunk_position) in [("reference_before", 0u32), ("reference_after", 3)] {
                if chunk == "reference_after" {
                    // The after-reference bracket follows the fifteen candidate chunks below.
                    continue;
                }
                let started = Instant::now();
                let timed = arms[0].measure(&mut harness, generic_config)?;
                if timed.correctness_checksum != expected_checksum
                    || timed.post_session_checksum != expected_checksum
                {
                    return Err("generic reference-before checksum drift".into());
                }
                append_sectioned_timing_samples(
                    &mut screens[0],
                    &arms[0],
                    coordinate,
                    log_trace,
                    options.seed,
                    R0PrototypeTimingPhaseV2::Retained,
                    u32::try_from(round)?,
                    chunk,
                    chunk_position,
                    generic_config,
                    &timed,
                    device_identity,
                )?;
                screens[0].candidate_wall_seconds += started.elapsed().as_secs_f64();
            }

            for (position, candidate_index) in
                sectioned_round_order(ACTIVE_SECTIONED_CANDIDATES, &coordinate_key, round)?
                    .into_iter()
                    .enumerate()
            {
                let arm_index = candidate_index + 1;
                let started = Instant::now();
                let timed = arms[arm_index].measure(&mut harness, candidate_config)?;
                if timed.correctness_checksum != expected_checksum
                    || timed.post_session_checksum != expected_checksum
                {
                    return Err(format!(
                        "sectioned retained checksum drift for {}",
                        arms[arm_index].candidate_id()
                    )
                    .into());
                }
                append_sectioned_timing_samples(
                    &mut screens[arm_index],
                    &arms[arm_index],
                    coordinate,
                    log_trace,
                    options.seed,
                    R0PrototypeTimingPhaseV2::Retained,
                    u32::try_from(round)?,
                    "candidate",
                    u32::try_from(position + 1)?,
                    candidate_config,
                    &timed,
                    device_identity,
                )?;
                screens[arm_index].candidate_wall_seconds += started.elapsed().as_secs_f64();
            }

            let started = Instant::now();
            let timed = arms[0].measure(&mut harness, generic_config)?;
            if timed.correctness_checksum != expected_checksum
                || timed.post_session_checksum != expected_checksum
            {
                return Err("generic reference-after checksum drift".into());
            }
            append_sectioned_timing_samples(
                &mut screens[0],
                &arms[0],
                coordinate,
                log_trace,
                options.seed,
                R0PrototypeTimingPhaseV2::Retained,
                u32::try_from(round)?,
                "reference_after",
                u32::try_from(ACTIVE_SECTIONED_CANDIDATES + 1)?,
                generic_config,
                &timed,
                device_identity,
            )?;
            screens[0].candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        for screen in &mut screens {
            screen.retained_samples = u32::try_from(screen.samples.len())?;
            if screen.pilot_samples.len() != 3 || screen.samples.len() != 50 {
                return Err(format!(
                    "sectioned screen sample cardinality mismatch for {}: pilot={} retained={}",
                    screen.observation.candidate_id,
                    screen.pilot_samples.len(),
                    screen.samples.len()
                )
                .into());
            }
        }

        let coordinate_execution_wall_seconds = coordinate_started.elapsed().as_secs_f64();
        for screen in &mut screens {
            screen.coordinate_execution_wall_seconds = coordinate_execution_wall_seconds;
            serde_json::to_writer(&mut output, screen)?;
            output.write_all(b"\n")?;
        }
        output.flush()?;
    }
    Ok(())
}

fn run_sectioned_matrix(
    options: &RuntimeOptions,
    bundle: &gpu_gkr_windowed_bench::r0_artifact::FrozenR0BundleV1,
    sectioned_manifest: &R0SectionedManifestV1,
    device_identity: &R0PrototypeDeviceIdentityV2,
) -> Result<(), Box<dyn std::error::Error>> {
    if !options.candidates.is_empty() {
        return Err("sectioned matrix measures the exact generated 2-arm domain".into());
    }
    let coordinates = selected_coordinates(options, bundle)?;
    let mut output = io::BufWriter::new(io::stdout().lock());
    for coordinate in coordinates {
        let coordinate_started = Instant::now();
        if !coordinate.trace_len.is_power_of_two() {
            return Err("production trace length is not a power of two".into());
        }
        let log_trace = coordinate.trace_len.ilog2();
        if options
            .log_trace
            .is_some_and(|requested| requested != log_trace)
        {
            return Err(format!(
                "sectioned matrix log {} differs from production log {log_trace}",
                options.log_trace.unwrap()
            )
            .into());
        }

        let cpu_setup_started = Instant::now();
        let preflight = production_memory_preflight(coordinate, 0)?;
        let prepared = build_prepared_r0_production_input(coordinate, log_trace, options.seed)?;
        let coordinate_cpu_setup_seconds = cpu_setup_started.elapsed().as_secs_f64();

        let harness_setup_started = Instant::now();
        let matrix_policy = match r0_sectioned_shape_merge_policy() {
            gpu_gkr_windowed_bench::r0_prototype_manifest::R0SectionedShapeMergePolicy::UnionBank => {
                R0SectionedShapePolicy::Compatible
            }
            gpu_gkr_windowed_bench::r0_prototype_manifest::R0SectionedShapeMergePolicy::Exact
            | gpu_gkr_windowed_bench::r0_prototype_manifest::R0SectionedShapeMergePolicy::Merged => {
                R0SectionedShapePolicy::Exact
            }
        };
        let (mut harness, shape_bits, candidates) =
            R0PrototypeHarness::new_prepared_sectioned_production_for_policy(
                coordinate,
                prepared,
                preflight,
                sectioned_manifest,
                matrix_policy,
            )?;
        validate_device_capacity_identity(device_identity, harness.device_capacity())?;
        let coordinate_harness_setup_seconds = harness_setup_started.elapsed().as_secs_f64();
        if candidates.is_empty() {
            return Err("sectioned matrix candidate selection is empty".into());
        }
        let arms = candidates
            .into_iter()
            .map(SectionedScreenArm::Sectioned)
            .collect::<Vec<_>>();

        let reference_started = Instant::now();
        let expected = arms[0].run(&mut harness)?;
        let reference_wall_seconds = reference_started.elapsed().as_secs_f64();
        let expected_cells = expected.cells;
        let expected_checksum = expected.checksum;
        let executable_sha256 = harness.base().hashes().executable_sha256.clone();
        let manifest_sha256 = r0_sectioned_manifest_sha256().to_owned();

        let mut screens = arms
            .iter()
            .map(|arm| {
                let candidate = match arm {
                    SectionedScreenArm::Sectioned(candidate) => candidate,
                    SectionedScreenArm::Generic(_) => unreachable!("matrix has no generic arm"),
                };
                Ok(SectionedScreenRow {
                    observation: sectioned_observation(
                        &harness,
                        candidate,
                        coordinate,
                        log_trace,
                        options.seed,
                        &expected_checksum,
                        device_identity,
                    )?,
                    arm_kind: "sectioned".to_owned(),
                    lowered_shape_bits: shape_bits,
                    compiled_shape_bits: candidate.shape_bits,
                    geometry: candidate.geometry.as_str().to_owned(),
                    min_blocks: candidate.min_blocks,
                    manifest_sha256: manifest_sha256.clone(),
                    executable_sha256: executable_sha256.clone(),
                    pilot_median_ms: 0.0,
                    retained_samples: 0,
                    pilot_samples: Vec::new(),
                    samples: Vec::new(),
                    candidate_wall_seconds: 0.0,
                    coordinate_cpu_setup_seconds,
                    coordinate_harness_setup_seconds,
                    coordinate_execution_wall_seconds: 0.0,
                })
            })
            .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;

        screens[0].observation.launch = Some(expected.launch);
        screens[0].observation.cells = Some(expected_cells.clone());
        screens[0].observation.checksum = Some(expected_checksum.clone());
        screens[0].observation.passing = true;
        screens[0].candidate_wall_seconds += reference_wall_seconds;

        for index in 1..arms.len() {
            let started = Instant::now();
            let observed = arms[index].run(&mut harness)?;
            if !sectioned_correctness_allows_timing(
                &expected_cells,
                &observed.cells,
                &expected_checksum,
                &observed.checksum,
            ) {
                return Err(format!(
                    "sectioned matrix correctness mismatch before timing for {}",
                    arms[index].candidate_id()
                )
                .into());
            }
            screens[index].observation.launch = Some(observed.launch);
            screens[index].observation.cells = Some(observed.cells);
            screens[index].observation.checksum = Some(observed.checksum);
            screens[index].observation.passing = true;
            screens[index].candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        let pilot_config = R0TimingConfig::screen(0, 3)?;
        for index in 0..arms.len() {
            let started = Instant::now();
            let pilot = arms[index].measure(&mut harness, pilot_config)?;
            if pilot.correctness_checksum != expected_checksum
                || pilot.post_session_checksum != expected_checksum
            {
                return Err(format!(
                    "sectioned matrix pilot checksum drift for {}",
                    arms[index].candidate_id()
                )
                .into());
            }
            screens[index].pilot_median_ms = median(
                pilot
                    .samples
                    .iter()
                    .map(|sample| sample.milliseconds)
                    .collect(),
            )?;
            append_sectioned_timing_samples(
                &mut screens[index],
                &arms[index],
                coordinate,
                log_trace,
                options.seed,
                R0PrototypeTimingPhaseV2::Pilot,
                0,
                "pilot",
                u32::try_from(index)?,
                pilot_config,
                &pilot,
                device_identity,
            )?;
            screens[index].candidate_wall_seconds += started.elapsed().as_secs_f64();
        }

        let coordinate_key = format!("{}:{}", coordinate.circuit, coordinate.layer);
        let timing_config = R0TimingConfig::screen(0, 10)?;
        for round in 0..5usize {
            for (position, arm_index) in
                sectioned_matrix_round_order(arms.len(), &coordinate_key, round)?
                    .into_iter()
                    .enumerate()
            {
                let started = Instant::now();
                let timed = arms[arm_index].measure(&mut harness, timing_config)?;
                if timed.correctness_checksum != expected_checksum
                    || timed.post_session_checksum != expected_checksum
                {
                    return Err(format!(
                        "sectioned matrix retained checksum drift for {}",
                        arms[arm_index].candidate_id()
                    )
                    .into());
                }
                append_sectioned_timing_samples(
                    &mut screens[arm_index],
                    &arms[arm_index],
                    coordinate,
                    log_trace,
                    options.seed,
                    R0PrototypeTimingPhaseV2::Retained,
                    u32::try_from(round)?,
                    "candidate",
                    u32::try_from(position)?,
                    timing_config,
                    &timed,
                    device_identity,
                )?;
                screens[arm_index].candidate_wall_seconds += started.elapsed().as_secs_f64();
            }
        }

        for screen in &mut screens {
            screen.retained_samples = u32::try_from(screen.samples.len())?;
            if screen.pilot_samples.len() != 3 || screen.samples.len() != 50 {
                return Err(format!(
                    "sectioned matrix sample cardinality mismatch for {}: pilot={} retained={}",
                    screen.observation.candidate_id,
                    screen.pilot_samples.len(),
                    screen.samples.len()
                )
                .into());
            }
        }

        let coordinate_execution_wall_seconds = coordinate_started.elapsed().as_secs_f64();
        for screen in &mut screens {
            screen.coordinate_execution_wall_seconds = coordinate_execution_wall_seconds;
            serde_json::to_writer(&mut output, screen)?;
            output.write_all(b"\n")?;
        }
        output.flush()?;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let options = RuntimeOptions::parse().map_err(|error| format!("{error}\n{}", usage()))?;
    if matches!(
        options.mode,
        Mode::SectionedCorrectness | Mode::SectionedMatrix | Mode::SectionedScreen
    ) {
        ensure_sectioned_runtime_available()?;
    }
    gpu_gkr_windowed_bench::runtime_paths::set_repository_root(&options.repo_root)?;
    if options.mode == Mode::LinkProof {
        println!("{}", r0_prototype_link_proof_summary());
        return Ok(());
    }
    if options.mode == Mode::DeviceInfo {
        println!("{}", serde_json::to_string(&query_device_identity()?)?);
        return Ok(());
    }
    fs::create_dir_all(&options.output_root)?;
    let (bundle, manifest) = checked_inputs(&options)?;
    let device_identity = query_device_identity()?;
    match options.mode {
        Mode::LinkProof | Mode::DeviceInfo => unreachable!(),
        Mode::ReferenceSmoke | Mode::Correctness => {
            run_correctness(&options, &bundle, &manifest, &device_identity)
        }
        Mode::SectionedCorrectness => {
            let sectioned_manifest = checked_sectioned_manifest(&options)?;
            run_sectioned_correctness(&options, &bundle, &sectioned_manifest, &device_identity)
        }
        Mode::SectionedScreen => {
            let sectioned_manifest = checked_sectioned_manifest(&options)?;
            run_sectioned_screen(
                &options,
                &bundle,
                &manifest,
                &sectioned_manifest,
                &device_identity,
            )
        }
        Mode::SectionedMatrix => {
            let sectioned_manifest = checked_sectioned_manifest(&options)?;
            run_sectioned_matrix(&options, &bundle, &sectioned_manifest, &device_identity)
        }
        Mode::Screen => run_screen(&options, &bundle, &manifest, &device_identity),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::{Path, PathBuf};

    use gpu_gkr_windowed_bench::r0_prototype_kernels::R0SectionedShapePolicy;
    use gpu_gkr_windowed_bench::r0_prototype_manifest::build_r0_prototype_manifest;

    use super::{
        discover_repository_root, ensure_sectioned_runtime_available, plan_sectioned_correctness,
        screen_pass_orders, sectioned_retained_layout, sectioned_round_order, selected_configs,
        usage, Mode, RuntimeOptions,
    };

    #[test]
    fn cpu_screen_passes_cover_every_candidate_in_distinct_orders() {
        let (pilot, retained) = screen_pass_orders(9, "some_circuit", 3).unwrap();
        assert_eq!(pilot, (0..9).collect::<Vec<_>>());
        assert_ne!(pilot, retained);
        let mut sorted = retained.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, pilot);
        assert!(screen_pass_orders(0, "some_circuit", 3).is_err());
    }

    #[test]
    fn cpu_repository_root_discovery_is_runtime_relative() {
        let fixture =
            std::env::temp_dir().join(format!("windowed-r0-runtime-root-{}", std::process::id()));
        let checkout = fixture.join("relocated-checkout");
        let executable = checkout.join("target/release/run_windowed_r0_prototype_bank");
        std::fs::create_dir_all(checkout.join("gpu/gkr_windowed_bench")).unwrap();
        std::fs::create_dir_all(executable.parent().unwrap()).unwrap();
        std::fs::write(checkout.join("Cargo.toml"), "[workspace]\n").unwrap();
        std::fs::write(
            checkout.join("gpu/gkr_windowed_bench/Cargo.toml"),
            "[package]\nname='fixture'\nversion='0.0.0'\n",
        )
        .unwrap();

        let discovered =
            discover_repository_root(&checkout.join("some/nested/runtime-directory"), &executable)
                .unwrap();
        assert_eq!(discovered, checkout);
        std::fs::remove_dir_all(fixture).unwrap();
    }

    #[test]
    fn cpu_relative_runtime_paths_resolve_against_explicit_relocated_root() {
        let fixture =
            std::env::temp_dir().join(format!("windowed-r0-explicit-root-{}", std::process::id()));
        std::fs::create_dir_all(fixture.join("gpu/gkr_windowed_bench")).unwrap();
        std::fs::write(fixture.join("Cargo.toml"), "[workspace]\n").unwrap();
        std::fs::write(
            fixture.join("gpu/gkr_windowed_bench/Cargo.toml"),
            "[package]\nname='fixture'\nversion='0.0.0'\n",
        )
        .unwrap();
        let args = [
            "--repo-root".to_owned(),
            fixture.display().to_string(),
            "--corpus".to_owned(),
            "runtime/corpus.bin".to_owned(),
            "--artifact-root".to_owned(),
            "runtime/artifacts".to_owned(),
            "--output-root".to_owned(),
            "runtime/output".to_owned(),
        ];
        let options = RuntimeOptions::parse_with_context(
            &args,
            |_| None,
            Path::new("/unrelated/cwd"),
            Path::new("/unrelated/executable"),
        )
        .unwrap();
        assert_eq!(options.corpus, fixture.join("runtime/corpus.bin"));
        assert_eq!(options.artifact_root, fixture.join("runtime/artifacts"));
        assert_eq!(options.output_root, fixture.join("runtime/output"));
        std::fs::remove_dir_all(fixture).unwrap();
    }

    #[test]
    fn cpu_runtime_paths_and_filters_use_cli_over_environment() {
        let env = BTreeMap::from([
            ("AB_R0_PROTOTYPE_CORPUS", "env-corpus"),
            ("AB_R0_PROTOTYPE_ARTIFACT_ROOT", "env-artifacts"),
            ("AB_R0_PROTOTYPE_OUTPUT_ROOT", "env-output"),
            ("AB_R0_PROTOTYPE_CANDIDATES", "env-candidate"),
            ("AB_R0_PROTOTYPE_COORDINATES", "env-coordinate"),
            ("AB_R0_PROTOTYPE_MODE", "correctness"),
        ]);
        let args = [
            "--corpus",
            "/tmp/cli-corpus",
            "--artifact-root",
            "/tmp/cli-artifacts",
            "--output-root",
            "/tmp/cli-output",
            "--candidate",
            "candidate-a,candidate-b",
            "--coordinate",
            "circuit:2",
            "--mode",
            "screen",
            "--log",
            "24",
            "--seed",
            "7",
        ]
        .map(str::to_owned);
        let options = RuntimeOptions::parse_with(&args, |name| {
            env.get(name).map(|value| (*value).to_owned())
        })
        .unwrap();
        assert_eq!(options.corpus, PathBuf::from("/tmp/cli-corpus"));
        assert_eq!(options.artifact_root, PathBuf::from("/tmp/cli-artifacts"));
        assert_eq!(options.output_root, PathBuf::from("/tmp/cli-output"));
        assert_eq!(options.candidates, ["candidate-a", "candidate-b"]);
        assert_eq!(options.coordinates, ["circuit:2"]);
        assert_eq!(options.mode, Mode::Screen);
        assert_eq!(options.log_trace, Some(24));
        assert_eq!(options.seed, 7);
    }

    #[test]
    fn cpu_device_info_is_an_explicit_runtime_mode() {
        assert_eq!(Mode::parse("device-info").unwrap(), Mode::DeviceInfo);
        assert!(usage().contains("device-info"));
    }

    #[test]
    fn cpu_sectioned_correctness_is_an_explicit_runtime_mode() {
        assert_eq!(
            Mode::parse("sectioned-correctness").unwrap(),
            Mode::SectionedCorrectness
        );
        assert!(usage().contains("sectioned-correctness"));
    }

    #[test]
    fn cpu_sectioned_shape_policy_parses_exactly_and_is_mode_scoped() {
        let compatible = RuntimeOptions::parse_with(
            &[
                "--mode".to_owned(),
                "sectioned-correctness".to_owned(),
                "--sectioned-shape".to_owned(),
                "compatible".to_owned(),
            ],
            |_| None,
        )
        .unwrap();
        assert_eq!(
            compatible.sectioned_shape,
            R0SectionedShapePolicy::Compatible
        );

        let universal = RuntimeOptions::parse_with(
            &[
                "--mode".to_owned(),
                "sectioned-correctness".to_owned(),
                "--sectioned-shape".to_owned(),
                "universal".to_owned(),
            ],
            |_| None,
        )
        .unwrap();
        assert_eq!(universal.sectioned_shape, R0SectionedShapePolicy::Universal);

        let exact = RuntimeOptions::parse_with(
            &["--mode".to_owned(), "sectioned-correctness".to_owned()],
            |_| None,
        )
        .unwrap();
        assert_eq!(exact.sectioned_shape, R0SectionedShapePolicy::Exact);

        for invalid in ["bogus", "Universal", "exact,universal"] {
            assert!(RuntimeOptions::parse_with(
                &[
                    "--mode".to_owned(),
                    "sectioned-correctness".to_owned(),
                    "--sectioned-shape".to_owned(),
                    invalid.to_owned(),
                ],
                |_| None,
            )
            .is_err());
        }
        assert!(RuntimeOptions::parse_with(
            &[
                "--mode".to_owned(),
                "sectioned-screen".to_owned(),
                "--sectioned-shape".to_owned(),
                "universal".to_owned(),
            ],
            |_| None,
        )
        .is_err());
    }

    #[test]
    fn cpu_sectioned_correctness_plan_has_exact_cardinality_and_symbol_partition() {
        let shapes = gpu_gkr_windowed_bench::r0_prototype_manifest::R0_SECTIONED_SPECIALIZED_SHAPES;
        let coordinates = (0..57)
            .map(|index| {
                (
                    format!("fixture_{index}"),
                    u32::try_from(index).unwrap(),
                    shapes[index % shapes.len()],
                )
            })
            .collect::<Vec<_>>();
        let exact =
            plan_sectioned_correctness(&coordinates, [3, 12], R0SectionedShapePolicy::Exact)
                .unwrap();
        let universal = plan_sectioned_correctness(
            &coordinates[..1],
            [3, 12],
            R0SectionedShapePolicy::Universal,
        )
        .unwrap();
        assert_eq!(exact.len(), 228);
        assert_eq!(universal.len(), 4);

        let exact_ids = exact
            .iter()
            .map(|row| row.candidate_id.as_str())
            .collect::<BTreeSet<_>>();
        let universal_ids = universal
            .iter()
            .map(|row| row.candidate_id.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(exact_ids.len(), 24);
        assert_eq!(universal_ids.len(), 2);
        assert!(exact_ids.is_disjoint(&universal_ids));
        assert_eq!(exact_ids.union(&universal_ids).count(), 26);

        for coordinate in &coordinates {
            for log_trace in [3, 12] {
                let ids = exact
                    .iter()
                    .filter(|row| {
                        row.circuit == coordinate.0
                            && row.layer == coordinate.1
                            && row.log_trace == log_trace
                    })
                    .map(|row| row.candidate_id.as_str())
                    .collect::<BTreeSet<_>>();
                assert_eq!(ids.len(), 2);
            }
        }
    }

    #[test]
    fn cpu_sectioned_runtime_manifest_requires_schema_v4_artifact() {
        let fixture = std::env::temp_dir().join(format!(
            "windowed-r0-sectioned-v4-only-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&fixture).unwrap();
        std::fs::write(
            fixture.join("windowed_r0_sectioned_manifest_v1.json"),
            b"{}\n",
        )
        .unwrap();
        let options = RuntimeOptions {
            repo_root: PathBuf::from("/tmp/repo"),
            corpus: PathBuf::from("/tmp/corpus"),
            artifact_root: fixture.clone(),
            output_root: PathBuf::from("/tmp/output"),
            candidates: vec![],
            coordinates: vec![],
            mode: Mode::SectionedCorrectness,
            log_trace: Some(3),
            seed: 0,
            sectioned_shape: R0SectionedShapePolicy::Exact,
        };
        super::checked_sectioned_manifest(&options).unwrap_err();
        std::fs::remove_dir_all(fixture).unwrap();
    }

    #[test]
    fn cpu_sectioned_screen_is_an_explicit_runtime_mode() {
        assert_eq!(
            Mode::parse("sectioned-screen").unwrap(),
            Mode::SectionedScreen
        );
        assert!(usage().contains("sectioned-screen"));
    }

    #[test]
    fn cpu_sectioned_matrix_rotates_an_arbitrary_compatible_union_domain_without_generic() {
        assert_eq!(
            Mode::parse("sectioned-matrix").unwrap(),
            Mode::SectionedMatrix
        );
        assert!(usage().contains("sectioned-matrix"));
        let layout = super::sectioned_matrix_retained_layout(16, "alpha:0").unwrap();
        assert_eq!(layout.chunks.len(), 80);
        assert_eq!(layout.chunk_positions, (0u32..16).collect::<BTreeSet<_>>());
        assert_eq!(layout.samples.len(), 800);
        assert!(layout.samples.iter().all(|sample| sample.arm != "generic"));
        for candidate in 0..16 {
            let keys = layout
                .samples
                .iter()
                .filter(|sample| sample.arm == candidate.to_string())
                .map(|sample| (sample.round_index, sample.chunk, sample.sample_index))
                .collect::<BTreeSet<_>>();
            assert_eq!(keys.len(), 50);
        }
        for round in 0..5 {
            let order = super::sectioned_matrix_round_order(16, "alpha:0", round).unwrap();
            assert_eq!(order.len(), 16);
            assert_eq!(
                order.iter().copied().collect::<BTreeSet<_>>(),
                (0..16).collect()
            );
        }
        assert!(super::sectioned_matrix_round_order(0, "alpha:0", 0).is_err());
    }

    #[test]
    fn cpu_sectioned_round_orders_are_complete_rotated_permutations() {
        for round in 0..5 {
            let order = sectioned_round_order(2, "alpha:0", round).unwrap();
            assert_eq!(order.len(), 2);
            assert_eq!(order[1], (order[0] + 1) % 2);
            let mut sorted = order.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, (0..2).collect::<Vec<_>>());
        }
        assert_ne!(
            sectioned_round_order(2, "alpha:0", 0).unwrap()[0],
            sectioned_round_order(2, "alpha:0", 1).unwrap()[0]
        );
        assert!(sectioned_round_order(3, "alpha:0", 0).is_err());
    }

    #[test]
    fn cpu_sectioned_retained_layout_has_exact_unique_fifty_sample_domains() {
        let layout = sectioned_retained_layout("alpha:0").unwrap();
        assert_eq!(layout.chunks.len(), 20);
        assert_eq!(layout.chunk_positions, (0u32..=3).collect::<BTreeSet<_>>());
        for candidate in 0..2 {
            let keys = layout
                .samples
                .iter()
                .filter(|sample| sample.arm == candidate.to_string())
                .map(|sample| (sample.round_index, sample.chunk, sample.sample_index))
                .collect::<BTreeSet<_>>();
            assert_eq!(keys.len(), 50);
        }
        let reference = layout
            .samples
            .iter()
            .filter(|sample| sample.arm == "generic")
            .map(|sample| (sample.round_index, sample.chunk, sample.sample_index))
            .collect::<BTreeSet<_>>();
        assert_eq!(reference.len(), 50);
        assert_eq!(layout.samples.len(), 150);
    }

    #[test]
    fn cpu_sectioned_timing_is_blocked_by_cell_drift_even_when_checksum_is_unchanged() {
        let expected = [[0u32; 4]; 27];
        let mut observed = expected;
        observed[0][0] = 1;
        assert!(!super::sectioned_correctness_allows_timing(
            &expected,
            &observed,
            "same-checksum",
            "same-checksum",
        ));
    }

    #[cfg(not(r0_prototype_bank_full))]
    #[test]
    fn cpu_off_native_mode_rejects_sectioned_execution_before_gpu() {
        let error = ensure_sectioned_runtime_available().unwrap_err();
        assert!(error.contains("GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE=full"));
    }

    #[test]
    fn cpu_default_runtime_paths_are_absolute_and_repository_relative() {
        let options = RuntimeOptions::parse_with(&[], |_| None).unwrap();
        assert!(options.corpus.is_absolute());
        assert!(options.artifact_root.is_absolute());
        assert!(options.output_root.is_absolute());
        assert!(options.corpus.ends_with(Path::new(
            "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.bin"
        )));
    }

    #[test]
    fn cpu_explicit_configuration_filter_preserves_requested_runtime_order() {
        let manifest = build_r0_prototype_manifest().unwrap();
        let first = manifest.configurations[0].configuration_id.clone();
        let last = manifest
            .configurations
            .last()
            .unwrap()
            .configuration_id
            .clone();
        let options = RuntimeOptions {
            repo_root: PathBuf::from("/tmp/repo"),
            corpus: PathBuf::from("/tmp/corpus"),
            artifact_root: PathBuf::from("/tmp/artifacts"),
            output_root: PathBuf::from("/tmp/output"),
            candidates: vec![last.clone(), first.clone()],
            coordinates: vec![],
            mode: Mode::Screen,
            log_trace: None,
            seed: 0,
            sectioned_shape: R0SectionedShapePolicy::Exact,
        };
        let rows = selected_configs(&options, &manifest).unwrap();
        assert_eq!(
            rows.iter()
                .map(|row| row.measurement.configuration_id.as_str())
                .collect::<Vec<_>>(),
            [last.as_str(), first.as_str()]
        );
    }
}
