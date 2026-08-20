use core::mem::size_of;
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::time::Duration;

use clap::{Parser, Subcommand, ValueEnum};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Field;
use gpu_gkr_compiler::backward::{compile_r0, R0LayerProgram, SOURCE_NONE};
use gpu_gkr_compiler::GpuResourceProfile;
use gpu_gkr_windowed_bench::abi::{BF, E4};
use gpu_gkr_windowed_bench::census::CORPUS;
use gpu_gkr_windowed_bench::r0_abi::{native_r0_abi_layout, rust_r0_abi_layout, R0AbiLayout};
use gpu_gkr_windowed_bench::r0_artifact::{decode_r0_bundle, FrozenR0Coordinate, R0_CORPUS_BYTES};
use gpu_gkr_windowed_bench::r0_geometry::{R0Geometry, R0LaunchMetadata, R0MemoryPreflight};
use gpu_gkr_windowed_bench::r0_harness::{
    production_memory_preflight, r0_cells_sha256, R0Harness, R0HarnessHashes, R0ProductionError,
    R0TimingConfig,
};
use gpu_gkr_windowed_bench::r0_input::{
    build_prepared_r0_production_input, build_r0_input_with_layer, FrozenE4,
    PreparedR0ProductionInput, ResolvedR0Input, R0_PRODUCTION_SEED,
};
use gpu_gkr_windowed_bench::r0_reference::{
    evaluate_canonical_r0_convention, evaluate_compiled_r0_tensor, evaluate_true_canonical_tensor,
    r0_output_checksum,
};
use gpu_gkr_windowed_bench::r0_report::{
    begin_checkpoint, complete_checkpoint, read_observation_rows, read_timing_samples,
    verify_reusable_checkpoint, write_jsonl_atomic, R0Bindings, R0CheckpointReuse,
    R0ObservationRowV1, R0ResultKey, R0RowsKind, R0TimingSampleV1, R0Traversal, R0_REPORT_VERSION,
};
use serde::{Deserialize, Serialize};

#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    #[command(name = "abi-probe")]
    AbiProbe,
    #[command(name = "geometry-smoke")]
    GeometrySmoke {
        #[arg(long)]
        coordinate: String,
        #[arg(long = "log")]
        log_trace: u32,
        #[arg(long)]
        seed: u64,
        #[arg(long, default_value = "all")]
        geometries: String,
    },
    #[command(name = "pair-smoke")]
    PairSmoke {
        #[arg(long)]
        coordinate: String,
        #[arg(long = "log")]
        log_trace: u32,
        #[arg(long)]
        seed: u64,
    },
    Correctness {
        #[arg(
            long,
            conflicts_with = "coordinate",
            required_unless_present = "coordinate"
        )]
        all: bool,
        #[arg(long, conflicts_with = "all")]
        coordinate: Option<String>,
        #[arg(long)]
        logs: String,
        #[arg(long)]
        seeds: String,
        #[arg(long, default_value = "all")]
        geometries: String,
    },
    Production {
        #[arg(long)]
        coordinate: String,
        #[arg(
            long,
            conflicts_with = "geometry",
            required_unless_present = "geometry"
        )]
        all_geometries: bool,
        #[arg(long, conflicts_with = "all_geometries")]
        geometry: Option<String>,
        #[arg(long, requires = "geometry")]
        once: bool,
        #[arg(long, requires = "geometry")]
        expected_checksum: Option<String>,
        #[arg(long)]
        output_dir: PathBuf,
        #[arg(long, default_value = "natural")]
        point: String,
        #[arg(long)]
        resume: bool,
        #[arg(long, default_value_t = 0)]
        runtime_bytes: u64,
    },
    #[command(name = "production-plan")]
    ProductionPlan {
        #[arg(long, default_value_t = 0)]
        runtime_bytes: u64,
    },
    #[command(name = "production-preflight")]
    ProductionPreflight {
        #[arg(long)]
        coordinate: String,
        #[arg(long, default_value_t = 0)]
        runtime_bytes: u64,
    },
    Timing {
        #[arg(long, default_value = "natural")]
        point: String,
        #[arg(long)]
        coordinate: String,
        #[arg(long)]
        geometries: String,
        #[arg(long, value_enum)]
        traversal: TimingTraversal,
        #[arg(long, default_value_t = 5)]
        warmups: u32,
        #[arg(long, default_value_t = 50)]
        samples: u32,
        #[arg(long)]
        expected_checksum: String,
        #[arg(long)]
        session_bindings: PathBuf,
        #[arg(long)]
        output_dir: PathBuf,
        #[arg(long)]
        resume: bool,
    },
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum TimingTraversal {
    Forward,
    Reverse,
}

#[derive(Serialize)]
struct AbiProbeOutput {
    rust: R0AbiLayout,
    native: R0AbiLayout,
    matches: bool,
}

#[derive(Clone, Serialize)]
struct ProgramCensus {
    records: u32,
    source_uses: u32,
    classes: [u32; 5],
}

#[derive(Serialize)]
struct EqLayout {
    high: [u32; 2],
    low: u32,
    high_lengths: [usize; 2],
    low_length: usize,
}

#[derive(Serialize)]
struct GeometryObservation {
    geometry: R0Geometry,
    launch: R0LaunchMetadata,
    census: ProgramCensus,
    cells: [FrozenE4; 27],
    checksum: u64,
}

#[derive(Serialize)]
struct GeometrySmokeOutput {
    coordinate: String,
    log_trace: u32,
    seed: u64,
    input_sha256: String,
    eq_layout: EqLayout,
    canonical_q: [FrozenE4; 27],
    canonical_q_checksum: u64,
    compiled_q: [FrozenE4; 27],
    compiled_q_checksum: u64,
    observations: Vec<GeometryObservation>,
}

#[derive(Serialize)]
struct CorrectnessRow {
    version: u32,
    circuit: String,
    layer: u32,
    log_trace: u32,
    seed: u64,
    geometry: R0Geometry,
    #[serde(flatten)]
    hashes: R0HarnessHashes,
    canonical_p_sha256: String,
    canonical_q_sha256: String,
    compiled_q_sha256: String,
    p_minus_q_sha256: String,
    launch: R0LaunchMetadata,
    cells: [FrozenE4; 27],
    checksum: String,
    canonical_q_matches_compiled: bool,
    gpu_matches_canonical_q: bool,
    gpu_matches_compiled_q: bool,
    passing: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    match args.command {
        Command::AbiProbe => run_abi_probe(),
        Command::GeometrySmoke {
            coordinate,
            log_trace,
            seed,
            geometries,
        } => run_geometry_smoke(&coordinate, log_trace, seed, &geometries),
        Command::PairSmoke {
            coordinate,
            log_trace,
            seed,
        } => run_geometry_smoke(
            &coordinate,
            log_trace,
            seed,
            "cta288_pair,cta96_partitioned",
        ),
        Command::Correctness {
            all,
            coordinate,
            logs,
            seeds,
            geometries,
        } => run_correctness(all, coordinate.as_deref(), &logs, &seeds, &geometries),
        Command::Production {
            coordinate,
            all_geometries,
            geometry,
            once,
            expected_checksum,
            output_dir,
            point,
            resume,
            runtime_bytes,
        } => run_production(
            &coordinate,
            all_geometries,
            geometry.as_deref(),
            once,
            expected_checksum.as_deref(),
            &output_dir,
            &point,
            resume,
            runtime_bytes,
        ),
        Command::ProductionPlan { runtime_bytes } => run_production_plan(runtime_bytes),
        Command::ProductionPreflight {
            coordinate,
            runtime_bytes,
        } => run_production_preflight(&coordinate, runtime_bytes),
        Command::Timing {
            point,
            coordinate,
            geometries,
            traversal,
            warmups,
            samples,
            expected_checksum,
            session_bindings,
            output_dir,
            resume,
        } => run_timing(
            &point,
            &coordinate,
            &geometries,
            traversal,
            warmups,
            samples,
            &expected_checksum,
            &session_bindings,
            &output_dir,
            resume,
        ),
    }
}

#[derive(Serialize)]
struct ProductionPlanRow {
    circuit: String,
    layer: u32,
    trace_len: u64,
    log_trace: u32,
    preflight: R0MemoryPreflight,
}

#[derive(Serialize)]
struct ProductionPreflightRow {
    circuit: String,
    layer: u32,
    trace_len: u64,
    log_trace: u32,
    preflight: R0MemoryPreflight,
    fits_device_free: bool,
    failure: Option<String>,
}

fn run_production_plan(runtime_bytes: u64) -> Result<(), Box<dyn std::error::Error>> {
    let bundle = decode_r0_bundle(R0_CORPUS_BYTES)?;
    for coordinate in bundle.coordinates {
        if !coordinate.trace_len.is_power_of_two() {
            return Err(format!(
                "production trace length {} is not a power of two for {}:{}",
                coordinate.trace_len, coordinate.circuit, coordinate.layer
            )
            .into());
        }
        let log_trace = coordinate.trace_len.ilog2();
        let preflight =
            R0MemoryPreflight::for_coordinate(&coordinate, log_trace, runtime_bytes, None)?;
        println!(
            "{}",
            serde_json::to_string(&ProductionPlanRow {
                circuit: coordinate.circuit,
                layer: coordinate.layer,
                trace_len: coordinate.trace_len,
                log_trace,
                preflight,
            })?
        );
    }
    Ok(())
}

fn run_production_preflight(
    coordinate_name: &str,
    runtime_bytes: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let (coordinate, _, _) = load_case(coordinate_name)?;
    if !coordinate.trace_len.is_power_of_two() {
        return Err("production trace length is not a power of two".into());
    }
    let log_trace = coordinate.trace_len.ilog2();
    let (preflight, failure) = match production_memory_preflight(&coordinate, runtime_bytes) {
        Ok(preflight) => (preflight, None),
        Err(error @ R0ProductionError::InsufficientDeviceMemory { .. }) => {
            let failure = error.to_string();
            let R0ProductionError::InsufficientDeviceMemory { preflight, .. } = error else {
                unreachable!()
            };
            (*preflight, Some(failure))
        }
        Err(error) => return Err(error.into()),
    };
    println!(
        "{}",
        serde_json::to_string(&ProductionPreflightRow {
            circuit: coordinate.circuit,
            layer: coordinate.layer,
            trace_len: coordinate.trace_len,
            log_trace,
            fits_device_free: failure.is_none(),
            preflight,
            failure: failure.clone(),
        })?
    );
    if let Some(failure) = failure {
        return Err(failure.into());
    }
    Ok(())
}

fn run_abi_probe() -> Result<(), Box<dyn std::error::Error>> {
    let rust = rust_r0_abi_layout();
    let native = native_r0_abi_layout()?;
    let matches = rust == native;
    println!(
        "{}",
        serde_json::to_string(&AbiProbeOutput {
            rust,
            native,
            matches,
        })?
    );
    if !matches {
        return Err("Rust/CUDA R0 ABI mismatch".into());
    }
    Ok(())
}

fn run_geometry_smoke(
    coordinate_name: &str,
    log_trace: u32,
    seed: u64,
    geometries: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let (coordinate, layer, program) = load_case(coordinate_name)?;
    let input = build_r0_input_with_layer(&coordinate, &layer, log_trace, seed)?;
    if log_trace == 3
        && (input.eq_tables.sizes.high != [0, 0]
            || input.eq_tables.sizes.low != 0
            || input.eq_tables.low != vec![E4::ONE])
    {
        return Err("log-3 equality layout is not the zero-group identity layout".into());
    }
    let canonical_q = evaluate_canonical_r0_convention(&layer, &coordinate.binding, &input)?;
    let compiled_q = evaluate_compiled_r0_tensor(&program, &input)?;
    if canonical_q != compiled_q {
        return Err("canonical-derived Q and compiled Q differ".into());
    }

    let census = program_census(&coordinate)?;
    let requested_geometries = parse_geometries(geometries)?;
    let mut harness = R0Harness::new(&coordinate, &input)?;
    let mut observations = Vec::new();
    for geometry in requested_geometries {
        let observed = harness.run_once(geometry)?;
        if observed.cells != freeze_tensor(&canonical_q) {
            return Err(format!("{geometry} differs from compiler-convention Q").into());
        }
        let output = thaw_tensor(&observed.cells);
        observations.push(GeometryObservation {
            geometry,
            launch: observed.launch,
            census: census.clone(),
            cells: observed.cells,
            checksum: r0_output_checksum(&output),
        });
    }
    if observations.windows(2).any(|pair| {
        pair[0].cells != pair[1].cells
            || pair[0].census.classes != pair[1].census.classes
            || pair[0].census.source_uses != pair[1].census.source_uses
    }) {
        return Err("geometries differ in cells or program census".into());
    }

    let output = GeometrySmokeOutput {
        coordinate: coordinate_name.to_owned(),
        log_trace,
        seed,
        input_sha256: input.identity.input_sha256,
        eq_layout: EqLayout {
            high: input.eq_tables.sizes.high,
            low: input.eq_tables.sizes.low,
            high_lengths: [input.eq_tables.high[0].len(), input.eq_tables.high[1].len()],
            low_length: input.eq_tables.low.len(),
        },
        canonical_q: freeze_tensor(&canonical_q),
        canonical_q_checksum: r0_output_checksum(&canonical_q),
        compiled_q: freeze_tensor(&compiled_q),
        compiled_q_checksum: r0_output_checksum(&compiled_q),
        observations,
    };
    println!("{}", serde_json::to_string(&output)?);
    Ok(())
}

fn run_correctness(
    all: bool,
    coordinate_name: Option<&str>,
    logs: &str,
    seeds: &str,
    geometries: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let logs = parse_logs(logs)?;
    let seeds = parse_seeds(seeds)?;
    let geometries = parse_correctness_geometries(geometries)?;
    let mut cases = load_cases()?;
    if !all {
        let coordinate_name = coordinate_name.ok_or("one coordinate or --all is required")?;
        cases.retain(|(coordinate, _, _)| {
            format!("{}:{}", coordinate.circuit, coordinate.layer) == coordinate_name
        });
        if cases.is_empty() {
            return Err(format!("coordinate {coordinate_name:?} is not in the R0 corpus").into());
        }
    }

    let stdout = io::stdout();
    let mut output = stdout.lock();
    let mut row_count = 0usize;
    for (coordinate, layer, program) in cases {
        for &log_trace in &logs {
            for &seed in &seeds {
                let input = build_r0_input_with_layer(&coordinate, &layer, log_trace, seed)?;
                let canonical_p =
                    evaluate_true_canonical_tensor(&layer, &coordinate.binding, &input)?;
                let canonical_q =
                    evaluate_canonical_r0_convention(&layer, &coordinate.binding, &input)?;
                let compiled_q = evaluate_compiled_r0_tensor(&program, &input)?;
                let p_minus_q = tensor_difference(canonical_p, canonical_q);
                let frozen_p = freeze_tensor(&canonical_p);
                let frozen_q = freeze_tensor(&canonical_q);
                let frozen_compiled = freeze_tensor(&compiled_q);
                let frozen_delta = freeze_tensor(&p_minus_q);
                let canonical_p_sha256 = r0_cells_sha256(&frozen_p)?;
                let canonical_q_sha256 = r0_cells_sha256(&frozen_q)?;
                let compiled_q_sha256 = r0_cells_sha256(&frozen_compiled)?;
                let p_minus_q_sha256 = r0_cells_sha256(&frozen_delta)?;
                let canonical_q_matches_compiled = canonical_q == compiled_q;
                let mut harness = R0Harness::new(&coordinate, &input)?;
                for &geometry in &geometries {
                    let observed = harness.run_once(geometry)?;
                    let gpu_matches_canonical_q = observed.cells == frozen_q;
                    let gpu_matches_compiled_q = observed.cells == frozen_compiled;
                    let passing = canonical_q_matches_compiled
                        && gpu_matches_canonical_q
                        && gpu_matches_compiled_q;
                    let row = CorrectnessRow {
                        version: 1,
                        circuit: coordinate.circuit.clone(),
                        layer: coordinate.layer,
                        log_trace,
                        seed,
                        geometry,
                        hashes: harness.hashes().clone(),
                        canonical_p_sha256: canonical_p_sha256.clone(),
                        canonical_q_sha256: canonical_q_sha256.clone(),
                        compiled_q_sha256: compiled_q_sha256.clone(),
                        p_minus_q_sha256: p_minus_q_sha256.clone(),
                        launch: observed.launch,
                        cells: observed.cells,
                        checksum: observed.checksum,
                        canonical_q_matches_compiled,
                        gpu_matches_canonical_q,
                        gpu_matches_compiled_q,
                        passing,
                    };
                    serde_json::to_writer(&mut output, &row)?;
                    output.write_all(b"\n")?;
                    output.flush()?;
                    row_count += 1;
                    if !passing {
                        return Err(format!(
                            "R0 correctness mismatch at {}:{} log={} seed={} geometry={}",
                            coordinate.circuit, coordinate.layer, log_trace, seed, geometry
                        )
                        .into());
                    }
                }
            }
        }
    }
    eprintln!("R0 correctness rows: {row_count}");
    Ok(())
}

struct PendingProduction {
    key: R0ResultKey,
    checkpoint_path: PathBuf,
    rows_path: PathBuf,
}

fn run_production(
    coordinate_name: &str,
    all_geometries: bool,
    geometry_name: Option<&str>,
    once: bool,
    expected_checksum: Option<&str>,
    output_dir: &Path,
    point: &str,
    resume: bool,
    runtime_bytes: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    if cfg!(debug_assertions) {
        return Err("production mode requires the release runner".into());
    }
    validate_point_name(point)?;
    let requested_geometries = if all_geometries {
        if once || expected_checksum.is_some() || geometry_name.is_some() {
            return Err("--all-geometries cannot use single-launch options".into());
        }
        R0Geometry::ALL.to_vec()
    } else {
        let geometry_name = geometry_name.ok_or("--geometry is required")?;
        if !once || expected_checksum.is_none() {
            return Err(
                "single-geometry production requires --once and --expected-checksum".into(),
            );
        }
        let parsed = parse_geometries(geometry_name)?;
        if parsed.len() != 1 {
            return Err("single-geometry production accepts exactly one geometry".into());
        }
        parsed
    };
    if let Some(expected) = expected_checksum {
        validate_sha256(expected, "expected checksum")?;
    }

    let (coordinate, layer, program) = load_case(coordinate_name)?;
    if !coordinate.trace_len.is_power_of_two() {
        return Err(format!(
            "production trace length {} is not a power of two",
            coordinate.trace_len
        )
        .into());
    }
    let log_trace = coordinate.trace_len.ilog2();
    let production_rows = coordinate.trace_len / 8;
    let preflight_result = production_memory_preflight(&coordinate, runtime_bytes);
    let (preflight, preflight_failure) = match preflight_result {
        Ok(preflight) => (preflight, None),
        Err(error @ R0ProductionError::InsufficientDeviceMemory { .. }) => {
            let failure = error.to_string();
            let R0ProductionError::InsufficientDeviceMemory { preflight, .. } = error else {
                unreachable!()
            };
            (*preflight, Some(failure))
        }
        Err(error) => return Err(error.into()),
    };

    // The checked memory plan and cudaMemGetInfo capacity gate precede this
    // potentially large host allocation. This constructor performs no DAG/CPU
    // semantic evaluation and fills every source backing as traffic.
    let (prepared_input, bindings) =
        prepared_production_input_and_bindings(&coordinate, log_trace)?;
    fs::create_dir_all(output_dir)?;

    let mut pending = Vec::new();
    let mut observations = Vec::new();
    for &geometry in &requested_geometries {
        let key = R0ResultKey {
            point: point.to_owned(),
            circuit: coordinate.circuit.clone(),
            layer: coordinate.layer,
            log_trace,
            seed: R0_PRODUCTION_SEED,
            geometry,
            traversal: None,
        };
        let stem = format!(
            "{}--{}-l{}--{}",
            point,
            coordinate.circuit,
            coordinate.layer,
            geometry.as_str()
        );
        let checkpoint_path = output_dir.join(format!("{stem}.checkpoint.json"));
        let rows_path = output_dir.join(format!("{stem}.observations.jsonl"));
        if checkpoint_path.exists() {
            match verify_reusable_checkpoint(
                &checkpoint_path,
                &rows_path,
                &key,
                &bindings,
                R0RowsKind::Observation,
            ) {
                Ok(R0CheckpointReuse::Complete) => {
                    let mut rows = read_observation_rows(&rows_path)?;
                    if rows.len() != 1 {
                        return Err(format!(
                            "complete production checkpoint {} has {} rows, expected one",
                            checkpoint_path.display(),
                            rows.len()
                        )
                        .into());
                    }
                    observations.push(rows.remove(0));
                    continue;
                }
                Ok(R0CheckpointReuse::Execute) => unreachable!(),
                Err(_) => {
                    // `begin_checkpoint` accepts only a matching Started record
                    // under explicit resume. A corrupt/mismatched Complete record
                    // remains immutable and therefore fails closed here.
                }
            }
        }
        begin_checkpoint(&checkpoint_path, &rows_path, &key, &bindings, resume)?;
        pending.push(PendingProduction {
            key,
            checkpoint_path,
            rows_path,
        });
    }

    pause_after_started_for_kill_smoke()?;

    if let Some(failure) = preflight_failure {
        for pending_row in pending {
            let row = production_failure_row(
                &coordinate,
                &bindings,
                pending_row.key.clone(),
                production_rows,
                Some(preflight.clone()),
                failure.clone(),
            );
            persist_observation(&pending_row, &bindings, &row)?;
            observations.push(row);
        }
        emit_production_rows(&observations)?;
        return Err(failure.into());
    }

    if pending.is_empty() {
        verify_production_observations(&observations, expected_checksum)?;
        emit_production_rows(&observations)?;
        return Ok(());
    }

    let mut harness =
        match R0Harness::new_prepared_production(&coordinate, prepared_input, preflight.clone()) {
            Ok(harness) => harness,
            Err(error) => {
                let failure = error.to_string();
                let is_oom = error.is_oom();
                for pending_row in pending {
                    let row = production_failure_row(
                        &coordinate,
                        &bindings,
                        pending_row.key.clone(),
                        production_rows,
                        Some(preflight.clone()),
                        failure.clone(),
                    );
                    persist_observation(&pending_row, &bindings, &row)?;
                    observations.push(row);
                }
                if is_oom {
                    run_log8_oom_diagnostic(&coordinate, &layer, &program, &requested_geometries)?;
                }
                emit_production_rows(&observations)?;
                return Err(failure.into());
            }
        };
    if harness.hashes().bundle_sha256 != bindings.bundle_sha256
        || harness.hashes().coordinate_sha256 != bindings.coordinate_sha256
        || harness.hashes().input_sha256 != bindings.input_sha256
        || harness.hashes().source_data_sha256 != bindings.source_data_sha256
        || harness.hashes().independent_source_sha256 != bindings.independent_source_sha256
        || harness.hashes().derived_source_sha256 != bindings.derived_source_sha256
        || harness.hashes().coefficient_sha256 != bindings.coefficient_sha256
        || harness.hashes().direct_eq_sha256 != bindings.direct_eq_sha256
        || harness.hashes().factored_eq_sha256 != bindings.factored_eq_sha256
        || harness.hashes().executable_sha256 != bindings.executable_sha256
    {
        return Err("production harness identity differs from checkpoint bindings".into());
    }

    let mut executed = Vec::new();
    for pending_row in pending {
        match harness.run_once_production(pending_row.key.geometry) {
            Ok(observed) => executed.push((pending_row, observed)),
            Err(error) => {
                let failure = error.to_string();
                let is_oom = error.is_oom();
                let row = production_failure_row(
                    &coordinate,
                    &bindings,
                    pending_row.key.clone(),
                    production_rows,
                    Some(preflight.clone()),
                    failure.clone(),
                );
                persist_observation(&pending_row, &bindings, &row)?;
                observations.push(row);
                drop(harness);
                if is_oom {
                    run_log8_oom_diagnostic(&coordinate, &layer, &program, &requested_geometries)?;
                }
                emit_production_rows(&observations)?;
                return Err(failure.into());
            }
        }
    }

    let mut prospective = observations
        .iter()
        .filter_map(|row| {
            row.cells
                .as_ref()
                .map(|cells| (cells, row.checksum.as_ref()))
        })
        .collect::<Vec<_>>();
    prospective.extend(
        executed
            .iter()
            .map(|(_, observed)| (&observed.cells, Some(&observed.checksum))),
    );
    if prospective.len() != requested_geometries.len()
        || prospective
            .windows(2)
            .any(|pair| pair[0].0 != pair[1].0 || pair[0].1 != pair[1].1)
    {
        return Err("production all-geometry literal 27-cell equality failed".into());
    }
    if let Some(expected) = expected_checksum {
        if prospective[0].1.map(String::as_str) != Some(expected) {
            return Err(format!(
                "production checksum {} differs from expected {expected}",
                prospective[0].1.expect("prospective checksum exists")
            )
            .into());
        }
    }

    for (pending_row, observed) in executed {
        let row = R0ObservationRowV1 {
            version: R0_REPORT_VERSION,
            key: pending_row.key.clone(),
            bindings: bindings.clone(),
            production_rows,
            shape: coordinate.shape.clone(),
            preflight: Some(preflight.clone()),
            launch: Some(observed.launch),
            cells: Some(observed.cells),
            checksum: Some(observed.checksum),
            failure: None,
        };
        persist_observation(&pending_row, &bindings, &row)?;
        observations.push(row);
    }
    verify_production_observations(&observations, expected_checksum)?;
    emit_production_rows(&observations)?;
    Ok(())
}

#[derive(Deserialize)]
struct TimingSessionBindings {
    version: u32,
    point: String,
    coordinate: String,
    traversal: String,
    geometries: Vec<String>,
    warmups: u32,
    samples: u32,
    executable_sha256: String,
    bundle_sha256: String,
    input_sha256: String,
    source_tree_sha256: String,
    build_flags_sha256: String,
    expected_checksum: String,
    production_bindings: R0Bindings,
}

#[derive(Serialize)]
struct TimingSessionOutput {
    key: R0ResultKey,
    reused: bool,
    launch: Option<R0LaunchMetadata>,
    correctness_checksum: String,
    post_session_checksum: String,
    warmups: u32,
    samples: u32,
}

struct PendingTiming {
    key: R0ResultKey,
    checkpoint_path: PathBuf,
    rows_path: PathBuf,
}

fn run_timing(
    point: &str,
    coordinate_name: &str,
    geometries: &str,
    traversal: TimingTraversal,
    warmups: u32,
    samples: u32,
    expected_checksum: &str,
    session_bindings_path: &Path,
    output_dir: &Path,
    resume: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    if cfg!(debug_assertions) {
        return Err("timing mode requires the release runner".into());
    }
    validate_point_name(point)?;
    if (warmups, samples) != (5, 50) {
        return Err("timing requires exactly five warmups and 50 samples per traversal".into());
    }
    validate_sha256(expected_checksum, "expected checksum")?;
    let parsed = parse_geometries(geometries)?;
    if parsed.len() != R0Geometry::ALL.len()
        || parsed
            .iter()
            .enumerate()
            .any(|(index, geometry)| parsed[..index].contains(geometry))
        || R0Geometry::ALL
            .iter()
            .any(|geometry| !parsed.contains(geometry))
    {
        return Err("timing requires each of the five geometries exactly once".into());
    }
    let key_traversal = match traversal {
        TimingTraversal::Forward => R0Traversal::Forward,
        TimingTraversal::Reverse => R0Traversal::Reverse,
    };

    let session_bindings: TimingSessionBindings =
        serde_json::from_slice(&fs::read(session_bindings_path)?)?;
    if session_bindings.version != 1
        || session_bindings.point != point
        || session_bindings.coordinate != coordinate_name
        || session_bindings.traversal
            != match key_traversal {
                R0Traversal::Forward => "forward",
                R0Traversal::Reverse => "reverse",
            }
        || session_bindings.geometries
            != parsed
                .iter()
                .map(|geometry| geometry.as_str().to_owned())
                .collect::<Vec<_>>()
        || session_bindings.warmups != warmups
        || session_bindings.samples != samples
        || session_bindings.expected_checksum != expected_checksum
    {
        return Err("timing session binding identity mismatch".into());
    }

    let (coordinate, _layer, _program) = load_case(coordinate_name)?;
    if !coordinate.trace_len.is_power_of_two() {
        return Err("timing coordinate trace length is not a power of two".into());
    }
    let log_trace = coordinate.trace_len.ilog2();
    let preflight = production_memory_preflight(&coordinate, 0)?;
    let (prepared_input, bindings) =
        prepared_production_input_and_bindings(&coordinate, log_trace)?;
    let production = &session_bindings.production_bindings;
    let semantic_binding_match = bindings.bundle_sha256 == production.bundle_sha256
        && bindings.coordinate_sha256 == production.coordinate_sha256
        && bindings.input_sha256 == production.input_sha256
        && bindings.source_data_sha256 == production.source_data_sha256
        && bindings.independent_source_sha256 == production.independent_source_sha256
        && bindings.derived_source_sha256 == production.derived_source_sha256
        && bindings.challenge_sha256 == production.challenge_sha256
        && bindings.equality_point_sha256 == production.equality_point_sha256
        && bindings.direct_eq_sha256 == production.direct_eq_sha256
        && bindings.factored_eq_sha256 == production.factored_eq_sha256
        && bindings.coefficient_sha256 == production.coefficient_sha256;
    if !semantic_binding_match
        || session_bindings.executable_sha256 != bindings.executable_sha256
        || session_bindings.bundle_sha256 != bindings.bundle_sha256
        || session_bindings.input_sha256 != bindings.input_sha256
        || session_bindings.source_tree_sha256 != bindings.source_tree_sha256
        || session_bindings.build_flags_sha256 != bindings.build_flags_sha256
    {
        return Err("timing session binding mismatch".into());
    }

    fs::create_dir_all(output_dir)?;
    let mut pending = Vec::new();
    let mut output_rows = Vec::new();
    for &geometry in &parsed {
        let key = R0ResultKey {
            point: point.to_owned(),
            circuit: coordinate.circuit.clone(),
            layer: coordinate.layer,
            log_trace,
            seed: R0_PRODUCTION_SEED,
            geometry,
            traversal: Some(key_traversal),
        };
        let checkpoint_path = output_dir.join(format!("{}.checkpoint.json", geometry.as_str()));
        let rows_path = output_dir.join(format!("{}.samples.jsonl", geometry.as_str()));
        if checkpoint_path.exists()
            && verify_reusable_checkpoint(
                &checkpoint_path,
                &rows_path,
                &key,
                &bindings,
                R0RowsKind::Timing,
            )
            .is_ok()
        {
            let rows = read_timing_samples(&rows_path)?;
            if rows.len() != 55 {
                return Err("reused timing checkpoint does not contain 55 rows".into());
            }
            output_rows.push(TimingSessionOutput {
                key,
                reused: true,
                launch: None,
                correctness_checksum: expected_checksum.to_owned(),
                post_session_checksum: expected_checksum.to_owned(),
                warmups: 5,
                samples: 50,
            });
            continue;
        }
        begin_checkpoint(&checkpoint_path, &rows_path, &key, &bindings, resume)?;
        pending.push(PendingTiming {
            key,
            checkpoint_path,
            rows_path,
        });
    }

    if !pending.is_empty() {
        let mut harness =
            R0Harness::new_prepared_production(&coordinate, prepared_input, preflight)?;
        let config = R0TimingConfig::production_traversal();
        for pending_row in pending {
            let session = harness.measure_geometry(pending_row.key.geometry, config)?;
            if session.correctness_checksum != expected_checksum
                || session.post_session_checksum != expected_checksum
            {
                return Err(format!(
                    "timing checksum differs from expected {expected_checksum}: correctness={} post-session={}",
                    session.correctness_checksum, session.post_session_checksum
                )
                .into());
            }
            let rows = session
                .samples
                .iter()
                .enumerate()
                .map(|(sample_index, sample)| R0TimingSampleV1 {
                    key: pending_row.key.clone(),
                    sample_index: sample_index as u32,
                    warmup: sample.warmup,
                    milliseconds: sample.milliseconds,
                })
                .collect::<Vec<_>>();
            write_jsonl_atomic(&pending_row.rows_path, &rows)?;
            complete_checkpoint(
                &pending_row.checkpoint_path,
                &pending_row.rows_path,
                &pending_row.key,
                &bindings,
                R0RowsKind::Timing,
            )?;
            output_rows.push(TimingSessionOutput {
                key: pending_row.key,
                reused: false,
                launch: Some(session.launch),
                correctness_checksum: session.correctness_checksum,
                post_session_checksum: session.post_session_checksum,
                warmups: config.warmups(),
                samples: config.samples(),
            });
        }
    }

    for row in output_rows {
        println!("{}", serde_json::to_string(&row)?);
    }
    Ok(())
}

fn prepared_production_input_and_bindings(
    coordinate: &FrozenR0Coordinate,
    log_trace: u32,
) -> Result<(PreparedR0ProductionInput, R0Bindings), Box<dyn std::error::Error>> {
    let prepared = build_prepared_r0_production_input(coordinate, log_trace, R0_PRODUCTION_SEED)?;
    let bindings = production_bindings(coordinate, prepared.resolved())?;
    Ok((prepared, bindings))
}

fn production_bindings(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
) -> Result<R0Bindings, Box<dyn std::error::Error>> {
    let challenge_sha256 = sha256_json(&(
        &input.identity.challenge_bases,
        &input.identity.challenge_values,
    ))?;
    let equality_point_sha256 = sha256_json(&input.identity.equality_point)?;
    let executable_sha256 = sha256_file(&std::env::current_exe()?)?;
    let source_tree_sha256 = source_tree_sha256()?;
    let build_flags_sha256 = sha256_bytes(
        format!(
            "profile=release;artifact-gen=true;cudaarchs={}",
            option_env!("CUDAARCHS").unwrap_or("native")
        )
        .as_bytes(),
    )?;
    Ok(R0Bindings {
        bundle_sha256: sha256_bytes(R0_CORPUS_BYTES)?,
        coordinate_sha256: coordinate.payload_sha256.clone(),
        input_sha256: input.identity.input_sha256.clone(),
        source_data_sha256: input.identity.source_data_sha256.clone(),
        independent_source_sha256: input.identity.independent_source_sha256.clone(),
        derived_source_sha256: input.identity.derived_source_sha256.clone(),
        challenge_sha256,
        equality_point_sha256,
        direct_eq_sha256: input.identity.direct_eq_sha256.clone(),
        factored_eq_sha256: input.identity.factored_eq_sha256.clone(),
        coefficient_sha256: input.identity.coefficient_sha256.clone(),
        executable_sha256,
        source_tree_sha256,
        build_flags_sha256,
    })
}

fn production_failure_row(
    coordinate: &FrozenR0Coordinate,
    bindings: &R0Bindings,
    key: R0ResultKey,
    production_rows: u64,
    preflight: Option<gpu_gkr_windowed_bench::r0_geometry::R0MemoryPreflight>,
    failure: String,
) -> R0ObservationRowV1 {
    R0ObservationRowV1 {
        version: R0_REPORT_VERSION,
        key,
        bindings: bindings.clone(),
        production_rows,
        shape: coordinate.shape.clone(),
        preflight,
        launch: None,
        cells: None,
        checksum: None,
        failure: Some(failure),
    }
}

fn persist_observation(
    pending: &PendingProduction,
    bindings: &R0Bindings,
    row: &R0ObservationRowV1,
) -> Result<(), Box<dyn std::error::Error>> {
    write_jsonl_atomic(&pending.rows_path, std::slice::from_ref(row))?;
    complete_checkpoint(
        &pending.checkpoint_path,
        &pending.rows_path,
        &pending.key,
        bindings,
        R0RowsKind::Observation,
    )?;
    Ok(())
}

fn verify_production_observations(
    rows: &[R0ObservationRowV1],
    expected_checksum: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    if rows.is_empty() {
        return Err("production produced no observations".into());
    }
    if let Some(failure) = rows.iter().find_map(|row| row.failure.as_deref()) {
        return Err(format!("production checkpoint records failure: {failure}").into());
    }
    let first_cells = rows[0]
        .cells
        .as_ref()
        .ok_or("production cells are missing")?;
    let first_checksum = rows[0]
        .checksum
        .as_deref()
        .ok_or("production checksum is missing")?;
    if rows.iter().any(|row| {
        row.cells.as_ref() != Some(first_cells) || row.checksum.as_deref() != Some(first_checksum)
    }) {
        return Err("production checkpoints differ across literal cells/checksums".into());
    }
    if expected_checksum.is_some_and(|expected| expected != first_checksum) {
        return Err(format!(
            "production checksum {first_checksum} differs from expected {}",
            expected_checksum.expect("expected checksum is present")
        )
        .into());
    }
    Ok(())
}

fn emit_production_rows(rows: &[R0ObservationRowV1]) -> Result<(), Box<dyn std::error::Error>> {
    let stdout = io::stdout();
    let mut output = stdout.lock();
    for row in rows {
        serde_json::to_writer(&mut output, row)?;
        output.write_all(b"\n")?;
    }
    output.flush()?;
    Ok(())
}

fn run_log8_oom_diagnostic(
    coordinate: &FrozenR0Coordinate,
    layer: &gkr_eval_ir::DagLayer,
    program: &R0LayerProgram,
    geometries: &[R0Geometry],
) -> Result<(), Box<dyn std::error::Error>> {
    let input = build_r0_input_with_layer(coordinate, layer, 8, 0)?;
    let canonical_q = evaluate_canonical_r0_convention(layer, &coordinate.binding, &input)?;
    let compiled_q = evaluate_compiled_r0_tensor(program, &input)?;
    if canonical_q != compiled_q {
        return Err("production-incomplete-oom log8 diagnostic CPU references differ".into());
    }
    let expected = freeze_tensor(&canonical_q);
    let mut harness = R0Harness::new(coordinate, &input)?;
    for &geometry in geometries {
        let observed = harness.run_once(geometry)?;
        if observed.cells != expected {
            return Err(
                format!("production-incomplete-oom log8 diagnostic failed for {geometry}").into(),
            );
        }
    }
    eprintln!(
        "production-incomplete-oom: bounded log8 correctness diagnostic passed; diagnostic is not production performance"
    );
    Ok(())
}

fn pause_after_started_for_kill_smoke() -> Result<(), Box<dyn std::error::Error>> {
    let Some(value) = std::env::var_os("AB_R0_PAUSE_AFTER_STARTED_MS") else {
        return Ok(());
    };
    let milliseconds = value
        .to_str()
        .ok_or("AB_R0_PAUSE_AFTER_STARTED_MS is not UTF-8")?
        .parse::<u64>()?;
    if milliseconds > 60_000 {
        return Err("AB_R0_PAUSE_AFTER_STARTED_MS exceeds the 60s test cap".into());
    }
    eprintln!("R0_PRODUCTION_STARTED pause_ms={milliseconds}");
    std::thread::sleep(Duration::from_millis(milliseconds));
    Ok(())
}

fn validate_point_name(point: &str) -> Result<(), Box<dyn std::error::Error>> {
    if point.is_empty()
        || !point
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err("point must be a nonempty ASCII identifier".into());
    }
    Ok(())
}

fn validate_sha256(value: &str, name: &str) -> Result<(), Box<dyn std::error::Error>> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!("{name} is not lowercase SHA-256").into());
    }
    Ok(())
}

fn sha256_json(value: &impl Serialize) -> Result<String, Box<dyn std::error::Error>> {
    sha256_bytes(&serde_json::to_vec(value)?)
}

fn sha256_file(path: &Path) -> Result<String, Box<dyn std::error::Error>> {
    let bytes = fs::read(path)?;
    sha256_bytes(&bytes)
}

fn sha256_bytes(bytes: &[u8]) -> Result<String, Box<dyn std::error::Error>> {
    let mut child = ProcessCommand::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let mut stdin = child.stdin.take().ok_or("sha256sum stdin is unavailable")?;
    stdin.write_all(bytes)?;
    drop(stdin);
    let output = child.wait_with_output()?;
    if !output.status.success() {
        return Err("sha256sum failed".into());
    }
    let stdout = String::from_utf8(output.stdout)?;
    let hash = stdout.split_whitespace().next().unwrap_or_default();
    validate_sha256(hash, "sha256sum output")?;
    Ok(hash.to_owned())
}

fn source_tree_sha256() -> Result<String, Box<dyn std::error::Error>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut paths = Vec::new();
    collect_source_files(&root.join("src"), &mut paths)?;
    collect_source_files(&root.join("native"), &mut paths)?;
    paths.push(root.join("Cargo.toml"));
    paths.push(root.join("build.rs"));
    paths.sort();
    let mut preimage = Vec::new();
    for path in paths {
        let relative = path.strip_prefix(&root)?.to_string_lossy();
        let bytes = fs::read(&path)?;
        preimage.extend_from_slice(&(relative.len() as u64).to_le_bytes());
        preimage.extend_from_slice(relative.as_bytes());
        preimage.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        preimage.extend_from_slice(&bytes);
    }
    sha256_bytes(&preimage)
}

fn collect_source_files(
    directory: &Path,
    paths: &mut Vec<PathBuf>,
) -> Result<(), Box<dyn std::error::Error>> {
    for entry in fs::read_dir(directory)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_source_files(&entry.path(), paths)?;
        } else if file_type.is_file() {
            paths.push(entry.path());
        }
    }
    Ok(())
}

fn parse_geometries(value: &str) -> Result<Vec<R0Geometry>, Box<dyn std::error::Error>> {
    if value == "all" {
        return Ok(R0Geometry::ALL.to_vec());
    }
    let geometries = value
        .split(',')
        .map(|name| match name {
            "cta288_pair" => Ok(R0Geometry::Cta288Pair),
            "cta96_partitioned" => Ok(R0Geometry::Cta96Partitioned),
            "cta96_x0_major" => Ok(R0Geometry::Cta96X0Major),
            "cta96_x1_major" => Ok(R0Geometry::Cta96X1Major),
            "cta96_x2_major" => Ok(R0Geometry::Cta96X2Major),
            _ => Err(format!("unknown R0 geometry {name:?}")),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if geometries.is_empty() {
        return Err("at least one R0 geometry is required".into());
    }
    Ok(geometries)
}

fn parse_correctness_geometries(
    value: &str,
) -> Result<Vec<R0Geometry>, Box<dyn std::error::Error>> {
    let geometries = parse_geometries(value)?;
    if geometries
        .iter()
        .enumerate()
        .any(|(index, geometry)| geometries[..index].contains(geometry))
    {
        return Err("correctness geometries must be unique".into());
    }
    Ok(geometries)
}

fn parse_logs(value: &str) -> Result<Vec<u32>, Box<dyn std::error::Error>> {
    let logs = parse_csv(value, "log", |entry| entry.parse::<u32>())?;
    if logs.iter().any(|log| !(3..=27).contains(log)) {
        return Err("correctness logs must be in 3..=27".into());
    }
    Ok(logs)
}

fn parse_seeds(value: &str) -> Result<Vec<u64>, Box<dyn std::error::Error>> {
    parse_csv(value, "seed", |entry| entry.parse::<u64>())
}

fn parse_csv<T, E>(
    value: &str,
    kind: &str,
    mut parse: impl FnMut(&str) -> Result<T, E>,
) -> Result<Vec<T>, Box<dyn std::error::Error>>
where
    T: Copy + Eq + std::hash::Hash,
    E: std::error::Error + 'static,
{
    if value.is_empty() {
        return Err(format!("at least one {kind} is required").into());
    }
    let values = value
        .split(',')
        .map(|entry| {
            parse(entry).map_err(|error| -> Box<dyn std::error::Error> {
                format!("invalid {kind} {entry:?}: {error}").into()
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.iter().copied().collect::<HashSet<_>>().len() != values.len() {
        return Err(format!("correctness {kind}s must be unique").into());
    }
    Ok(values)
}

fn load_case(
    coordinate_name: &str,
) -> Result<(FrozenR0Coordinate, gkr_eval_ir::DagLayer, R0LayerProgram), Box<dyn std::error::Error>>
{
    load_cases()?
        .into_iter()
        .find(|(coordinate, _, _)| {
            format!("{}:{}", coordinate.circuit, coordinate.layer) == coordinate_name
        })
        .ok_or_else(|| "coordinate is not present in the frozen R0 corpus".into())
}

type R0Case = (FrozenR0Coordinate, gkr_eval_ir::DagLayer, R0LayerProgram);

fn load_cases() -> Result<Vec<R0Case>, Box<dyn std::error::Error>> {
    let bundle = decode_r0_bundle(R0_CORPUS_BYTES)?;
    let mut cases = Vec::with_capacity(bundle.coordinates.len());
    for layout in CORPUS {
        let circuit = layout
            .strip_suffix("_layout_gkr.json")
            .ok_or("canonical layout has an unexpected filename")?;
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits")
            .join(layout);
        let bytes = std::fs::read(path)?;
        let artifact: GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes)?;
        let dag = gkr_eval_ir::lower_dag(&artifact)?;
        gkr_eval_ir::validate(&dag).map_err(|error| format!("canonical DAG: {error}"))?;
        let compiled = compile_r0(&dag, &GpuResourceProfile::production())?;
        for program in compiled.layers {
            let coordinate = bundle
                .coordinates
                .iter()
                .find(|coordinate| {
                    coordinate.circuit == circuit && coordinate.layer as usize == program.layer
                })
                .cloned()
                .ok_or("compiler produced a coordinate absent from the frozen bundle")?;
            if program.program.words != coordinate.program_words
                || program.binding != coordinate.binding
                || program.program.term_count != coordinate.term_count as usize
            {
                return Err(format!(
                    "live compiler R0 program differs from {}:{}",
                    coordinate.circuit, coordinate.layer
                )
                .into());
            }
            let canonical_layer = dag
                .layers
                .get(program.layer)
                .cloned()
                .ok_or("canonical layer is missing")?;
            cases.push((coordinate, canonical_layer, program));
        }
    }
    cases.sort_by(|left, right| {
        (&left.0.circuit, left.0.layer).cmp(&(&right.0.circuit, right.0.layer))
    });
    if cases.len() != bundle.coordinates.len()
        || cases
            .iter()
            .zip(&bundle.coordinates)
            .any(|(case, coordinate)| case.0 != *coordinate)
    {
        return Err("live compiler R0 coordinate set differs from the frozen bundle".into());
    }
    Ok(cases)
}

fn program_census(
    coordinate: &FrozenR0Coordinate,
) -> Result<ProgramCensus, Box<dyn std::error::Error>> {
    let mut classes = [0u32; 5];
    let mut source_uses = 0u32;
    for words in coordinate.program_words.chunks_exact(4) {
        let class = usize::from(words[0] >> 13);
        let count = classes
            .get_mut(class)
            .ok_or("invalid class in checked coordinate")?;
        *count += 1;
        source_uses += 1;
        if words[2] != SOURCE_NONE {
            source_uses += 1;
        }
    }
    Ok(ProgramCensus {
        records: coordinate.term_count,
        source_uses,
        classes,
    })
}

fn freeze_tensor(values: &[E4; 27]) -> [FrozenE4; 27] {
    core::array::from_fn(|index| FrozenE4::from_e4(values[index]))
}

fn thaw_tensor(values: &[FrozenE4; 27]) -> [E4; 27] {
    core::array::from_fn(|index| values[index].to_e4())
}

fn tensor_difference(mut left: [E4; 27], right: [E4; 27]) -> [E4; 27] {
    for (left, right) in left.iter_mut().zip(right) {
        left.sub_assign(&right);
    }
    left
}

const _: () = assert!(size_of::<E4>() == 16);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_geometry_smoke_parser_pins_all_five_dispatch_order() {
        assert_eq!(parse_geometries("all").unwrap(), R0Geometry::ALL);
        assert_eq!(
            parse_geometries("cta96_x0_major,cta96_x1_major,cta96_x2_major").unwrap(),
            vec![
                R0Geometry::Cta96X0Major,
                R0Geometry::Cta96X1Major,
                R0Geometry::Cta96X2Major,
            ],
        );
        assert!(parse_geometries("x2").is_err());
    }

    #[test]
    fn cpu_correctness_parser_accepts_the_complete_all_corpus_request() {
        let args = Args::try_parse_from([
            "run_windowed_r0_corpus",
            "correctness",
            "--all",
            "--logs",
            "3,8",
            "--seeds",
            "0,1,16045690984503098046",
            "--geometries",
            "all",
        ])
        .unwrap();
        let Command::Correctness {
            all,
            coordinate,
            logs,
            seeds,
            geometries,
        } = args.command
        else {
            panic!("expected correctness command");
        };
        assert!(all);
        assert_eq!(coordinate, None);
        assert_eq!(logs, "3,8");
        assert_eq!(seeds, "0,1,16045690984503098046");
        assert_eq!(geometries, "all");
    }

    #[test]
    fn cpu_production_parser_pins_all_geometry_and_single_launch_forms() {
        let all = Args::try_parse_from([
            "run_windowed_r0_corpus",
            "production",
            "--coordinate",
            "add_sub_lui_auipc_mop:0",
            "--all-geometries",
            "--output-dir",
            "/tmp/r0-production",
        ])
        .unwrap();
        assert!(matches!(
            all.command,
            Command::Production {
                all_geometries: true,
                geometry: None,
                once: false,
                expected_checksum: None,
                ..
            }
        ));

        let single = Args::try_parse_from([
            "run_windowed_r0_corpus",
            "production",
            "--coordinate",
            "add_sub_lui_auipc_mop:0",
            "--geometry",
            "cta96_x2_major",
            "--once",
            "--expected-checksum",
            "01abcdef",
            "--output-dir",
            "/tmp/r0-production",
        ])
        .unwrap();
        assert!(matches!(
            single.command,
            Command::Production {
                all_geometries: false,
                geometry: Some(_),
                once: true,
                expected_checksum: Some(_),
                ..
            }
        ));
    }

    #[test]
    fn cpu_prepared_production_bindings_precede_owned_harness_transfer() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == 0
            })
            .unwrap();
        let (prepared, bindings) = prepared_production_input_and_bindings(&coordinate, 3).unwrap();
        assert_eq!(
            bindings.input_sha256,
            prepared.resolved().identity.input_sha256
        );
        assert_eq!(
            bindings.source_data_sha256,
            prepared.resolved().identity.source_data_sha256
        );

        let source = include_str!("run_windowed_r0_corpus.rs");
        let bind = source
            .find("let bindings = production_bindings(coordinate, prepared.resolved())?")
            .unwrap();
        let transfer = source.find("Ok((prepared, bindings))").unwrap();
        assert!(bind < transfer);
        let old_builder = ["build_r0_", "production_input("].concat();
        let old_harness = ["R0Harness::new_", "production("].concat();
        assert!(!source.contains(&old_builder));
        assert!(!source.contains(&old_harness));
    }

    #[test]
    fn cpu_timing_parser_requires_a_named_traversal() {
        let checksum = "ab".repeat(32);
        assert!(Args::try_parse_from([
            "run_windowed_r0_corpus",
            "timing",
            "--coordinate",
            "add_sub_lui_auipc_mop:0",
            "--geometries",
            "cta288_pair,cta96_partitioned,cta96_x0_major,cta96_x1_major,cta96_x2_major",
            "--expected-checksum",
            &checksum,
            "--session-bindings",
            "/tmp/r0-session-bindings.json",
            "--output-dir",
            "/tmp/r0-timing",
        ])
        .is_err());
    }

    #[test]
    fn cpu_timing_parser_pins_ordered_session_and_resume_contract() {
        let checksum = "ab".repeat(32);
        let args = Args::try_parse_from([
            "run_windowed_r0_corpus",
            "timing",
            "--point",
            "natural",
            "--coordinate",
            "add_sub_lui_auipc_mop:0",
            "--geometries",
            "cta96_x1_major,cta96_x2_major,cta288_pair,cta96_partitioned,cta96_x0_major",
            "--traversal",
            "reverse",
            "--warmups",
            "5",
            "--samples",
            "50",
            "--expected-checksum",
            &checksum,
            "--session-bindings",
            "/tmp/r0-session-bindings.json",
            "--output-dir",
            "/tmp/r0-timing",
            "--resume",
        ])
        .unwrap();
        assert!(matches!(
            args.command,
            Command::Timing {
                point,
                geometries,
                warmups: 5,
                samples: 50,
                resume: true,
                ..
            } if point == "natural" && geometries.starts_with("cta96_x1_major")
        ));
    }

    #[test]
    fn cpu_production_plan_parser_is_read_only() {
        let args = Args::try_parse_from(["run_windowed_r0_corpus", "production-plan"]).unwrap();
        assert!(matches!(args.command, Command::ProductionPlan { .. }));
    }

    #[test]
    fn cpu_production_preflight_parser_names_one_exact_coordinate() {
        let args = Args::try_parse_from([
            "run_windowed_r0_corpus",
            "production-preflight",
            "--coordinate",
            "shift_binop:0",
        ])
        .unwrap();
        assert!(matches!(args.command, Command::ProductionPreflight { .. }));
    }
}
