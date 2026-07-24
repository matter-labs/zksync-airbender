use super::factory::SyntheticRequestFactory;
use super::model::{
    circuit_stable_name, generate_policy, mark_preferred, stable_cases, write_csv, SweepRow,
    TimingSummary,
};
use super::probe::{run_sweep_case, warm_setup_cache};
use crate::circuit_type::CircuitType;
use crate::prover::context::{ProverContext, ProverContextConfig};
use crate::prover::gpu_memory::{GpuMemoryPreset, PRODUCTION_SMALL_POOL_BYTES};
use crate::prover::memory_policy::MemoryPolicy;
use clap::Parser;
use era_cudart::device::set_device;
use era_cudart_sys::CudaError;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::path::PathBuf;
use verifier_common::security_80::Security80Marker;

const MIB_BYTES: usize = 1 << 20;
const GIB_BYTES: u128 = 1 << 30;

#[derive(Debug, Parser)]
struct Arguments {
    #[arg(long, value_parser = parse_arena_gib)]
    arena_gib: Vec<usize>,
    #[arg(long, default_value_t = 5)]
    rounds: usize,
    #[arg(long)]
    output_csv: Option<PathBuf>,
    #[arg(long, default_value_t = 0)]
    device_id: i32,
    #[arg(long)]
    generate_policy: bool,
    #[arg(long)]
    input_csv: Option<PathBuf>,
    #[arg(long)]
    output_rust: Option<PathBuf>,
}

#[derive(Debug)]
struct SweepError(String);

impl Display for SweepError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for SweepError {}

enum FitOutcome<T> {
    Fits(T),
    DoesNotFit,
}

struct FittingCase {
    row: usize,
    prepared: usize,
    policy: MemoryPolicy,
}

pub(super) fn main_entry() -> Result<(), Box<dyn Error>> {
    let arguments = Arguments::parse();
    if arguments.generate_policy {
        ensure_no_sweep_arguments(&arguments)?;
        let input = arguments
            .input_csv
            .as_ref()
            .ok_or_else(|| SweepError("--generate-policy requires --input-csv".to_owned()))?;
        let output = arguments
            .output_rust
            .as_ref()
            .ok_or_else(|| SweepError("--generate-policy requires --output-rust".to_owned()))?;
        generate_policy(File::open(input)?, File::create(output)?)?;
        return Ok(());
    }
    if arguments.rounds == 0 {
        return Err(SweepError("--rounds must be greater than zero".to_owned()).into());
    }
    if arguments.arena_gib.is_empty() {
        return Err(SweepError("a sweep requires at least one --arena-gib".to_owned()).into());
    }
    let output = arguments
        .output_csv
        .as_ref()
        .ok_or_else(|| SweepError("a sweep requires --output-csv".to_owned()))?;
    run_sweep(
        arguments.device_id,
        &arguments.arena_gib,
        arguments.rounds,
        output,
    )
}

fn ensure_no_sweep_arguments(arguments: &Arguments) -> Result<(), SweepError> {
    if !arguments.arena_gib.is_empty() || arguments.output_csv.is_some() {
        return Err(SweepError(
            "policy generation cannot be combined with a sweep".to_owned(),
        ));
    }
    Ok(())
}

fn run_sweep(
    device_id: i32,
    arenas: &[usize],
    rounds: usize,
    output: &PathBuf,
) -> Result<(), Box<dyn Error>> {
    set_device(device_id).map_err(cuda_error)?;
    let mut rows = Vec::new();
    for &arena_bytes in arenas {
        match sweep_arena(arena_bytes, rounds, &mut rows)? {
            true => {}
            false => eprintln!(
                "arena {arena_bytes} bytes is below the sweep floor; no rows were recorded"
            ),
        }
    }
    write_csv(File::create(output)?, &rows)?;
    Ok(())
}

fn sweep_arena(
    arena_bytes: usize,
    rounds: usize,
    rows: &mut Vec<SweepRow>,
) -> Result<bool, Box<dyn Error>> {
    let mut context = ProverContext::new(&ProverContextConfig {
        max_device_allocation_blocks_count: Some(arena_bytes / MIB_BYTES),
        gpu_memory_preset: GpuMemoryPreset::Low,
        ..Default::default()
    })
    .map_err(cuda_error)?;
    assert_empty(&context);

    let factory = SyntheticRequestFactory::new();
    let mut prepared = Vec::new();
    let mut sequence_id = 0usize;
    for circuit in CircuitType::get_all() {
        let precomputations = factory.precomputations(circuit);
        let request = factory.request(circuit, sequence_id, precomputations.clone())?;
        sequence_id += 1;
        if matches!(
            classify(|| warm_setup_cache(&mut context, request))?,
            FitOutcome::DoesNotFit
        ) {
            assert_empty(&context);
            return Ok(false);
        }
        assert_empty(&context);
        prepared.push(factory.prepare(circuit, precomputations)?);
    }

    let follower_index = prepared
        .iter()
        .enumerate()
        .max_by(|(_, left), (_, right)| {
            left.input_bytes.cmp(&right.input_bytes).then_with(|| {
                circuit_stable_name(right.circuit).cmp(circuit_stable_name(left.circuit))
            })
        })
        .map(|(index, _)| index)
        .expect("supported circuit list is non-empty");

    let warm_target = prepared[follower_index].request(sequence_id);
    sequence_id += 1;
    let warm_follower = prepared[follower_index].request(sequence_id);
    sequence_id += 1;
    if matches!(
        classify(|| run_sweep_case::<Security80Marker>(
            &mut context,
            warm_target,
            MemoryPolicy::all_recompute(),
            warm_follower,
        ))?,
        FitOutcome::DoesNotFit
    ) {
        assert_empty(&context);
        return Ok(false);
    }
    assert_empty(&context);

    let start = rows.len();
    let cases = stable_cases(
        prepared.iter().map(|item| item.circuit),
        MemoryPolicy::fixed_tree_configurations(),
    );
    let mut fitting = Vec::new();
    for case in cases {
        let prepared_index = prepared
            .iter()
            .position(|item| item.circuit == case.circuit)
            .expect("stable case references a prepared circuit");
        assert_empty(&context);
        reset_peaks(&context);
        let target = prepared[prepared_index].request(sequence_id);
        sequence_id += 1;
        let follower = prepared[follower_index].request(sequence_id);
        sequence_id += 1;
        let outcome = classify(|| {
            run_sweep_case::<Security80Marker>(&mut context, target, case.policy, follower)
        })?;
        assert_empty(&context);
        let fits = matches!(outcome, FitOutcome::Fits(_));
        let row = SweepRow {
            arena_bytes,
            circuit: circuit_stable_name(case.circuit).to_owned(),
            configuration: case.policy.stable_name(),
            setup: case.policy.setup,
            witness: case.policy.witness,
            memory: case.policy.memory,
            stage_two: case.policy.stage_two,
            fits,
            input_bytes: prepared[prepared_index].input_bytes,
            peak_bytes: fits.then(|| context.get_device_allocator().get_used_mem_peak()),
            timing_samples: 0,
            median_ms: None,
            min_ms: None,
            max_ms: None,
            preferred: false,
        };
        let row_index = rows.len();
        rows.push(row);
        if fits {
            fitting.push(FittingCase {
                row: row_index,
                prepared: prepared_index,
                policy: case.policy,
            });
        }
    }

    let mut samples = vec![Vec::with_capacity(rounds); fitting.len()];
    for _ in 0..rounds {
        for (case_index, case) in fitting.iter().enumerate() {
            assert_empty(&context);
            reset_peaks(&context);
            let target = prepared[case.prepared].request(sequence_id);
            sequence_id += 1;
            let follower = prepared[follower_index].request(sequence_id);
            sequence_id += 1;
            match classify(|| {
                run_sweep_case::<Security80Marker>(&mut context, target, case.policy, follower)
            })? {
                FitOutcome::Fits(elapsed_ms) => samples[case_index].push(elapsed_ms),
                FitOutcome::DoesNotFit => {
                    return Err(SweepError(format!(
                        "{} stopped fitting during timed rounds",
                        rows[case.row].configuration
                    ))
                    .into());
                }
            }
            assert_empty(&context);
        }
    }

    for (case, samples) in fitting.iter().zip(samples) {
        let summary = TimingSummary::from_samples(&samples)
            .expect("successful proof timings are finite and non-empty");
        let row = &mut rows[case.row];
        row.timing_samples = summary.samples;
        row.median_ms = Some(summary.median_ms);
        row.min_ms = Some(summary.min_ms);
        row.max_ms = Some(summary.max_ms);
    }
    mark_preferred(&mut rows[start..])?;
    Ok(true)
}

fn classify<T>(
    operation: impl FnOnce() -> Result<T, CudaError>,
) -> Result<FitOutcome<T>, SweepError> {
    let _ = era_cudart::error::get_last_error();
    match operation() {
        Ok(elapsed_ms) => Ok(FitOutcome::Fits(elapsed_ms)),
        Err(CudaError::ErrorMemoryAllocation)
            if era_cudart::error::get_last_error() == CudaError::Success =>
        {
            Ok(FitOutcome::DoesNotFit)
        }
        Err(error) => Err(cuda_error(error)),
    }
}

fn assert_empty(context: &ProverContext) {
    let allocator = context.get_device_allocator();
    assert_eq!(
        allocator.get_used_mem_current(),
        PRODUCTION_SMALL_POOL_BYTES,
        "root allocator leaked between sweep cases"
    );
    assert_eq!(
        allocator
            .small_allocator()
            .expect("small allocator is configured")
            .get_used_mem_current(),
        0,
        "small allocator leaked between sweep cases"
    );
}

fn reset_peaks(context: &ProverContext) {
    context.get_device_allocator().reset_used_mem_peak();
}

fn parse_arena_gib(value: &str) -> Result<usize, String> {
    let (whole, fraction) = value.split_once('.').unwrap_or((value, ""));
    if whole.is_empty()
        || !whole.bytes().all(|byte| byte.is_ascii_digit())
        || !fraction.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err("arena GiB must be an unsigned decimal".to_owned());
    }
    let denominator = 10u128
        .checked_pow(fraction.len().try_into().map_err(|_| "too many digits")?)
        .ok_or("too many digits")?;
    let numerator = whole
        .parse::<u128>()
        .map_err(|_| "arena GiB is too large")?
        .checked_mul(denominator)
        .and_then(|scaled| fraction.parse::<u128>().unwrap_or(0).checked_add(scaled))
        .and_then(|scaled| scaled.checked_mul(GIB_BYTES))
        .ok_or("arena GiB is too large")?;
    if !numerator.is_multiple_of(denominator) {
        return Err("arena GiB does not produce an exact byte count".to_owned());
    }
    let bytes: usize = (numerator / denominator)
        .try_into()
        .map_err(|_| "arena GiB is too large")?;
    if bytes == 0 || !bytes.is_multiple_of(MIB_BYTES) {
        return Err(format!(
            "arena must be a positive multiple of {MIB_BYTES} bytes"
        ));
    }
    Ok(bytes)
}

fn cuda_error(error: CudaError) -> SweepError {
    SweepError(format!("CUDA error: {error:?}"))
}
