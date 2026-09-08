// Offline budget sweep ported from dev's gpu_prover harness.
use super::factory::{PreparedCircuit, SyntheticRequestFactory};
use super::model::{
    all_circuits, circuit_stable_name, generate_policy, mark_preferred, policy_fields,
    stable_cases, stable_name, write_csv, SweepRow, TimingSummary,
};
use super::probe::{commit_memory, drain, input_footprint, run_replay_case, run_sweep_case};
use crate::memory_policy::{validate_device_budget, PolicyGeometry};
use crate::upstream::SecurityLevel;
use clap::Parser;
use era_cudart::device::set_device;
use era_cudart_sys::CudaError;
use gpu_circuit_prover::proof::memory_policy::ProofMemoryPolicy as MemoryPolicy;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::path::PathBuf;

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
    /// Restrict a bounded invocation. Merge diagnostic CSVs before generation.
    #[arg(long)]
    circuit: Vec<String>,
    #[arg(long)]
    configuration: Vec<String>,
    #[arg(long)]
    fit_only: bool,
    /// Print selectors without creating a CUDA context.
    #[arg(long)]
    list: bool,
    /// Validate installed presets: every selected circuit is proved with the
    /// policy production selection picks (no overrides) after the worker's
    /// exact-budget admission check. `--configuration` then only asserts
    /// which policies production may select.
    #[arg(long)]
    replay_presets: bool,
}

fn validate_mode(a: &Arguments) -> Result<(), SweepError> {
    if a.replay_presets && (a.fit_only || a.generate_policy || a.list) {
        return Err(SweepError(
            "--replay-presets measures production selection only; it cannot be combined with --fit-only, --generate-policy or --list".into(),
        ));
    }
    if a.replay_presets && a.rounds == 0 {
        return Err(SweepError(
            "--replay-presets requires positive --rounds".into(),
        ));
    }
    Ok(())
}

#[derive(Debug)]
struct SweepError(String);
impl Display for SweepError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl Error for SweepError {}

enum FitOutcome<T> {
    Fits(T),
    DoesNotFit,
}

pub(super) fn main_entry() -> Result<(), Box<dyn Error>> {
    run_arguments(Arguments::parse())
}

fn run_arguments(a: Arguments) -> Result<(), Box<dyn Error>> {
    validate_mode(&a)?;
    if a.list {
        for c in all_circuits() {
            println!("circuit {}", circuit_stable_name(c));
        }
        for p in MemoryPolicy::candidates() {
            println!("configuration {}", stable_name(p));
        }
        return Ok(());
    }
    if a.generate_policy {
        if !a.arena_gib.is_empty() || a.output_csv.is_some() {
            return Err(
                SweepError("policy generation cannot be combined with a sweep".into()).into(),
            );
        }
        let input = a
            .input_csv
            .as_ref()
            .ok_or_else(|| SweepError("--input-csv required".into()))?;
        let output = a
            .output_rust
            .as_ref()
            .ok_or_else(|| SweepError("--output-rust required".into()))?;
        // Validate into memory before replacing the destination.
        let mut generated = Vec::new();
        generate_policy(File::open(input)?, &mut generated)?;
        std::fs::write(output, generated)?;
        return Ok(());
    }
    if a.arena_gib.is_empty() || (!a.fit_only && a.rounds == 0) {
        return Err(
            SweepError("provide --arena-gib and positive --rounds (or --fit-only)".into()).into(),
        );
    }
    let output = a
        .output_csv
        .as_ref()
        .ok_or_else(|| SweepError("--output-csv required".into()))?;
    for name in &a.circuit {
        if !all_circuits()
            .iter()
            .any(|c| circuit_stable_name(*c) == name)
        {
            return Err(SweepError(format!("unknown circuit {name}")).into());
        }
    }
    for name in &a.configuration {
        if !MemoryPolicy::candidates().any(|p| stable_name(p) == *name) {
            return Err(SweepError(format!("unknown configuration {name}")).into());
        }
    }
    set_device(a.device_id).map_err(cuda_error)?;
    let mut rows = Vec::new();
    for &arena in &a.arena_gib {
        if a.replay_presets {
            replay_arena(&a, arena, &mut rows)?;
        } else {
            sweep_arena(&a, arena, &mut rows)?;
        }
        write_csv(File::create(output)?, &rows)?;
    }
    Ok(())
}

/// Context, warmed setups, prepared inputs, largest follower and memory caps
/// for one arena. `None` when the arena was rejected (rows already record it).
struct PreparedArena {
    context: ProverContext,
    prepared: Vec<PreparedCircuit>,
    input_bytes: Vec<usize>,
    follower_index: usize,
    sequence: usize,
}

fn is_selected(a: &Arguments, prepared: &PreparedCircuit) -> bool {
    a.circuit.is_empty()
        || a.circuit
            .iter()
            .any(|c| *c == circuit_stable_name(prepared.circuit))
}

fn prepare_arena(
    a: &Arguments,
    arena_bytes: usize,
    rows: &mut Vec<SweepRow>,
) -> Result<Option<PreparedArena>, Box<dyn Error>> {
    let context =
        ProverContext::new_with_exact_device_budget(&ProverContextConfig::default(), arena_bytes)
            .map_err(cuda_error)?;
    if a.replay_presets {
        // The production worker's admission: rejects an unmeasured device or
        // allocator profile and an arena below the all-circuits minimum.
        validate_device_budget(&context).map_err(cuda_error)?;
    }
    assert_empty(&context);
    let factory = SyntheticRequestFactory::new(SecurityLevel::Sec100);
    let mut prepared = Vec::new();
    for circuit in all_circuits() {
        eprintln!(
            "prepare {} arena={arena_bytes}",
            circuit_stable_name(circuit)
        );
        let precomputations = factory.precomputations(circuit);
        if matches!(
            classify(|| {
                let result = precomputations.setup_host.get_or_init(&context);
                drain(&context)?;
                result
            })?,
            FitOutcome::DoesNotFit
        ) {
            assert_empty(&context);
            record_arena_failure(
                a,
                arena_bytes,
                &format!("setup_init:{}", circuit_stable_name(circuit)),
                rows,
            );
            return Ok(None);
        }
        assert_empty(&context);
        prepared.push(factory.prepare(circuit, precomputations)?);
    }
    let input_bytes = prepared
        .iter()
        .map(|p| p.input_bytes())
        .collect::<Result<Vec<_>, _>>()?;
    let follower_index = (0..prepared.len())
        .max_by(|&l, &r| {
            input_bytes[l].cmp(&input_bytes[r]).then_with(|| {
                circuit_stable_name(prepared[r].circuit)
                    .cmp(circuit_stable_name(prepared[l].circuit))
            })
        })
        .expect("supported circuit set is nonempty");
    eprintln!(
        "largest follower {} input_bytes={}",
        circuit_stable_name(prepared[follower_index].circuit),
        input_bytes[follower_index]
    );
    let needed: Vec<_> = (0..prepared.len())
        .filter(|&i| is_selected(a, &prepared[i]) || i == follower_index)
        .collect();
    let mut sequence = 0;
    for i in needed {
        let caps = match classify(|| {
            commit_memory(
                a.device_id,
                &context,
                prepared[i].memory_commitment_request(sequence),
            )
        })? {
            FitOutcome::Fits(caps) => caps,
            FitOutcome::DoesNotFit => {
                assert_empty(&context);
                record_arena_failure(
                    a,
                    arena_bytes,
                    &format!("memory_commit:{}", circuit_stable_name(prepared[i].circuit)),
                    rows,
                );
                return Ok(None);
            }
        };
        sequence += 1;
        prepared[i].set_memory_caps(caps);
        assert_empty(&context);
        let actual = input_footprint(a.device_id, &context, prepared[i].proof_request(sequence)?)
            .map_err(cuda_error)?;
        sequence += 1;
        assert_eq!(
            actual, input_bytes[i],
            "synthetic input accounting must match production transfers for {:?}",
            prepared[i].circuit
        );
        assert_empty(&context);
    }
    Ok(Some(PreparedArena {
        context,
        prepared,
        input_bytes,
        follower_index,
        sequence,
    }))
}

fn sweep_arena(
    a: &Arguments,
    arena_bytes: usize,
    rows: &mut Vec<SweepRow>,
) -> Result<(), Box<dyn Error>> {
    let Some(PreparedArena {
        mut context,
        prepared,
        input_bytes,
        follower_index,
        mut sequence,
    }) = prepare_arena(a, arena_bytes, rows)?
    else {
        return Ok(());
    };
    let policies: Vec<_> = MemoryPolicy::candidates()
        .filter(|p| a.configuration.is_empty() || a.configuration.contains(&stable_name(*p)))
        .collect();
    let cases = stable_cases(
        prepared
            .iter()
            .filter(|p| is_selected(a, p))
            .map(|p| p.circuit),
        policies,
    );
    let mut fingerprints = BTreeMap::new();
    let mut fitting = Vec::new();
    let start = rows.len();
    for case in cases {
        let i = prepared
            .iter()
            .position(|p| p.circuit == case.circuit)
            .unwrap();
        let geometry = PolicyGeometry::new(
            case.circuit,
            SecurityLevel::Sec100,
            &prepared[i].precomputations,
            &context,
        );
        let (setup, memory, witness_commitment, witness_opening) = policy_fields(case.policy);
        let mut row = SweepRow {
            arena_bytes,
            circuit: circuit_stable_name(case.circuit).into(),
            configuration: stable_name(case.policy),
            geometry: serde_json::to_string(&geometry)?,
            setup,
            memory,
            witness_commitment,
            witness_opening,
            failure_stage: None,
            raw_samples_ms: "[]".into(),
            proof_fingerprint: None,
            fits: false,
            input_bytes: input_bytes[i],
            peak_bytes: None,
            timing_samples: 0,
            median_ms: None,
            min_ms: None,
            max_ms: None,
            preferred: false,
        };
        // First two successful runs warm this exact policy; their timings are
        // retained separately in logs and excluded from the measured median.
        let runs = if a.fit_only { 1 } else { 2 };
        for iteration in 0..runs {
            assert_empty(&context);
            context.reset_used_mem_peak();
            let target = prepared[i].proof_request(sequence)?;
            let follower = prepared[follower_index].proof_request(sequence + 1)?;
            sequence += 2;
            match classify(|| {
                run_sweep_case(a.device_id, &mut context, target, case.policy, follower)
            })? {
                FitOutcome::DoesNotFit => {
                    if iteration > 0 {
                        return Err(SweepError(
                            "policy stopped fitting after a successful run".into(),
                        )
                        .into());
                    }
                    row.failure_stage = Some("target_with_largest_follower".into());
                    break;
                }
                FitOutcome::Fits(sample) => {
                    let expected = fingerprints.entry(i).or_insert(sample.fingerprint);
                    if *expected != sample.fingerprint {
                        return Err(SweepError(format!(
                            "proof differs between policies for {}",
                            row.circuit
                        ))
                        .into());
                    }
                    row.fits = true;
                    row.proof_fingerprint = Some(sample.fingerprint);
                    let peak = context.get_used_mem_peak();
                    row.peak_bytes = Some(row.peak_bytes.unwrap_or(0).max(peak));
                    eprintln!(
                        "sample {} {} iteration={iteration} ms={} peak={peak}",
                        row.circuit, row.configuration, sample.elapsed_ms
                    );
                }
            }
            assert_empty(&context);
        }
        assert_empty(&context);
        eprintln!(
            "fit {} {} fits={}",
            row.circuit, row.configuration, row.fits
        );
        if row.fits {
            fitting.push((rows.len(), i, case.policy));
        }
        rows.push(row);
        write_csv(File::create(a.output_csv.as_ref().unwrap())?, rows)?;
    }
    // v2's rounds-outer order spreads drift across configurations. Fit/warm
    // timings above are excluded; retain every measured sample in the CSV.
    let mut all_samples = vec![Vec::with_capacity(a.rounds); fitting.len()];
    if !a.fit_only {
        for round in 0..a.rounds {
            for (slot, &(row_index, i, policy)) in fitting.iter().enumerate() {
                assert_empty(&context);
                context.reset_used_mem_peak();
                let target = prepared[i].proof_request(sequence)?;
                let follower = prepared[follower_index].proof_request(sequence + 1)?;
                sequence += 2;
                let sample = match classify(|| {
                    run_sweep_case(a.device_id, &mut context, target, policy, follower)
                })? {
                    FitOutcome::Fits(sample) => sample,
                    FitOutcome::DoesNotFit => {
                        return Err(
                            SweepError("policy stopped fitting in a timed round".into()).into()
                        )
                    }
                };
                assert_empty(&context);
                let row = &mut rows[row_index];
                if row.proof_fingerprint != Some(sample.fingerprint) {
                    return Err(SweepError(format!(
                        "proof changed during timing for {}",
                        row.circuit
                    ))
                    .into());
                }
                all_samples[slot].push(sample.elapsed_ms);
                let summary = TimingSummary::from_samples(&all_samples[slot])
                    .ok_or_else(|| SweepError("invalid elapsed proof time".into()))?;
                row.raw_samples_ms = serde_json::to_string(&all_samples[slot])?;
                row.timing_samples = summary.samples;
                row.median_ms = Some(summary.median_ms);
                row.min_ms = Some(summary.min_ms);
                row.max_ms = Some(summary.max_ms);
                row.peak_bytes = Some(row.peak_bytes.unwrap().max(context.get_used_mem_peak()));
                eprintln!(
                    "timed {} {} round={round} ms={}",
                    row.circuit, row.configuration, sample.elapsed_ms
                );
            }
            write_csv(File::create(a.output_csv.as_ref().unwrap())?, rows)?;
        }
    }
    mark_preferred(&mut rows[start..])?;
    Ok(())
}

fn new_row(
    arena_bytes: usize,
    circuit_name: &str,
    configuration: String,
    policy: MemoryPolicy,
    geometry: &PolicyGeometry,
    input_bytes: usize,
) -> Result<SweepRow, Box<dyn Error>> {
    let (setup, memory, witness_commitment, witness_opening) = policy_fields(policy);
    Ok(SweepRow {
        arena_bytes,
        circuit: circuit_name.into(),
        configuration,
        geometry: serde_json::to_string(geometry)?,
        setup,
        memory,
        witness_commitment,
        witness_opening,
        failure_stage: None,
        raw_samples_ms: "[]".into(),
        proof_fingerprint: None,
        fits: false,
        input_bytes,
        peak_bytes: None,
        timing_samples: 0,
        median_ms: None,
        min_ms: None,
        max_ms: None,
        preferred: false,
    })
}

/// Prove every selected circuit with the policy production selection picks for
/// this arena, through the production phase-one/phase-two worker paths, and
/// record one row per circuit with the same fingerprint and timing evidence as
/// a sweep row. Rows are never marked preferred: replay validates presets, it
/// does not choose them.
fn replay_arena(
    a: &Arguments,
    arena_bytes: usize,
    rows: &mut Vec<SweepRow>,
) -> Result<(), Box<dyn Error>> {
    let Some(PreparedArena {
        mut context,
        prepared,
        input_bytes,
        follower_index,
        mut sequence,
    }) = prepare_arena(a, arena_bytes, rows)?
    else {
        write_csv(File::create(a.output_csv.as_ref().unwrap())?, rows)?;
        return Err(SweepError(format!(
            "replay: setup initialization or memory commitment does not fit at {arena_bytes} bytes"
        ))
        .into());
    };
    struct Replay {
        row: usize,
        i: usize,
        policy: MemoryPolicy,
    }
    let mut replays = Vec::new();
    let mut failures = Vec::new();
    for i in (0..prepared.len()).filter(|&i| is_selected(a, &prepared[i])) {
        let circuit_name = circuit_stable_name(prepared[i].circuit);
        let geometry = PolicyGeometry::new(
            prepared[i].circuit,
            SecurityLevel::Sec100,
            &prepared[i].precomputations,
            &context,
        );
        let mut row: Option<SweepRow> = None;
        let mut selected: Option<MemoryPolicy> = None;
        // Two warm proofs with the production-selected policy; the first also
        // fixes which policy that is.
        for _ in 0..2 {
            assert_empty(&context);
            context.reset_used_mem_peak();
            let target = prepared[i].proof_request(sequence)?;
            let follower = prepared[follower_index].proof_request(sequence + 1)?;
            sequence += 2;
            match classify(|| run_replay_case(a.device_id, &mut context, target, follower))? {
                FitOutcome::DoesNotFit => {
                    let mut failed = new_row(
                        arena_bytes,
                        circuit_name,
                        "production_selection".into(),
                        MemoryPolicy::default(),
                        &geometry,
                        input_bytes[i],
                    )?;
                    failed.failure_stage = Some("replay_target_with_largest_follower".into());
                    failures.push(circuit_name.to_owned());
                    row = Some(failed);
                    break;
                }
                FitOutcome::Fits((sample, policy)) => {
                    let name = stable_name(policy);
                    if !a.configuration.is_empty() && !a.configuration.contains(&name) {
                        return Err(SweepError(format!(
                            "production selected {name} for {circuit_name}; not among --configuration"
                        ))
                        .into());
                    }
                    if *selected.get_or_insert(policy) != policy {
                        return Err(SweepError(format!(
                            "production selection changed between proofs for {circuit_name}"
                        ))
                        .into());
                    }
                    let current = match row.as_mut() {
                        Some(current) => current,
                        None => row.insert(new_row(
                            arena_bytes,
                            circuit_name,
                            name,
                            policy,
                            &geometry,
                            input_bytes[i],
                        )?),
                    };
                    if current
                        .proof_fingerprint
                        .is_some_and(|f| f != sample.fingerprint)
                    {
                        return Err(SweepError(format!(
                            "proof changed between proofs for {circuit_name}"
                        ))
                        .into());
                    }
                    current.fits = true;
                    current.proof_fingerprint = Some(sample.fingerprint);
                    let peak = context.get_used_mem_peak();
                    current.peak_bytes = Some(current.peak_bytes.unwrap_or(0).max(peak));
                    eprintln!(
                        "replay {circuit_name} {} ms={} peak={peak}",
                        current.configuration, sample.elapsed_ms
                    );
                }
            }
            assert_empty(&context);
        }
        let row = row.expect("replay produces one row per circuit");
        if row.fits {
            replays.push(Replay {
                row: rows.len(),
                i,
                policy: selected.unwrap(),
            });
        }
        rows.push(row);
        write_csv(File::create(a.output_csv.as_ref().unwrap())?, rows)?;
    }
    let mut all_samples = vec![Vec::with_capacity(a.rounds); replays.len()];
    for round in 0..a.rounds {
        for (slot, replay) in replays.iter().enumerate() {
            assert_empty(&context);
            context.reset_used_mem_peak();
            let target = prepared[replay.i].proof_request(sequence)?;
            let follower = prepared[follower_index].proof_request(sequence + 1)?;
            sequence += 2;
            let (sample, policy) =
                match classify(|| run_replay_case(a.device_id, &mut context, target, follower))? {
                    FitOutcome::Fits(result) => result,
                    FitOutcome::DoesNotFit => {
                        return Err(SweepError(
                            "production selection stopped fitting in a timed round".into(),
                        )
                        .into())
                    }
                };
            assert_empty(&context);
            let row = &mut rows[replay.row];
            if policy != replay.policy || row.proof_fingerprint != Some(sample.fingerprint) {
                return Err(SweepError(format!(
                    "selection or proof changed during timing for {}",
                    row.circuit
                ))
                .into());
            }
            all_samples[slot].push(sample.elapsed_ms);
            let summary = TimingSummary::from_samples(&all_samples[slot])
                .ok_or_else(|| SweepError("invalid elapsed proof time".into()))?;
            row.raw_samples_ms = serde_json::to_string(&all_samples[slot])?;
            row.timing_samples = summary.samples;
            row.median_ms = Some(summary.median_ms);
            row.min_ms = Some(summary.min_ms);
            row.max_ms = Some(summary.max_ms);
            row.peak_bytes = Some(row.peak_bytes.unwrap().max(context.get_used_mem_peak()));
            eprintln!(
                "replay timed {} {} round={round} ms={}",
                row.circuit, row.configuration, sample.elapsed_ms
            );
        }
        write_csv(File::create(a.output_csv.as_ref().unwrap())?, rows)?;
    }
    if !failures.is_empty() {
        return Err(SweepError(format!(
            "replay: production selection does not fit at {arena_bytes} bytes for {failures:?}"
        ))
        .into());
    }
    Ok(())
}

fn record_arena_failure(a: &Arguments, arena_bytes: usize, stage: &str, rows: &mut Vec<SweepRow>) {
    eprintln!("arena {arena_bytes} rejected: {stage} does not fit; all circuits are required");
    for circuit in all_circuits().into_iter().filter(|c| {
        a.circuit.is_empty() || a.circuit.iter().any(|name| name == circuit_stable_name(*c))
    }) {
        for policy in MemoryPolicy::candidates()
            .filter(|p| a.configuration.is_empty() || a.configuration.contains(&stable_name(*p)))
        {
            let (setup, memory, witness_commitment, witness_opening) = policy_fields(policy);
            rows.push(SweepRow {
                arena_bytes,
                circuit: circuit_stable_name(circuit).into(),
                configuration: stable_name(policy),
                geometry: "{}".into(),
                setup,
                memory,
                witness_commitment,
                witness_opening,
                failure_stage: Some(stage.into()),
                raw_samples_ms: "[]".into(),
                proof_fingerprint: None,
                fits: false,
                input_bytes: 0,
                peak_bytes: None,
                timing_samples: 0,
                median_ms: None,
                min_ms: None,
                max_ms: None,
                preferred: false,
            });
        }
    }
}

fn classify<T>(
    operation: impl FnOnce() -> Result<T, CudaError>,
) -> Result<FitOutcome<T>, SweepError> {
    let prior = era_cudart::error::get_last_error();
    if prior != CudaError::Success {
        return Err(cuda_error(prior));
    }
    match operation() {
        Ok(value) => Ok(FitOutcome::Fits(value)),
        Err(CudaError::ErrorMemoryAllocation)
            if era_cudart::error::get_last_error() == CudaError::Success =>
        {
            Ok(FitOutcome::DoesNotFit)
        }
        Err(error) => Err(cuda_error(error)),
    }
}

fn assert_empty(context: &ProverContext) {
    // v3 current usage combines large and small allocations, excluding the
    // permanently reserved small-pool backing (unlike v2).
    assert_eq!(
        context.get_used_mem_current(),
        0,
        "allocator leaked between sweep cases"
    );
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

#[cfg(test)]
mod cpu_cli_tests {
    use super::*;

    fn parse(args: &[&str]) -> Arguments {
        Arguments::try_parse_from(std::iter::once("gpu_memory_sweep").chain(args.iter().copied()))
            .expect("arguments parse")
    }

    #[test]
    fn cpu_replay_rejects_list_through_the_entry_path() {
        assert!(run_arguments(parse(&["--replay-presets", "--list"])).is_err());
    }

    #[test]
    fn cpu_replay_mode_flag_compatibility() {
        let base = [
            "--replay-presets",
            "--arena-gib",
            "36",
            "--output-csv",
            "replay.csv",
        ];
        assert!(validate_mode(&parse(&base)).is_ok());
        let with_filter: Vec<&str> = base
            .iter()
            .copied()
            .chain(["--configuration", "x"])
            .collect();
        assert!(validate_mode(&parse(&with_filter)).is_ok());
        let fit_only: Vec<&str> = base.iter().copied().chain(["--fit-only"]).collect();
        assert!(validate_mode(&parse(&fit_only)).is_err());
        assert!(validate_mode(&parse(&["--replay-presets", "--generate-policy"])).is_err());
        let zero_rounds: Vec<&str> = base.iter().copied().chain(["--rounds", "0"]).collect();
        assert!(validate_mode(&parse(&zero_rounds)).is_err());
        assert!(validate_mode(&parse(&[
            "--arena-gib",
            "36",
            "--output-csv",
            "s.csv",
            "--fit-only"
        ]))
        .is_ok());
    }
}
