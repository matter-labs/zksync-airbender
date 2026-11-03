use super::factory::{PreparedCircuit, SyntheticInputFactory};
use super::model::{
    all_circuits, candidates, circuit_stable_name, generate_policy, gkr_name, mark_preferred,
    policy_fields, stable_name, write_csv, SweepRow, TimingSummary,
};
use super::probe::{commit_memory, drain, input_footprint, run_case};
use crate::upstream::SecurityLevel;
use clap::Parser;
use era_cudart::device::set_device;
use era_cudart_sys::CudaError;
use gpu_circuit_prover::proof::memory_policy::ProofMemoryPolicy as MemoryPolicy;
use gpu_core::allocator::tracker::AllocationDirection;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use std::collections::BTreeMap;
use std::error::Error;
use std::fs::File;
use std::path::PathBuf;

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
    /// Select circuit=configuration pairs without a Cartesian product.
    #[arg(long = "case", value_parser = parse_case, conflicts_with_all = ["circuit", "configuration", "replay_presets", "list", "generate_policy"])]
    cases: Vec<(String, String)>,
    #[arg(long)]
    fit_only: bool,
    /// Print selectors without creating a CUDA context.
    #[arg(long)]
    list: bool,
    /// Replay production selection; --configuration asserts the expected policy.
    #[arg(long, conflicts_with_all = ["fit_only", "generate_policy", "list"])]
    replay_presets: bool,
}

pub(super) fn main_entry() -> Result<(), Box<dyn Error>> {
    run_arguments(Arguments::parse())
}

fn run_arguments(a: Arguments) -> Result<(), Box<dyn Error>> {
    if a.list {
        for c in all_circuits() {
            println!("circuit {}", circuit_stable_name(c));
        }
        for p in candidates() {
            println!("configuration {}", stable_name(p));
        }
        return Ok(());
    }
    if a.generate_policy {
        if !a.arena_gib.is_empty() || a.output_csv.is_some() {
            return Err("policy generation cannot be combined with a sweep".into());
        }
        let input = a.input_csv.as_ref().ok_or("--input-csv required")?;
        let output = a.output_rust.as_ref().ok_or("--output-rust required")?;
        // Validate into memory before replacing the destination.
        let mut generated = Vec::new();
        generate_policy(File::open(input)?, &mut generated)?;
        std::fs::write(output, generated)?;
        return Ok(());
    }
    if a.arena_gib.is_empty() || (!a.fit_only && a.rounds == 0) {
        return Err("provide --arena-gib and positive --rounds (or --fit-only)".into());
    }
    let output = a.output_csv.as_ref().ok_or("--output-csv required")?;
    for name in a.circuit.iter().chain(a.cases.iter().map(|(c, _)| c)) {
        if !all_circuits()
            .iter()
            .any(|c| circuit_stable_name(*c) == name)
        {
            return Err(format!("unknown circuit {name}").into());
        }
    }
    for name in a.configuration.iter().chain(a.cases.iter().map(|(_, p)| p)) {
        if !candidates().any(|p| stable_name(p) == *name) {
            return Err(format!("unknown configuration {name}").into());
        }
    }
    set_device(a.device_id)?;
    let mut rows = Vec::new();
    for &arena in &a.arena_gib {
        sweep_arena(&a, arena, &mut rows)?;
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
}

fn is_selected(a: &Arguments, circuit: &str) -> bool {
    (a.circuit.is_empty() || a.circuit.iter().any(|c| c == circuit))
        && (a.cases.is_empty() || a.cases.iter().any(|(c, _)| c == circuit))
}

fn policy_selected(a: &Arguments, circuit: &str, policy: MemoryPolicy) -> bool {
    let name = stable_name(policy);
    (a.configuration.is_empty() || a.configuration.contains(&name))
        && (a.cases.is_empty() || a.cases.iter().any(|(c, p)| c == circuit && *p == name))
}

fn prepare_arena(
    a: &Arguments,
    arena_bytes: usize,
    rows: &mut Vec<SweepRow>,
) -> Result<Option<PreparedArena>, Box<dyn Error>> {
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(
            arena_bytes >> ProverContextConfig::default().allocator_block_log_size,
        ),
        inputs_reserve_bytes: crate::memory_policy::INPUTS_RESERVE_BYTES,
        ..Default::default()
    })?;
    if a.replay_presets {
        // Use the same arena admission as the production worker.
        crate::memory_policy::select_arena_bytes(context.get_mem_size());
    }
    assert_empty(&context);
    let factory = SyntheticInputFactory::new(SecurityLevel::Sec100);
    let mut prepared = Vec::new();
    for circuit in all_circuits() {
        eprintln!(
            "prepare {} arena={arena_bytes}",
            circuit_stable_name(circuit)
        );
        let inputs = factory.prepare(circuit)?;
        if classify(|| {
            let result = inputs.precomputations.setup_host.get_or_init(&context);
            drain(&context)?;
            result
        })?
        .is_none()
        {
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
        prepared.push(inputs);
    }
    let mut input_bytes = Vec::new();
    for circuit in &mut prepared {
        let caps = match classify(|| commit_memory(&context, circuit))? {
            Some(caps) => caps,
            None => {
                assert_empty(&context);
                record_arena_failure(
                    a,
                    arena_bytes,
                    &format!("memory_commit:{}", circuit_stable_name(circuit.circuit)),
                    rows,
                );
                return Ok(None);
            }
        };
        circuit.set_memory_caps(caps);
        assert_empty(&context);
        let actual = input_footprint(a.device_id, &context, circuit)?;
        input_bytes.push(actual);
        assert_empty(&context);
    }
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
    Ok(Some(PreparedArena {
        context,
        prepared,
        input_bytes,
        follower_index,
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
    }) = prepare_arena(a, arena_bytes, rows)?
    else {
        if a.replay_presets {
            return Err("replay arena preparation does not fit".into());
        }
        return Ok(());
    };
    let mut cases = Vec::new();
    for (i, circuit) in prepared
        .iter()
        .enumerate()
        .filter(|(_, p)| is_selected(a, circuit_stable_name(p.circuit)))
    {
        if a.replay_presets {
            let policy = crate::memory_policy::policy(circuit.circuit, context.get_mem_size());
            let name = stable_name(policy);
            if !a.configuration.is_empty() && !a.configuration.contains(&name) {
                return Err(
                    format!("production selected {name}; not among --configuration").into(),
                );
            }
            cases.push((i, policy));
        } else {
            cases.extend(
                candidates()
                    .filter(|p| policy_selected(a, circuit_stable_name(circuit.circuit), *p))
                    .map(|policy| (i, policy)),
            );
        }
    }
    let mut fingerprints = BTreeMap::new();
    let mut fitting = Vec::new();
    let start = rows.len();
    for (i, policy) in cases {
        let mut row = new_row(
            arena_bytes,
            circuit_stable_name(prepared[i].circuit),
            policy,
            input_bytes[i],
        );
        // One run per direction; both also warm this exact policy, so their
        // timings are retained separately in logs and excluded from the median.
        for (iteration, direction) in [
            AllocationDirection::Ascending,
            AllocationDirection::Descending,
        ]
        .into_iter()
        .enumerate()
        {
            assert_empty(&context);
            context.reset_used_mem_peak();
            let target = &prepared[i];
            let follower = &prepared[follower_index];
            match classify(|| {
                run_case(
                    a.device_id,
                    &mut context,
                    target,
                    (!a.replay_presets).then_some(policy),
                    follower,
                    direction,
                )
            })? {
                None => {
                    if a.replay_presets {
                        return Err(format!("replay policy does not fit ({direction:?})").into());
                    }
                    row.fits = false;
                    row.failure_stage = Some("target_with_largest_follower".into());
                    break;
                }
                Some((sample, selected)) => {
                    if selected != policy {
                        return Err("production selection changed between proofs".into());
                    }
                    let expected = fingerprints.entry(i).or_insert(sample.fingerprint);
                    if *expected != sample.fingerprint {
                        return Err(
                            format!("proof differs between policies for {}", row.circuit).into(),
                        );
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
            fitting.push((rows.len(), i, policy));
        }
        rows.push(row);
        write_csv(File::create(a.output_csv.as_ref().unwrap())?, rows)?;
    }
    // Rounds-outer order spreads drift across configurations. Fit/warm
    // timings above are excluded; retain every measured sample in the CSV.
    let mut all_samples = vec![Vec::with_capacity(a.rounds); fitting.len()];
    if !a.fit_only {
        for round in 0..a.rounds {
            for (slot, &(row_index, i, policy)) in fitting.iter().enumerate() {
                assert_empty(&context);
                context.reset_used_mem_peak();
                let target = &prepared[i];
                let follower = &prepared[follower_index];
                let (sample, selected) = match classify(|| {
                    run_case(
                        a.device_id,
                        &mut context,
                        target,
                        (!a.replay_presets).then_some(policy),
                        follower,
                        AllocationDirection::Ascending,
                    )
                })? {
                    Some(sample) => sample,
                    None => return Err("policy stopped fitting in a timed round".into()),
                };
                assert_empty(&context);
                let row = &mut rows[row_index];
                if selected != policy || row.proof_fingerprint != Some(sample.fingerprint) {
                    return Err(format!(
                        "selection or proof changed during timing for {}",
                        row.circuit
                    )
                    .into());
                }
                all_samples[slot].push(sample.elapsed_ms);
                let summary = TimingSummary::from_samples(&all_samples[slot])
                    .ok_or("invalid elapsed proof time")?;
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
    if !a.replay_presets {
        mark_preferred(&mut rows[start..])?;
    }
    Ok(())
}

fn new_row(
    arena_bytes: usize,
    circuit_name: &str,
    policy: MemoryPolicy,
    input_bytes: usize,
) -> SweepRow {
    let (setup, memory, witness_commitment, witness_post_commitment, witness_opening) =
        policy_fields(policy);
    SweepRow {
        arena_bytes,
        circuit: circuit_name.into(),
        configuration: stable_name(policy),
        gkr: gkr_name(policy),
        setup,
        memory,
        witness_commitment,
        witness_post_commitment,
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
    }
}

fn record_arena_failure(a: &Arguments, arena_bytes: usize, stage: &str, rows: &mut Vec<SweepRow>) {
    eprintln!("arena {arena_bytes} rejected: {stage} does not fit; all circuits are required");
    for circuit in all_circuits()
        .into_iter()
        .filter(|c| is_selected(a, circuit_stable_name(*c)))
    {
        for policy in candidates().filter(|p| policy_selected(a, circuit_stable_name(circuit), *p))
        {
            let mut row = new_row(arena_bytes, circuit_stable_name(circuit), policy, 0);
            row.failure_stage = Some(stage.into());
            rows.push(row);
        }
    }
}

fn classify<T>(
    operation: impl FnOnce() -> Result<T, CudaError>,
) -> Result<Option<T>, Box<dyn Error>> {
    let prior = era_cudart::error::get_last_error();
    if prior != CudaError::Success {
        return Err(prior.into());
    }
    match operation() {
        Ok(value) => Ok(Some(value)),
        Err(CudaError::ErrorMemoryAllocation)
            if era_cudart::error::get_last_error() == CudaError::Success =>
        {
            Ok(None)
        }
        Err(error) => Err(error.into()),
    }
}

fn assert_empty(context: &ProverContext) {
    // Usage counts live large and small allocations, excluding the reserved pool backing.
    assert_eq!(
        context.get_used_mem_current(),
        0,
        "allocator leaked between sweep cases"
    );
}

fn parse_case(value: &str) -> Result<(String, String), String> {
    let (circuit, configuration) = value
        .split_once('=')
        .ok_or("case must be circuit=configuration")?;
    if circuit.is_empty() || configuration.is_empty() {
        return Err("case must contain both circuit and configuration".to_owned());
    }
    Ok((circuit.to_owned(), configuration.to_owned()))
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
    let block_bytes = 1usize << ProverContextConfig::default().allocator_block_log_size;
    if bytes == 0 || !bytes.is_multiple_of(block_bytes) {
        return Err(format!(
            "arena must be a positive multiple of {block_bytes} bytes"
        ));
    }
    Ok(bytes)
}
