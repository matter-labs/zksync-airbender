use std::collections::BTreeMap;
use std::fmt::Debug;
use std::sync::Arc;
use std::time::Instant;

use cpu_execution_prover::test_support::{with_l1_wrap_fixture, L1WrapFixture};
use cpu_execution_prover::CpuExecutionProverConfiguration;
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use execution_prover::{CommitmentMode, ProofProfile};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_gkr::proth120::backward::{
    preflight_dr_tail_resources_pr, GKRBackwardStageSnapshotPr, GKRBackwardStageSnapshotSinkPr,
    ResourceCountsPr, ResourceEventPr, ResourceIdPr, ResourceRecordPr,
};
use gpu_gkr::proth120::inputs::Proth120GkrWitnessInputs;
use gpu_gkr::proth120::packed_challenges::{derive, PackedChallengeConfig};
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::proth120::proof_layout::{M6ProofFields, ProofLayoutPr, ProofSlabPr};
use gpu_gkr::proth120::{schedule_gkr, GkrOutputPr};
use gpu_gkr::setup::{L1WrapSetupHost, PackedSetupSource};
use gpu_prover_context::transfer::{single_shot_h2d, Transfer};
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::proth120::{
    generate_fused_values, generate_inits_and_teardowns, generate_lookup_multiplicities,
    prepare_lookup_relations, Proth120WitnessBuffers,
};
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceDevice, UnrolledUnifiedTraceDevice,
    PAGE_SIZE_LOG2,
};
use prover::definitions::{GKRExternalChallenges, SecurityLevel};
use prover::field::Field;
use prover::gkr::prover::SumcheckIntermediateProofValues;
use prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
};
use prover::gkr::prover_config::pow_bits;
use serde::Serialize;

use super::m6_replay::{
    replay_gkr_challenges, ReplayPowBits, ReplayedClaims, ReplayedGkr, M4_CHALLENGE_DRAWS,
};
use super::{
    check_file, checkpoint, download, fsv_feeder, l1_reference_dir, proof_manifest, read_typed,
    write_mismatch, ReferenceBundle, LOG_ROWS,
};
use full_statement_verifier::host_utils::build_unified_stream;

const M6_ARENA_BLOCKS: usize = 80 << 10;
const READBACK_CHUNK_FIELDS: usize = (64 << 20) / size_of::<PR>();

#[repr(C, align(32))]
#[derive(Clone, Copy)]
struct Aligned32([u8; 32]);

#[derive(Serialize)]
struct PhaseRecord {
    phase: &'static str,
    start_main_allocator_live_bytes: usize,
    absolute_main_allocator_peak_bytes: usize,
    end_adjusted_live_bytes: usize,
    exec_stream_elapsed_ms: f32,
    synchronized_wall_ms: f64,
}

#[derive(Serialize)]
struct LedgerLine<'a> {
    seq: usize,
    stage: &'a str,
    layer: Option<usize>,
    event: String,
    owner: &'a str,
    address: usize,
    bytes: usize,
    strong: Option<usize>,
    views: Option<usize>,
    adjusted_live_bytes: usize,
    main_peak_bytes: usize,
}

#[derive(Serialize)]
struct WallRecord {
    capture_ms: f64,
    host_preparation_ms: f64,
    comparisons_ms: f64,
    total_through_parse_ms: f64,
}

struct Phase {
    name: &'static str,
    start_live: usize,
    range: Range,
    wall: Instant,
}

impl Phase {
    fn begin(name: &'static str, context: &ProverContext) -> Self {
        context.reset_used_mem_peak();
        let start_live = context.get_used_mem_peak();
        let range = Range::new(format!("t7.{name}")).unwrap();
        range.start(context.get_exec_stream()).unwrap();
        Self {
            name,
            start_live,
            range,
            wall: Instant::now(),
        }
    }

    fn end(self, context: &ProverContext) -> PhaseRecord {
        self.range.end(context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        context.get_h2d_stream().synchronize().unwrap();
        let record = PhaseRecord {
            phase: self.name,
            start_main_allocator_live_bytes: self.start_live,
            absolute_main_allocator_peak_bytes: context.get_used_mem_peak(),
            end_adjusted_live_bytes: context.get_used_mem_current(),
            exec_stream_elapsed_ms: self.range.elapsed().unwrap(),
            synchronized_wall_ms: self.wall.elapsed().as_secs_f64() * 1e3,
        };
        println!("M6_PHASE {}", serde_json::to_string(&record).unwrap());
        record
    }
}

struct DeviceInputs {
    trace: UnrolledUnifiedTraceDevice,
    inits: InitsAndTeardownsTraceDevice,
    decoder: DeviceAllocation<ExecutorFamilyDecoderData>,
}

fn configuration() -> CpuExecutionProverConfiguration {
    CpuExecutionProverConfiguration {
        max_thread_pool_threads: Some(8),
        replay_worker_threads_count: 1,
        expected_concurrent_jobs: 1,
        ..Default::default()
    }
}

fn alloc_input<T>(len: usize, capacity: usize, context: &ProverContext) -> DeviceAllocation<T> {
    assert!(len <= capacity, "M6 stage parity input capacity");
    let mut allocation = context.alloc(capacity, AllocationPlacement::Top).unwrap();
    allocation.shrink_len_to(len);
    allocation
}

fn upload_inputs<'a>(
    fixture: &'a L1WrapFixture<'_>,
    context: &ProverContext,
) -> (DeviceInputs, Transfer<'a>) {
    let setup = fixture.setup;
    let trace_len = setup.trace_len;
    let teardown_capacity = setup.circuit.memory_layout.teardown_sets.len() * trace_len;
    let mut inputs = DeviceInputs {
        trace: UnrolledUnifiedTraceDevice {
            tracing_data: alloc_input(fixture.tracing_data.len(), trace_len, context),
        },
        inits: InitsAndTeardownsTraceDevice {
            page_indices: alloc_input(
                fixture.inits_and_teardowns.page_indices.len(),
                teardown_capacity >> PAGE_SIZE_LOG2,
                context,
            ),
            values_packed: alloc_input(
                fixture.inits_and_teardowns.values_packed.len(),
                teardown_capacity,
                context,
            ),
            timestamps_packed: alloc_input(
                fixture.inits_and_teardowns.timestamps_packed.len(),
                teardown_capacity,
                context,
            ),
        },
        decoder: context
            .alloc(setup.decoder_table.len(), AllocationPlacement::Top)
            .unwrap(),
    };
    let mut transfer = Transfer::new().unwrap();
    transfer.record_allocated(context).unwrap();
    transfer
        .schedule_multiple(
            &fixture.tracing_data.chunks,
            &mut inputs.trace.tracing_data,
            context,
        )
        .unwrap();
    transfer
        .schedule_multiple(
            &fixture.inits_and_teardowns.page_indices.chunks,
            &mut inputs.inits.page_indices,
            context,
        )
        .unwrap();
    transfer
        .schedule_multiple(
            &fixture.inits_and_teardowns.values_packed.chunks,
            &mut inputs.inits.values_packed,
            context,
        )
        .unwrap();
    transfer
        .schedule_multiple(
            &fixture.inits_and_teardowns.timestamps_packed.chunks,
            &mut inputs.inits.timestamps_packed,
            context,
        )
        .unwrap();
    let decoder: Vec<ExecutorFamilyDecoderData> = setup
        .decoder_table
        .iter()
        .copied()
        .map(|row| row.unwrap_or_default().into())
        .collect();
    let decoder = Arc::new(alloc_static_pinned_box_from_slice(&decoder).unwrap());
    transfer
        .schedule(decoder, &mut inputs.decoder, context)
        .unwrap();
    transfer.record_transferred(context).unwrap();
    transfer.ensure_transferred(context).unwrap();
    (inputs, transfer)
}

fn observe<T>(
    sink: &GKRBackwardStageSnapshotSinkPr,
    context: &ProverContext,
    stage: &'static str,
    event: ResourceEventPr,
    owner: &str,
    slice: &DeviceSlice<T>,
) {
    sink.record(
        context,
        stage,
        None,
        event,
        owner,
        ResourceIdPr::device(slice),
        None,
    );
}

fn observe_raw_backing(
    sink: &GKRBackwardStageSnapshotSinkPr,
    context: &ProverContext,
    stage: &'static str,
    owner: &str,
    holder: &TraceHolder<PR>,
) -> usize {
    let backing = holder.raw_hypercube_backing();
    let strong = Arc::strong_count(&backing) - 1;
    sink.record(
        context,
        stage,
        None,
        ResourceEventPr::Observed,
        owner,
        ResourceIdPr::device(&**backing),
        Some(ResourceCountsPr { strong, views: 1 }),
    );
    strong
}

fn print_ledger(records: &[ResourceRecordPr]) {
    for record in records {
        let line = LedgerLine {
            seq: record.seq,
            stage: record.stage,
            layer: record.layer,
            event: format!("{:?}", record.event),
            owner: &record.owner,
            address: record.id.address,
            bytes: record.id.bytes,
            strong: record.counts.map(|counts| counts.strong),
            views: record.counts.map(|counts| counts.views),
            adjusted_live_bytes: record.adjusted_live_bytes,
            main_peak_bytes: record.main_peak_bytes,
        };
        println!("M6_LEDGER {}", serde_json::to_string(&line).unwrap());
    }
}

fn read_slab(slab: &ProofSlabPr, context: &ProverContext) -> Vec<Aligned32> {
    let bytes = slab.layout.bytes_len();
    assert_eq!(bytes % 32, 0, "M6 stage parity slab length alignment");
    let mut host = vec![Aligned32([0; 32]); bytes / 32];
    let fields =
        unsafe { std::slice::from_raw_parts_mut(host.as_mut_ptr().cast::<PR>(), bytes / 16) };
    let device = &slab.backing[..bytes / 16];
    for start in (0..fields.len()).step_by(READBACK_CHUNK_FIELDS) {
        let end = (start + READBACK_CHUNK_FIELDS).min(fields.len());
        memory_copy_async(
            &mut fields[start..end],
            &device[start..end],
            context.get_exec_stream(),
        )
        .unwrap();
    }
    host
}

fn host_bytes(host: &[Aligned32]) -> &[u8] {
    unsafe { std::slice::from_raw_parts(host.as_ptr().cast::<u8>(), size_of_val(host)) }
}

fn host_fields(host: &[Aligned32], range: &std::ops::Range<usize>) -> Vec<PR> {
    assert!(
        range.start.is_multiple_of(16) && range.len().is_multiple_of(16),
        "M6 stage parity slab field range alignment"
    );
    let fields =
        unsafe { std::slice::from_raw_parts(host.as_ptr().cast::<PR>(), size_of_val(host) / 16) };
    fields[range.start / 16..range.end / 16].to_vec()
}

fn expect_eq<T: PartialEq + Debug + Serialize + ?Sized>(stage: &str, expected: &T, actual: &T) {
    if expected != actual {
        write_mismatch(stage, expected, actual);
        panic!("M6 stage parity {stage}: expected {expected:?}, actual {actual:?}");
    }
    println!("M6_PARITY {stage} ok");
}

fn expect_slice_eq<T: PartialEq + Debug + Serialize>(stage: &str, expected: &[T], actual: &[T]) {
    if let Some(index) = expected.iter().zip(actual).position(|(e, a)| e != a) {
        write_mismatch(stage, expected, actual);
        panic!(
            "M6 stage parity {stage}[{index}]: expected {:?}, actual {:?}",
            expected[index], actual[index]
        );
    }
    if expected.len() != actual.len() {
        write_mismatch(stage, expected, actual);
        panic!(
            "M6 stage parity {stage}: expected {} entries, actual {}",
            expected.len(),
            actual.len()
        );
    }
    println!("M6_PARITY {stage} ok {}", expected.len());
}

fn compare_layer(
    layer: usize,
    expected: &SumcheckIntermediateProofValues<PR, PR>,
    actual: &SumcheckIntermediateProofValues<PR, PR>,
) {
    expect_eq(
        &format!("layer{layer}.sumcheck_num_rounds"),
        &expected.sumcheck_num_rounds,
        &actual.sumcheck_num_rounds,
    );
    let coefficients = |values: &SumcheckIntermediateProofValues<PR, PR>| -> Vec<[PR; 4]> {
        values
            .internal_round_coefficients
            .iter()
            .map(|round| *round.as_multilinear())
            .collect()
    };
    expect_slice_eq(
        &format!("layer{layer}.round_coefficients"),
        &coefficients(expected),
        &coefficients(actual),
    );
    let final_addresses = |values: &SumcheckIntermediateProofValues<PR, PR>| {
        values
            .final_step_evaluations
            .keys()
            .copied()
            .collect::<Vec<_>>()
    };
    expect_slice_eq(
        &format!("layer{layer}.final_step_addresses"),
        &final_addresses(expected),
        &final_addresses(actual),
    );
    let final_values = |values: &SumcheckIntermediateProofValues<PR, PR>| {
        values
            .final_step_evaluations
            .values()
            .flatten()
            .copied()
            .collect::<Vec<_>>()
    };
    expect_slice_eq(
        &format!("layer{layer}.final_step_evaluations"),
        &final_values(expected),
        &final_values(actual),
    );
    let extras = |values: &SumcheckIntermediateProofValues<PR, PR>| {
        values
            .extra_evaluations_from_caching_relations
            .iter()
            .map(|(address, value)| (*address, *value))
            .collect::<Vec<_>>()
    };
    expect_slice_eq(
        &format!("layer{layer}.extra_evaluations"),
        &extras(expected),
        &extras(actual),
    );
}

fn compare_snapshots(replay: &ReplayedGkr, snapshots: &[GKRBackwardStageSnapshotPr]) {
    expect_eq("snapshots.count", &replay.snapshots.len(), &snapshots.len());
    for (expected, actual) in replay.snapshots.iter().zip(snapshots) {
        let layer = expected.layer_idx;
        expect_eq(
            &format!("snapshot{layer}.layer_idx"),
            &layer,
            &actual.layer_idx,
        );
        expect_eq(
            &format!("snapshot{layer}.seed"),
            &expected.seed,
            &actual.seed,
        );
        expect_slice_eq(
            &format!("snapshot{layer}.claim_point"),
            &expected.claim_point,
            &actual.claim_point,
        );
        expect_eq(
            &format!("snapshot{layer}.batching_challenge"),
            &expected.batching_challenge,
            &actual.batching_challenge,
        );
        match &expected.claims {
            ReplayedClaims::Ordered(claims) => expect_slice_eq(
                &format!("snapshot{layer}.claims"),
                claims,
                &actual.claims.values().copied().collect::<Vec<_>>(),
            ),
            ReplayedClaims::ByAddress(claims) => expect_slice_eq(
                &format!("snapshot{layer}.claims"),
                &claims.iter().map(|(a, v)| (*a, *v)).collect::<Vec<_>>(),
                &actual
                    .claims
                    .iter()
                    .map(|(a, v)| (*a, *v))
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

struct GpuOutputs {
    nine_challenges: Vec<PR>,
    lookup_nonce: u64,
    merged_cap: Vec<[u32; 8]>,
    slab_nine_challenges: Vec<PR>,
    fields: M6ProofFields,
    merged_claims: Vec<PR>,
    evaluation_point: Vec<PR>,
    batching_challenge: Vec<PR>,
    seed: Vec<u8>,
    snapshots: Vec<GKRBackwardStageSnapshotPr>,
}

fn compare_all(
    bundle: &ReferenceBundle,
    replay: &ReplayedGkr,
    top_bits: &[u32],
    setup_cap: &[[u32; 8]],
    gpu: &GpuOutputs,
) {
    let proof = &bundle.proof;
    let whir = &proof.whir_proof;
    assert_eq!(
        (
            whir.witness_commitment.num_columns,
            whir.witness_commitment.evals.len()
        ),
        (0, 0),
        "M6 stage parity bundle witness commitment must be empty"
    );
    expect_slice_eq("m4.top_bits", &proof.inits_and_teardowns_top_bits, top_bits);
    expect_slice_eq(
        "m4.setup_cap",
        &whir.setup_commitment.commitment.cap.cap,
        setup_cap,
    );
    expect_slice_eq(
        "m4.merged_cap",
        &whir.memory_commitment.commitment.cap.cap,
        &gpu.merged_cap,
    );
    expect_eq(
        "m4.lookup_nonce",
        &proof.lookup_challenges_pow_nonce,
        &gpu.lookup_nonce,
    );
    expect_eq(
        "m4.slab_lookup_nonce",
        &proof.lookup_challenges_pow_nonce,
        &gpu.fields.lookup_challenges_pow_nonce,
    );
    expect_slice_eq(
        "m4.nine_challenges",
        &replay.m4_challenges[..],
        &gpu.nine_challenges,
    );
    expect_slice_eq(
        "m4.slab_nine_challenges",
        &replay.m4_challenges[..],
        &gpu.slab_nine_challenges,
    );
    expect_eq(
        "m4.external_challenges",
        &proof.external_challenges,
        &gpu.fields.external_challenges,
    );
    expect_slice_eq(
        "explicit.output_types",
        &proof
            .final_explicit_evaluations
            .keys()
            .copied()
            .collect::<Vec<_>>(),
        &gpu.fields
            .final_explicit_evaluations
            .keys()
            .copied()
            .collect::<Vec<_>>(),
    );
    let explicit = |map: &BTreeMap<_, [Vec<PR>; 2]>| {
        map.values()
            .flat_map(|pair| pair.iter().flatten().copied())
            .collect::<Vec<_>>()
    };
    expect_slice_eq(
        "explicit.values",
        &explicit(&proof.final_explicit_evaluations),
        &explicit(&gpu.fields.final_explicit_evaluations),
    );
    let (expected, actual) = (&replay.snapshots[0], &gpu.snapshots[0]);
    expect_slice_eq("handoff.point", &expected.claim_point, &actual.claim_point);
    expect_eq(
        "handoff.batching_challenge",
        &expected.batching_challenge,
        &actual.batching_challenge,
    );
    expect_eq(
        "layers.indices",
        &proof
            .sumcheck_intermediate_values
            .keys()
            .copied()
            .collect::<Vec<_>>(),
        &gpu.fields
            .sumcheck_intermediate_values
            .keys()
            .copied()
            .collect::<Vec<_>>(),
    );
    for (&layer, expected) in proof.sumcheck_intermediate_values.iter().rev() {
        compare_layer(
            layer,
            expected,
            &gpu.fields.sumcheck_intermediate_values[&layer],
        );
    }
    compare_snapshots(replay, &gpu.snapshots);
    expect_eq(
        "main0.seed_before_packing",
        &replay.main0_seed,
        &gpu.snapshots
            .last()
            .expect("M6 stage parity snapshots")
            .seed,
    );
    expect_eq(
        "grand_product_accumulator",
        &proof.grand_product_accumulator_computed,
        &gpu.fields.grand_product_accumulator_computed,
    );
    let stored_point = whir
        .original_evaluation_point
        .as_ref()
        .expect("M6 stage parity bundle evaluation point");
    expect_slice_eq(
        "handoff.evaluation_point",
        stored_point,
        &gpu.fields.evaluation_point,
    );
    expect_slice_eq(
        "handoff.evaluation_point.replay",
        &replay.evaluation_point,
        &gpu.fields.evaluation_point,
    );
    expect_slice_eq(
        "handoff.evaluation_point.device",
        &gpu.fields.evaluation_point,
        &gpu.evaluation_point,
    );
    expect_slice_eq(
        "handoff.extra_coordinates",
        &replay.extra,
        &gpu.fields.evaluation_point[replay.z.len()..],
    );
    expect_slice_eq(
        "handoff.memory_claims",
        &whir.memory_commitment.evals,
        &gpu.fields.merged_claims.0,
    );
    expect_slice_eq(
        "handoff.setup_claims",
        &whir.setup_commitment.evals,
        &gpu.fields.merged_claims.1,
    );
    expect_slice_eq(
        "handoff.merged_claims.device",
        &gpu.fields
            .merged_claims
            .0
            .iter()
            .chain(&gpu.fields.merged_claims.1)
            .copied()
            .collect::<Vec<_>>(),
        &gpu.merged_claims,
    );
    expect_eq(
        "batched_pow_nonce",
        &proof.batched_proximity_check_pow_nonce,
        &gpu.fields.batched_proximity_check_pow_nonce,
    );
    let stored_batching = whir
        .batching_challenge
        .expect("M6 stage parity bundle batching challenge");
    expect_eq(
        "handoff.batching_challenge",
        &stored_batching,
        &gpu.fields.batching_challenge,
    );
    expect_eq(
        "handoff.batching_challenge.replay",
        &replay.batching_challenge,
        &gpu.fields.batching_challenge,
    );
    expect_slice_eq(
        "handoff.batching_challenge.device",
        &[gpu.fields.batching_challenge],
        &gpu.batching_challenge,
    );
    let stored_seed = proof
        .intermediate_transcript_seed
        .expect("M6 stage parity bundle pre-WHIR seed");
    expect_eq(
        "intermediate_transcript_seed",
        &stored_seed,
        &gpu.fields.intermediate_transcript_seed,
    );
    expect_eq(
        "intermediate_transcript_seed.replay",
        &replay.final_seed,
        &gpu.fields.intermediate_transcript_seed,
    );
    expect_slice_eq(
        "intermediate_transcript_seed.device",
        &gpu.fields.intermediate_transcript_seed[..],
        &gpu.seed,
    );
}

fn run_stages(
    fixture: L1WrapFixture<'_>,
    bundle: ReferenceBundle,
    capture_start: Instant,
) -> WallRecord {
    let capture_ms = capture_start.elapsed().as_secs_f64() * 1e3;
    let total = Instant::now();
    assert_eq!(
        fixture.commitment_mode, bundle.commitment_mode,
        "M6 stage parity boundary state differs from the committed bundle"
    );
    let circuit = &fixture.setup.circuit;
    let rows = circuit.trace_len;
    assert_eq!(rows, 1 << LOG_ROWS, "M6 stage parity trace length");
    let config = ProofProfile::L1Wrap.prover_config(LOG_ROWS as usize, SecurityLevel::Sec100);
    assert_eq!(
        config.sumcheck_explicit_output_size_log_2, 4,
        "M6 stage parity explicit output log"
    );
    let pack_log2 = EVM_PRODUCTION_PACK_LOG2 as u32;
    let cfg = PackedCommitConfig::from_prover_config(&config, LOG_ROWS + pack_log2);
    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        external_challenges_pow_bits,
        ..
    } = fixture.commitment_mode
    else {
        panic!("M6 stage parity requires the packed commitment mode");
    };
    let lookup_pow_bits = pow_bits::lookup_challenges_pow_bits(
        config.security_level.security_bits(),
        pow_bits::lookup_identity_degree(circuit),
    )
    .max(external_challenges_pow_bits);
    let base_lde_log2 = config.whir_schedule.base_lde_factor.trailing_zeros() as usize;
    let base_columns = pow_bits::total_base_oracle_columns(circuit);
    let batched_pow_bits = pow_bits::batched_proximity_check_pow_bits(
        config.security_level.security_bits(),
        LOG_ROWS as usize,
        base_lde_log2,
        base_columns,
    );
    assert_eq!(
        (
            lookup_pow_bits,
            base_lde_log2,
            base_columns,
            batched_pow_bits
        ),
        (20, 5, 114, 11),
        "M6 stage parity PoW inputs"
    );
    let replay = replay_gkr_challenges(
        &bundle,
        ReplayPowBits {
            lookup: lookup_pow_bits,
            batched: batched_pow_bits,
        },
    );
    replay.assert_matches_bundle(&bundle);

    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(M6_ARENA_BLOCKS),
        proth120_ntt_log_max_domain: Some(31),
        ..Default::default()
    })
    .unwrap();
    println!("M6_ARENA bytes={}", context.get_mem_size());
    let mut sink = GKRBackwardStageSnapshotSinkPr::default();

    let phase = Phase::begin("p0.setup_precompute", &context);
    let host = Arc::new(
        L1WrapSetupHost::precompute(&fixture.setup.setup, pack_log2, cfg, &context).unwrap(),
    );
    phase.end(&context);
    let setup_cap = host.cap().cap;

    let phase = Phase::begin("p1.setup_and_input_upload", &context);
    let mut source = PackedSetupSource::new(Arc::clone(&host), &context).unwrap();
    let setup_transfer = single_shot_h2d(
        |transfer| source.schedule_transfer(transfer, &context),
        &context,
    )
    .unwrap();
    setup_transfer.ensure_transferred(&context).unwrap();
    let relations = prepare_lookup_relations(circuit, &context).unwrap();
    let (inputs, input_transfer) = upload_inputs(&fixture, &context);
    let mut top_bits = context
        .alloc(
            fixture.inits_and_teardowns.top_bits.len(),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    memory_copy_async(
        &mut top_bits,
        &fixture.inits_and_teardowns.top_bits,
        context.get_exec_stream(),
    )
    .unwrap();
    phase.end(&context);
    for (owner, slice) in [
        ("m4.setup.raw", source.raw().get_hypercube_evals()),
        ("m4.setup.monomials", source.oracle().monomials()),
    ] {
        observe(
            &sink,
            &context,
            "p1.setup_and_input_upload",
            ResourceEventPr::Observed,
            owner,
            slice,
        );
    }
    observe(
        &sink,
        &context,
        "p1.setup_and_input_upload",
        ResourceEventPr::Observed,
        "m5.inputs.tracing_data",
        &inputs.trace.tracing_data,
    );
    observe(
        &sink,
        &context,
        "p1.setup_and_input_upload",
        ResourceEventPr::Observed,
        "m5.inputs.decoder",
        &inputs.decoder,
    );

    let phase = Phase::begin("p2.m5_witness", &context);
    let memory_width = circuit.memory_layout.total_width;
    let witness_width = circuit.witness_layout.total_width;
    let mut holder = TraceHolder::new_without_cosets(
        LOG_ROWS,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        memory_width + witness_width,
        TreesCacheMode::CacheNone,
        &context,
    )
    .unwrap();
    let mut scratch: DeviceAllocation<PR> = context
        .alloc(
            rows * circuit.scratch_space_size,
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let generic_columns = circuit.generic_lookups.len();
    let mut generic: DeviceAllocation<u32> = context
        .alloc(
            rows * (generic_columns + usize::from(circuit.has_decoder_lookup)),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let mut range_check_16: DeviceAllocation<u32> = context
        .alloc(
            rows * circuit.range_check_16_lookup_expressions.len(),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let mut timestamp: DeviceAllocation<u32> = context
        .alloc(
            rows * circuit.timestamp_range_check_lookup_expressions.len(),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let stream = context.get_exec_stream();
    {
        let (memory, witness) = holder
            .get_uninit_hypercube_evals_mut()
            .split_at_mut(memory_width * rows);
        generate_inits_and_teardowns(
            &circuit.memory_layout,
            LOG_ROWS,
            PAGE_SIZE_LOG2,
            &inputs.inits,
            &mut DeviceMatrixMut::new(&mut *memory, rows),
            stream,
        )
        .unwrap();
        let (generic_mapping, decoder_mapping) = generic.split_at_mut(rows * generic_columns);
        generate_fused_values(
            circuit,
            &inputs.decoder,
            &inputs.trace,
            &DeviceMatrix::new(source.raw().get_hypercube_evals(), rows),
            &relations,
            &mut Proth120WitnessBuffers {
                memory: DeviceMatrixMut::new(&mut *memory, rows),
                witness: DeviceMatrixMut::new(&mut *witness, rows),
                scratch: DeviceMatrixMut::new(&mut scratch, rows),
                generic_lookup_mapping: DeviceMatrixMut::new(generic_mapping, rows),
                range_check_16_lookup_mapping: DeviceMatrixMut::new(&mut range_check_16, rows),
                range_check_timestamp_lookup_mapping: DeviceMatrixMut::new(&mut timestamp, rows),
                decoder_lookup_mapping: decoder_mapping,
            },
            stream,
        )
        .unwrap();
        let layout = &circuit.witness_layout;
        for (mapping, columns, active_counts_len) in [
            (
                &mut generic,
                layout.multiplicities_columns_for_generic_lookup.clone(),
                circuit.total_tables_size,
            ),
            (
                &mut range_check_16,
                layout.multiplicities_columns_for_range_check_16.clone(),
                1 << 16,
            ),
            (
                &mut timestamp,
                layout
                    .multiplicities_columns_for_timestamp_range_check
                    .clone(),
                1 << common_constants::TIMESTAMP_COLUMNS_NUM_BITS,
            ),
        ] {
            generate_lookup_multiplicities(
                &mut DeviceMatrixMut::new(mapping, rows),
                &mut DeviceMatrixMut::new(
                    &mut witness[columns.start * rows..columns.end * rows],
                    rows,
                ),
                active_counts_len,
                &context,
            )
            .unwrap();
        }
    }
    drop(inputs);
    phase.end(&context);
    drop(input_transfer);
    drop(relations);
    for (owner, slice) in [
        ("m5.mapping.generic_and_decoder", &*generic),
        ("m5.mapping.range_check_16", &*range_check_16),
        ("m5.mapping.timestamp", &*timestamp),
    ] {
        observe(
            &sink,
            &context,
            "p2.m5_witness",
            ResourceEventPr::Observed,
            owner,
            slice,
        );
    }
    observe(
        &sink,
        &context,
        "p2.m5_witness",
        ResourceEventPr::Observed,
        "m5.scratch",
        &scratch,
    );
    observe(
        &sink,
        &context,
        "p2.m5_witness",
        ResourceEventPr::Observed,
        "m4.raw.memory_witness",
        holder.get_hypercube_evals(),
    );

    let phase = Phase::begin("p3.m4_commit_and_challenges", &context);
    let mut oracle =
        PackedCosetRecomputeOracle::pack_from_columns(holder, pack_log2, &context).unwrap();
    oracle.commit(&cfg, &context).unwrap();
    let challenge_cfg =
        PackedChallengeConfig::new(circuit, &config, &fixture.commitment_mode, true);
    assert_eq!(
        challenge_cfg.pow_bits, lookup_pow_bits,
        "M6 stage parity lookup PoW bits"
    );
    let mut seed = context.alloc(32, AllocationPlacement::BestFit).unwrap();
    let challenges = derive(
        &mut seed,
        &fixture.commitment_mode,
        &top_bits,
        source.cap(),
        oracle.cap(),
        &challenge_cfg,
        &context,
    )
    .unwrap();
    phase.end(&context);
    let merged_cap = download(oracle.cap_digests(), [0u32; 8], &context);
    let lookup_nonce = download(challenges.nonce(), 0u64, &context)[0];
    let nine_challenges = download(challenges.challenges(), PR::ZERO, &context);
    for (owner, slice) in [
        ("m4.merged.monomials", oracle.monomials()),
        ("m4.challenges", challenges.challenges()),
    ] {
        observe(
            &sink,
            &context,
            "p3.m4_commit_and_challenges",
            ResourceEventPr::Observed,
            owner,
            slice,
        );
    }
    let retained = ResourceIdPr::device(oracle.uninit_retained_mut());
    let roots = ResourceIdPr::device(oracle.uninit_roots_mut());
    let top_nodes = ResourceIdPr::device(oracle.uninit_top_nodes_mut());
    for (owner, id) in [
        ("m4.merged.retained", retained),
        ("m4.merged.roots", roots),
        ("m4.merged.top_nodes", top_nodes),
    ] {
        sink.record(
            &context,
            "p3.m4_commit_and_challenges",
            None,
            ResourceEventPr::Observed,
            owner,
            id,
            None,
        );
    }

    let preparation = Instant::now();
    let programs = Arc::new(
        GkrProgramsPr::compile(CircuitType::L1Wrap, Arc::new(circuit.clone()))
            .unwrap_or_else(|error| panic!("M6 stage parity program compile: {error}")),
    );
    let dr_tail_plan = preflight_dr_tail_resources_pr(&programs, 4, &context);
    let layout = Arc::new(ProofLayoutPr::new(&programs, &config));
    let witness_layout = &circuit.witness_layout;
    assert_eq!(
        (
            witness_layout.multiplicities_columns_for_range_check_16.end,
            witness_layout
                .multiplicities_columns_for_timestamp_range_check
                .end
        ),
        (
            witness_layout
                .multiplicities_columns_for_timestamp_range_check
                .start,
            witness_layout
                .multiplicities_columns_for_generic_lookup
                .start
        ),
        "M6 stage parity multiplicity columns must be contiguous"
    );
    let multiplicities = (memory_width
        + witness_layout
            .multiplicities_columns_for_range_check_16
            .start)
        * rows
        ..(memory_width + witness_layout.multiplicities_columns_for_generic_lookup.end) * rows;
    let host_preparation_ms = preparation.elapsed().as_secs_f64() * 1e3;

    let phase = Phase::begin("p4.m6_facade", &context);
    let mut slab = ProofSlabPr::new(Arc::clone(&layout), &context).unwrap();
    observe(
        &sink,
        &context,
        "p4.m6_facade",
        ResourceEventPr::Allocated,
        "m6.proof_slab",
        &slab.backing,
    );
    let raw_strong_before = observe_raw_backing(
        &sink,
        &context,
        "p4.m6_facade",
        "m4.raw.memory_witness",
        oracle.raw(),
    );
    let setup_strong_before = observe_raw_backing(
        &sink,
        &context,
        "p4.m6_facade",
        "m4.setup.raw",
        source.raw(),
    );
    #[allow(clippy::arc_with_non_send_sync)]
    let scratch = Arc::new(scratch);
    let raw = oracle.raw().get_hypercube_evals();
    let witness_inputs = Proth120GkrWitnessInputs::new(
        circuit,
        scratch,
        circuit.scratch_space_size,
        rows,
        DeviceMatrix::new(&generic[..rows * generic_columns], rows),
        DeviceMatrix::new(&range_check_16, rows),
        DeviceMatrix::new(&timestamp, rows),
        &generic[rows * generic_columns..],
        DeviceMatrix::new(&raw[multiplicities], rows),
    );
    sink.record(
        &context,
        "p4.m6_facade",
        None,
        ResourceEventPr::Observed,
        "m5.scratch",
        ResourceIdPr::device(&**witness_inputs.scratch),
        Some(ResourceCountsPr::shared(&witness_inputs.scratch, 1)),
    );
    let mut callbacks = Callbacks::new();
    let mut output: GkrOutputPr = schedule_gkr(
        Arc::clone(&programs),
        &oracle,
        &source,
        witness_inputs,
        &fixture.inits_and_teardowns.top_bits,
        &challenges,
        &config,
        batched_pow_bits,
        seed,
        &mut slab,
        &dr_tail_plan,
        Some(UnsafeMutAccessor::new(&mut sink)),
        &mut callbacks,
        &context,
    )
    .unwrap();
    let raw_strong_after = observe_raw_backing(
        &sink,
        &context,
        "p4.m6_facade",
        "m4.raw.memory_witness",
        oracle.raw(),
    );
    let setup_strong_after = observe_raw_backing(
        &sink,
        &context,
        "p4.m6_facade",
        "m4.setup.raw",
        source.raw(),
    );
    for (owner, slice) in [
        ("m5.mapping.generic_and_decoder", &*generic),
        ("m5.mapping.range_check_16", &*range_check_16),
        ("m5.mapping.timestamp", &*timestamp),
    ] {
        observe(
            &sink,
            &context,
            "p4.m6_facade",
            ResourceEventPr::Released,
            owner,
            slice,
        );
    }
    drop(generic);
    drop(range_check_16);
    drop(timestamp);
    phase.end(&context);
    drop(callbacks);
    assert_eq!(
        (raw_strong_after, setup_strong_after),
        (raw_strong_before, setup_strong_before),
        "M6 stage parity: the facade must not retain raw holder clones"
    );

    let phase = Phase::begin("p5.terminal_readback", &context);
    let slab_host = read_slab(&slab, &context);
    let merged_claims = download(output.merged_claims(), PR::ZERO, &context);
    let evaluation_point = download(output.evaluation_point(), PR::ZERO, &context);
    let batching_challenge = download(output.whir_handoff().batching_challenge, PR::ZERO, &context);
    let output_seed = download(&*output.seed(), 0u8, &context);
    phase.end(&context);
    let fields = layout.parse_m6_fields(host_bytes(&slab_host));
    let slab_nine_challenges = host_fields(&slab_host, &layout.external_challenges);
    drop(output);
    let total_through_parse_ms = total.elapsed().as_secs_f64() * 1e3;

    let (snapshots, resources) = sink.into_parts();
    print_ledger(&resources);
    let comparisons = Instant::now();
    compare_all(
        &bundle,
        &replay,
        &fixture.inits_and_teardowns.top_bits,
        &setup_cap,
        &GpuOutputs {
            nine_challenges,
            lookup_nonce,
            merged_cap,
            slab_nine_challenges,
            fields,
            merged_claims,
            evaluation_point,
            batching_challenge,
            seed: output_seed,
            snapshots,
        },
    );
    assert_eq!(
        replay.m4_challenges.len(),
        M4_CHALLENGE_DRAWS,
        "M6 stage parity M4 challenge count"
    );
    let wall = WallRecord {
        capture_ms,
        host_preparation_ms,
        comparisons_ms: comparisons.elapsed().as_secs_f64() * 1e3,
        total_through_parse_ms,
    };
    println!("M6_WALL {}", serde_json::to_string(&wall).unwrap());
    wall
}

pub(super) fn run() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .format_timestamp_millis()
        .try_init();
    let start = Instant::now();
    let manifest = proof_manifest();
    let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    check_file(&manifest, "l1_bundle.json");
    let bundle: ReferenceBundle = read_typed(&l1_reference_dir().join("l1_bundle.json"));
    assert!(
        matches!(
            bundle.commitment_mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2: EVM_PRODUCTION_PACK_LOG2,
                external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ),
        "L1 reference bundle is not in the EVM-production packed commitment mode"
    );
    assert_eq!(
        GKRExternalChallenges::<PR, PR>::TOTAL_CHALLENGES + 2,
        M4_CHALLENGE_DRAWS,
        "M6 stage parity challenge draw count"
    );
    let (bin, text) = fsv_feeder(&manifest);
    let nd_words = build_unified_stream(&feeder.setups, &feeder.proof);
    drop(feeder);
    let capture_start = Instant::now();
    let wall = with_l1_wrap_fixture(configuration(), bin, text, nd_words, None, move |fixture| {
        run_stages(fixture, bundle, capture_start)
    });
    println!(
        "M6_TEST_WALL total_ms={} through_parse_ms={}",
        start.elapsed().as_secs_f64() * 1e3,
        wall.total_through_parse_ms
    );
}
