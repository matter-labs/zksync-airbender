#![cfg(not(no_cuda))]
#![feature(allocator_api)]

gpu_core::force_serial_libtest!();

use cpu_execution_prover::test_support::{with_l1_wrap_fixture, L1WrapFixture};
use cpu_execution_prover::CpuExecutionProverConfiguration;
use cs::definitions::GKRAddress;
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use execution_prover::{CommitmentMode, ProofProfile};
use fft::Twiddles;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_circuit_prover::proof::memory_policy;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::alloc_static_pinned_box_uninit;
use gpu_gkr::proth120::packed_challenges::{
    derive, split_challenges, PackedChallengeConfig, PACKED_CHALLENGE_DRAWS,
};
use gpu_gkr::setup::{L1WrapSetupHost, PackedSetupSource};
use gpu_prover_context::transfer::single_shot_h2d;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_whir::proth120::{
    schedule_l1_whir_fold, L1WhirInputs, L1WhirProof, L1WhirShape, L1_WHIR_TILE_BYTES,
};
use prover::definitions::{GKRExternalChallenges, SecurityLevel};
use prover::field::{Field, Proth120};
use prover::gkr::prover::GKRProof;
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::{
    EXTERNAL_CHALLENGES_POW_BITS, PACK_LOG2,
};
use prover::gkr::prover_config::pow_bits;
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::merkle_trees::{MerkleTreeCapVarLength, PathQueryable};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::alloc::Global;
use std::fs::{self, File};
use std::io::{BufReader, BufWriter};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[path = "l1_stage_parity/m6_replay.rs"]
mod m6_replay;
#[path = "l1_stage_parity/m6_stage.rs"]
mod m6_stage;

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

const LOG_ROWS: u32 = 21;
const ARENA_BLOCKS: usize = 40 << 10;

#[derive(Deserialize)]
struct ReferenceBundle {
    proof: L1Proof,
    commitment_mode: CommitmentMode,
}

#[derive(Deserialize)]
struct FileIdentity {
    name: String,
    bytes: u64,
    keccak256: String,
}

#[derive(Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
}

#[derive(Deserialize)]
struct ReferenceConfiguration {
    security_level: String,
    backend: String,
    batch_id: u64,
}

#[derive(Deserialize)]
struct ProofManifest {
    format_version: u32,
    configuration: ReferenceConfiguration,
    fsv: Vec<FsvIdentity>,
    files: Vec<FileIdentity>,
}

#[derive(Deserialize)]
struct Checkpoint {
    schema_version: u32,
    target: String,
    security_level: String,
    proof: ProgramProof,
    setups: Setups,
}

struct Expected {
    commitment_mode: CommitmentMode,
    top_bits: Vec<u32>,
    setup_cap: MerkleTreeCapVarLength,
    merged_cap: MerkleTreeCapVarLength,
    nonce: u64,
    external: GKRExternalChallenges<Proth120, Proth120>,
}

struct WhirExpected {
    commitment_mode: CommitmentMode,
    seed: [u8; 32],
    whir: L1WhirProof,
}

struct WhirReport {
    differences: Vec<String>,
    baseline_bytes: usize,
    peak_bytes: usize,
    enqueue: Duration,
    wall: Duration,
    gpu_ms: f32,
    phases: Vec<(String, f32)>,
}

struct StageReport {
    differences: Vec<String>,
    measured_peak_bytes: usize,
}

fn l1_reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference_2p21")
        })
}

fn read_typed<T: DeserializeOwned>(path: &Path) -> T {
    let file = File::open(path)
        .unwrap_or_else(|error| panic!("L1 reference open {}: {error}", path.display()));
    serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|error| panic!("L1 reference deserialize {}: {error}", path.display()))
}

fn keccak_hex(bytes: &[u8]) -> String {
    Keccak256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn proof_manifest() -> ProofManifest {
    let manifest: ProofManifest = read_typed(&l1_reference_dir().join("manifest.json"));
    assert_eq!(
        manifest.format_version, 1,
        "L1 stage parity proof manifest format"
    );
    assert_eq!(
        manifest.configuration.security_level, "Sec100",
        "L1 stage parity reference security level"
    );
    assert_eq!(
        manifest.configuration.backend, "Cpu",
        "L1 stage parity reference backend"
    );
    assert_eq!(
        manifest.configuration.batch_id, 0,
        "L1 stage parity reference batch id"
    );
    manifest
}

fn check_file(manifest: &ProofManifest, name: &str) {
    let entry = manifest
        .files
        .iter()
        .find(|file| file.name == name)
        .unwrap_or_else(|| panic!("L1 stage parity manifest omits {name}"));
    let path = l1_reference_dir().join(name);
    let data = fs::read(&path)
        .unwrap_or_else(|error| panic!("L1 stage parity read {}: {error}", path.display()));
    assert_eq!(
        data.len() as u64,
        entry.bytes,
        "L1 stage parity reference size differs: {name}"
    );
    assert_eq!(
        keccak_hex(&data),
        entry.keccak256,
        "L1 stage parity reference identity differs: {name}"
    );
}

fn checkpoint(manifest: &ProofManifest, name: &str, target: &str) -> Checkpoint {
    check_file(manifest, name);
    let checkpoint: Checkpoint = read_typed(&l1_reference_dir().join(name));
    assert_eq!(
        checkpoint.schema_version, 5,
        "L1 stage parity checkpoint schema: {name}"
    );
    assert_eq!(
        checkpoint.target, target,
        "L1 stage parity checkpoint target: {name}"
    );
    assert_eq!(
        checkpoint.security_level, manifest.configuration.security_level,
        "L1 stage parity checkpoint security level: {name}"
    );
    checkpoint
}

fn fsv_feeder(manifest: &ProofManifest) -> (Vec<u32>, Vec<u32>) {
    let dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/gkr_verifier"));
    let program = FsvProgram::UnifiedRecursionLayerL1FeederWrap;
    let mode = BlakeMode::BlakeSpecialOpcodes;
    let stem = program.file_stem(mode);
    let entry = manifest
        .fsv
        .iter()
        .find(|entry| entry.role == "feeder_wrap")
        .expect("L1 stage parity manifest omits fsv role feeder_wrap");
    assert_eq!(
        stem, entry.stem,
        "L1 stage parity fsv stem differs: feeder_wrap"
    );
    for (extension, expected) in [
        ("bin", &entry.bin_keccak256),
        ("text", &entry.text_keccak256),
    ] {
        let path = dir.join(format!("{stem}.{extension}"));
        let data = fs::read(&path)
            .unwrap_or_else(|error| panic!("L1 stage parity fsv read {}: {error}", path.display()));
        assert_eq!(
            keccak_hex(&data),
            *expected,
            "L1 stage parity fsv identity differs: feeder_wrap.{extension}"
        );
    }
    load_fsv_program(&dir, program, mode)
}

fn write_mismatch<T: Serialize + ?Sized>(stage: &str, expected: &T, actual: &T) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/l1_stage_parity");
    fs::create_dir_all(&dir).expect("L1 stage parity mismatch directory");
    for (kind, value) in [("expected", expected), ("actual", actual)] {
        let path = dir.join(format!("{kind}-{stage}.json"));
        let file = File::create(&path)
            .unwrap_or_else(|error| panic!("L1 stage parity write {}: {error}", path.display()));
        serde_json::to_writer_pretty(BufWriter::new(file), value)
            .expect("L1 stage parity mismatch serializes");
    }
}

fn compare<T: Serialize + PartialEq + ?Sized>(
    stage: &str,
    expected: &T,
    actual: &T,
    differences: &mut Vec<String>,
) {
    if expected == actual {
        log::info!("L1 stage parity: {stage} matches the reference");
    } else {
        log::error!("L1 stage parity: {stage} differs from the reference");
        write_mismatch(stage, expected, actual);
        differences.push(stage.into());
    }
}

fn compare_bytes<T: Serialize + ?Sized>(
    stage: &str,
    expected: &T,
    actual: &T,
    differences: &mut Vec<String>,
) {
    let expected_bytes = serde_json::to_vec(expected).expect("L1 stage parity serializes");
    let actual_bytes = serde_json::to_vec(actual).expect("L1 stage parity serializes");
    if expected_bytes == actual_bytes {
        log::info!("L1 stage parity: {stage} matches the reference");
    } else {
        log::error!("L1 stage parity: {stage} differs from the reference");
        write_mismatch(stage, expected, actual);
        differences.push(stage.into());
    }
}

fn vm_status() -> String {
    fs::read_to_string("/proc/self/status")
        .expect("L1 stage parity reads /proc/self/status")
        .lines()
        .filter(|line| line.starts_with("VmHWM") || line.starts_with("VmRSS"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn upload<T: Copy>(values: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    device
}

fn download<T: Copy>(device: &DeviceSlice<T>, initial: T, context: &ProverContext) -> Vec<T> {
    let mut host = vec![initial; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn localize_setup_cap(
    fixture: &L1WrapFixture<'_>,
    cfg: PackedCommitConfig,
    context: &ProverContext,
) {
    let pack_log2 = PACK_LOG2 as u32;
    let columns: Vec<&[Proth120]> = fixture
        .setup
        .setup
        .hypercube_evals
        .iter()
        .map(|column| &column[..])
        .collect();
    let twiddles = Twiddles::<Proth120, Global>::new(1 << (LOG_ROWS + pack_log2), fixture.worker);
    let cpu = CosetByCosetBaseCommitment::<Proth120, Keccak256MerkleTreeWithCap>::commit_packed(
        &columns,
        &twiddles,
        1 << cfg.log_lde_factor,
        cfg.log_values_per_leaf as usize,
        1 << cfg.cap_log,
        LOG_ROWS as usize,
        PACK_LOG2,
        fixture.worker,
    );
    let mut holder = TraceHolder::new_without_cosets(
        LOG_ROWS,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        columns.len(),
        TreesCacheMode::CacheNone,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        context,
    )
    .unwrap();
    let flat: Vec<Proth120> = columns.concat();
    memory_copy_async(
        holder.get_uninit_hypercube_evals_mut(),
        &flat,
        context.get_exec_stream(),
    )
    .unwrap();
    let mut oracle =
        PackedCosetRecomputeOracle::pack_from_columns(holder, pack_log2, context).unwrap();
    oracle.commit(&cfg, context).unwrap();
    let roots = download(oracle.uninit_roots_mut(), [0u32; 8], context);
    let differing: Vec<usize> = (0..roots.len())
        .filter(|&physical| roots[physical] != cpu.top_tree.get_proof(physical).0)
        .collect();
    log::error!(
        "L1 stage parity: CPU commit_packed setup cap {} the device cap; physical setup roots differing from CPU: {differing:?}",
        if download(oracle.cap_digests(), [0u32; 8], context) == cpu.get_cap().cap { "equals" } else { "differs from" }
    );
}

fn run_stages(fixture: L1WrapFixture<'_>, expected: Expected) -> StageReport {
    assert_eq!(
        fixture.commitment_mode, expected.commitment_mode,
        "L1 stage parity boundary state differs from the committed bundle"
    );
    assert_eq!(
        fixture.inits_and_teardowns.top_bits, expected.top_bits,
        "L1 stage parity inits/teardowns windows differ from the committed bundle"
    );
    let mut differences = Vec::new();
    let config = ProofProfile::L1Wrap.prover_config(LOG_ROWS as usize, SecurityLevel::Sec100);
    let pack_log2 = PACK_LOG2 as u32;
    // The production L1 wrap: setup host precompute at the default depth
    // (precomputations/l1_wrap.rs), merged commit and setup source at the preset's.
    let partial_trees =
        memory_policy::presets::partial_trees(CircuitType::L1Wrap21, ProofProfile::L1Wrap);
    let setup_cfg = PackedCommitConfig::from_prover_config(
        &config,
        LOG_ROWS + pack_log2,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
    );
    let cfg =
        PackedCommitConfig::from_prover_config(&config, LOG_ROWS + pack_log2, partial_trees.memory);
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(ARENA_BLOCKS),
        proth120_ntt_log_max_domain: Some(31),
        ..Default::default()
    })
    .unwrap();

    let start = Instant::now();
    let host =
        L1WrapSetupHost::precompute(&fixture.setup.setup, pack_log2, setup_cfg, &context).unwrap();
    log::info!("L1 stage parity: setup precompute {:?}", start.elapsed());
    let setup_cap = host.cap();
    compare(
        "setup-cap",
        &expected.setup_cap,
        &setup_cap,
        &mut differences,
    );
    if setup_cap != expected.setup_cap {
        localize_setup_cap(&fixture, setup_cfg, &context);
    }

    let start = Instant::now();
    let witness = fixture.evaluate_witness();
    log::info!("L1 stage parity: witness evaluation {:?}", start.elapsed());
    let columns_count =
        witness.column_major_memory_trace.len() + witness.column_major_witness_trace.len();
    assert_eq!(
        columns_count,
        fixture.setup.circuit.memory_layout.total_width
            + fixture.setup.circuit.witness_layout.total_width,
        "L1 stage parity merged column count"
    );
    let rows = 1usize << LOG_ROWS;
    let mut holder = TraceHolder::new_without_cosets(
        LOG_ROWS,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        columns_count,
        TreesCacheMode::CacheNone,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    let mut staging = alloc_static_pinned_box_uninit::<PR>(rows).unwrap();
    let start = Instant::now();
    for (index, column) in witness
        .column_major_memory_trace
        .iter()
        .chain(witness.column_major_witness_trace.iter())
        .enumerate()
    {
        assert_eq!(column.len(), rows, "L1 stage parity column {index} length");
        staging.copy_from_slice(column);
        memory_copy_async(
            &mut holder.get_uninit_hypercube_evals_mut()[index * rows..(index + 1) * rows],
            &staging[..],
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    drop(staging);
    drop(witness);
    log::info!("L1 stage parity: trace upload {:?}", start.elapsed());

    let host = Arc::new(host);
    let mut source =
        PackedSetupSource::new(Arc::clone(&host), partial_trees.setup, &context).unwrap();
    let start = Instant::now();
    let transfer = single_shot_h2d(
        |transfer| source.schedule_transfer(transfer, &context),
        &context,
    )
    .unwrap();
    transfer.ensure_transferred(&context).unwrap();
    drop(transfer);
    log::info!("L1 stage parity: setup upload {:?}", start.elapsed());

    context.get_exec_stream().synchronize().unwrap();
    context.reset_used_mem_peak();
    let start = Instant::now();
    let mut oracle =
        PackedCosetRecomputeOracle::pack_from_columns(holder, pack_log2, &context).unwrap();
    oracle.commit(&cfg, &context).unwrap();
    let merged_cap = MerkleTreeCapVarLength {
        cap: download(oracle.cap_digests(), [0u32; 8], &context),
    };
    log::info!(
        "L1 stage parity: merged pack + commit {:?}",
        start.elapsed()
    );
    let measured_peak_bytes = context.get_used_mem_peak();
    log::info!("L1 stage parity: MEASURED_M4_PEAK_BYTES = {measured_peak_bytes}");
    compare(
        "merged-cap",
        &expected.merged_cap,
        &merged_cap,
        &mut differences,
    );

    let mut top_bits = context
        .alloc(expected.top_bits.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut top_bits, &expected.top_bits, context.get_exec_stream()).unwrap();
    let challenge_cfg = PackedChallengeConfig::new(
        &fixture.setup.circuit,
        &config,
        &fixture.commitment_mode,
        true,
    );
    assert_eq!(
        challenge_cfg.pow_bits, 20,
        "L1 stage parity lookup PoW bits"
    );
    let mut seed = context.alloc(32, AllocationPlacement::BestFit).unwrap();
    let start = Instant::now();
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
    let nonce = download(challenges.nonce(), 0u64, &context)[0];
    let values: [PR; PACKED_CHALLENGE_DRAWS] =
        download(challenges.challenges(), PR::ZERO, &context)
            .try_into()
            .unwrap();
    log::info!("L1 stage parity: derive {:?}", start.elapsed());
    compare("nonce", &expected.nonce, &nonce, &mut differences);
    compare(
        "external-challenges",
        &expected.external,
        &split_challenges(&values).0,
        &mut differences,
    );
    StageReport {
        differences,
        measured_peak_bytes,
    }
}

fn run_whir(fixture: L1WrapFixture<'_>, expected: WhirExpected) -> WhirReport {
    assert_eq!(
        fixture.commitment_mode, expected.commitment_mode,
        "L1 WHIR parity boundary state differs from the committed bundle"
    );
    let mut differences = Vec::new();
    let whir = &expected.whir;
    let config = ProofProfile::L1Wrap.prover_config(LOG_ROWS as usize, SecurityLevel::Sec100);
    compare(
        "whir-schedule-config",
        &whir.whir_schedule,
        &config.whir_schedule,
        &mut differences,
    );
    let pack_log2 = PACK_LOG2 as u32;
    let cfg = PackedCommitConfig::from_prover_config(
        &config,
        LOG_ROWS + pack_log2,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
    );
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(ARENA_BLOCKS),
        proth120_ntt_log_max_domain: Some(31),
        ..Default::default()
    })
    .unwrap();

    let start = Instant::now();
    let host = L1WrapSetupHost::precompute(&fixture.setup.setup, pack_log2, cfg, &context).unwrap();
    log::info!("L1 WHIR parity: setup precompute {:?}", start.elapsed());
    assert_eq!(
        host.cap(),
        whir.setup_commitment.commitment.cap,
        "L1 WHIR parity setup cap precondition"
    );

    let start = Instant::now();
    let witness = fixture.evaluate_witness();
    log::info!("L1 WHIR parity: witness evaluation {:?}", start.elapsed());
    let columns_count =
        witness.column_major_memory_trace.len() + witness.column_major_witness_trace.len();
    let rows = 1usize << LOG_ROWS;
    let mut holder = TraceHolder::new_without_cosets(
        LOG_ROWS,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        columns_count,
        TreesCacheMode::CacheNone,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    let mut staging = alloc_static_pinned_box_uninit::<PR>(rows).unwrap();
    for (index, column) in witness
        .column_major_memory_trace
        .iter()
        .chain(witness.column_major_witness_trace.iter())
        .enumerate()
    {
        assert_eq!(column.len(), rows, "L1 WHIR parity column {index} length");
        staging.copy_from_slice(column);
        memory_copy_async(
            &mut holder.get_uninit_hypercube_evals_mut()[index * rows..(index + 1) * rows],
            &staging[..],
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    drop(staging);
    drop(witness);

    let host = Arc::new(host);
    let mut source = PackedSetupSource::new(
        Arc::clone(&host),
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    let transfer = single_shot_h2d(
        |transfer| source.schedule_transfer(transfer, &context),
        &context,
    )
    .unwrap();
    transfer.ensure_transferred(&context).unwrap();
    drop(transfer);

    let mut oracle =
        PackedCosetRecomputeOracle::pack_from_columns(holder, pack_log2, &context).unwrap();
    oracle.commit(&cfg, &context).unwrap();
    assert_eq!(
        download(oracle.cap_digests(), [0u32; 8], &context),
        whir.memory_commitment.commitment.cap.cap,
        "L1 WHIR parity merged cap precondition"
    );

    let mut claims = whir.memory_commitment.evals.clone();
    claims.extend_from_slice(&whir.setup_commitment.evals);
    let point = whir
        .original_evaluation_point
        .clone()
        .expect("L1 reference records the original evaluation point");
    let batching_challenge = whir
        .batching_challenge
        .expect("L1 reference records the batching challenge");
    let mut seed = upload(&expected.seed, &context);
    let claims = upload(&claims, &context);
    let point = upload(&point, &context);
    let batching_challenge = upload(&[batching_challenge], &context);
    let shape = L1WhirShape::from_schedule(
        &whir.whir_schedule,
        LOG_ROWS + pack_log2,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        L1_WHIR_TILE_BYTES,
    );
    let stream = context.get_exec_stream();
    stream.synchronize().unwrap();
    let baseline_bytes = context.get_used_mem_current();
    context.reset_used_mem_peak();
    let start_event = CudaEvent::create().unwrap();
    let end_event = CudaEvent::create().unwrap();
    let start = Instant::now();
    start_event.record(stream).unwrap();
    let scheduled = schedule_l1_whir_fold(
        &mut oracle,
        &mut source,
        &mut seed,
        L1WhirInputs {
            claims: &claims,
            base_layer_point: &point,
            batching_challenge: &batching_challenge,
        },
        &whir.whir_schedule,
        &shape,
        &context,
    )
    .unwrap();
    end_event.record(stream).unwrap();
    let enqueue = start.elapsed();
    stream.synchronize().unwrap();
    let wall = start.elapsed();
    let peak_bytes = context.get_used_mem_peak();
    let gpu_ms = elapsed_time(&start_event, &end_event).unwrap();
    let phases = scheduled.phase_times_after_completion().unwrap();
    let proof = scheduled.into_proof_after_completion();

    compare_bytes(
        "whir-setup-commitment",
        &whir.setup_commitment,
        &proof.setup_commitment,
        &mut differences,
    );
    compare_bytes(
        "whir-memory-commitment",
        &whir.memory_commitment,
        &proof.memory_commitment,
        &mut differences,
    );
    compare_bytes(
        "whir-witness-commitment",
        &whir.witness_commitment,
        &proof.witness_commitment,
        &mut differences,
    );
    assert_eq!(
        whir.intermediate_whir_oracles.len(),
        proof.intermediate_whir_oracles.len(),
        "L1 WHIR parity intermediate oracle count"
    );
    for (index, (expected, actual)) in whir
        .intermediate_whir_oracles
        .iter()
        .zip(&proof.intermediate_whir_oracles)
        .enumerate()
    {
        compare_bytes(
            &format!("whir-intermediate-{index}"),
            expected,
            actual,
            &mut differences,
        );
    }
    compare_bytes(
        "whir-ood-samples",
        &whir.ood_samples,
        &proof.ood_samples,
        &mut differences,
    );
    compare_bytes(
        "whir-sumcheck-polys",
        &whir.sumcheck_polys,
        &proof.sumcheck_polys,
        &mut differences,
    );
    if let Some(first) = (0..whir.sumcheck_polys.len().min(proof.sumcheck_polys.len()))
        .find(|&i| whir.sumcheck_polys[i] != proof.sumcheck_polys[i])
    {
        log::error!("L1 WHIR parity: first differing sumcheck polynomial {first}");
    }
    compare_bytes(
        "whir-pow-nonces",
        &whir.pow_nonces,
        &proof.pow_nonces,
        &mut differences,
    );
    compare_bytes(
        "whir-final-monomials",
        &whir.final_monomials,
        &proof.final_monomials,
        &mut differences,
    );
    compare_bytes(
        "whir-schedule",
        &whir.whir_schedule,
        &proof.whir_schedule,
        &mut differences,
    );
    compare_bytes(
        "whir-batching-challenge",
        &whir.batching_challenge,
        &proof.batching_challenge,
        &mut differences,
    );
    compare_bytes(
        "whir-original-evaluation-point",
        &whir.original_evaluation_point,
        &proof.original_evaluation_point,
        &mut differences,
    );
    compare_bytes(
        "whir-batched-opening",
        &whir.batched_opening,
        &proof.batched_opening,
        &mut differences,
    );
    compare_bytes("whir-proof", whir, &proof, &mut differences);
    WhirReport {
        differences,
        baseline_bytes,
        peak_bytes,
        enqueue,
        wall,
        gpu_ms,
        phases,
    }
}

#[test]
#[ignore]
fn l1_wrap_m4_stages_match_reference() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .format_timestamp_millis()
        .try_init();
    let manifest = proof_manifest();
    let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    check_file(&manifest, "l1_bundle.json");
    let bundle: ReferenceBundle = read_typed(&l1_reference_dir().join("l1_bundle.json"));
    assert!(
        matches!(
            bundle.commitment_mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2: PACK_LOG2,
                external_challenges_pow_bits: EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ),
        "L1 reference bundle is not in the EVM-production packed commitment mode"
    );
    let (bin, text) = fsv_feeder(&manifest);
    let nd_words = build_unified_stream(&feeder.setups, &feeder.proof);
    drop(feeder);
    let whir = &bundle.proof.whir_proof;
    let expected = Expected {
        commitment_mode: bundle.commitment_mode,
        top_bits: bundle.proof.inits_and_teardowns_top_bits.clone(),
        setup_cap: whir.setup_commitment.commitment.cap.clone(),
        merged_cap: whir.memory_commitment.commitment.cap.clone(),
        nonce: bundle.proof.lookup_challenges_pow_nonce,
        external: bundle.proof.external_challenges,
    };
    drop(bundle);
    let start = Instant::now();
    let report = with_l1_wrap_fixture(
        CpuExecutionProverConfiguration::default(),
        bin,
        text,
        nd_words,
        None,
        move |fixture| run_stages(fixture, expected),
    );
    log::info!(
        "L1 stage parity: total {:?}, MEASURED_M4_PEAK_BYTES = {}",
        start.elapsed(),
        report.measured_peak_bytes
    );
    assert!(
        report.differences.is_empty(),
        "L1 stage parity differs from the reference in {:?} (see target/l1_stage_parity/)",
        report.differences
    );
}

#[test]
#[ignore]
fn l1_whir_matches_reference() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .format_timestamp_millis()
        .try_init();
    let manifest = proof_manifest();
    let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    check_file(&manifest, "l1_bundle.json");
    let bundle: ReferenceBundle = read_typed(&l1_reference_dir().join("l1_bundle.json"));
    let (bin, text) = fsv_feeder(&manifest);
    let nd_words = build_unified_stream(&feeder.setups, &feeder.proof);
    drop(feeder);
    let expected = WhirExpected {
        commitment_mode: bundle.commitment_mode,
        seed: bundle
            .proof
            .intermediate_transcript_seed
            .expect("L1 reference records the intermediate transcript seed"),
        whir: bundle.proof.whir_proof,
    };
    let start = Instant::now();
    let report = with_l1_wrap_fixture(
        CpuExecutionProverConfiguration::default(),
        bin,
        text,
        nd_words,
        None,
        move |fixture| run_whir(fixture, expected),
    );
    log::info!("L1 WHIR parity: total {:?}", start.elapsed());
    log::info!(
        "L1 WHIR parity: device baseline {} B, absolute peak {} B (peak - baseline {} B)",
        report.baseline_bytes,
        report.peak_bytes,
        report.peak_bytes - report.baseline_bytes
    );
    log::info!(
        "L1 WHIR parity: enqueue {:?}, synchronized wall {:?}, CUDA-event {:.3} ms",
        report.enqueue,
        report.wall,
        report.gpu_ms
    );
    for (name, ms) in &report.phases {
        log::info!("L1 WHIR parity: phase {name} {ms:.3} ms");
    }
    log::info!("L1 WHIR parity: {}", vm_status());
    assert!(
        report.differences.is_empty(),
        "L1 WHIR parity differs from the reference in {:?} (see target/l1_stage_parity/)",
        report.differences
    );
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
#[ignore]
fn cpu_l1_wrap_m6_replay_matches_bundle() {
    let manifest = proof_manifest();
    check_file(&manifest, "l1_bundle.json");
    let bundle: ReferenceBundle = read_typed(&l1_reference_dir().join("l1_bundle.json"));
    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        external_challenges_pow_bits,
        ..
    } = bundle.commitment_mode
    else {
        panic!("L1 reference bundle is not in the packed commitment mode");
    };
    assert_eq!(
        external_challenges_pow_bits, 20,
        "M6 replay lookup PoW bits (M4 effective lookup bits)"
    );
    let config = ProofProfile::L1Wrap.prover_config(LOG_ROWS as usize, SecurityLevel::Sec100);
    let layer0 = &bundle.proof.sumcheck_intermediate_values[&0];
    let base_columns = layer0
        .final_step_evaluations
        .keys()
        .chain(layer0.extra_evaluations_from_caching_relations.keys())
        .filter(|address| {
            matches!(
                address,
                GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::Setup(_)
            )
        })
        .count();
    let base_lde_log2 = config.whir_schedule.base_lde_factor.trailing_zeros() as usize;
    let batched = pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.trace_len_log2 + PACK_LOG2,
        base_lde_log2,
        base_columns,
    );
    assert_eq!(
        (config.trace_len_log2, base_lde_log2, base_columns, batched),
        (21, 6, 114, 16),
        "M6 replay batched proximity PoW inputs"
    );
    let replay = m6_replay::replay_gkr_challenges(
        &bundle,
        m6_replay::ReplayPowBits {
            lookup: external_challenges_pow_bits,
            batched,
        },
    );
    replay.assert_matches_bundle(&bundle);
    for snapshot in &replay.snapshots {
        let claims = match &snapshot.claims {
            m6_replay::ReplayedClaims::Ordered(claims) => claims.len(),
            m6_replay::ReplayedClaims::ByAddress(claims) => claims.len(),
        };
        println!(
            "M6_REPLAY_SNAPSHOT layer={} point={} claims={} seed={} batching={:?}",
            snapshot.layer_idx,
            snapshot.claim_point.len(),
            claims,
            hex(&snapshot.seed),
            snapshot.batching_challenge,
        );
    }
    println!(
        "M6_REPLAY layers={} snapshots={} rounds={} m4_seed={} main0_seed={} z={} extra={:?} final_seed={}",
        replay.round_challenges.len(),
        replay.snapshots.len(),
        replay.round_challenges.values().map(Vec::len).sum::<usize>(),
        hex(&replay.m4_seed),
        hex(&replay.main0_seed),
        replay.z.len(),
        replay.extra,
        hex(&replay.final_seed),
    );
}

#[test]
#[ignore]
fn l1_wrap_m6_stage_parity() {
    m6_stage::run();
}
