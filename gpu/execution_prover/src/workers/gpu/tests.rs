use super::*;
use crate::config::{GpuBackendConfiguration, MemoryPreset};
use crate::upstream::{L1WrapSetup, OperationMode};
use cpu_execution_prover::test_support::{with_l1_wrap_fixture_for, L1WrapFixture};
use cpu_execution_prover::CpuExecutionProverConfiguration;
use crossbeam_channel::unbounded;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use execution_prover::messages::{L1WrapProofRequest, SetupInitializationRequest, WorkRequest};
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover::ExecutionKind;
use execution_prover_model::trace::ChunkedTraceHolder;
use fft::GoodAllocator;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_circuit_prover::l1_wrap::L1Proof;
use gpu_trace::witness::circuit_type::UnrolledCircuitType;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::cell::RefCell;
use std::fs::{self, File};
use std::io::BufReader;
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[derive(Clone, Copy, Debug)]
struct Observed {
    batch_id: u64,
    identity: RequestIdentity,
    direction: Option<AllocationDirection>,
    follower: Option<RequestIdentity>,
}

thread_local! {
    static OBSERVED: RefCell<Vec<Observed>> = const { RefCell::new(Vec::new()) };
}

pub(super) fn observe(state: &RequestState) {
    OBSERVED.with(|observed| {
        observed.borrow_mut().push(Observed {
            batch_id: state.batch_id,
            identity: state.identity(),
            direction: state.direction,
            follower: state.follower,
        })
    });
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
struct ProofManifest {
    format_version: u32,
    fsv: Vec<FsvIdentity>,
    files: Vec<FileIdentity>,
}

#[derive(Deserialize)]
struct FeederArtifact {
    schema_version: u32,
    target: String,
    proof: ProgramProof,
    setups: Setups,
}

#[derive(Deserialize)]
struct Bundle {
    proof: L1Proof,
    operation_mode: OperationMode,
}

fn reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference_2p21")
        })
}

fn keccak_hex(bytes: &[u8]) -> String {
    Keccak256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn read_checked<T: DeserializeOwned>(manifest: &ProofManifest, name: &str) -> T {
    let entry = manifest
        .files
        .iter()
        .find(|file| file.name == name)
        .unwrap_or_else(|| panic!("L1 reference manifest omits {name}"));
    let path = reference_dir().join(name);
    let data = fs::read(&path)
        .unwrap_or_else(|error| panic!("L1 reference read {}: {error}", path.display()));
    assert!(
        data.len() as u64 == entry.bytes && keccak_hex(&data) == entry.keccak256,
        "L1 reference identity differs: {name}"
    );
    serde_json::from_slice(&data)
        .unwrap_or_else(|error| panic!("L1 reference deserialize {name}: {error}"))
}

fn wrap_program(manifest: &ProofManifest) -> (Vec<u32>, Vec<u32>) {
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
        .expect("L1 reference manifest omits the feeder_wrap fsv role");
    assert_eq!(stem, entry.stem, "L1 reference wrap fsv stem differs");
    for (extension, expected) in [
        ("bin", &entry.bin_keccak256),
        ("text", &entry.text_keccak256),
    ] {
        let path = dir.join(format!("{stem}.{extension}"));
        let data = fs::read(&path)
            .unwrap_or_else(|error| panic!("L1 reference fsv read {}: {error}", path.display()));
        assert_eq!(
            keccak_hex(&data),
            *expected,
            "L1 reference wrap fsv identity differs: {extension}"
        );
    }
    load_fsv_program(&dir, program, mode)
}

fn pinned_copy<T: Copy, B: GoodAllocator>(
    holder: &ChunkedTraceHolder<T, B>,
) -> ChunkedTraceHolder<T, A> {
    const LOG_CHUNK_SIZE: u32 = 20;
    let chunks = holder
        .chunks
        .iter()
        .map(|chunk| {
            let bytes = (chunk.len() * size_of::<T>())
                .max(1)
                .next_multiple_of(1 << LOG_CHUNK_SIZE);
            let backing = HostAllocation::alloc(bytes, CudaHostAllocFlags::DEFAULT)
                .expect("pinned host copy of the L1 wrap trace");
            let mut copy = Vec::with_capacity_in(chunk.len(), A::new([backing], LOG_CHUNK_SIZE));
            copy.extend_from_slice(chunk);
            Arc::new(copy)
        })
        .collect();
    ChunkedTraceHolder { chunks }
}

fn clone_setup(setup: &L1WrapSetup) -> L1WrapSetup {
    L1WrapSetup {
        circuit: setup.circuit.clone(),
        table_driver: setup.table_driver.clone(),
        decoder_table: setup.decoder_table.clone(),
        setup: prover::gkr::prover::setup::GKRSetup {
            hypercube_evals: setup.setup.hypercube_evals.clone(),
        },
        trace_len: setup.trace_len,
        rom: setup.rom,
    }
}

fn run_followed_worker(fixture: &L1WrapFixture<'_>, bundle: &Bundle) -> Vec<Observed> {
    const WRAPS: u64 = 3;
    assert_eq!(fixture.circuit_type, CircuitType::L1Wrap21);
    set_device(0).unwrap();
    let precomputations = CircuitPrecomputations::from_canonical(
        CircuitType::L1Wrap21,
        CanonicalCircuitSetup::L1Wrap(clone_setup(fixture.setup)),
        SecurityLevel::Sec100,
        &[ProofProfile::L1Wrap],
    )
    .unwrap();
    let inits_and_teardowns = InitsAndTeardownsTraceHost {
        page_indices: pinned_copy(&fixture.inits_and_teardowns.page_indices),
        values_packed: pinned_copy(&fixture.inits_and_teardowns.values_packed),
        timestamps_packed: pinned_copy(&fixture.inits_and_teardowns.timestamps_packed),
        top_bits: fixture.inits_and_teardowns.top_bits.clone(),
    };
    let tracing_data = pinned_copy(fixture.tracing_data);
    let (requests_sender, requests) = unbounded();
    requests_sender
        .send(Some(WorkRequest::SetupInitialization(
            SetupInitializationRequest {
                batch_id: 0,
                circuit_type: CircuitType::L1Wrap21,
                sequence_id: 0,
                precomputations: precomputations.clone(),
                security_level: SecurityLevel::Sec100,
            },
        )))
        .unwrap();
    for batch_id in 1..=WRAPS {
        requests_sender
            .send(Some(WorkRequest::L1WrapProof(L1WrapProofRequest {
                batch_id,
                circuit_type: CircuitType::L1Wrap21,
                precomputations: precomputations.clone(),
                inits_and_teardowns: inits_and_teardowns.clone(),
                tracing_data: tracing_data.clone(),
                operation_mode: fixture.operation_mode,
            })))
            .unwrap();
    }
    requests_sender.send(None).unwrap();
    requests_sender.send(None).unwrap();
    drop(requests_sender);
    let (initialized_sender, _initialized) = unbounded();
    let (results_sender, results) = unbounded();
    let config = GpuBackendConfiguration {
        memory_preset: MemoryPreset::GiB30,
        ..Default::default()
    }
    .context_config();
    gpu_worker(0, config, initialized_sender, requests, results_sender).unwrap();
    let mut proven = 0;
    for result in results.try_iter().flatten() {
        if let GpuWorkResult::L1WrapProof(result) = result {
            proven += 1;
            assert!(
                serde_json::to_vec(&result.result.operation_mode).unwrap()
                    == serde_json::to_vec(&bundle.operation_mode).unwrap(),
                "L1 wrap operation mode of batch {} differs from the reference",
                result.batch_id
            );
            assert!(
                serde_json::to_vec(&result.result.proof).unwrap()
                    == serde_json::to_vec(&bundle.proof).unwrap(),
                "L1 wrap proof of batch {} differs from the reference bundle",
                result.batch_id
            );
        }
    }
    assert_eq!(proven, WRAPS, "every L1 wrap request must produce a proof");
    OBSERVED.with(|observed| observed.borrow().clone())
}

#[test]
#[ignore = "proves the 2^21 L1 wrap three times on the GPU"]
fn l1_wrap_followed_worker_parity() {
    let _ = env_logger::builder()
        .is_test(true)
        .format_timestamp_millis()
        .try_init();
    let manifest: ProofManifest = {
        let path = reference_dir().join("manifest.json");
        let file = File::open(&path)
            .unwrap_or_else(|error| panic!("L1 reference open {}: {error}", path.display()));
        serde_json::from_reader(BufReader::new(file)).expect("L1 reference manifest")
    };
    assert_eq!(manifest.format_version, 1, "L1 reference manifest format");
    let feeder: FeederArtifact = read_checked(&manifest, "l1_feeder.json");
    assert!(
        feeder.schema_version == 5 && feeder.target == "L1Feeder",
        "L1 reference last-feeder checkpoint must be a schema-5 L1Feeder artifact"
    );
    let bundle: Bundle = read_checked(&manifest, "l1_bundle.json");
    let (bin, text) = wrap_program(&manifest);
    let nd_words = build_unified_stream(&feeder.setups, &feeder.proof);
    drop(feeder);
    let observed = with_l1_wrap_fixture_for(
        ExecutionKind::L1Wrap21,
        CpuExecutionProverConfiguration::default(),
        bin,
        text,
        nd_words,
        None,
        move |fixture| run_followed_worker(&fixture, &bundle),
    );
    let wrap = RequestIdentity {
        circuit_type: CircuitType::L1Wrap21,
        profile: ProofProfile::L1Wrap,
        kind: RequestKind::L1WrapProof,
    };
    let wraps: Vec<_> = observed
        .iter()
        .filter(|entry| entry.identity == wrap)
        .collect();
    for entry in &observed {
        log::info!(
            "observed batch {} {:?} direction {:?} follower {}",
            entry.batch_id,
            entry.identity,
            entry.direction,
            follower_label(entry.follower)
        );
    }
    assert_eq!(
        wraps.iter().map(|entry| entry.batch_id).collect::<Vec<_>>(),
        [1, 2, 3]
    );
    assert_eq!(
        wraps[0].follower,
        Some(wrap),
        "request 1 ran without a wrap follower"
    );
    assert_eq!(
        wraps[1].follower,
        Some(wrap),
        "request 2 ran without a wrap follower"
    );
    assert_eq!(wraps[2].follower, None, "request 3 ran with a follower");
    assert!(
        wraps[0].direction.is_some() && wraps[0].direction != wraps[1].direction,
        "requests 1 and 2 must run in opposite allocation directions, got {:?} and {:?}",
        wraps[0].direction,
        wraps[1].direction
    );
}

fn tagged_partial_trees(circuit_type: CircuitType, profile: ProofProfile) -> MemoryPartialTrees {
    MemoryPartialTrees {
        layout_version: 1,
        circuit_type,
        profile,
        log_domain_size: 22,
        log_lde_factor: 4,
        log_rows_per_leaf: 1,
        log_tree_cap_size: 4,
        reduction_layers: 10,
        columns_count: 104,
        nodes: vec![[7; 8]; 3],
    }
}

const UNIFIED: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified);
const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);

#[test]
fn cpu_proof_partial_trees_follow_the_profile() {
    let trees = proof_partial_trees(
        UNIFIED22,
        ProofProfile::L1Feeder,
        Some(tagged_partial_trees(UNIFIED22, ProofProfile::L1Feeder)),
    )
    .expect("L1Feeder proofs import their trees");
    assert_eq!(trees.layout_version, 1);
    assert_eq!(
        trees.geometry,
        PartialTreesGeometry {
            log_domain_size: 22,
            log_lde_factor: 4,
            log_rows_per_leaf: 1,
            log_tree_cap_size: 4,
            reduction_layers: 10,
            columns_count: 104,
        }
    );
    assert_eq!(trees.nodes, vec![[7; 8]; 3]);
    assert!(proof_partial_trees(UNIFIED, ProofProfile::Standard, None).is_none());
}

#[test]
#[should_panic(
    expected = "Unrolled(Unified22)/L1Feeder proof requires the memory partial trees persisted by its commitment"
)]
fn cpu_feeder_proof_without_partial_trees_panics() {
    proof_partial_trees(UNIFIED22, ProofProfile::L1Feeder, None);
}

#[test]
#[should_panic(expected = "Unrolled(Unified)/Standard proof does not take memory partial trees")]
fn cpu_standard_proof_with_partial_trees_panics() {
    proof_partial_trees(
        UNIFIED,
        ProofProfile::Standard,
        Some(tagged_partial_trees(UNIFIED, ProofProfile::Standard)),
    );
}

#[test]
#[should_panic(expected = "memory partial trees belong to another circuit or profile")]
fn cpu_partial_trees_of_another_circuit_panic() {
    proof_partial_trees(
        UNIFIED22,
        ProofProfile::L1Feeder,
        Some(tagged_partial_trees(UNIFIED, ProofProfile::L1Feeder)),
    );
}
