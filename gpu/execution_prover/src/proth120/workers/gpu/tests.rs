use super::*;
use crate::config::{GpuBackendConfiguration, MemoryPreset};
use crate::upstream::{L1WrapSetup, OperationMode};
use crate::workers::gpu::gpu_worker;
use cpu_execution_prover::test_support::{with_l1_wrap_fixture, L1WrapFixture};
use cpu_execution_prover::CpuExecutionProverConfiguration;
use crossbeam_channel::unbounded;
use era_cudart::device::set_device;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use execution_prover::messages::{L1WrapProofRequest, SetupInitializationRequest, WorkRequest};
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::trace::ChunkedTraceHolder;
use fft::GoodAllocator;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_exact};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_circuit_prover::proth120::L1Proof;
use gpu_trace::witness::trace_unrolled::InitsAndTeardownsTraceHost;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use setups::Setups;
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile};

#[derive(Deserialize)]
struct CompressionArtifact {
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

#[derive(Deserialize)]
struct L1Artifact {
    l1: Bundle,
}

fn read_reference<T: DeserializeOwned>(chain: &str) -> T {
    proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        chain,
    ))
}

fn wrap_program() -> (Vec<u32>, Vec<u32>) {
    let dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tools/gkr_verifier/full_statement_verifiers")
        });
    load_fsv_exact(
        &dir,
        &FsvDescriptor::pessimistic_compression(FsvProfile::CompressionFinalWrap),
    )
    .into_words()
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

fn run_followed_worker(fixture: &L1WrapFixture<'_>, bundle: &Bundle) {
    const WRAPS: u64 = 3;
    assert_eq!(fixture.circuit_type, CircuitType::L1Wrap);
    set_device(0).unwrap();
    let precomputations = CircuitPrecomputations::from_canonical(
        CircuitType::L1Wrap,
        CanonicalCircuitSetup::L1Wrap(clone_setup(fixture.setup)),
        execution_prover::config::SoundnessMode::PessimisticConjecture,
        &[ProofProfile::L1Wrap],
    );
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
                circuit_type: CircuitType::L1Wrap,
                sequence_id: 0,
                precomputations: precomputations.clone(),
            },
        )))
        .unwrap();
    for batch_id in 1..=WRAPS {
        requests_sender
            .send(Some(WorkRequest::L1WrapProof(L1WrapProofRequest {
                batch_id,
                circuit_type: CircuitType::L1Wrap,
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
    let mut proven = Vec::new();
    for result in results.try_iter().flatten() {
        if let GpuWorkResult::L1WrapProof(result) = result {
            proven.push(result.batch_id);
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
    assert!(
        proven.into_iter().eq(1..=WRAPS),
        "every L1 wrap request must produce a proof in batch order"
    );
}

#[test]
#[ignore = "proves the 2^21 L1 wrap three times on the GPU"]
fn l1_wrap_followed_worker_pessimistic_parity() {
    let _ = env_logger::builder()
        .is_test(true)
        .format_timestamp_millis()
        .try_init();
    let compression: CompressionArtifact = read_reference("compression");
    assert!(
        compression.schema_version == 5 && compression.target == "Compression",
        "L1 reference last-compression checkpoint must be a schema-5 Compression artifact"
    );
    let L1Artifact { l1: bundle } = read_reference("l1");
    let (bin, text) = wrap_program();
    let nd_words = build_unified_stream(
        &compression.setups,
        &compression.proof,
        BlakeMode::BlakeSpecialOpcodes,
    );
    drop(compression);
    with_l1_wrap_fixture(
        CpuExecutionProverConfiguration::default(),
        bin,
        text,
        nd_words,
        None,
        move |fixture| run_followed_worker(&fixture, &bundle),
    );
}
