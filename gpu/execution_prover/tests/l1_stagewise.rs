#![cfg(all(not(no_cuda), feature = "deterministic_pow"))]

gpu_core::force_serial_libtest!();

use cpu_execution_prover::test_support::with_l1_wrap_fixture;
use cpu_execution_prover::CpuExecutionProverConfiguration;
use execution_prover::config::SoundnessMode;
use execution_prover::{OperationMode, ProofProfile};
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_exact};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_circuit_prover::l1_wrap::{
    prove_stagewise, L1Proof, L1WrapConstantsHost, L1WrapGeometry, L1WrapInputs,
    L1_WRAP_NTT_LOG_MAX_DOMAIN,
};
use gpu_circuit_prover::proof::memory_policy::presets;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_gkr::proth120::backward::prepare_dr_tail_resources_pr;
use gpu_gkr::proth120::packed_challenges::{
    transcript_prefix_words, PackedChallengeConfig, PACKED_CHALLENGE_DRAWS,
};
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::setup::L1WrapSetupHost;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::packed::PackedCommitConfig;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;
use prover::gkr::prover::transcript_utils::draw_random_field_els;
use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::EXPLICIT_OUTPUT_LOG2;
use prover::transcript::{Keccak256Transcript, Transcript};
use serde::de::DeserializeOwned;
use serde::Deserialize;
use setups::Setups;
use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile};

#[path = "../../circuit_prover/src/tests/stagewise_replay.rs"]
mod replay;

#[derive(Deserialize)]
struct ReferenceBundle {
    proof: L1Proof,
    operation_mode: OperationMode,
}

#[derive(Deserialize)]
struct CompressionCheckpoint {
    proof: ProgramProof,
    setups: Setups,
}

fn read_typed<T: DeserializeOwned>(filename: &Path) -> T {
    serde_json::from_reader(BufReader::new(File::open(filename).unwrap())).unwrap()
}

/// Local gate after wrap scheduling or GKR transcript changes:
/// `cargo test -p gpu_execution_prover --test l1_stagewise --release -- --ignored --exact l1_wrap_stagewise_pessimistic_conjecture`
#[test]
#[ignore]
fn l1_wrap_stagewise_pessimistic_conjecture() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let references = std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("../../prover_pipeline/fixtures/l1_reference_2p21"));
    let reference: ReferenceBundle = read_typed(&references.join("l1_bundle.json"));
    let compression: CompressionCheckpoint = read_typed(&references.join("compression.json"));
    let nd_words = build_unified_stream(
        &compression.setups,
        &compression.proof,
        BlakeMode::BlakeSpecialOpcodes,
    );
    drop(compression);
    let fsv_dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("../../tools/gkr_verifier/full_statement_verifiers"));
    let (binary, text) = load_fsv_exact(
        &fsv_dir,
        &FsvDescriptor::compression(FsvProfile::CompressionFinalWrap),
    )
    .into_words();
    with_l1_wrap_fixture(
        CpuExecutionProverConfiguration {
            max_thread_pool_threads: Some(8),
            replay_worker_threads_count: 1,
            expected_concurrent_jobs: 1,
            soundness_mode: SoundnessMode::PessimisticConjecture,
            ..Default::default()
        },
        binary,
        text,
        nd_words,
        None,
        move |fixture| {
            let circuit_type = fixture.circuit_type;
            let config = ProofProfile::L1Wrap.prover_config(
                fixture.setup.trace_len.trailing_zeros() as usize,
                SoundnessMode::PessimisticConjecture,
            );
            let geometry =
                L1WrapGeometry::new(circuit_type, &config, &fixture.setup.circuit, fixture.setup);
            let circuit = Arc::new(fixture.setup.circuit.clone());
            let programs = Arc::new(GkrProgramsPr::compile(circuit_type, Arc::clone(&circuit)));
            let context_config = ProverContextConfig {
                device_allocation_blocks_count: Some(
                    (21usize << 30) >> ProverContextConfig::default().allocator_block_log_size,
                ),
                host_allocator_blocks_count: (256usize << 20)
                    >> ProverContextConfig::default().host_allocator_block_log_size,
                inputs_reserve_bytes: presets::INPUTS_RESERVE_BYTES,
                h2d_staging_bytes: presets::H2D_STAGING_BYTES,
                proth120_ntt_log_max_domain: Some(L1_WRAP_NTT_LOG_MAX_DOMAIN),
                ..Default::default()
            };
            let context = ProverContext::new(&context_config).unwrap();
            let setup_host = Arc::new(
                L1WrapSetupHost::precompute(
                    &fixture.setup.setup,
                    geometry.pack_log2,
                    PackedCommitConfig::from_prover_config(
                        &config,
                        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
                    ),
                    &context,
                )
                .unwrap(),
            );
            let constants = Arc::new(
                L1WrapConstantsHost::new(&programs, &circuit, &config, &geometry).unwrap(),
            );
            let decoder: Vec<ExecutorFamilyDecoderData> = fixture
                .setup
                .decoder_table
                .iter()
                .map(|row| row.unwrap_or_default().into())
                .collect();
            let decoder = Some(Arc::new(
                alloc_static_pinned_box_from_slice(&decoder).unwrap(),
            ));
            let partial_trees = presets::l1_wrap::PARTIAL_TREES;
            let mut inputs = L1WrapInputs::new(
                &geometry,
                decoder,
                fixture.inits_and_teardowns.clone(),
                fixture.tracing_data.clone(),
                setup_host,
                partial_trees.setup,
                constants,
                &fixture.operation_mode,
                &context,
            )
            .unwrap();
            inputs.schedule(&context).unwrap();
            let tail =
                prepare_dr_tail_resources_pr(&programs, EXPLICIT_OUTPUT_LOG2 as u32, &context);
            let job = prove_stagewise(
                &programs,
                &circuit,
                &geometry,
                &config,
                fixture.operation_mode.clone(),
                inputs,
                &tail,
                partial_trees,
                &context,
            )
            .unwrap();
            let (actual, snapshots) = job.finish_stagewise().unwrap();
            let expected = &reference.proof;
            for (label, actual, expected) in [
                (
                    "setup",
                    &actual.proof.whir_proof.setup_commitment,
                    &expected.whir_proof.setup_commitment,
                ),
                (
                    "memory+witness",
                    &actual.proof.whir_proof.memory_commitment,
                    &expected.whir_proof.memory_commitment,
                ),
            ] {
                assert_eq!(
                    actual.commitment.cap, expected.commitment.cap,
                    "{label} cap"
                );
            }
            assert_eq!(
                actual.proof.final_explicit_evaluations,
                expected.final_explicit_evaluations
            );

            let mut words = transcript_prefix_words(
                &reference.operation_mode,
                &expected.inits_and_teardowns_top_bits,
            );
            flatten_merkle_caps_iter_into(
                [
                    expected.whir_proof.setup_commitment.commitment.cap.clone(),
                    expected.whir_proof.memory_commitment.commitment.cap.clone(),
                ]
                .into_iter(),
                &mut words,
            );
            let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&words);
            let challenge_config =
                PackedChallengeConfig::new(&circuit, &config, &reference.operation_mode, true);
            <Keccak256Transcript as Transcript<PR, PR>>::verify_pow(
                &mut seed,
                expected.lookup_challenges_pow_nonce,
                challenge_config.pow_bits,
            );
            draw_random_field_els::<PR, PR, Keccak256Transcript>(&mut seed, PACKED_CHALLENGE_DRAWS);
            let expected_snapshots =
                replay::replay_expected_snapshots::<PR, PR, Keccak256Transcript, _>(
                    expected,
                    seed,
                    programs.runtime_circuit.layers.len(),
                );
            replay::assert_stage_snapshots(&snapshots, &expected_snapshots);
            assert_eq!(
                serde_json::to_vec(&actual.proof).unwrap(),
                serde_json::to_vec(expected).unwrap(),
                "final wrap proof",
            );
            assert_eq!(
                serde_json::to_vec(&actual.operation_mode).unwrap(),
                serde_json::to_vec(&reference.operation_mode).unwrap(),
            );
        },
    );
}
