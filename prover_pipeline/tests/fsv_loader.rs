//! Regression coverage for unpadded canonical FSV loading.

use full_statement_verifier::host_utils::{
    build_unified_stream, compute_end_params, load_fsv_program, native_verify_unified,
    FsvRecursionChain,
};
use std::path::PathBuf;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

fn fsv_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier")
}

#[test]
fn regular_fsv_loader_returns_unpadded_images() {
    let program = FsvProgram::UnifiedRecursionLayer;
    let mode = BlakeMode::Compression;
    let (bin, text) = load_fsv_program(fsv_dir(), program, mode);
    let (_, raw_bin) =
        setups::read_binary(&fsv_dir().join(format!("{}.bin", program.file_stem(mode))));
    let (_, raw_text) =
        setups::read_binary(&fsv_dir().join(format!("{}.text", program.file_stem(mode))));
    assert_eq!(bin, raw_bin);
    assert_eq!(text, raw_text);
    assert!(bin.len() < program.rom().word_size());
    assert!(text.len() < program.rom().word_size());
}

/// Uses production Unified23 dimensions twice. Run with release, deterministic
/// PoW, one test thread, and sufficient available memory (about 75 GiB).
#[test]
#[ignore = "two production Unified23 CPU proofs; minutes and many GiB"]
fn regular_fsv_padding_preserves_proof_bytes() {
    use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
    use execution_prover::{ExecutionKind, MachineType, ProofProfile};
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

    let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/l1_reference_2p21/recursion_unified.json");
    let fixture: prover_pipeline::ProofArtifact =
        serde_json::from_reader(std::fs::File::open(fixture_path).unwrap()).unwrap();
    let stream = build_unified_stream(&fixture.setups, &fixture.proof);
    native_verify_unified(stream.clone(), false);
    let mut chain = FsvRecursionChain::resume(fixture.proof.recursion_chain_preimage.unwrap());
    chain.extend(&compute_end_params(&fixture.setups, fixture.proof.final_pc));

    let (bin, text) = load_fsv_program(
        fsv_dir(),
        FsvProgram::UnifiedRecursionLayer,
        BlakeMode::Compression,
    );
    let prove = |padded: bool| {
        let config = CpuExecutionProverConfiguration {
            max_thread_pool_threads: Some(24),
            ram_config: riscv_transpiler::jit::JitRunnerRam::Tiny,
            ..Default::default()
        };
        let mut prover = CpuExecutionProver::with_configuration(config);
        let mut binary = bin.clone();
        let mut code = text.clone();
        if padded {
            setups::pad_bytecode_for_proving(&mut binary);
            setups::pad_bytecode_for_proving(&mut code);
        }
        let handle = prover.add_binary(
            ExecutionKind::Unified,
            MachineType::Reduced,
            binary,
            code,
            None,
            &[ProofProfile::Standard],
        );
        let result = prover.commit_memory_and_prove(
            0,
            &handle,
            QuasiUARTSource::new_with_reads(stream.clone()),
            ProofProfile::Standard,
        );
        let artifacts = prover.program_artifacts(&handle, ProofProfile::Standard);
        let (mut proof, setups) = program_prover::assemble_program_proof(&artifacts, result);
        proof.set_recursion_chain(&chain);
        let end_params = compute_end_params(&setups, proof.final_pc);
        let native_output = native_verify_unified(build_unified_stream(&setups, &proof), false);
        (
            serde_json::to_vec(&proof).unwrap(),
            serde_json::to_vec(&setups).unwrap(),
            end_params,
            native_output,
        )
    };
    let old_padded = prove(true);
    let new_unpadded = prove(false);
    assert_eq!(
        new_unpadded.0, old_padded.0,
        "regular recursive proof bytes changed"
    );
    assert_eq!(new_unpadded.1, old_padded.1, "trusted setup bytes changed");
    assert_eq!(new_unpadded.2, old_padded.2, "chain end parameters changed");
    assert_eq!(new_unpadded.3, old_padded.3, "native output changed");
    println!("padded/unpadded regular recursion: identical {} proof bytes, {} setup bytes, end parameters {:?}, and all 16 native output words",
        new_unpadded.0.len(), new_unpadded.1.len(), new_unpadded.2);
}
