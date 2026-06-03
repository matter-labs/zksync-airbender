use super::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration};
use crate::upstream::{read_binary, SecurityLevel};
use gpu_core::primitives::machine_type::MachineType;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use serial_test::serial;

fn test_artifact(relative_path: &str) -> std::path::PathBuf {
    // Workspace-root-relative paths; crate is at gpu/circuit_prover/, so two "..".
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative_path)
}

#[test]
#[cfg(not(no_cuda))]
#[ignore]
#[serial]
fn test_execution_prover() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Trace)
        .try_init();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let (_, binary_image) = read_binary(&test_artifact("examples/hashed_fibonacci/app.bin"));
    let (_, text_section) = read_binary(&test_artifact("examples/hashed_fibonacci/app.text"));
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        None,
    );
    // hashed_fibonacci's first ND read is `n` (register-only fibonacci
    // iterations — no memory accesses, so chunk-fill never fires
    // intermediate snapshots); the second is `h` (Blake hashes — heavy
    // mem + delegation). Pick small values that exercise the full
    // pipeline (mem ops + delegation) without producing a multi-GB
    // single snapshot.
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![100, 5]);
    let _base_layer_result = prover.commit_memory_and_prove(0, &handle, non_determinism_source);
    drop(prover);
}

#[test]
#[cfg(not(no_cuda))]
#[ignore]
#[serial]
fn test_execution_prover_commit_then_prove() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Trace)
        .try_init();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let (_, binary_image) = read_binary(&test_artifact("examples/hashed_fibonacci/app.bin"));
    let (_, text_section) = read_binary(&test_artifact("examples/hashed_fibonacci/app.text"));
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        None,
    );
    // QuasiUARTSource reads are deterministic — feed the same value sequence
    // to the commit phase and the prove phase. Equivalent results should
    // match `commit_memory_and_prove` on a single source.
    let nd_inputs = vec![100u32, 5];
    let commit_source = QuasiUARTSource::new_with_reads(nd_inputs.clone());
    let memory_commitment = prover.commit_memory(0, &handle, commit_source);
    let prove_source = QuasiUARTSource::new_with_reads(nd_inputs);
    let prove_result = prover.prove(0, memory_commitment, prove_source);
    drop(prove_result);
    drop(prover);
}

#[test]
fn rejects_unsupported_security_level_in_configuration() {
    let mut configuration = ExecutionProverConfiguration::default();
    configuration.security_level = SecurityLevel::Sec100;

    let err = ExecutionProver::with_configuration(configuration)
        .err()
        .expect("Sec100 should be rejected before GPU prover construction");

    assert_eq!(err.requested, SecurityLevel::Sec100);
    assert_eq!(
        ExecutionProverConfiguration::supported_security_levels(),
        &[SecurityLevel::Sec80],
    );
}
