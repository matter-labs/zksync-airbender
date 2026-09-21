//! GPU execution end-to-end tests: these drive the real `ExecutionProver`
//! against a device, so they live with the GPU backend rather than in the
//! backend-independent crate.

use era_cudart_sys::CudaError;
use gpu_execution_prover::MachineType;
use gpu_execution_prover::GPU_SUPPORTED_SECURITY_LEVELS;
use gpu_execution_prover::{
    ExecutionKind, ExecutionProver, ExecutionProverConfiguration, GpuBackendError, ProveResult,
};
use gpu_trace::witness::circuit_type::{DelegationCircuitType, UnrolledCircuitType};
use prover::definitions::SecurityLevel;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use setups::read_binary;

/// Workspace-root-relative; this crate is at `gpu/execution_prover/`.
fn test_artifact(relative_path: &str) -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative_path)
}

fn init_test_logger() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Trace)
        .try_init();
}

/// Shared e2e driver: register one binary and run the combined
/// commit-memory + prove flow on it.
fn commit_and_prove_binary(
    execution_kind: ExecutionKind,
    machine_type: MachineType,
    binary_path: &str,
    text_path: &str,
    non_determinism_reads: Vec<u32>,
) -> ProveResult {
    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let (_, binary_image) = read_binary(&test_artifact(binary_path));
    let (_, text_section) = read_binary(&test_artifact(text_path));
    let handle = prover.add_binary(
        execution_kind,
        machine_type,
        binary_image,
        text_section,
        None,
    );
    let non_determinism_source = QuasiUARTSource::new_with_reads(non_determinism_reads);
    prover.commit_memory_and_prove(0, &handle, non_determinism_source)
}

fn assert_delegation_proofs_present(result: &ProveResult, delegation_type: DelegationCircuitType) {
    let delegation_id = delegation_type.get_delegation_type_id() as u32;
    let proofs = result
        .delegation_proofs
        .get(&delegation_id)
        .unwrap_or_else(|| {
            panic!(
                "expected delegation proofs for {delegation_type:?} (id {delegation_id}), got families {:?}",
                result.delegation_proofs.keys().collect::<Vec<_>>()
            )
        });
    assert!(
        !proofs.is_empty(),
        "delegation proof list for {delegation_type:?} is empty"
    );
}

#[test]
#[ignore]
fn test_execution_prover() {
    // hashed_fibonacci's ND reads are `n` (register-only iterations) and `h`
    // (Blake hashes — heavy mem ops); small values exercise the full pipeline
    // without a multi-GB snapshot. `app.bin` is the feature-less build, whose
    // blake2s is pure software, so this covers the NO-delegation path.
    let result = commit_and_prove_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        "examples/hashed_fibonacci/app.bin",
        "examples/hashed_fibonacci/app.text",
        vec![100, 5],
    );
    assert!(
        result.delegation_proofs.values().all(|v| v.is_empty()),
        "app.bin is built without delegation features and must produce no delegation proofs"
    );
}

#[test]
#[ignore]
fn test_execution_prover_commit_then_prove() {
    init_test_logger();
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
    // QuasiUARTSource reads are deterministic, so the same value sequence
    // feeds both phases and must match `commit_memory_and_prove`.
    let nd_inputs = vec![100u32, 5];
    let commit_source = QuasiUARTSource::new_with_reads(nd_inputs.clone());
    let memory_commitment = prover.commit_memory(0, &handle, commit_source);
    let top_bits = memory_commitment.inits_and_teardowns_top_bits.clone();
    assert_eq!(
        top_bits.len(),
        memory_commitment.inits_and_teardowns_memory_caps.len()
    );
    assert!(!top_bits.is_empty());
    let prove_source = QuasiUARTSource::new_with_reads(nd_inputs);
    let prove_result = prover.prove(0, memory_commitment, prove_source);
    assert_eq!(
        top_bits.len(),
        prove_result.inits_and_teardowns_proofs.len()
    );
    for (sequence_id, proof) in prove_result.inits_and_teardowns_proofs.iter().enumerate() {
        assert_eq!(proof.inits_and_teardowns_top_bits, top_bits[&sequence_id]);
    }
    drop(prove_result);
    drop(prover);
}

/// Same workload as `test_execution_prover`, built with the
/// `blake2_with_compression` feature so every blake round fires the
/// Blake2WithCompression delegation CSR.
#[test]
#[ignore]
fn test_execution_prover_blake2_with_compression_delegation() {
    let result = commit_and_prove_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        "examples/hashed_fibonacci/app_blake2_with_compression.bin",
        "examples/hashed_fibonacci/app_blake2_with_compression.text",
        vec![100, 5],
    );
    assert_delegation_proofs_present(&result, DelegationCircuitType::Blake2WithCompression);
}

/// As above, with the `blake2_g_function` build.
///
/// KNOWN BLOCKER: the transpiler JIT has no Blake2GFunction delegation
/// (`riscv_transpiler/src/jit/impls.rs` `Op::ZicsrDelegation` panics with
/// "Unknown CSR 1992"), so this aborts until that lands.
#[test]
#[ignore]
fn test_execution_prover_blake2_g_function_delegation() {
    let result = commit_and_prove_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        "examples/hashed_fibonacci/app_blake2_g_function.bin",
        "examples/hashed_fibonacci/app_blake2_g_function.text",
        vec![100, 5],
    );
    assert_delegation_proofs_present(&result, DelegationCircuitType::Blake2GFunction);
}

/// Unified execution over `multi_family_smoke` with blake2_with_compression
/// and non-determinism inputs `(n, seed)`.
#[test]
#[ignore]
fn test_execution_prover_unified() {
    let result = commit_and_prove_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        "examples/multi_family_smoke/app_blake2_with_compression.bin",
        "examples/multi_family_smoke/app_blake2_with_compression.text",
        vec![50, 0xDEAD_BEEF],
    );
    let unified_family_idx = UnrolledCircuitType::Unified.get_family_idx();
    let unified_proofs = result
        .circuit_families_proofs
        .get(&unified_family_idx)
        .expect("unified execution must produce proofs for the unified circuit family");
    assert!(
        !unified_proofs.is_empty(),
        "unified circuit family proof list is empty"
    );
    assert_delegation_proofs_present(&result, DelegationCircuitType::Blake2WithCompression);
}

/// Every upstream `SecurityLevel` is currently GPU-supported; this fails the
/// moment upstream adds one the GPU stack does not handle, forcing a decision
/// instead of a runtime rejection. The support list is the backend's, so it is
/// asserted directly; shared `validate()` deliberately admits every level and
/// is checked separately rather than being credited with the GPU check.
#[test]
fn cpu_all_security_levels_supported_by_the_gpu_backend() {
    assert_eq!(GPU_SUPPORTED_SECURITY_LEVELS, SecurityLevel::ALL);
    for &level in SecurityLevel::ALL {
        let configuration = ExecutionProverConfiguration {
            security_level: level,
            ..Default::default()
        };
        assert!(
            configuration.validate().is_ok(),
            "{level:?} must pass shared configuration validation"
        );
    }
}

/// The point of keeping the CUDA status typed: a caller can still read it back
/// after the error has been boxed into the backend-neutral one.
#[test]
fn cpu_backend_errors_survive_as_an_execution_prover_error_source() {
    let startup = GpuBackendError::cuda(
        "GPU worker 3 failed to initialize",
        CudaError::ErrorInvalidValue,
    );
    let error = execution_prover::ExecutionProverError::backend_initialization("gpu", startup);

    let source = std::error::Error::source(&error).expect("source chain preserved");
    let downcast = source
        .downcast_ref::<GpuBackendError>()
        .expect("the typed GPU error survives boxing");
    assert_eq!(downcast.source, Some(CudaError::ErrorInvalidValue));
    assert_eq!(
        downcast.detail,
        "GPU worker 3 failed to initialize: ErrorInvalidValue"
    );
    assert!(error.to_string().contains("gpu"));
}

gpu_core::force_serial_libtest!();
