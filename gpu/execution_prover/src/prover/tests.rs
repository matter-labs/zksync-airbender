use super::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration, ProveResult};
use crate::upstream::{read_binary, SecurityLevel};
use gpu_core::primitives::machine_type::MachineType;
use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

fn test_artifact(relative_path: &str) -> std::path::PathBuf {
    // Workspace-root-relative paths; crate is at gpu/execution_prover/, so two "..".
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative_path)
}

#[cfg(not(no_cuda))]
fn init_test_logger() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Trace)
        .try_init();
}

/// Shared e2e driver: register one binary, run the combined
/// commit-memory + prove flow on it, and return the result for
/// test-specific assertions.
#[cfg(not(no_cuda))]
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

#[cfg(not(no_cuda))]
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
#[cfg(not(no_cuda))]
#[ignore]
fn test_execution_prover() {
    // hashed_fibonacci's first ND read is `n` (register-only fibonacci
    // iterations — no memory accesses, so chunk-fill never fires
    // intermediate snapshots); the second is `h` (Blake hashes — heavy
    // mem ops). Pick small values that exercise the full pipeline
    // without producing a multi-GB single snapshot. NOTE: `app.bin` is
    // the default (feature-less) build of the example, whose blake2s is
    // pure software — this test intentionally covers the
    // NO-delegation path; the delegation-enabled variants are covered
    // by the dedicated tests below.
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
#[cfg(not(no_cuda))]
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

/// Same workload as `test_execution_prover`, but the binary is built with the
/// `blake2_with_compression` feature, so every blake round fires the
/// Blake2WithCompression delegation CSR — covering the delegation
/// commit + prove dispatch end to end.
#[test]
#[cfg(not(no_cuda))]
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

/// As above, with the `blake2_g_function` build — fires the Blake2GFunction
/// delegation CSR instead.
///
/// KNOWN BLOCKER: the transpiler JIT has no Blake2GFunction delegation
/// implementation (`riscv_transpiler/src/jit/impls.rs` `Op::ZicsrDelegation`
/// panics with "Unknown CSR 1992"; `jit/delegations/` has blake/bigint/keccak
/// only). This test documents the gap and validates the fix once JIT support
/// lands — expect it to abort until then.
#[test]
#[cfg(not(no_cuda))]
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

/// Unified (reduced-machine) execution over the `multi_family_smoke` workload
/// gpu_circuit_prover's unified GPU tests use, with the same ND inputs
/// (`n` = loop/cycle target, `seed`). Uses the blake2_with_compression
/// variant rather than gpu_circuit_prover's blake2_g_function one because the
/// transpiler JIT only implements the Blake2WithCompression delegation (see
/// `test_execution_prover_blake2_g_function_delegation`). Covers the
/// `ExecutionKind::Unified` dispatch path end to end: unified circuit family
/// proofs plus the delegation proofs the smoke workload fires.
#[test]
#[cfg(not(no_cuda))]
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
/// moment upstream adds a level the GPU stack does not handle, forcing an
/// explicit decision instead of a silent `validate()` rejection at runtime.
#[test]
fn cpu_all_security_levels_supported_in_configuration() {
    assert_eq!(
        ExecutionProverConfiguration::supported_security_levels(),
        SecurityLevel::ALL,
    );
    for &level in SecurityLevel::ALL {
        let configuration = ExecutionProverConfiguration {
            security_level: level,
            ..Default::default()
        };
        assert!(
            configuration.validate().is_ok(),
            "{level:?} must pass configuration validation"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[ignore]
fn test_setup_hosts_initialized_by_constructor_and_add_binary() {
    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    for (circuit_type, precomputations) in prover.common_precomputations.iter() {
        assert!(
            precomputations.setup_host.is_initialized(),
            "{circuit_type:?} setup lock not filled by the constructor batch"
        );
        let expected_columns = match circuit_type {
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => false,
            _ => true,
        };
        assert_eq!(
            precomputations.setup_host.get_initialized().is_some(),
            expected_columns,
            "{circuit_type:?} initialized-absence state is wrong"
        );
    }
    let (_, binary_image) = read_binary(&test_artifact("examples/hashed_fibonacci/app.bin"));
    let (_, text_section) = read_binary(&test_artifact("examples/hashed_fibonacci/app.text"));
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        None,
    );
    for (circuit_type, precomputations) in prover.binary_holders[&0].precomputations.iter() {
        assert!(
            precomputations
                .setup_host
                .get_initialized()
                .is_some(),
            "{circuit_type:?} family setup not initialized by add_binary"
        );
    }
    let artifacts = prover.program_artifacts(&handle);
    assert!(!artifacts.riscv_families.is_empty());
    for (family_idx, artifact) in artifacts.riscv_families.iter() {
        assert!(
            !artifact.setup_cap.cap.is_empty(),
            "family {family_idx} artifact carries an empty setup cap"
        );
    }
}
