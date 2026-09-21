//! CPU program proofs and native verification. Delegation cases assert that
//! their workload actually delegates.
//!
//! Ignored by default because they use production circuit dimensions.

use cpu_execution_prover::{
    CpuExecutionProver, CpuExecutionProverConfiguration, ExecutionKind, MachineType,
};
use execution_prover_model::circuit_type::DelegationCircuitType;
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

fn workload(directory: &str, stem: &str) -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let base = root.join("examples").join(directory);
    let (_, binary) = setups::read_and_pad_binary(&base.join(format!("{stem}.bin")));
    let (_, text) = setups::read_and_pad_binary(&base.join(format!("{stem}.text")));
    (binary, text)
}

fn prove(
    execution_kind: ExecutionKind,
    machine_type: MachineType,
    workload: (Vec<u32>, Vec<u32>),
    inputs: Vec<u32>,
) -> (ProgramProof, setups::Setups) {
    let mut prover =
        CpuExecutionProver::with_configuration(CpuExecutionProverConfiguration::default())
            .expect("the CPU defaults must be a valid configuration");
    let (binary, text) = workload;
    let handle = prover.add_binary(execution_kind, machine_type, binary, text, None);
    let result =
        prover.commit_memory_and_prove(1, &handle, QuasiUARTSource::new_with_reads(inputs));
    let artifacts = prover.program_artifacts(&handle);
    program_prover::assemble_program_proof(&artifacts, result)
}

fn assert_verifies_unrolled(proof: &ProgramProof, setups: &setups::Setups) {
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(setups, proof);
    let output = full_statement_verifier::host_utils::native_verify_unrolled(stream, true);
    assert_ne!(
        output, [0u32; 16],
        "native verification produced an empty output"
    );
}

fn assert_delegated(proof: &ProgramProof, delegation: DelegationCircuitType) {
    let key = delegation.get_delegation_type_id() as u32;
    let proofs = proof
        .delegation_proofs
        .get(&key)
        .unwrap_or_else(|| panic!("{delegation:?} produced no delegation proofs at all"));
    assert!(
        !proofs.is_empty(),
        "{delegation:?} is registered but was never called: this workload does not exercise it"
    );
}

#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn the_cpu_prover_proves_and_natively_verifies_a_real_binary() {
    let (proof, setups) = prove(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        workload("hashed_fibonacci", "app"),
        vec![100, 5],
    );
    assert_verifies_unrolled(&proof, &setups);
}

#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn a_blake2_with_compression_workload_delegates_and_verifies() {
    let (proof, setups) = prove(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        workload("hashed_fibonacci", "app_blake2_with_compression"),
        vec![100, 5],
    );
    assert_delegated(&proof, DelegationCircuitType::Blake2WithCompression);
    assert_verifies_unrolled(&proof, &setups);
}

#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn a_bigint_workload_delegates_and_verifies() {
    let (proof, setups) = prove(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        workload("bigint_with_control", "app"),
        // Reads no non-determinism: the example builds its 256-bit operands
        // inline (see its README and src/main.rs).
        vec![],
    );
    assert_delegated(&proof, DelegationCircuitType::BigIntWithControl);
    assert_verifies_unrolled(&proof, &setups);
}

#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn a_keccak_workload_delegates_and_verifies() {
    let (proof, setups) = prove(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        workload("keccak", "app"),
        // Reads no non-determinism: the example runs a built-in Keccak-f1600
        // sanity suite against a known test vector.
        vec![],
    );
    assert_delegated(&proof, DelegationCircuitType::KeccakSpecial5);
    assert_verifies_unrolled(&proof, &setups);
}

/// Unified execution: a different circuit shape, a different verifier, and the
/// inline inits-and-teardowns the unrolled path carries separately.
#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn a_unified_execution_proves_and_natively_verifies() {
    let (proof, setups) = prove(
        ExecutionKind::Unified,
        MachineType::Reduced,
        workload("multi_family_smoke", "app_blake2_with_compression"),
        vec![50, 0xDEAD_BEEF],
    );
    assert!(
        proof.num_it_circuits.is_some(),
        "a unified proof carries its inits-and-teardowns circuit count"
    );
    let stream = full_statement_verifier::host_utils::build_unified_stream(&setups, &proof);
    let output = full_statement_verifier::host_utils::native_verify_unified(stream, true);
    assert_ne!(
        output, [0u32; 16],
        "native verification produced an empty output"
    );
}
