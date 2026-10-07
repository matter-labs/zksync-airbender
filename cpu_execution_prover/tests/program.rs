//! CPU program proofs and native verification. Delegation cases assert that
//! their workload actually delegates.
//!
//! Ignored by default because they use production circuit dimensions.

#![feature(allocator_api)]

use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
use execution_prover::{CommitmentMode, ExecutionKind, MachineType};
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
        CpuExecutionProver::with_configuration(CpuExecutionProverConfiguration::default());
    let (binary, text) = workload;
    let handle = prover.add_binary(
        execution_kind,
        machine_type,
        binary,
        text,
        None,
        &[execution_prover::ProofProfile::Standard],
    );
    let result = prover.commit_memory_and_prove(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(inputs),
        CommitmentMode::SeparateMemoryAndWitness,
        execution_prover::ProofProfile::Standard,
    );
    let artifacts = prover.program_artifacts(&handle, execution_prover::ProofProfile::Standard);
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
    assert_delegated(&proof, DelegationCircuitType::KeccakThetaRho);
    assert_delegated(&proof, DelegationCircuitType::KeccakColumnParity);
    assert_delegated(&proof, DelegationCircuitType::KeccakChi5);
    assert_verifies_unrolled(&proof, &setups);
}

#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn legacy_prover_keccak_f1600_workload_delegates_and_verifies() {
    let (binary, text) = workload("keccak", "app");
    let worker = worker::Worker::new();
    let (proof, setups) = program_prover::unrolled::prove_unrolled_execution_with_replayer::<
        riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly,
        std::alloc::Global,
        _,
        _,
    >(
        1 << 29,
        &binary,
        &text,
        true,
        QuasiUARTSource::new_with_reads(vec![]),
        1 << 30,
        &worker,
        prover::definitions::SecurityLevel::Sec100,
        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
        &prover::gkr::prover::DefaultBabyBearBackend::default(),
        &prover::gkr::prover::DefaultBabyBearGKRBackend::default(),
    );
    assert_delegated(&proof, DelegationCircuitType::KeccakThetaRho);
    assert_delegated(&proof, DelegationCircuitType::KeccakColumnParity);
    assert_delegated(&proof, DelegationCircuitType::KeccakChi5);
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

const BASIC_FIBONACCI_INPUTS: [u32; 2] = [15, 1];

#[test]
#[ignore = "production circuit dimensions: minutes and ~75 GiB"]
fn one_setup_proves_standard_and_l1_feeder() {
    use execution_prover::ProofProfile;
    use full_statement_verifier::host_utils::{
        build_unified_stream, native_verify_unified, native_verify_unified_l1_feeder,
    };

    let mut prover =
        CpuExecutionProver::with_configuration(CpuExecutionProverConfiguration::default());
    let (binary, text) = workload("basic_fibonacci", "app");
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        binary,
        text,
        None,
        &[ProofProfile::Standard, ProofProfile::L1Feeder],
    );
    let prove_with = |commitment_mode, profile| {
        let result = prover.commit_memory_and_prove(
            1,
            &handle,
            QuasiUARTSource::new_with_reads(BASIC_FIBONACCI_INPUTS.to_vec()),
            commitment_mode,
            profile,
        );
        program_prover::assemble_program_proof(&prover.program_artifacts(&handle, profile), result)
    };

    let (standard_proof, standard_setups) = prove_with(
        CommitmentMode::SeparateMemoryAndWitness,
        ProofProfile::Standard,
    );
    let standard_output = native_verify_unified(
        build_unified_stream(&standard_setups, &standard_proof),
        true,
    );

    let (feeder_proof, feeder_setups) = prove_with(
        CommitmentMode::MergedMemoryAndWitness,
        ProofProfile::L1Feeder,
    );
    let feeder_output =
        native_verify_unified_l1_feeder(build_unified_stream(&feeder_setups, &feeder_proof), true);

    assert_ne!(standard_output, [0u32; 16]);
    assert_ne!(feeder_output, [0u32; 16]);
    assert_eq!(standard_output[..8], feeder_output[..8]);
    assert_ne!(standard_output[8..], feeder_output[8..]);
}
