//! CPU program proofs and native verification. Delegation cases assert that
//! their workload actually delegates.
//!
//! Ignored by default because they use production circuit dimensions.

#![feature(allocator_api)]

use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
use execution_prover::{ExecutionKind, MachineType};
use execution_prover_model::circuit_type::DelegationCircuitType;
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

fn workload(directory: &str, stem: &str) -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let base = root.join("examples").join(directory);
    riscv_transpiler::elf::load_legacy_binaries(
        &base.join(format!("{stem}.bin")),
        &base.join(format!("{stem}.text")),
    )
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
        execution_prover::ProofProfile::Standard,
    );
    let artifacts = prover.program_artifacts(&handle, execution_prover::ProofProfile::Standard);
    program_prover::assemble_program_proof(&artifacts, result)
}

fn assert_verifies_unrolled(proof: &ProgramProof, setups: &setups::Setups) {
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(
        setups,
        proof,
        verifier_common::BLAKE_MODE,
    );
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
    let stream = full_statement_verifier::host_utils::build_unified_stream(
        &setups,
        &proof,
        verifier_common::BLAKE_MODE,
    );
    let output = full_statement_verifier::host_utils::native_verify_unified(stream, true);
    assert_ne!(
        output, [0u32; 16],
        "native verification produced an empty output"
    );
}

/// First Task S resource gate: one standard ethproofs CPU base proof, followed
/// by verification with the explicitly selected schedule. The optional private
/// JSON bundle is versioned and includes selection; it is not a pipeline v3 artifact.
#[test]
#[ignore = "production circuit dimensions: measure time/RSS before scheduling recursion"]
fn ethproofs_base_measurement() {
    selected_base_measurement(prover::definitions::SoundnessMode::EthproofsSoundnessCalc);
}

/// Pessimistic counterpart with exactly the same inputs and execution configuration.
#[test]
#[ignore = "production circuit dimensions: measure time/RSS on the same workload as ethproofs"]
fn pessimistic_base_measurement() {
    selected_base_measurement(prover::definitions::SoundnessMode::PessimisticConjecture);
}

fn selected_base_measurement(soundness_mode: prover::definitions::SoundnessMode) {
    use prover::definitions::ProvingSelection;
    let selection = ProvingSelection {
        soundness_mode,
        ..ProvingSelection::default()
    };
    let (proof, setups) = {
        let mut prover = CpuExecutionProver::try_with_configuration(
            CpuExecutionProverConfiguration::for_selection(selection),
        )
        .expect("CPU must support the selected ethproofs schedule");
        assert_eq!(prover.selection(), selection);
        let (binary, text) = workload("basic_fibonacci", "app");
        let handle = prover
            .try_add_binary(
                ExecutionKind::Unrolled,
                MachineType::FullUnsigned,
                binary,
                text,
                None,
                &[execution_prover::ProofProfile::Standard],
            )
            .expect("basic Fibonacci configs must resolve in ethproofs mode");
        let result = prover.commit_memory_and_prove(
            1,
            &handle,
            QuasiUARTSource::new_with_reads(vec![15, 1]),
            execution_prover::ProofProfile::Standard,
        );
        program_prover::assemble_program_proof(
            &prover.program_artifacts(&handle, execution_prover::ProofProfile::Standard),
            result,
        )
    };
    let proof_count: usize = proof.riscv_proofs.values().map(Vec::len).sum();
    assert!(
        proof_count > 0,
        "measurement must produce actual base proofs"
    );
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(
        &setups,
        &proof,
        verifier_common::BLAKE_MODE,
    );
    let output = full_statement_verifier::host_utils::native_verify_unrolled_in_mode(
        stream,
        true,
        selection.soundness_mode,
    );
    assert_ne!(output, [0u32; 16], "selected base proof must verify");
    if let Ok(checkpoint) = std::env::var("TASK_S_BASE_PROOF_OUT") {
        program_prover::bundle::write_program_proof_bundle(
            std::path::Path::new(&checkpoint),
            selection,
            &proof,
            &setups,
        )
        .expect("write the mode-tagged JSON measurement bundle");
    }
    println!("Task S CPU base measurement: {selection:?}, {proof_count} RISC-V proof chunks, native verification succeeded");
}
