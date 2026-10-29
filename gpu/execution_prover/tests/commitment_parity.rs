//! Compare CPU/GPU setup caps and ordered memory caps. The transcript
//! challenges are derived from these by shared code.
//!
//! Test names must not start with `cpu_`: nextest treats that prefix as GPU-free
//! and would disable device serialization.

use cpu_execution_prover::{CpuBackend, CpuExecutionProverConfiguration};
use execution_prover::{
    BinaryHandle, CommitMemoryResult, ExecutionKind, ExecutionProver, MachineType,
};
use gpu_execution_prover::{ExecutionProverConfiguration as GpuConfiguration, GpuBackend};
use prover::definitions::SecurityLevel;
use riscv_transpiler::elf::ProgramSource;
use riscv_transpiler::jit::JitRunnerRam;
use riscv_transpiler::vm::FlatResponsesSource;

// Both backends must use identical execution and proof parameters.
const RAM: JitRunnerRam = JitRunnerRam::Medium;
const CYCLES_BOUND: u32 = 1 << 20;
const SECURITY: SecurityLevel = SecurityLevel::Sec100;

type CircuitProof = prover::gkr::prover::GKRProof<
    field::baby_bear::base::BabyBearField,
    field::baby_bear::ext4::BabyBearExt4,
    prover::merkle_trees::DefaultTreeConstructor,
>;

struct Workload {
    directory: &'static str,
    stem: &'static str,
    non_determinism: &'static [u32],
}

/// `n` register-only iterations then `h` blake hashes.
const UNROLLED_WORKLOAD: &Workload = &Workload {
    directory: "hashed_fibonacci",
    stem: "app",
    non_determinism: &[100, 5],
};

/// The same workload the unified GPU e2e uses: `n` then a seed.
const UNIFIED_WORKLOAD: &Workload = &Workload {
    directory: "multi_family_smoke",
    stem: "app_blake2_with_compression",
    non_determinism: &[50, 0xDEAD_BEEF],
};

fn workspace_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn load(workload: &Workload) -> (Vec<u32>, Vec<u32>) {
    let root = workspace_root().join("examples").join(workload.directory);
    ProgramSource::legacy_binaries(
        root.join(format!("{}.bin", workload.stem)),
        root.join(format!("{}.text", workload.stem)),
    )
    .load_unpadded()
}

fn commit<B>(
    mut prover: ExecutionProver<B>,
    kind: ExecutionKind,
    machine: MachineType,
    workload: &Workload,
) -> (ExecutionProver<B>, BinaryHandle, CommitMemoryResult)
where
    B: execution_prover::backend::ExecutionBackend,
{
    let (bin, text) = load(workload);
    let handle = prover.add_binary(kind, machine, bin, text, Some(CYCLES_BOUND));
    let commitment = prover.commit_memory(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(workload.non_determinism.to_vec()),
    );
    (prover, handle, commitment)
}

fn cpu_prover() -> ExecutionProver<CpuBackend> {
    let configuration = CpuExecutionProverConfiguration {
        ram_config: RAM,
        security_level: SECURITY,
        ..Default::default()
    };
    ExecutionProver::with_configuration(configuration)
}

fn gpu_prover() -> ExecutionProver<GpuBackend> {
    let configuration = GpuConfiguration {
        ram_config: RAM,
        security_level: SECURITY,
        // `multi_family_smoke` feeds raw non-determinism words (e.g. `0xDEAD_BEEF`) into the
        // field operations, so their inputs can not be assumed canonical
        assume_canonical_mop_inputs: false,
        ..Default::default()
    };
    ExecutionProver::with_configuration(configuration)
}

#[test]
#[ignore]
fn test_cpu_gpu_agree_on_unrolled_caps_and_challenges() {
    compare_commitments(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        UNROLLED_WORKLOAD,
    );
}

#[test]
#[ignore]
fn test_cpu_gpu_agree_on_unified_caps_and_challenges() {
    compare_commitments(
        ExecutionKind::Unified,
        MachineType::Reduced,
        UNIFIED_WORKLOAD,
    );
}

fn compare_commitments(kind: ExecutionKind, machine: MachineType, workload: &Workload) {
    let _ = env_logger::builder().is_test(true).try_init();

    let (cpu, cpu_handle, cpu_commitment) = commit(cpu_prover(), kind, machine, workload);
    let (gpu, gpu_handle, gpu_commitment) = commit(gpu_prover(), kind, machine, workload);

    let cpu_artifacts = cpu.program_artifacts(&cpu_handle);
    let gpu_artifacts = gpu.program_artifacts(&gpu_handle);
    assert_eq!(
        cpu_artifacts.riscv_families.keys().collect::<Vec<_>>(),
        gpu_artifacts.riscv_families.keys().collect::<Vec<_>>(),
        "different RISC-V families registered"
    );
    for (family, cpu_family) in cpu_artifacts.riscv_families.iter() {
        let gpu_family = &gpu_artifacts.riscv_families[family];
        assert!(
            !cpu_family.setup_cap.cap.is_empty(),
            "family {family} produced an empty setup cap, so this comparison is vacuous"
        );
        assert_eq!(
            cpu_family.setup_cap.cap, gpu_family.setup_cap.cap,
            "family {family} setup cap differs"
        );
    }
    assert_eq!(
        cpu_artifacts.delegations.keys().collect::<Vec<_>>(),
        gpu_artifacts.delegations.keys().collect::<Vec<_>>(),
        "different delegation circuits registered"
    );
    assert_eq!(cpu_commitment.final_pc, gpu_commitment.final_pc);
    assert_eq!(
        cpu_commitment.final_timestamp,
        gpu_commitment.final_timestamp
    );
    assert_eq!(
        cpu_commitment.final_register_values, gpu_commitment.final_register_values,
        "final register values differ"
    );
    assert_eq!(
        cpu_commitment.num_trivial_unified_circuits,
        gpu_commitment.num_trivial_unified_circuits
    );
    assert_eq!(
        cpu_commitment.inits_and_teardowns_top_bits, gpu_commitment.inits_and_teardowns_top_bits,
        "inits-and-teardowns windows differ"
    );

    // Equality must preserve instance and coset order, which feeds the transcript.
    assert_eq!(
        cpu_commitment.circuit_families_memory_caps,
        gpu_commitment.circuit_families_memory_caps,
    );
    assert_eq!(
        cpu_commitment.inits_and_teardowns_memory_caps,
        gpu_commitment.inits_and_teardowns_memory_caps,
    );
    assert_eq!(
        cpu_commitment.delegation_circuits_memory_caps,
        gpu_commitment.delegation_circuits_memory_caps,
    );
    assert!(
        cpu_commitment
            .circuit_families_memory_caps
            .values()
            .any(|caps| !caps.is_empty()),
        "the workload must produce RISC-V memory caps",
    );
}

/// The shared CPU execution backend is the reference, including its independent
/// memory pass. Drop each backend before constructing the next one.
fn prove<B: execution_prover::backend::ExecutionBackend>(
    mut prover: ExecutionProver<B>,
    kind: ExecutionKind,
    machine: MachineType,
    workload: &Workload,
) -> execution_prover::ProveResult {
    let (binary, text) = load(workload);
    let handle = prover.add_binary(kind, machine, binary, text, Some(CYCLES_BOUND));
    prover.commit_memory_and_prove(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(workload.non_determinism.to_vec()),
    )
}

fn compare_execution(
    kind: ExecutionKind,
    machine: MachineType,
    workload: &Workload,
    expected_delegations: &[execution_prover_model::circuit_type::DelegationCircuitType],
) {
    use gpu_execution_prover::{GpuBackendConfiguration, MemoryPreset};
    let _ = env_logger::builder().is_test(true).try_init();
    let expected = prove(cpu_prover(), kind, machine, workload);
    for delegation in expected_delegations {
        assert!(
            !expected.delegation_proofs[&(delegation.get_delegation_type_id() as u32)].is_empty(),
            "the reference must actually prove {delegation:?}"
        );
    }
    for preset in [MemoryPreset::GiB21, MemoryPreset::GiB30] {
        let gpu = ExecutionProver::<GpuBackend>::with_configuration(GpuConfiguration {
            ram_config: RAM,
            security_level: SECURITY,
            assume_canonical_mop_inputs: false,
            backend: GpuBackendConfiguration {
                memory_preset: preset,
                ..Default::default()
            },
            ..Default::default()
        });
        let actual = prove(gpu, kind, machine, workload);
        assert_eq!(actual.register_final_values, expected.register_final_values);
        assert_eq!(actual.final_pc, expected.final_pc);
        assert_eq!(actual.final_timestamp, expected.final_timestamp);
        assert_eq!(actual.pow_challenge, expected.pow_challenge);
        assert_eq!(
            actual.num_unified_it_circuits,
            expected.num_unified_it_circuits
        );
        assert_eq!(
            actual.circuit_families_proofs.keys().collect::<Vec<_>>(),
            expected.circuit_families_proofs.keys().collect::<Vec<_>>()
        );
        assert_eq!(
            actual.delegation_proofs.keys().collect::<Vec<_>>(),
            expected.delegation_proofs.keys().collect::<Vec<_>>()
        );
        let mut compared = 0;
        let mut compare = |label: &str, actual: &[CircuitProof], expected: &[CircuitProof]| {
            assert_eq!(actual.len(), expected.len(), "{label} proof count");
            for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
                assert_eq!(actual.external_challenges, expected.external_challenges);
                assert_eq!(
                    actual.whir_proof.memory_commitment.commitment.cap.cap,
                    expected.whir_proof.memory_commitment.commitment.cap.cap
                );
                let actual_bytes = serde_json::to_vec(actual).unwrap();
                let expected_bytes = serde_json::to_vec(expected).unwrap();
                assert!(
                    actual_bytes == expected_bytes,
                    "{label}[{index}] differs at {preset:?}"
                );
                eprintln!(
                    "execution CPU/GPU bytes equal: preset={preset:?} {label}[{index}] bytes={}",
                    actual_bytes.len()
                );
                compared += 1;
            }
        };
        for (family, proofs) in &actual.circuit_families_proofs {
            compare(
                &format!("family {family}"),
                proofs,
                &expected.circuit_families_proofs[family],
            );
        }
        compare(
            "inits/teardowns",
            &actual.inits_and_teardowns_proofs,
            &expected.inits_and_teardowns_proofs,
        );
        for (delegation, proofs) in &actual.delegation_proofs {
            compare(
                &format!("delegation {delegation}"),
                proofs,
                &expected.delegation_proofs[delegation],
            );
        }
        assert!(compared > 0, "execution proof comparison must not be empty");
    }
}

#[test]
#[ignore = "CPU execution reference and both production GPU arenas"]
fn test_cpu_gpu_agree_on_blake_execution_proof_bytes() {
    use execution_prover_model::circuit_type::DelegationCircuitType as D;
    compare_execution(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        &Workload {
            directory: "hashed_fibonacci",
            stem: "app_blake2_with_compression",
            non_determinism: &[100, 5],
        },
        &[D::Blake2WithCompression],
    );
}

#[test]
#[ignore = "CPU execution reference and both production GPU arenas"]
fn test_cpu_gpu_agree_on_bigint_execution_proof_bytes() {
    use execution_prover_model::circuit_type::DelegationCircuitType as D;
    compare_execution(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        &Workload {
            directory: "bigint_with_control",
            stem: "app",
            non_determinism: &[],
        },
        &[D::BigIntWithControl],
    );
}

#[test]
#[ignore = "CPU execution reference and both production GPU arenas"]
fn test_cpu_gpu_agree_on_keccak_execution_proof_bytes() {
    use execution_prover_model::circuit_type::DelegationCircuitType as D;
    compare_execution(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        &Workload {
            directory: "keccak",
            stem: "app",
            non_determinism: &[],
        },
        &[D::KeccakChi5, D::KeccakColumnParity, D::KeccakThetaRho],
    );
}

#[test]
#[ignore = "CPU execution reference and both production GPU arenas"]
fn test_cpu_gpu_agree_on_unified_execution_proof_bytes() {
    use execution_prover_model::circuit_type::DelegationCircuitType as D;
    compare_execution(
        ExecutionKind::Unified,
        MachineType::Reduced,
        UNIFIED_WORKLOAD,
        &[D::Blake2WithCompression],
    );
}

gpu_core::force_serial_libtest!();

#[test]
#[ignore = "CPU execution reference and both production GPU arenas"]
fn test_cpu_gpu_agree_on_special5_execution_proof_bytes() {
    use execution_prover_model::circuit_type::DelegationCircuitType as D;
    compare_execution(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        &Workload {
            directory: "../riscv_transpiler/examples/keccak_f1600",
            stem: "app",
            non_determinism: &[15, 1],
        },
        &[D::KeccakSpecial5],
    );
}
