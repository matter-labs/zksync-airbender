//! Compare CPU/GPU setup caps and ordered memory caps. The transcript
//! challenges are derived from these by shared code.
//!
//! Test names must not start with `cpu_`: nextest treats that prefix as GPU-free
//! and would disable device serialization.

use cpu_execution_prover::{CpuBackend, CpuExecutionProverConfiguration};
use execution_prover::{
    BinaryHandle, CommitMemoryResult, CommitmentMode, ExecutionKind, ExecutionProver, MachineType,
};
use gpu_execution_prover::{ExecutionProverConfiguration as GpuConfiguration, GpuBackend};
use prover::definitions::SecurityLevel;
use riscv_transpiler::jit::JitRunnerRam;
use riscv_transpiler::vm::FlatResponsesSource;
use setups::read_binary;

// Both backends must use identical execution and proof parameters.
const RAM: JitRunnerRam = JitRunnerRam::Medium;
const CYCLES_BOUND: u32 = 1 << 20;
const SECURITY: SecurityLevel = SecurityLevel::Sec100;

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

/// Delegation-free: the merged commitment mode rejects delegation calls.
const BASIC_FIBONACCI_WORKLOAD: &Workload = &Workload {
    directory: "basic_fibonacci",
    stem: "app",
    non_determinism: &[15, 1],
};

fn workspace_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn load(workload: &Workload) -> (Vec<u32>, Vec<u32>) {
    let root = workspace_root().join("examples").join(workload.directory);
    let (_, bin) = read_binary(&root.join(format!("{}.bin", workload.stem)));
    let (_, text) = read_binary(&root.join(format!("{}.text", workload.stem)));
    (bin, text)
}

fn commit<B>(
    mut prover: ExecutionProver<B>,
    kind: ExecutionKind,
    machine: MachineType,
    workload: &Workload,
    commitment_mode: CommitmentMode,
) -> (ExecutionProver<B>, BinaryHandle, CommitMemoryResult)
where
    B: execution_prover::backend::ExecutionBackend,
{
    let (bin, text) = load(workload);
    let handle = prover.add_binary(
        kind,
        machine,
        bin,
        text,
        Some(CYCLES_BOUND),
        &[execution_prover::ProofProfile::Standard],
    );
    let commitment = prover.commit_memory(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(workload.non_determinism.to_vec()),
        commitment_mode,
        execution_prover::ProofProfile::Standard,
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
        CommitmentMode::SeparateMemoryAndWitness,
    );
}

#[test]
#[ignore]
fn test_cpu_gpu_agree_on_unified_caps_and_challenges() {
    compare_commitments(
        ExecutionKind::Unified,
        MachineType::Reduced,
        UNIFIED_WORKLOAD,
        CommitmentMode::SeparateMemoryAndWitness,
    );
}

#[test]
#[ignore]
fn test_cpu_gpu_agree_on_unified_merged_caps_challenges_and_proofs() {
    let workload = BASIC_FIBONACCI_WORKLOAD;
    let (cpu, cpu_commitment, gpu, gpu_commitment) = compare_commitments(
        ExecutionKind::Unified,
        MachineType::Reduced,
        workload,
        CommitmentMode::MergedMemoryAndWitness,
    );
    let reads = || FlatResponsesSource::new_with_reads(workload.non_determinism.to_vec());
    let cpu_result = cpu.prove(1, cpu_commitment, reads());
    let gpu_result = gpu.prove(1, gpu_commitment, reads());
    assert_eq!(cpu_result.pow_challenge, gpu_result.pow_challenge);
    assert_eq!(
        cpu_result.num_unified_it_circuits,
        gpu_result.num_unified_it_circuits
    );
    let cpu_proofs = serde_json::to_vec(&cpu_result.circuit_families_proofs).unwrap();
    let gpu_proofs = serde_json::to_vec(&gpu_result.circuit_families_proofs).unwrap();
    assert!(
        !cpu_result
            .circuit_families_proofs
            .values()
            .all(Vec::is_empty),
        "the workload must produce unified proofs"
    );
    assert!(cpu_proofs == gpu_proofs, "CPU and GPU merged proofs differ");
}

fn compare_commitments(
    kind: ExecutionKind,
    machine: MachineType,
    workload: &Workload,
    commitment_mode: CommitmentMode,
) -> (
    ExecutionProver<CpuBackend>,
    CommitMemoryResult,
    ExecutionProver<GpuBackend>,
    CommitMemoryResult,
) {
    let _ = env_logger::builder().is_test(true).try_init();

    let (cpu, cpu_handle, cpu_commitment) =
        commit(cpu_prover(), kind, machine, workload, commitment_mode);
    let (gpu, gpu_handle, gpu_commitment) =
        commit(gpu_prover(), kind, machine, workload, commitment_mode);

    let cpu_artifacts =
        cpu.program_artifacts(&cpu_handle, execution_prover::ProofProfile::Standard);
    let gpu_artifacts =
        gpu.program_artifacts(&gpu_handle, execution_prover::ProofProfile::Standard);
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
    (cpu, cpu_commitment, gpu, gpu_commitment)
}

gpu_core::force_serial_libtest!();
