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
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::jit::JitRunnerRam;
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
) -> (ExecutionProver<B>, BinaryHandle, CommitMemoryResult)
where
    B: execution_prover::backend::ExecutionBackend,
{
    let (bin, text) = load(workload);
    let handle = prover.add_binary(kind, machine, bin, text, Some(CYCLES_BOUND));
    let commitment = prover.commit_memory(
        0,
        &handle,
        QuasiUARTSource::new_with_reads(workload.non_determinism.to_vec()),
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

gpu_core::force_serial_libtest!();
