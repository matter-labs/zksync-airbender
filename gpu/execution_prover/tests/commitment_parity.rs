//! Compare CPU/GPU setup caps and ordered memory caps. The transcript
//! challenges are derived from these by shared code.
//!
//! Test names must not start with `cpu_`: nextest treats that prefix as GPU-free
//! and would disable device serialization.

use cpu_execution_prover::{CpuBackend, CpuExecutionProverConfiguration};
use execution_prover::{
    BinaryHandle, CommitMemoryResult, CommitmentMode, ExecutionKind, ExecutionProver, MachineType,
    ProofProfile,
};
use gpu_execution_prover::{
    ExecutionProverConfiguration as GpuConfiguration, GpuBackend, MemoryPreset,
};
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
    profile: ProofProfile,
) -> (ExecutionProver<B>, BinaryHandle, CommitMemoryResult)
where
    B: execution_prover::backend::ExecutionBackend,
{
    let (bin, text) = load(workload);
    let handle = prover.add_binary(kind, machine, bin, text, Some(CYCLES_BOUND), &[profile]);
    let commitment = prover.commit_memory(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(workload.non_determinism.to_vec()),
        commitment_mode,
        profile,
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

fn gpu_prover(memory_preset: MemoryPreset) -> ExecutionProver<GpuBackend> {
    let mut configuration = GpuConfiguration {
        ram_config: RAM,
        security_level: SECURITY,
        // `multi_family_smoke` feeds raw non-determinism words (e.g. `0xDEAD_BEEF`) into the
        // field operations, so their inputs can not be assumed canonical
        assume_canonical_mop_inputs: false,
        ..Default::default()
    };
    configuration.backend.memory_preset = memory_preset;
    ExecutionProver::with_configuration(configuration)
}

/// The W4 feeder gates run at the 30 GiB preset; the other cases keep Auto.
fn gpu_preset(profile: ProofProfile) -> MemoryPreset {
    match profile {
        ProofProfile::L1Feeder => MemoryPreset::GiB30,
        ProofProfile::Standard | ProofProfile::L1Wrap => MemoryPreset::Auto,
    }
}

#[test]
#[ignore]
fn test_cpu_gpu_agree_on_unrolled_caps_and_challenges() {
    compare_commitments(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        UNROLLED_WORKLOAD,
        CommitmentMode::SeparateMemoryAndWitness,
        ProofProfile::Standard,
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
        ProofProfile::Standard,
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
        ProofProfile::Standard,
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

#[test]
#[ignore]
fn l1_feeder_merged_commitment_cpu_parity() {
    let config = ProofProfile::L1Feeder.prover_config(22, SECURITY);
    let (cpu, cpu_commitment, gpu, mut gpu_commitment) = compare_commitments(
        ExecutionKind::Unified22,
        MachineType::Reduced,
        BASIC_FIBONACCI_WORKLOAD,
        CommitmentMode::MergedMemoryAndWitness,
        ProofProfile::L1Feeder,
    );
    assert_eq!(cpu_commitment.profile, ProofProfile::L1Feeder);
    assert_eq!(gpu_commitment.profile, ProofProfile::L1Feeder);
    assert_eq!(
        cpu_commitment.commitment_mode,
        CommitmentMode::MergedMemoryAndWitness
    );
    assert!(!cpu_commitment.circuit_families_memory_caps.is_empty());
    for instances in cpu_commitment.circuit_families_memory_caps.values() {
        assert!(!instances.is_empty());
        for caps in instances {
            assert_eq!(caps.len(), config.lde_factor);
            for cap in caps {
                assert_eq!(cap.cap.len(), config.cap_size / config.lde_factor);
                assert!(!cap.cap.is_empty());
            }
        }
    }
    let challenges = cpu.external_challenges(&cpu_commitment);
    assert_eq!(gpu.external_challenges(&gpu_commitment), challenges);
    // Rejection control: the last cap node reaches the external challenges.
    let last_node = gpu_commitment
        .circuit_families_memory_caps
        .values_mut()
        .flat_map(|instances| instances.iter_mut())
        .flat_map(|caps| caps.iter_mut())
        .flat_map(|cap| cap.cap.iter_mut())
        .last()
        .expect("the feeder commitment has a cap node");
    last_node[0] ^= 1;
    assert_ne!(gpu.external_challenges(&gpu_commitment), challenges);
}

#[test]
#[ignore]
fn mixed_profile_setup_caps() {
    let _ = env_logger::builder().is_test(true).try_init();
    // One binary under two handles, as the pipeline registers the final layer
    // (Unified, Standard) and the first feeder layer (Unified22, L1Feeder).
    let registrations = [
        (ExecutionKind::Unified, ProofProfile::Standard),
        (ExecutionKind::Unified22, ProofProfile::L1Feeder),
    ];
    let mut cpu = cpu_prover();
    let mut gpu = gpu_prover(MemoryPreset::GiB30);
    let (bin, text) = load(BASIC_FIBONACCI_WORKLOAD);
    let handles: Vec<_> = registrations
        .iter()
        .map(|&(kind, profile)| {
            let cpu_handle = cpu.add_binary(
                kind,
                MachineType::Reduced,
                bin.clone(),
                text.clone(),
                Some(CYCLES_BOUND),
                &[profile],
            );
            let gpu_handle = gpu.add_binary(
                kind,
                MachineType::Reduced,
                bin.clone(),
                text.clone(),
                Some(CYCLES_BOUND),
                &[profile],
            );
            (profile, cpu_handle, gpu_handle)
        })
        .collect();
    for lookup_order in [[0, 1], [1, 0]] {
        for index in lookup_order {
            let (profile, cpu_handle, gpu_handle) = &handles[index];
            let profile = *profile;
            let cpu_artifacts = cpu.program_artifacts(cpu_handle, profile);
            let gpu_artifacts = gpu.program_artifacts(gpu_handle, profile);
            assert!(!cpu_artifacts.riscv_families.is_empty());
            assert_eq!(
                cpu_artifacts.riscv_families.keys().collect::<Vec<_>>(),
                gpu_artifacts.riscv_families.keys().collect::<Vec<_>>()
            );
            for (family, cpu_family) in &cpu_artifacts.riscv_families {
                let gpu_family = &gpu_artifacts.riscv_families[family];
                assert!(!cpu_family.setup_cap.cap.is_empty());
                assert_eq!(
                    cpu_family.setup_cap.cap, gpu_family.setup_cap.cap,
                    "family {family} setup cap differs for profile {profile:?}"
                );
            }
        }
    }
}

fn compare_commitments(
    kind: ExecutionKind,
    machine: MachineType,
    workload: &Workload,
    commitment_mode: CommitmentMode,
    profile: ProofProfile,
) -> (
    ExecutionProver<CpuBackend>,
    CommitMemoryResult,
    ExecutionProver<GpuBackend>,
    CommitMemoryResult,
) {
    let _ = env_logger::builder().is_test(true).try_init();

    let (cpu, cpu_handle, cpu_commitment) = commit(
        cpu_prover(),
        kind,
        machine,
        workload,
        commitment_mode,
        profile,
    );
    let (gpu, gpu_handle, gpu_commitment) = commit(
        gpu_prover(gpu_preset(profile)),
        kind,
        machine,
        workload,
        commitment_mode,
        profile,
    );

    let cpu_artifacts = cpu.program_artifacts(&cpu_handle, profile);
    let gpu_artifacts = gpu.program_artifacts(&gpu_handle, profile);
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
