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
use riscv_transpiler::elf::ProgramSource;
use riscv_transpiler::jit::JitRunnerRam;
use riscv_transpiler::vm::FlatResponsesSource;

// Both backends must use identical execution and proof parameters.
const RAM: JitRunnerRam = JitRunnerRam::Medium;
const CYCLES_BOUND: u32 = 1 << 20;
const SECURITY: SecurityLevel = SecurityLevel::Sec100;

struct Workload {
    directory: &'static str,
    stem: &'static str,
    non_determinism: &'static [u32],
}

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
    expected_mode: CommitmentMode,
    profile: ProofProfile,
) -> (ExecutionProver<B>, BinaryHandle, CommitMemoryResult)
where
    B: execution_prover::backend::ExecutionBackend,
{
    let (bin, text) = load(workload);
    let handle = prover.add_binary_variants(
        bin,
        text,
        &[(kind, machine, &[profile])],
        Some(CYCLES_BOUND),
    )[0];
    prover.finalize_setup();
    // Independent reference of the resolver: the unified circuit's own config for `Standard`,
    // the profile's special config otherwise; per-family unrolled executions commit separately.
    let resolved_mode = match kind.unified_circuit() {
        Some(circuit) => {
            match profile {
                ProofProfile::Standard => circuit.prover_config(SECURITY),
                l1 => l1.prover_config(
                    circuit.get_domain_size_log2() as usize,
                    execution_prover::config::SoundnessMode::PessimisticConjecture,
                ),
            }
            .commitment_mode
        }
        None => CommitmentMode::SeparateMemoryAndWitness,
    };
    assert_eq!(expected_mode, resolved_mode);
    let commitment = prover.commit_memory(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(workload.non_determinism.to_vec()),
        profile,
    );
    (prover, handle, commitment)
}

fn cpu_prover() -> ExecutionProver<CpuBackend> {
    let configuration = CpuExecutionProverConfiguration {
        ram_config: RAM,

        ..Default::default()
    };
    ExecutionProver::with_configuration(configuration)
}

fn gpu_prover(memory_preset: MemoryPreset) -> ExecutionProver<GpuBackend> {
    let mut configuration = GpuConfiguration {
        ram_config: RAM,

        // `multi_family_smoke` feeds raw non-determinism words (e.g. `0xDEAD_BEEF`) into the
        // field operations, so their inputs can not be assumed canonical
        assume_canonical_mop_inputs: false,
        ..Default::default()
    };
    configuration.backend.memory_preset = memory_preset;
    ExecutionProver::with_configuration(configuration)
}

/// The compression compression gates run at the 30 GiB preset; the other cases keep Auto.
fn gpu_preset(profile: ProofProfile) -> MemoryPreset {
    match profile {
        ProofProfile::CompressionFinal | ProofProfile::Compression => MemoryPreset::GiB30,
        ProofProfile::Standard | ProofProfile::L1Wrap => MemoryPreset::Auto,
    }
}

#[test]
#[ignore]
fn compression_merged_commitment_cpu_parity() {
    let config = ProofProfile::CompressionFinal.prover_config(
        22,
        prover::definitions::SoundnessMode::PessimisticConjecture,
    );
    let (cpu, cpu_commitment, gpu, mut gpu_commitment) = compare_commitments(
        ExecutionKind::Unified22,
        MachineType::Reduced,
        BASIC_FIBONACCI_WORKLOAD,
        CommitmentMode::MergedMemoryAndWitness,
        ProofProfile::CompressionFinal,
    );
    assert_eq!(cpu_commitment.profile, ProofProfile::CompressionFinal);
    assert_eq!(gpu_commitment.profile, ProofProfile::CompressionFinal);
    assert!(!cpu_commitment.circuit_families_memory_caps.is_empty());
    for instances in cpu_commitment.circuit_families_memory_caps.values() {
        assert!(!instances.is_empty());
        for caps in instances {
            assert_eq!(caps.len(), config.lde_factor());
            for cap in caps {
                assert_eq!(cap.cap.len(), config.cap_size / config.lde_factor());
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
        .expect("the compression commitment has a cap node");
    last_node[0] ^= 1;
    assert_ne!(gpu.external_challenges(&gpu_commitment), challenges);
}

#[test]
#[ignore]
fn mixed_profile_setup_caps() {
    let _ = env_logger::builder().is_test(true).try_init();
    // One binary under two handles, as the pipeline registers the final layer
    // (Unified, Standard) and the first compression layer (Unified22, Compression).
    let registrations = [
        (ExecutionKind::Unified, ProofProfile::Standard),
        (ExecutionKind::Unified22, ProofProfile::CompressionFinal),
    ];
    let mut cpu = cpu_prover();
    let mut gpu = gpu_prover(MemoryPreset::GiB30);
    let (bin, text) = load(BASIC_FIBONACCI_WORKLOAD);
    let profiles: Vec<_> = registrations
        .iter()
        .map(|&(_, profile)| [profile])
        .collect();
    let variants: Vec<_> = registrations
        .iter()
        .zip(&profiles)
        .map(|(&(kind, _), profiles)| (kind, MachineType::Reduced, profiles.as_slice()))
        .collect();
    let cpu_handles =
        cpu.add_binary_variants(bin.clone(), text.clone(), &variants, Some(CYCLES_BOUND));
    let gpu_handles = gpu.add_binary_variants(bin, text, &variants, Some(CYCLES_BOUND));
    cpu.finalize_setup();
    gpu.finalize_setup();
    let handles: Vec<_> = registrations
        .iter()
        .zip(cpu_handles)
        .zip(gpu_handles)
        .map(|((&(_, profile), cpu_handle), gpu_handle)| (profile, cpu_handle, gpu_handle))
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
    expected_mode: CommitmentMode,
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
        expected_mode,
        profile,
    );
    let (gpu, gpu_handle, gpu_commitment) = commit(
        gpu_prover(gpu_preset(profile)),
        kind,
        machine,
        workload,
        expected_mode,
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
