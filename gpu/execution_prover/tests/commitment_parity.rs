//! Compare CPU/GPU setup caps, ordered memory caps, then shared challenges.
//! Program proof-diff tests use the legacy CPU path and do not cover this backend.
//!
//! Test names must not start with `cpu_`: nextest treats that prefix as GPU-free
//! and would disable device serialization.

use cpu_execution_prover::{CpuBackend, CpuExecutionProverConfiguration};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::{
    BinaryHandle, CommitMemoryResult, ExecutionKind, ExecutionProver, MachineType,
};
use gpu_execution_prover::{ExecutionProverConfiguration as GpuConfiguration, GpuBackend};
use prover::definitions::SecurityLevel;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::jit::JitRunnerRam;
use setups::read_binary;

/// Both legs run THIS configuration. The comparison is void if they differ in
/// RAM, cycle bound or security level: any one of those changes the trace, the
/// instance counts and therefore every cap below.
const RAM: JitRunnerRam = JitRunnerRam::Medium;
const CYCLES_BOUND: u32 = 1 << 20;
const SECURITY: SecurityLevel = SecurityLevel::Sec100;

/// A fixture plus the non-determinism it expects.
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

/// Workspace root for test fixtures.
///
/// `AB_TEST_ARTIFACT_ROOT` wins when set, because `CARGO_MANIFEST_DIR` is
/// baked in at BUILD time: a test binary copied to another machine resolves
/// the builder's path, not the checkout it is running against.
fn workspace_root() -> std::path::PathBuf {
    if let Ok(root) = std::env::var("AB_TEST_ARTIFACT_ROOT") {
        return std::path::PathBuf::from(root);
    }
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

/// Register the workload and commit, returning everything the comparison needs.
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
    let mut configuration = CpuExecutionProverConfiguration {
        ram_config: RAM,
        security_level: SECURITY,
        ..Default::default()
    };
    // After the RAM: the producer reserve is derived from it.
    let minimum = configuration.minimum_host_allocators_per_job().unwrap();
    configuration.host_allocators_per_job_count =
        configuration.host_allocators_per_job_count.max(minimum);
    ExecutionProver::with_configuration(configuration).expect("CPU construction must succeed")
}

fn gpu_prover() -> ExecutionProver<GpuBackend> {
    let mut configuration = GpuConfiguration {
        ram_config: RAM,
        security_level: SECURITY,
        ..Default::default()
    };
    let minimum = configuration.minimum_host_allocators_per_job().unwrap();
    configuration.host_allocators_per_job_count =
        configuration.host_allocators_per_job_count.max(minimum);
    ExecutionProver::with_configuration(configuration).expect("GPU construction must succeed")
}

/// Per-coset caps, compared IN ORDER.
///
/// The trees are built with `bitreverse_cosets`, so the flat cap is in stage-1
/// order while the protocol carries per-coset caps in natural order. A sorted
/// or set comparison would pass across exactly the permutation bug the shared
/// cap helpers exist to prevent, and at the production LDE factor of 2 that
/// permutation is the identity.
fn assert_caps_equal(
    what: &str,
    cpu: &[Vec<prover::merkle_trees::MerkleTreeCapVarLength>],
    gpu: &[Vec<prover::merkle_trees::MerkleTreeCapVarLength>],
) {
    assert_eq!(cpu.len(), gpu.len(), "{what}: different instance counts");
    for (sequence_id, (cpu_instance, gpu_instance)) in cpu.iter().zip(gpu.iter()).enumerate() {
        assert_eq!(
            cpu_instance.len(),
            gpu_instance.len(),
            "{what}[{sequence_id}]: different coset counts"
        );
        for (coset, (cpu_cap, gpu_cap)) in cpu_instance.iter().zip(gpu_instance.iter()).enumerate()
        {
            assert_eq!(
                cpu_cap.cap, gpu_cap.cap,
                "{what}[{sequence_id}] coset {coset} differs"
            );
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
#[ignore]
fn test_cpu_gpu_agree_on_unrolled_caps_and_challenges() {
    compare_commitments(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        UNROLLED_WORKLOAD,
    );
}

/// The unified (reduced-machine) case: not a duplicate of the unrolled one,
/// because unified carries its inits and teardowns inline, has a different
/// family set, and its trivial leading instances take a separate FS-seed path.
#[test]
#[cfg(not(no_cuda))]
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

    // 1. Setup caps: they depend only on the circuits and the configuration,
    //    so a mismatch means nothing below is worth reading.
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
    // Delegation and common-circuit SETUP CAPS, not merely the key set: equal
    // keys are a far weaker claim than equal setup commitments. They live on
    // the backend precomputations rather than in `ProgramArtifacts` because
    // delegation setup params are compile-time constants in the fsv verifiers
    // and carry no program-level cap.
    let cpu_common = cpu.common_precomputations();
    let gpu_common = gpu.common_precomputations();
    assert_eq!(
        cpu_common.keys().collect::<Vec<_>>(),
        gpu_common.keys().collect::<Vec<_>>(),
        "different common circuits precomputed"
    );
    let mut compared_setups = 0usize;
    for (circuit_type, cpu_precomputation) in cpu_common.iter() {
        let cpu_cap = cpu_precomputation.setup_cap();
        let gpu_cap = gpu_common[circuit_type].setup_cap();
        assert_eq!(
            cpu_cap.is_some(),
            gpu_cap.is_some(),
            "{circuit_type:?}: one backend has a setup cap and the other does not"
        );
        if let (Some(cpu_cap), Some(gpu_cap)) = (cpu_cap, gpu_cap) {
            assert_eq!(
                cpu_cap.cap, gpu_cap.cap,
                "{circuit_type:?} setup cap differs"
            );
            compared_setups += 1;
        }
    }
    assert!(
        compared_setups > 0,
        "no common-circuit setup caps were compared, so this leg is vacuous"
    );

    // 2. Execution end state, before the caps that depend on it.
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

    // 3. Ordered memory caps, every family and delegation.
    assert_eq!(
        cpu_commitment
            .circuit_families_memory_caps
            .keys()
            .collect::<Vec<_>>(),
        gpu_commitment
            .circuit_families_memory_caps
            .keys()
            .collect::<Vec<_>>(),
    );
    let mut compared = 0usize;
    for (family, cpu_caps) in cpu_commitment.circuit_families_memory_caps.iter() {
        assert_caps_equal(
            &format!("family {family} memory caps"),
            cpu_caps,
            &gpu_commitment.circuit_families_memory_caps[family],
        );
        compared += cpu_caps.len();
    }
    assert_caps_equal(
        "inits-and-teardowns memory caps",
        &cpu_commitment.inits_and_teardowns_memory_caps,
        &gpu_commitment.inits_and_teardowns_memory_caps,
    );
    compared += cpu_commitment.inits_and_teardowns_memory_caps.len();
    assert_eq!(
        cpu_commitment
            .delegation_circuits_memory_caps
            .keys()
            .collect::<Vec<_>>(),
        gpu_commitment
            .delegation_circuits_memory_caps
            .keys()
            .collect::<Vec<_>>(),
    );
    for (delegation, cpu_caps) in cpu_commitment.delegation_circuits_memory_caps.iter() {
        assert_caps_equal(
            &format!("delegation {delegation} memory caps"),
            cpu_caps,
            &gpu_commitment.delegation_circuits_memory_caps[delegation],
        );
        compared += cpu_caps.len();
    }
    // Without this the test would pass on a workload that committed nothing.
    assert!(
        compared > 0,
        "no memory caps were compared, so this test proves nothing"
    );

    // 4. Shared challenges last: they absorb every cap above, so agreement
    //    here says both backends fed the transcript the same bytes in order.
    let (cpu_pow, cpu_challenges) = cpu.shared_challenges(&cpu_handle, &cpu_commitment);
    let (gpu_pow, gpu_challenges) = gpu.shared_challenges(&gpu_handle, &gpu_commitment);
    assert_eq!(cpu_pow, gpu_pow, "PoW challenge differs");
    assert_eq!(
        cpu_challenges, gpu_challenges,
        "external GKR challenges differ"
    );
}

gpu_core::force_serial_libtest!();
