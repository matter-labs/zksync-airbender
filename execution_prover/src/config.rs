use crate::upstream::{GKRCircuitArtifact, BF};
use crate::{CommitmentMode, ExecutionKind, ProofProfile};
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
pub use prover::definitions::SoundnessMode;
use prover::gkr::prover_config::ProverConfig;
use riscv_transpiler::jit::JitRunnerRam;

/// Assert the profile pairing before registration or direct backend preparation.
pub fn assert_profiles_for_circuit(circuit: CircuitType, profiles: &[ProofProfile]) {
    assert!(
        !profiles.is_empty(),
        "at least one ProofProfile is required"
    );
    let valid = match circuit {
        CircuitType::L1Wrap => profiles == [ProofProfile::L1Wrap],
        CircuitType::Unrolled(UnrolledCircuitType::Unified22) => {
            profiles == [ProofProfile::CompressionFinal]
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => profiles
            .iter()
            .all(|profile| matches!(profile, ProofProfile::Standard | ProofProfile::Compression)),
        _ => profiles == [ProofProfile::Standard],
    };
    assert!(valid, "{circuit:?} does not support profiles {profiles:?}");
}

/// The config of `circuit_type` under `profile` and `soundness_mode`: `Standard` resolves the selected
/// mode from the compiled columns, the L1 profiles use their special configs
/// ([`ProofProfile::prover_config`], Pessimistic only).
pub fn prover_config_in_mode(
    circuit_type: CircuitType,
    compiled: &GKRCircuitArtifact<BF>,
    profile: ProofProfile,
    soundness_mode: SoundnessMode,
) -> ProverConfig {
    match profile {
        ProofProfile::Standard => circuit_type.prover_config_in_mode(compiled, soundness_mode),
        l1 => l1.prover_config(circuit_type.get_domain_size_log2() as usize, soundness_mode),
    }
}

/// Unified executions take their mode from the selected circuit configuration; `compiled`
/// returns the unified circuit's compiled columns. Per-family unrolled executions only
/// support separate commitments.
pub fn execution_commitment_mode<'a>(
    kind: ExecutionKind,
    profile: ProofProfile,
    soundness_mode: SoundnessMode,
    compiled: impl FnOnce(CircuitType) -> &'a GKRCircuitArtifact<BF>,
) -> CommitmentMode {
    match kind.unified_circuit() {
        Some(circuit) => {
            prover_config_in_mode(circuit, compiled(circuit), profile, soundness_mode)
                .commitment_mode
        }
        None => {
            assert_eq!(profile, ProofProfile::Standard);
            CommitmentMode::SeparateMemoryAndWitness
        }
    }
}

pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    fn execution_defaults(soundness_mode: SoundnessMode) -> ExecutionProverConfiguration<Self>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration<C> {
    /// Shared host-work pool, also used for CPU proving; simulation and replay
    /// run on their own threads.
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_per_job_count: usize,
    /// Free blocks the cache is trimmed back towards; pressure relief, not a bound.
    pub min_free_host_allocators_per_job: usize,
    pub soundness_mode: SoundnessMode,
    pub ram_config: JitRunnerRam,
    /// Simulate the field operations (MOPs) without the reduction of their inputs
    /// (`MopField::BabyBearAssumeCanonical`). It is only valid for the programs that never
    /// feed a non-canonical value into a field operation: the simulated execution diverges
    /// from the replayed one otherwise.
    pub assume_canonical_mop_inputs: bool,
    pub backend: C,
}

impl<C: BackendConfiguration> Default for ExecutionProverConfiguration<C> {
    fn default() -> Self {
        Self::for_mode(SoundnessMode::DEFAULT)
    }
}

impl<C: BackendConfiguration> ExecutionProverConfiguration<C> {
    pub fn for_mode(soundness_mode: SoundnessMode) -> Self {
        C::execution_defaults(soundness_mode)
    }
}
