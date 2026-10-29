use crate::{CommitmentMode, ExecutionKind, ProofProfile};
use prover::definitions::SecurityLevel;
pub use prover::definitions::SoundnessMode;
use riscv_transpiler::jit::JitRunnerRam;

/// Unified executions take their mode from the selected circuit configuration.
/// Per-family unrolled executions only support separate commitments.
pub fn execution_commitment_mode(
    kind: ExecutionKind,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> CommitmentMode {
    match kind.unified_circuit() {
        Some(circuit) => {
            match profile {
                ProofProfile::Standard => circuit.prover_config(security_level),
                l1 => l1.prover_config(circuit.get_domain_size_log2() as usize, security_level),
            }
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
