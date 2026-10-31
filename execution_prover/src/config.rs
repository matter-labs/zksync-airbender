use crate::upstream::{GKRCircuitArtifact, ProverConfig, SecurityLevel, BF};
use crate::{CommitmentMode, ExecutionKind, ProofProfile};
use execution_prover_model::circuit_type::CircuitType;
pub use prover::definitions::{ProvingSelection, SoundnessMode};
use prover::gkr::prover_config::example_configs::ConfigSelectionError;
use riscv_transpiler::jit::JitRunnerRam;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SelectionError {
    UnsupportedBackendSoundnessMode {
        backend: &'static str,
        selection: ProvingSelection,
    },
    ConfigSelection(ConfigSelectionError),
    PreparedSelectionMismatch {
        prepared: ProvingSelection,
        requested: ProvingSelection,
    },
    PreparedCircuitMismatch {
        prepared: CircuitType,
        requested: CircuitType,
    },
}

impl std::fmt::Display for SelectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedBackendSoundnessMode { backend, selection } => write!(f,
                "UnsupportedBackendSoundnessMode: {backend} cannot prove {:?}: missing internal folding-PoW and OOD-PoW",
                selection.soundness_mode),
            Self::ConfigSelection(error) => write!(f, "ConfigSelectionFailed: {error}"),
            Self::PreparedSelectionMismatch { prepared, requested } => write!(f,
                "prepared selection {prepared:?} differs from requested selection {requested:?}"),
            Self::PreparedCircuitMismatch { prepared, requested } => write!(f,
                "prepared circuit {prepared:?} differs from requested circuit {requested:?}"),
        }
    }
}

impl std::error::Error for SelectionError {}

impl From<ConfigSelectionError> for SelectionError {
    fn from(error: ConfigSelectionError) -> Self {
        Self::ConfigSelection(error)
    }
}

/// Commitments and proofs use the circuit's own config unless an L1 profile overrides it:
/// `Standard` resolves the selected mode from the compiled columns, the L1 profiles use their
/// special configs.
pub fn try_prover_config_in_mode(
    circuit_type: CircuitType,
    compiled: &GKRCircuitArtifact<BF>,
    profile: ProofProfile,
    selection: ProvingSelection,
) -> Result<ProverConfig, ConfigSelectionError> {
    match profile {
        ProofProfile::Standard => circuit_type.try_prover_config_in_mode(compiled, selection),
        l1 => l1.try_prover_config(circuit_type.get_domain_size_log2() as usize, selection),
    }
}

/// Pessimistic compatibility wrapper of [`try_prover_config_in_mode`].
pub fn prover_config(
    circuit_type: CircuitType,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> ProverConfig {
    match profile {
        ProofProfile::Standard => circuit_type.prover_config(security_level),
        l1 => l1.prover_config(circuit_type.get_domain_size_log2() as usize, security_level),
    }
}

/// Unified executions take their mode from the selected circuit configuration; `compiled`
/// returns the unified circuit's compiled columns. Per-family unrolled executions only
/// support separate commitments.
pub fn try_execution_commitment_mode<'a>(
    kind: ExecutionKind,
    profile: ProofProfile,
    selection: ProvingSelection,
    compiled: impl FnOnce(CircuitType) -> &'a GKRCircuitArtifact<BF>,
) -> Result<CommitmentMode, ConfigSelectionError> {
    match kind.unified_circuit() {
        Some(circuit) => {
            Ok(
                try_prover_config_in_mode(circuit, compiled(circuit), profile, selection)?
                    .commitment_mode,
            )
        }
        None => {
            assert_eq!(profile, ProofProfile::Standard);
            Ok(CommitmentMode::SeparateMemoryAndWitness)
        }
    }
}

/// Pessimistic compatibility wrapper of [`try_execution_commitment_mode`].
pub fn execution_commitment_mode(
    kind: ExecutionKind,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> CommitmentMode {
    match kind.unified_circuit() {
        Some(circuit) => prover_config(circuit, profile, security_level).commitment_mode,
        None => {
            assert_eq!(profile, ProofProfile::Standard);
            CommitmentMode::SeparateMemoryAndWitness
        }
    }
}

pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    fn execution_defaults(selection: ProvingSelection) -> ExecutionProverConfiguration<Self>;
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
    pub security_level: SecurityLevel,
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
        Self::for_selection(ProvingSelection::default())
    }
}

impl<C: BackendConfiguration> ExecutionProverConfiguration<C> {
    pub fn for_selection(selection: ProvingSelection) -> Self {
        C::execution_defaults(selection)
    }

    pub fn selection(&self) -> ProvingSelection {
        ProvingSelection {
            security_level: self.security_level,
            soundness_mode: self.soundness_mode,
        }
    }
}
