use crate::config::{
    BackendConfiguration, ExecutionProverConfiguration, ProvingSelection, SelectionError,
    SoundnessMode,
};
use crate::messages::WorkBatch;
use crate::setup::CanonicalCircuitSetup;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel, BF};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::ops::DerefMut;
use std::sync::Arc;
use worker::Worker;

pub trait CircuitPrecomputation: Clone + Send + Sync + 'static {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>>;

    /// Available after setup initialization. `None` means no setup columns.
    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength>;
}

/// Drop must drain accepted work and join workers before borrowed setup or
/// allocation owners are dropped.
pub trait ExecutionBackend: Send + Sync + Sized + 'static {
    type Configuration: BackendConfiguration;
    type Allocator: HostTraceAllocator;
    type Memory: DerefMut<Target = MemoryHolder> + Send + 'static;
    type Snapshot: DerefMut<Target = TraceChunk> + Send + 'static;
    type Precomputations: CircuitPrecomputation;

    /// Capability preflight, called before workers, allocation or backend initialization.
    /// Backends must explicitly opt in before accepting a non-default schedule.
    fn validate_selection(selection: ProvingSelection) -> Result<(), SelectionError> {
        if selection.soundness_mode != SoundnessMode::PessimisticConjecture {
            return Err(SelectionError::UnsupportedBackendSoundnessMode {
                backend: core::any::type_name::<Self>(),
                selection,
            });
        }
        Ok(())
    }

    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        worker: Arc<Worker>,
    ) -> Self;

    fn allocate_trace_block(&self, bytes: usize) -> Self::Allocator;

    fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory;

    fn allocate_snapshot(&self) -> Self::Snapshot;

    /// Blocks beyond the per-job allowance, such as GPU per-device reserves.
    fn extra_trace_blocks(&self) -> usize {
        0
    }

    /// Must assert that compiled circuit geometry agrees with `circuit`.
    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
    ) -> Self::Precomputations;

    /// Selection-aware preparation. The compatibility bridge accepts pessimistic only.
    fn prepare_with_selection(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        selection: ProvingSelection,
    ) -> Result<Self::Precomputations, SelectionError> {
        Self::validate_selection(selection)?;
        Ok(self.prepare(circuit, setup, selection.security_level))
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>);
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::test_support::{TestBackend, TestConfiguration};

    struct MustNotInitialize;

    impl ExecutionBackend for MustNotInitialize {
        type Configuration = TestConfiguration;
        type Allocator = <TestBackend as ExecutionBackend>::Allocator;
        type Memory = <TestBackend as ExecutionBackend>::Memory;
        type Snapshot = <TestBackend as ExecutionBackend>::Snapshot;
        type Precomputations = <TestBackend as ExecutionBackend>::Precomputations;

        fn initialize(_: &ExecutionProverConfiguration<TestConfiguration>, _: Arc<Worker>) -> Self {
            panic!("backend initialization preceded capability rejection")
        }
        fn allocate_trace_block(&self, _: usize) -> Self::Allocator {
            unreachable!()
        }
        fn allocate_memory(&self, _: JitRunnerRam) -> Self::Memory {
            unreachable!()
        }
        fn allocate_snapshot(&self) -> Self::Snapshot {
            unreachable!()
        }
        fn prepare(
            &self,
            _: CircuitType,
            _: CanonicalCircuitSetup,
            _: SecurityLevel,
        ) -> Self::Precomputations {
            unreachable!()
        }
        fn submit(&self, _: WorkBatch<Self::Allocator, Self::Precomputations>) {
            unreachable!()
        }
    }

    #[test]
    fn unsupported_backend_mode_precedes_initialize() {
        let selection = ProvingSelection {
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProvingSelection::default()
        };
        let config = ExecutionProverConfiguration::<TestConfiguration>::for_selection(selection);
        assert_eq!(config.selection(), selection);
        let result = crate::ExecutionProver::<MustNotInitialize>::try_with_configuration(config);
        match result {
            Err(SelectionError::UnsupportedBackendSoundnessMode {
                selection: rejected,
                ..
            }) => assert_eq!(rejected, selection),
            _ => panic!("expected UnsupportedBackendSoundnessMode before initialization"),
        }
    }
}
