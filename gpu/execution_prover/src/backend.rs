use crate::config::GpuBackendConfiguration;
use crate::host_storage::{LockedBoxedMemoryHolder, LockedBoxedTraceChunk};
use crate::precomputations::CircuitPrecomputations;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel};
use crate::workers::gpu_manager::GpuManager;
use crate::A;
use era_cudart::device::get_device_count;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use execution_prover::backend::{CircuitPrecomputation, ExecutionBackend};
use execution_prover::config::ExecutionProverConfiguration;
use execution_prover::config::{ProvingSelection, SelectionError, SoundnessMode};
use execution_prover::messages::WorkBatch;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover::{ExecutionKind, ProofProfile};
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::MachineType;
use gpu_core::primitives::field::BF;
use riscv_transpiler::jit::JitRunnerRam;
use std::sync::Arc;
use worker::Worker;

impl CircuitPrecomputation for CircuitPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        self.gkr_programs.compiled_circuit()
    }

    fn setup_cap(&self, _profile: ProofProfile) -> Option<MerkleTreeCapVarLength> {
        self.setup_host
            .get_initialized()
            .map(|setup_host| MerkleTreeCapVarLength {
                cap: setup_host.unified_tree_cap().to_vec(),
            })
    }
}

pub struct GpuBackend {
    manager: GpuManager,
    extra_trace_blocks: usize,
}

impl ExecutionBackend for GpuBackend {
    type Configuration = GpuBackendConfiguration;
    type Allocator = A;
    type Memory = LockedBoxedMemoryHolder;
    type Snapshot = LockedBoxedTraceChunk;
    type Precomputations = CircuitPrecomputations;

    fn validate_selection(_selection: ProvingSelection) -> Result<(), SelectionError> {
        Ok(())
    }

    fn initialize(
        config: &ExecutionProverConfiguration<Self::Configuration>,
        _worker: Arc<Worker>,
    ) -> Self {
        let device_count = get_device_count().expect("CUDA device count query failed") as usize;
        assert_ne!(device_count, 0, "no CUDA capable devices found");
        let extra_trace_blocks = device_count * config.backend.host_allocators_per_device_count;
        // The manager serves batches only once every GPU worker is initialized,
        // so that initialization overlaps the host-side cache allocation below.
        let manager = GpuManager::new(config.backend.context_config());
        Self {
            manager,
            extra_trace_blocks,
        }
    }

    fn allocate_trace_block(&self, bytes: usize) -> Self::Allocator {
        let allocation = HostAllocation::alloc(bytes, CudaHostAllocFlags::DEFAULT)
            .expect("pinned host allocation for ExecutionProver pool failed");
        A::new([allocation], bytes.trailing_zeros())
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory {
        LockedBoxedMemoryHolder::new(ram)
    }

    fn allocate_snapshot(&self) -> Self::Snapshot {
        LockedBoxedTraceChunk::new()
    }

    fn extra_trace_blocks(&self) -> usize {
        self.extra_trace_blocks
    }

    fn admit_binary(&self, kind: ExecutionKind, _machine: MachineType, profiles: &[ProofProfile]) {
        assert_supported_registration(kind, profiles);
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
        profiles: &[ProofProfile],
    ) -> Self::Precomputations {
        self.prepare_with_selection(
            circuit,
            setup,
            ProvingSelection {
                security_level: security,
                soundness_mode: SoundnessMode::PessimisticConjecture,
            },
            profiles,
        )
        .unwrap_or_else(|error| panic!("{error}"))
    }

    fn prepare_with_selection(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        selection: ProvingSelection,
        _profiles: &[ProofProfile],
    ) -> Result<Self::Precomputations, SelectionError> {
        // `admit_binary` has already restricted this backend to `ProofProfile::Standard`.
        CircuitPrecomputations::from_canonical(circuit, setup, selection)
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        self.manager.send_batch(batch);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_gpu_backend_accepts_every_soundness_mode() {
        for &soundness_mode in SoundnessMode::ALL {
            let selection = ProvingSelection {
                soundness_mode,
                ..ProvingSelection::default()
            };
            assert_eq!(GpuBackend::validate_selection(selection), Ok(()));
        }
    }
}

fn assert_supported_registration(kind: ExecutionKind, profiles: &[ProofProfile]) {
    assert!(
        matches!(kind, ExecutionKind::Unrolled | ExecutionKind::Unified),
        "GPU backend does not support this CPU-only execution kind"
    );
    assert!(
        profiles
            .iter()
            .all(|profile| *profile == ProofProfile::Standard),
        "GPU backend only supports ProofProfile::Standard"
    );
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn l1_registration_is_rejected_before_setup() {
        for kind in [ExecutionKind::Unified22, ExecutionKind::L1Wrap21] {
            assert!(std::panic::catch_unwind(|| assert_supported_registration(
                kind,
                &[ProofProfile::Standard]
            ))
            .is_err());
        }
        for profile in [
            ProofProfile::L1Feeder,
            ProofProfile::L1FeederA,
            ProofProfile::L1Wrap,
        ] {
            assert!(std::panic::catch_unwind(|| assert_supported_registration(
                ExecutionKind::Unified,
                &[profile]
            ))
            .is_err());
        }
    }
}
