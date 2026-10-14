use crate::config::GpuBackendConfiguration;
use crate::host_storage::{LockedBoxedMemoryHolder, LockedBoxedTraceChunk};
use crate::precomputations::{validate_profiles, CircuitPrecomputations};
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel};
use crate::workers::gpu_manager::GpuManager;
use crate::A;
use era_cudart::device::get_device_count;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use execution_prover::backend::{CircuitPrecomputation, ExecutionBackend};
use execution_prover::config::ExecutionProverConfiguration;
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
        self.baby_bear().gkr_programs.compiled_circuit()
    }

    fn setup_cap(&self, profile: ProofProfile) -> Option<MerkleTreeCapVarLength> {
        self.baby_bear()
            .setup_host
            .get_initialized(profile)
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

    fn admit_binary(
        &self,
        execution_kind: ExecutionKind,
        _machine_type: MachineType,
        profiles: &[ProofProfile],
    ) {
        admit_binary_registration(execution_kind, profiles).unwrap_or_else(|err| panic!("{err}"));
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
        profiles: &[ProofProfile],
    ) -> Self::Precomputations {
        let profiles: Vec<ProofProfile> = validate_profiles(circuit, &setup, profiles)
            .into_iter()
            .collect();
        CircuitPrecomputations::from_canonical(circuit, setup, security, &profiles).unwrap()
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        self.manager.send_batch(batch);
    }
}

/// The GPU backend does not prove the 2^21 L1 wrap until W5: reject it before
/// any host setup is built.
pub(crate) fn admit_binary_registration(
    execution_kind: ExecutionKind,
    profiles: &[ProofProfile],
) -> Result<(), String> {
    if execution_kind == ExecutionKind::L1Wrap21 {
        return Err(format!(
            "the GPU backend does not support the 2^21 L1 wrap (ExecutionKind::L1Wrap21) until W5, got {profiles:?}"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn cpu_l1_wrap21_is_rejected_before_setup() {
        let err = admit_binary_registration(ExecutionKind::L1Wrap21, &[ProofProfile::L1Wrap])
            .unwrap_err();
        assert!(
            err.starts_with("the GPU backend does not support the 2^21 L1 wrap"),
            "{err}"
        );
    }
}
