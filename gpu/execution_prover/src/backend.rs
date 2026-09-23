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
use execution_prover::messages::WorkBatch;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::circuit_type::CircuitType;
use gpu_core::primitives::field::BF;
use riscv_transpiler::jit::JitRunnerRam;
use std::sync::Arc;
use worker::Worker;

impl CircuitPrecomputation for CircuitPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        self.gkr_programs.compiled_circuit()
    }

    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength> {
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

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        security: SecurityLevel,
    ) -> Self::Precomputations {
        CircuitPrecomputations::from_canonical(circuit, setup, security).unwrap()
    }

    fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
        self.manager.send_batch(batch);
    }
}
