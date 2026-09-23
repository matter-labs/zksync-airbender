//! A finite host pool with synthetic commitments for orchestration tests.

use crate::backend::{CircuitPrecomputation, ExecutionBackend};
use crate::config::{BackendConfiguration, ExecutionProverConfiguration};
use crate::messages::{
    MemoryCommitmentResult, SetupInitializationResult, WorkBatch, WorkRequest, WorkResult,
    WorkerResult,
};
use crate::setup::CanonicalCircuitSetup;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel, BF};
use execution_prover_model::allocator::CpuTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use worker::Worker;

const BLOCK_BYTES: usize = 64 << 20;
const POOL_BLOCKS: usize = 64;
static REQUESTS: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone)]
pub(crate) struct TestPrecomputations(Arc<GKRCircuitArtifact<BF>>);

impl CircuitPrecomputation for TestPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.0
    }

    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength> {
        None
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct TestConfiguration;

impl BackendConfiguration for TestConfiguration {
    fn execution_defaults() -> ExecutionProverConfiguration<Self> {
        ExecutionProverConfiguration {
            max_thread_pool_threads: Some(1),
            expected_concurrent_jobs: 1,
            replay_worker_threads_count: 1,
            host_allocator_backing_allocation_size: BLOCK_BYTES,
            host_allocators_per_job_count: POOL_BLOCKS,
            min_free_host_allocators_per_job: 1,
            security_level: SecurityLevel::Sec100,
            ram_config: JitRunnerRam::Medium,
            backend: Self,
        }
    }
}

pub(crate) struct TestBackend {
    batches: Mutex<Vec<JoinHandle<()>>>,
}

impl Drop for TestBackend {
    fn drop(&mut self) {
        let mut panicked = false;
        for thread in self.batches.get_mut().unwrap().drain(..) {
            panicked |= thread.join().is_err();
        }
        assert!(!panicked, "test backend thread panicked");
    }
}

impl ExecutionBackend for TestBackend {
    type Configuration = TestConfiguration;
    type Allocator = CpuTraceAllocator;
    type Memory = Box<MemoryHolder>;
    type Snapshot = Box<TraceChunk>;
    type Precomputations = TestPrecomputations;

    fn initialize(
        _config: &ExecutionProverConfiguration<TestConfiguration>,
        _worker: Arc<Worker>,
    ) -> Self {
        Self {
            batches: Mutex::new(Vec::new()),
        }
    }

    fn allocate_trace_block(&self, bytes: usize) -> CpuTraceAllocator {
        CpuTraceAllocator::new(bytes)
    }

    fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory {
        MemoryHolder::allocate_zeroed(ram, Default::default())
    }

    fn allocate_snapshot(&self) -> Self::Snapshot {
        unsafe { Box::<TraceChunk>::new_zeroed().assume_init() }
    }

    fn prepare(
        &self,
        circuit: CircuitType,
        setup: CanonicalCircuitSetup,
        _security: SecurityLevel,
    ) -> TestPrecomputations {
        let compiled_circuit = match setup {
            CanonicalCircuitSetup::Riscv(setup) => setup.compiled_circuit,
            CanonicalCircuitSetup::Delegation(setup) => setup.compiled_circuit,
        };
        assert_eq!(compiled_circuit.trace_len, circuit.get_domain_size());
        TestPrecomputations(Arc::new(compiled_circuit))
    }

    fn submit(&self, batch: WorkBatch<CpuTraceAllocator, TestPrecomputations>) {
        self.batches
            .lock()
            .unwrap()
            .push(std::thread::spawn(move || {
                for request in batch.receiver {
                    assert_eq!(request.batch_id(), batch.batch_id);
                    if !matches!(request, WorkRequest::SetupInitialization(_)) {
                        REQUESTS.fetch_add(1, Ordering::SeqCst);
                    }
                    let result = match request {
                        WorkRequest::SetupInitialization(request) => {
                            WorkResult::SetupInitialization(SetupInitializationResult {
                                batch_id: request.batch_id,
                                circuit_type: request.circuit_type,
                                sequence_id: request.sequence_id,
                            })
                        }
                        WorkRequest::MemoryCommitment(request) => {
                            let config =
                                crate::prover_config(request.circuit_type, request.security_level);
                            WorkResult::MemoryCommitment(MemoryCommitmentResult {
                                batch_id: request.batch_id,
                                circuit_type: request.circuit_type,
                                sequence_id: request.sequence_id,
                                inits_and_teardowns: request.inits_and_teardowns,
                                tracing_data: request.tracing_data,
                                merkle_tree_caps: vec![
                                    MerkleTreeCapVarLength {
                                        cap: vec![[0; 8]; config.cap_size / config.lde_factor]
                                    };
                                    config.lde_factor
                                ],
                            })
                        }
                        WorkRequest::Proof(_) => panic!("test backend only commits"),
                    };
                    batch
                        .sender
                        .send(WorkerResult::BackendWorkResult(result))
                        .unwrap();
                }
            }));
    }
}

mod orchestrator;
