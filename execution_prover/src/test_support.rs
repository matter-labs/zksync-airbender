//! A finite host pool with synthetic commitments for orchestration tests.

use crate::backend::{CircuitPrecomputation, ExecutionBackend};
use crate::config::{BackendConfiguration, ExecutionProverConfiguration};
use crate::messages::{
    MemoryCommitmentResult, ProofResult, SetupInitializationResult, WorkBatch, WorkRequest,
    WorkResult, WorkerResult,
};
use crate::setup::CanonicalCircuitSetup;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength, SecurityLevel, BF};
use crate::ProofProfile;
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
pub(crate) static PROFILES: Mutex<Vec<(u64, CircuitType, bool, ProofProfile)>> =
    Mutex::new(Vec::new());

#[derive(Clone)]
pub(crate) struct TestPrecomputations(pub(crate) Option<Arc<GKRCircuitArtifact<BF>>>);

impl CircuitPrecomputation for TestPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        self.0
            .as_ref()
            .expect("L1Wrap has no BabyBear compiled circuit")
    }

    fn setup_cap(&self, _profile: ProofProfile) -> Option<MerkleTreeCapVarLength> {
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
            assume_canonical_mop_inputs: false,
            backend: Self,
        }
    }
}

pub(crate) struct TestBackend {
    batches: Mutex<Vec<JoinHandle<()>>>,
    active_batches: Arc<Mutex<std::collections::HashSet<u64>>>,
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
            active_batches: Default::default(),
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
        _profiles: &[ProofProfile],
    ) -> TestPrecomputations {
        let compiled_circuit = match setup {
            CanonicalCircuitSetup::L1Wrap(_) => return TestPrecomputations(None),
            CanonicalCircuitSetup::Riscv(setup) => setup.compiled_circuit,
            CanonicalCircuitSetup::Delegation(setup) => setup.compiled_circuit,
        };
        assert_eq!(compiled_circuit.trace_len, circuit.get_domain_size());
        TestPrecomputations(Some(Arc::new(compiled_circuit)))
    }

    fn submit(&self, batch: WorkBatch<CpuTraceAllocator, TestPrecomputations>) {
        assert!(
            self.active_batches.lock().unwrap().insert(batch.batch_id),
            "test batch is already active"
        );
        let active_batches = self.active_batches.clone();
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
                        WorkRequest::L1WrapProof(request) => {
                            PROFILES.lock().unwrap().push((
                                request.batch_id,
                                CircuitType::L1Wrap,
                                true,
                                ProofProfile::L1Wrap,
                            ));
                            WorkResult::L1WrapProof(crate::messages::L1WrapProofResult {
                                batch_id: request.batch_id,
                                inits_and_teardowns: request.inits_and_teardowns,
                                tracing_data: request.tracing_data,
                                result: crate::L1WrapResult {
                                    proof: empty_l1_proof(),
                                    commitment_mode: request.commitment_mode,
                                },
                            })
                        }
                        WorkRequest::SetupInitialization(request) => {
                            WorkResult::SetupInitialization(SetupInitializationResult {
                                batch_id: request.batch_id,
                                circuit_type: request.circuit_type,
                                sequence_id: request.sequence_id,
                            })
                        }
                        WorkRequest::MemoryCommitment(request) => {
                            PROFILES.lock().unwrap().push((
                                request.batch_id,
                                request.circuit_type,
                                false,
                                request.profile,
                            ));
                            let config = crate::prover_config(
                                request.circuit_type,
                                request.profile,
                                request.security_level,
                            );
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
                        WorkRequest::Proof(request) => {
                            PROFILES.lock().unwrap().push((
                                request.batch_id,
                                request.circuit_type,
                                true,
                                request.profile,
                            ));
                            WorkResult::Proof(ProofResult {
                                batch_id: request.batch_id,
                                circuit_type: request.circuit_type,
                                sequence_id: request.sequence_id,
                                inits_and_teardowns: request.inits_and_teardowns,
                                tracing_data: request.tracing_data,
                                proof: crate::upstream::GKRProof {
                                    external_challenges: request.external_challenges,
                                    final_explicit_evaluations: Default::default(),
                                    sumcheck_intermediate_values: Default::default(),
                                    whir_proof: Default::default(),
                                    grand_product_accumulator_computed: Default::default(),
                                    inits_and_teardowns_top_bits: Vec::new(),
                                    lookup_challenges_pow_nonce: 0,
                                    batched_proximity_check_pow_nonce: 0,
                                    intermediate_transcript_seed: None,
                                },
                            })
                        }
                    };
                    batch
                        .sender
                        .send(WorkerResult::BackendWorkResult(result))
                        .unwrap();
                }
                assert!(active_batches.lock().unwrap().remove(&batch.batch_id));
            }));
    }
}

pub(crate) fn empty_l1_proof() -> crate::L1Proof {
    use ::prover::field::{Field, Proth120};
    crate::upstream::GKRProof {
        external_challenges: crate::upstream::GKRExternalChallenges {
            permutation_argument_linearization_challenges: [Proth120::ZERO;
                ::prover::cs::definitions::NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1],
            permutation_argument_additive_part: Proth120::ZERO,
            _marker: Default::default(),
        },
        final_explicit_evaluations: Default::default(),
        sumcheck_intermediate_values: Default::default(),
        whir_proof: Default::default(),
        grand_product_accumulator_computed: Default::default(),
        inits_and_teardowns_top_bits: Vec::new(),
        lookup_challenges_pow_nonce: 0,
        batched_proximity_check_pow_nonce: 0,
        intermediate_transcript_seed: None,
    }
}

mod orchestrator;
