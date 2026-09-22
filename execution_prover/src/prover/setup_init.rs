use crate::backend::ExecutionBackend;
use crate::messages::{
    SetupInitializationRequest, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use crate::upstream::SecurityLevel;
use crossbeam_channel::{unbounded, Receiver};
use execution_prover_model::circuit_type::CircuitType;

/// Collision with caller-chosen batch ids is structurally impossible: setup
/// batches are fully drained before the constructor / `add_binary` returns,
/// and user batches are retired before `commit_memory`/`prove` return.
pub(super) const SETUP_BATCH_ID: u64 = 0;

pub(super) struct PendingSetupInitialization<
    A: execution_prover_model::allocator::HostTraceAllocator,
> {
    expected_circuit_types: Vec<CircuitType>,
    result_receiver: Receiver<WorkerResult<A>>,
}

/// Submit a setup-initialization batch for every circuit.
///
/// Every registered circuit is initialized, including families with no
/// execution instances: their setup cap still prefixes the verifier's
/// non-determinism stream, so it must exist before `add_binary` returns.
pub(super) fn request_setup_initialization<B: ExecutionBackend>(
    backend: &B,
    security_level: SecurityLevel,
    precomputations: Vec<(CircuitType, B::Precomputations)>,
) -> PendingSetupInitialization<B::Allocator> {
    assert!(
        !precomputations.is_empty(),
        "setup initialization batch must contain at least one circuit"
    );
    let (request_sender, request_receiver) = unbounded();
    let (result_sender, result_receiver) = unbounded();
    backend.submit(WorkBatch {
        batch_id: SETUP_BATCH_ID,
        receiver: request_receiver,
        sender: result_sender,
    });
    let expected_circuit_types: Vec<CircuitType> = precomputations
        .iter()
        .map(|(circuit_type, _)| *circuit_type)
        .collect();
    for (sequence_id, (circuit_type, precomputations)) in precomputations.into_iter().enumerate() {
        request_sender
            .send(WorkRequest::SetupInitialization(
                SetupInitializationRequest {
                    batch_id: SETUP_BATCH_ID,
                    circuit_type,
                    sequence_id,
                    precomputations,
                    security_level,
                },
            ))
            .expect("backend batch channel closed before setup initialization was submitted");
    }
    PendingSetupInitialization {
        expected_circuit_types,
        result_receiver,
    }
}

impl<A: execution_prover_model::allocator::HostTraceAllocator> PendingSetupInitialization<A> {
    /// Block until every submitted setup has completed: `new` and
    /// `add_binary` must not return while a setup cap is still unavailable.
    pub fn wait(self) {
        let mut seen = vec![false; self.expected_circuit_types.len()];
        for result in self.result_receiver {
            match result {
                WorkerResult::BackendWorkResult(WorkResult::SetupInitialization(result)) => {
                    assert_eq!(result.batch_id, SETUP_BATCH_ID);
                    let expected_circuit_type = *self
                        .expected_circuit_types
                        .get(result.sequence_id)
                        .expect("setup initialization result has an out-of-range sequence id");
                    assert_eq!(result.circuit_type, expected_circuit_type);
                    assert!(
                        !std::mem::replace(&mut seen[result.sequence_id], true),
                        "duplicate setup initialization result for {expected_circuit_type:?}"
                    );
                }
                _ => panic!("unexpected worker result in setup initialization batch"),
            }
        }
        assert!(
            seen.iter().all(|&seen| seen),
            "backend terminated before all setup initializations completed"
        );
    }
}
