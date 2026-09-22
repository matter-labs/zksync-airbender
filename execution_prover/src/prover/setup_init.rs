use crate::backend::ExecutionBackend;
use crate::messages::{
    SetupInitializationRequest, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use crate::upstream::SecurityLevel;
use crossbeam_channel::{unbounded, Receiver};
use execution_prover_model::circuit_type::CircuitType;

// Setup batches drain before construction or `add_binary` returns, so they
// cannot overlap user batches.
pub(super) const SETUP_BATCH_ID: u64 = 0;

pub(super) struct PendingSetupInitialization<
    A: execution_prover_model::allocator::HostTraceAllocator,
> {
    expected_circuit_types: Vec<Option<CircuitType>>,
    result_receiver: Receiver<WorkerResult<A>>,
}

// Even unused families need setup caps for the verifier's non-determinism stream.
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
    let expected_circuit_types: Vec<Option<CircuitType>> = precomputations
        .iter()
        .map(|(circuit_type, _)| Some(*circuit_type))
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
    pub fn wait(mut self) {
        for result in self.result_receiver {
            let WorkerResult::BackendWorkResult(WorkResult::SetupInitialization(result)) = result
            else {
                panic!("unexpected worker result in setup initialization batch");
            };
            assert_eq!(result.batch_id, SETUP_BATCH_ID);
            assert_eq!(
                self.expected_circuit_types[result.sequence_id].take(),
                Some(result.circuit_type),
            );
        }
        assert!(self.expected_circuit_types.iter().all(Option::is_none));
    }
}
