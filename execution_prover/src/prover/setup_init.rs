use crate::backend::ExecutionBackend;
use crate::messages::{
    SetupInitializationRequest, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use crossbeam_channel::{unbounded, Receiver};
use execution_prover_model::circuit_type::CircuitType;
use fft::GoodAllocator;

pub(super) struct PendingSetupInitialization<A: GoodAllocator> {
    batch_id: u64,
    expected_circuit_types: Vec<CircuitType>,
    result_receiver: Receiver<WorkerResult<A>>,
}

pub(super) fn request_setup_initialization<B: ExecutionBackend>(
    backend: &B,
    // Setup batches use distinct ids until finalize_setup drains them all.
    // Proving finalizes first, so caller-chosen batch ids cannot collide.
    batch_id: u64,
    precomputations: Vec<(CircuitType, B::Precomputations)>,
) -> PendingSetupInitialization<B::Allocator> {
    assert!(
        !precomputations.is_empty(),
        "setup initialization batch must contain at least one circuit"
    );
    let (request_sender, request_receiver) = unbounded();
    let (result_sender, result_receiver) = unbounded();
    backend.submit(WorkBatch {
        batch_id,
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
                    batch_id,
                    circuit_type,
                    sequence_id,
                    precomputations,
                },
            ))
            .expect("backend batch channel closed before setup initialization was submitted");
    }
    PendingSetupInitialization {
        batch_id,
        expected_circuit_types,
        result_receiver,
    }
}

impl<A: GoodAllocator> PendingSetupInitialization<A> {
    pub fn wait(self) {
        let mut seen = vec![false; self.expected_circuit_types.len()];
        for result in self.result_receiver {
            match result {
                WorkerResult::BackendWorkResult(WorkResult::SetupInitialization(result)) => {
                    assert_eq!(result.batch_id, self.batch_id);
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
