use crate::messages::{
    GpuWorkBatch, GpuWorkRequest, GpuWorkResult, SetupInitializationRequest, WorkerResult,
};
use crate::precomputations::CircuitPrecomputations;
use crate::upstream::SecurityLevel;
use crate::workers::gpu_manager::GpuManager;
use crate::A;
use crossbeam_channel::{unbounded, Receiver};
use gpu_trace::witness::circuit_type::CircuitType;

/// Collision with caller-chosen batch ids is structurally impossible: setup
/// batches are fully drained before the constructor / `add_binary` returns
/// (`add_binary` is `&mut self`), and user batches are retired from the
/// manager before `commit_memory`/`prove` return.
pub(super) const SETUP_BATCH_ID: u64 = 0;

pub(super) struct PendingSetupInitialization {
    expected_circuit_types: Vec<CircuitType>,
    result_receiver: Receiver<WorkerResult<A>>,
}

pub(super) fn request_setup_initialization(
    gpu_manager: &GpuManager,
    security_level: SecurityLevel,
    precomputations: Vec<(CircuitType, CircuitPrecomputations)>,
) -> PendingSetupInitialization {
    assert!(
        !precomputations.is_empty(),
        "setup initialization batch must contain at least one circuit"
    );
    let (request_sender, request_receiver) = unbounded();
    let (result_sender, result_receiver) = unbounded();
    gpu_manager.send_batch(GpuWorkBatch {
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
            .send(GpuWorkRequest::SetupInitialization(
                SetupInitializationRequest {
                    batch_id: SETUP_BATCH_ID,
                    circuit_type,
                    sequence_id,
                    precomputations,
                    security_level,
                },
            ))
            .expect("GPU manager batch channel closed before setup initialization was submitted");
    }
    PendingSetupInitialization {
        expected_circuit_types,
        result_receiver,
    }
}

impl PendingSetupInitialization {
    pub fn wait(self) {
        let mut seen = vec![false; self.expected_circuit_types.len()];
        for result in self.result_receiver {
            match result {
                WorkerResult::GpuWorkResult(GpuWorkResult::SetupInitialization(result)) => {
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
            "GPU manager terminated before all setup initializations completed"
        );
    }
}
