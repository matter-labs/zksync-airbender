use super::*;
use crate::CpuTraceAllocator;
use execution_prover::messages::{SetupInitializationRequest, SetupInitializationResult};
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use prover::definitions::SecurityLevel;
use std::time::Duration;

type Manager = CpuManager<CpuTraceAllocator, Arc<()>>;
type Event = WorkerResult<CpuTraceAllocator>;
type Identity = (u64, usize);
const TIMEOUT: Duration = Duration::from_secs(20);

enum Action {
    Complete,
    Fail,
    Panic,
}

struct Executor {
    started: Sender<Identity>,
    actions: Receiver<Action>,
}

impl RequestExecutor<CpuTraceAllocator, Arc<()>> for Executor {
    fn execute(
        &self,
        request: WorkRequest<CpuTraceAllocator, Arc<()>>,
        _worker: &Worker,
    ) -> Result<WorkResult<CpuTraceAllocator>, String> {
        let identity = (request.batch_id(), request.sequence_id());
        self.started.send(identity).unwrap();
        match self.actions.recv_timeout(TIMEOUT).unwrap() {
            Action::Complete => Ok(WorkResult::SetupInitialization(SetupInitializationResult {
                batch_id: identity.0,
                sequence_id: identity.1,
                circuit_type: request.circuit_type(),
            })),
            Action::Fail => Err("execution failed".to_owned()),
            Action::Panic => panic!("execution failed"),
        }
    }
}

fn manager() -> (Manager, Receiver<Identity>, Sender<Action>) {
    let (started_sender, started) = unbounded();
    let (actions, action_receiver) = unbounded();
    let manager = CpuManager::try_new(
        Arc::new(Worker::new_with_num_threads(1)),
        Executor {
            started: started_sender,
            actions: action_receiver,
        },
    )
    .unwrap();
    (manager, started, actions)
}

fn batch(manager: &Manager, batch_id: u64, count: usize, owner: &Arc<()>) -> Receiver<Event> {
    let (requests, receiver) = unbounded();
    let (sender, results) = unbounded();
    for sequence_id in 0..count {
        requests
            .send(WorkRequest::SetupInitialization(
                SetupInitializationRequest {
                    batch_id,
                    sequence_id,
                    circuit_type: CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
                    precomputations: owner.clone(),
                    security_level: SecurityLevel::Sec100,
                },
            ))
            .unwrap();
    }
    drop(requests);
    manager.send_batch(WorkBatch {
        batch_id,
        receiver,
        sender,
    });
    results
}

fn failure(results: &Receiver<Event>) -> String {
    let Event::BackendFailure(failure) = results.recv_timeout(TIMEOUT).unwrap() else {
        panic!("expected a failure before channel closure");
    };
    assert!(matches!(
        results.recv_timeout(TIMEOUT),
        Err(crossbeam_channel::RecvTimeoutError::Disconnected)
    ));
    failure.reason
}

#[test]
fn shutdown_completes_accepted_work_serially_and_releases_owners() {
    let (manager, started, actions) = manager();
    let owner = Arc::new(());
    let first = batch(&manager, 1, 2, &owner);
    let second = batch(&manager, 2, 2, &owner);
    let (done_sender, done) = unbounded();
    let shutdown = thread::spawn(move || {
        drop(manager);
        done_sender.send(()).unwrap();
    });
    let mut identities = Vec::new();
    for _ in 0..4 {
        identities.push(started.recv_timeout(TIMEOUT).unwrap());
        assert!(matches!(
            started.recv_timeout(Duration::from_millis(50)),
            Err(crossbeam_channel::RecvTimeoutError::Timeout)
        ));
        actions.send(Action::Complete).unwrap();
    }
    done.recv_timeout(TIMEOUT).unwrap();
    shutdown.join().unwrap();
    identities.sort();
    assert_eq!(identities, [(1, 0), (1, 1), (2, 0), (2, 1)]);
    let mut completed = Vec::new();
    for results in [first, second] {
        for event in results.try_iter() {
            let Event::BackendWorkResult(result) = event else {
                panic!("expected a completion");
            };
            completed.push((result.batch_id(), result.sequence_id()));
        }
        assert!(results.is_empty());
        assert!(matches!(
            results.try_recv(),
            Err(crossbeam_channel::TryRecvError::Disconnected)
        ));
    }
    completed.sort();
    assert_eq!(completed, identities);
    assert_eq!(Arc::strong_count(&owner), 1);
    assert!(matches!(
        started.try_recv(),
        Err(crossbeam_channel::TryRecvError::Disconnected)
    ));
}

#[test]
fn duplicate_batch_id_preserves_the_original_batch() {
    let (manager, started, actions) = manager();
    let owner = Arc::new(());
    let original = batch(&manager, 7, 1, &owner);
    assert_eq!(started.recv_timeout(TIMEOUT).unwrap(), (7, 0));
    let duplicate = batch(&manager, 7, 1, &owner);
    assert!(failure(&duplicate).contains("already active"));
    actions.send(Action::Complete).unwrap();
    assert!(matches!(
        original.recv_timeout(TIMEOUT).unwrap(),
        Event::BackendWorkResult(_)
    ));
    drop(manager);
    assert_eq!(Arc::strong_count(&owner), 1);
}

#[test]
fn failure_notifies_running_queued_racing_and_future_batches() {
    for action in [Action::Fail, Action::Panic] {
        let (manager, started, actions) = manager();
        let manager = Arc::new(manager);
        let owner = Arc::new(());
        let running = batch(&manager, 1, 2, &owner);
        started.recv_timeout(TIMEOUT).unwrap();
        let queued = batch(&manager, 2, 1, &owner);
        let racing = {
            let manager = manager.clone();
            let owner = owner.clone();
            thread::spawn(move || batch(&manager, 3, 1, &owner))
        };
        actions.send(action).unwrap();
        let reason = failure(&running);
        assert!(reason.contains("execution failed"));
        assert_eq!(failure(&queued), reason);
        assert_eq!(failure(&racing.join().unwrap()), reason);
        assert_eq!(failure(&batch(&manager, 4, 1, &owner)), reason);
        drop(manager);
        assert_eq!(Arc::strong_count(&owner), 1);
        assert!(matches!(
            started.try_recv(),
            Err(crossbeam_channel::TryRecvError::Disconnected)
        ));
    }
}
