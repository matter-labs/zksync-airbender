//! Lifecycle properties of the CPU manager, driven by an injected executor.
//!
//! Everything here is about ordering, ownership and termination rather than
//! proving, so the request payload is a sentinel owning a slice of a finite
//! trace block: a leaked payload shows up as a credit that never came back.
//! Every wait has an explicit timeout, so a regression fails rather than hangs.
#![feature(allocator_api)]

use cpu_execution_prover::test_support::{CpuManager, RequestExecutor};
use cpu_execution_prover::CpuTraceAllocator;
use crossbeam_channel::{bounded, unbounded, Receiver, RecvTimeoutError, Sender};
use execution_prover::messages::{
    SetupInitializationRequest, SetupInitializationResult, WorkBatch, WorkRequest, WorkResult,
    WorkerResult,
};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use prover::definitions::SecurityLevel;
use std::alloc::{Allocator, Layout};
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Duration;
use worker::Worker;

const TIMEOUT: Duration = Duration::from_secs(20);
const BLOCK_BYTES: usize = 1 << 16;
const OWNER_BYTES: usize = 1 << 10;

type Alloc = CpuTraceAllocator;
type Request = WorkRequest<Alloc, Owner>;
type Event = WorkerResult<Alloc>;
type Manager = CpuManager<Alloc, Owner>;

/// Stands in for the backend precomputations a request carries, with the one
/// property the manager is responsible for: it owns part of a finite block, so
/// dropping the request is what returns the credit.
struct Owner {
    _block: Vec<u8, Alloc>,
    live: Arc<AtomicUsize>,
}

impl Drop for Owner {
    fn drop(&mut self) {
        self.live.fetch_sub(1, Ordering::SeqCst);
    }
}

struct Credits {
    allocator: Alloc,
    live: Arc<AtomicUsize>,
}

impl Credits {
    fn new() -> Self {
        Self {
            allocator: CpuTraceAllocator::new(BLOCK_BYTES),
            live: Arc::new(AtomicUsize::new(0)),
        }
    }

    fn owner(&self) -> Owner {
        self.live.fetch_add(1, Ordering::SeqCst);
        Owner {
            _block: Vec::with_capacity_in(OWNER_BYTES, self.allocator.clone()),
            live: self.live.clone(),
        }
    }

    /// Every payload dropped, and the block whole again: a full-capacity
    /// allocation succeeds exactly when nothing is outstanding.
    fn assert_returned(&self) {
        assert_eq!(
            self.live.load(Ordering::SeqCst),
            0,
            "request payloads were not released"
        );
        let whole = Layout::from_size_align(self.allocator.capacity(), 1).unwrap();
        let block = self
            .allocator
            .allocate(whole)
            .expect("every credit returned to the block");
        // SAFETY: the probe allocation is returned exactly once.
        unsafe { self.allocator.deallocate(block.cast::<u8>(), whole) };
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
struct Identity {
    batch_id: u64,
    sequence_id: usize,
}

enum Injected {
    Fail,
    Panic,
}

const INJECTED_FAILURE: &str = "injected executor failure";

struct TestExecutor {
    started: Sender<Identity>,
    release: Option<Receiver<()>>,
    active: Arc<AtomicUsize>,
    max_active: Arc<AtomicUsize>,
    injected: Option<(Identity, Injected)>,
    dropped: Arc<AtomicBool>,
}

impl Drop for TestExecutor {
    fn drop(&mut self) {
        self.dropped.store(true, Ordering::SeqCst);
    }
}

impl RequestExecutor<Alloc, Owner> for TestExecutor {
    fn execute(&self, request: Request, _worker: &Worker) -> Result<WorkResult<Alloc>, String> {
        let identity = Identity {
            batch_id: request.batch_id(),
            sequence_id: request.sequence_id(),
        };
        let circuit_type = request.circuit_type();
        let active = self.active.fetch_add(1, Ordering::SeqCst) + 1;
        self.max_active.fetch_max(active, Ordering::SeqCst);
        self.started.send(identity).expect("start is observed");
        if let Some(release) = &self.release {
            release
                .recv_timeout(TIMEOUT)
                .expect("release signal arrives");
        }
        self.active.fetch_sub(1, Ordering::SeqCst);
        // Released in every outcome, including the injected failures below.
        drop(request);
        match &self.injected {
            Some((target, Injected::Fail)) if *target == identity => {
                return Err(INJECTED_FAILURE.to_owned())
            }
            Some((target, Injected::Panic)) if *target == identity => {
                panic!("{INJECTED_FAILURE}")
            }
            _ => {}
        }
        Ok(WorkResult::SetupInitialization(SetupInitializationResult {
            batch_id: identity.batch_id,
            circuit_type,
            sequence_id: identity.sequence_id,
        }))
    }
}

struct Handles {
    started: Receiver<Identity>,
    release: Option<Sender<()>>,
    max_active: Arc<AtomicUsize>,
    dropped: Arc<AtomicBool>,
}

/// A gated executor blocks in `execute` until the test releases it, which is
/// how a test holds one request "running" while it submits more.
fn executor(gated: bool, injected: Option<(Identity, Injected)>) -> (TestExecutor, Handles) {
    let (started_sender, started) = unbounded();
    let (release_sender, release) = if gated {
        let (sender, receiver) = bounded(0);
        (Some(sender), Some(receiver))
    } else {
        (None, None)
    };
    let max_active = Arc::new(AtomicUsize::new(0));
    let dropped = Arc::new(AtomicBool::new(false));
    let executor = TestExecutor {
        started: started_sender,
        release,
        active: Arc::new(AtomicUsize::new(0)),
        max_active: max_active.clone(),
        injected,
        dropped: dropped.clone(),
    };
    let handles = Handles {
        started,
        release: release_sender,
        max_active,
        dropped,
    };
    (executor, handles)
}

struct Batch {
    requests: Sender<Request>,
    events: Receiver<Event>,
}

fn open_batch(manager: &Manager, batch_id: u64) -> Batch {
    let (requests, receiver) = unbounded();
    let (sender, events) = unbounded();
    manager.send_batch(WorkBatch {
        batch_id,
        receiver,
        sender,
    });
    Batch { requests, events }
}

fn submit(batch: &Batch, credits: &Credits, batch_id: u64, count: usize) -> Vec<Identity> {
    (0..count)
        .map(|sequence_id| {
            batch
                .requests
                .send(WorkRequest::SetupInitialization(
                    SetupInitializationRequest {
                        batch_id,
                        circuit_type: CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
                        sequence_id,
                        precomputations: credits.owner(),
                        security_level: SecurityLevel::Sec100,
                    },
                ))
                .expect("the manager accepts the request");
            Identity {
                batch_id,
                sequence_id,
            }
        })
        .collect()
}

/// Close a batch's input and read it to closure. Returning at all is the
/// property under test: the orchestrator's collector loop ends only when the
/// manager drops the batch's result sender.
fn drain(batch: Batch, label: &str) -> Vec<Identity> {
    let Batch { requests, events } = batch;
    drop(requests);
    let mut identities = Vec::new();
    loop {
        match events.recv_timeout(TIMEOUT) {
            Ok(WorkerResult::BackendWorkResult(result)) => identities.push(Identity {
                batch_id: result.batch_id(),
                sequence_id: result.sequence_id(),
            }),
            Ok(WorkerResult::BackendFailure(failure)) => {
                panic!("{label}: unexpected backend failure: {}", failure.reason)
            }
            Ok(_) => panic!("{label}: unexpected event"),
            Err(RecvTimeoutError::Disconnected) => break,
            Err(RecvTimeoutError::Timeout) => {
                panic!("{label}: the result channel neither delivered nor closed in {TIMEOUT:?}")
            }
        }
    }
    identities
}

fn with_timeout<T: Send + 'static>(
    label: &'static str,
    body: impl FnOnce() -> T + Send + 'static,
) -> T {
    let (done, wait) = bounded(1);
    let handle = thread::spawn(move || {
        let _ = done.send(body());
    });
    match wait.recv_timeout(TIMEOUT) {
        Ok(value) => {
            let _ = handle.join();
            value
        }
        Err(RecvTimeoutError::Timeout) => panic!("{label} did not finish within {TIMEOUT:?}"),
        Err(RecvTimeoutError::Disconnected) => match handle.join() {
            Err(payload) => std::panic::resume_unwind(payload),
            Ok(()) => unreachable!(),
        },
    }
}

fn await_failure(events: &Receiver<Event>, label: &str) -> String {
    loop {
        match events.recv_timeout(TIMEOUT) {
            Ok(WorkerResult::BackendFailure(failure)) => return failure.reason,
            Ok(_) => continue,
            Err(RecvTimeoutError::Disconnected) => {
                panic!("{label}: the batch closed without reporting the failure")
            }
            Err(RecvTimeoutError::Timeout) => {
                panic!("{label}: no failure was reported within {TIMEOUT:?}")
            }
        }
    }
}

/// Read a batch to closure and require that it learned its fate on the way.
/// A channel that only closes tells the orchestrator nothing: its collector
/// ends when *every* sender is gone.
fn assert_told_before_closing(events: &Receiver<Event>, label: &str) {
    let mut informed = false;
    loop {
        match events.recv_timeout(TIMEOUT) {
            Ok(WorkerResult::BackendWorkResult(_)) | Ok(WorkerResult::BackendFailure(_)) => {
                informed = true
            }
            Ok(_) => continue,
            Err(RecvTimeoutError::Disconnected) => break,
            Err(RecvTimeoutError::Timeout) => {
                panic!("{label}: the result channel stayed open for {TIMEOUT:?}")
            }
        }
    }
    assert!(
        informed,
        "{label}: the batch was dropped without completions or a failure"
    );
}

fn await_closure(events: &Receiver<Event>, label: &str) {
    loop {
        match events.recv_timeout(TIMEOUT) {
            Ok(_) => continue,
            Err(RecvTimeoutError::Disconnected) => return,
            Err(RecvTimeoutError::Timeout) => {
                panic!("{label}: the result channel stayed open for {TIMEOUT:?}")
            }
        }
    }
}

#[test]
fn one_request_runs_at_a_time_across_batches() {
    let worker = Arc::new(Worker::new_with_num_threads(4));
    let credits = Credits::new();
    let (executor, handles) = executor(true, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let first = open_batch(&manager, 1);
    let second = open_batch(&manager, 2);
    let mut expected = submit(&first, &credits, 1, 2);
    expected.extend(submit(&second, &credits, 2, 2));

    let release = handles.release.as_ref().expect("gated executor");
    for _ in 0..expected.len() {
        let started = handles
            .started
            .recv_timeout(TIMEOUT)
            .expect("a request starts");
        assert!(
            handles.started.try_recv().is_err(),
            "a second request started while {started:?} was still running"
        );
        release
            .send_timeout((), TIMEOUT)
            .expect("the running request is released");
    }
    assert_eq!(handles.max_active.load(Ordering::SeqCst), 1);

    let mut completed = drain(first, "batch 1");
    completed.extend(drain(second, "batch 2"));
    completed.sort();
    expected.sort();
    assert_eq!(completed, expected);
    credits.assert_returned();
}

#[test]
fn a_duplicate_batch_id_is_refused_without_disturbing_the_original() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let (executor, handles) = executor(true, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let original = open_batch(&manager, 7);
    let mut expected = submit(&original, &credits, 7, 2);
    let release = handles.release.as_ref().expect("gated executor");

    // The duplicate arrives while the original is unambiguously live: its first
    // request is running and its second is still queued.
    handles
        .started
        .recv_timeout(TIMEOUT)
        .expect("the original batch starts running");
    let duplicate = open_batch(&manager, 7);
    let reason = await_failure(&duplicate.events, "duplicate batch");
    assert!(reason.contains("already active"), "{reason}");
    await_closure(&duplicate.events, "duplicate batch");
    drop(duplicate);

    // A release is a rendezvous, so each send lands exactly when the next
    // request is waiting to be let go.
    for _ in 0..expected.len() {
        release
            .send_timeout((), TIMEOUT)
            .expect("the running request is released");
    }
    let mut completed = drain(original, "original batch 7");
    completed.sort();
    expected.sort();
    assert_eq!(completed, expected);

    // A duplicate id is a caller error, not a manager failure: it keeps serving.
    assert_eq!(manager.terminal_reason(), None);
    let next = open_batch(&manager, 8);
    let expected_next = submit(&next, &credits, 8, 1);
    release
        .send_timeout((), TIMEOUT)
        .expect("the follow-up request is released");
    assert_eq!(drain(next, "batch 8").len(), expected_next.len());
    credits.assert_returned();
}

#[test]
fn every_accepted_identity_completes_exactly_once() {
    let worker = Arc::new(Worker::new_with_num_threads(4));
    let credits = Credits::new();
    let (executor, handles) = executor(false, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let batches: Vec<_> = (1..=3).map(|id| (id, open_batch(&manager, id))).collect();
    let mut expected = Vec::new();
    for (batch_id, batch) in &batches {
        expected.extend(submit(batch, &credits, *batch_id, 3));
    }

    let mut counts: HashMap<Identity, usize> = HashMap::new();
    for (batch_id, batch) in batches {
        for identity in drain(batch, "batch") {
            assert_eq!(identity.batch_id, batch_id);
            *counts.entry(identity).or_default() += 1;
        }
    }
    assert_eq!(counts.len(), expected.len());
    for identity in expected {
        assert_eq!(counts.get(&identity), Some(&1), "{identity:?}");
    }
    credits.assert_returned();
    drop(handles);
}

#[test]
fn repeated_batches_return_every_owner_and_credit() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let (executor, handles) = executor(false, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();
    for round in 0..4 {
        let batch = open_batch(&manager, round);
        let expected = submit(&batch, &credits, round, 3);
        assert_eq!(drain(batch, "round").len(), expected.len());
        credits.assert_returned();
    }
    drop(handles);
}

#[test]
fn closing_input_closes_the_result_channel() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let (executor, handles) = executor(false, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();

    let empty = open_batch(&manager, 10);
    assert!(drain(empty, "empty batch").is_empty());

    let batch = open_batch(&manager, 11);
    let expected = submit(&batch, &credits, 11, 2);
    assert_eq!(drain(batch, "batch 11").len(), expected.len());

    // A batch id is reusable once its predecessor has retired.
    let reused = open_batch(&manager, 11);
    assert_eq!(drain(reused, "reused batch 11").len(), 0);
    credits.assert_returned();
    drop(handles);
}

#[test]
fn shutdown_drains_accepted_work_and_joins() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let (executor, handles) = executor(false, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let batch = open_batch(&manager, 5);
    let expected = submit(&batch, &credits, 5, 4);
    let Batch { requests, events } = batch;
    drop(requests);

    let dropped = handles.dropped.clone();
    with_timeout("manager shutdown", move || drop(manager));
    assert!(
        dropped.load(Ordering::SeqCst),
        "shutdown returned before the request thread was joined"
    );

    let mut completed = 0;
    while let Ok(event) = events.try_recv() {
        match event {
            WorkerResult::BackendWorkResult(_) => completed += 1,
            _ => panic!("unexpected event after shutdown"),
        }
    }
    assert_eq!(completed, expected.len());
    credits.assert_returned();
}

#[test]
fn a_single_proving_thread_still_completes_every_request() {
    let worker = Arc::new(Worker::new_with_num_threads(1));
    let credits = Credits::new();
    let (executor, handles) = executor(false, None);
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let batch = open_batch(&manager, 42);
    let expected = submit(&batch, &credits, 42, 4);
    assert_eq!(drain(batch, "single-thread batch").len(), expected.len());
    credits.assert_returned();
    drop(handles);
}

#[test]
fn an_executor_failure_terminates_the_manager() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let failing = Identity {
        batch_id: 1,
        sequence_id: 1,
    };
    let (executor, handles) = executor(false, Some((failing, Injected::Fail)));
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let first = open_batch(&manager, 1);
    let second = open_batch(&manager, 2);
    submit(&first, &credits, 1, 2);
    submit(&second, &credits, 2, 1);

    // Both batches keep their input open, so both must be told.
    let reason = await_failure(&first.events, "batch 1");
    assert!(reason.contains(INJECTED_FAILURE), "{reason}");
    await_failure(&second.events, "batch 2");
    await_closure(&first.events, "batch 1");
    await_closure(&second.events, "batch 2");
    assert_eq!(manager.terminal_reason().as_deref(), Some(reason.as_str()));

    // A later batch is refused naming the failure, not a generic closure.
    let late = open_batch(&manager, 3);
    let late_reason = await_failure(&late.events, "late batch");
    assert_eq!(late_reason, reason);
    await_closure(&late.events, "late batch");

    drop(first);
    drop(second);
    drop(late);
    let dropped = handles.dropped.clone();
    with_timeout("shutdown after failure", move || drop(manager));
    assert!(dropped.load(Ordering::SeqCst));
    // Abandoned requests are dropped, not recycled; dropping releases them.
    credits.assert_returned();
}

/// Submission lands first: the batch is in service when the failure is raised.
#[test]
fn a_batch_admitted_before_the_failure_is_told_about_it() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let failing = Identity {
        batch_id: 1,
        sequence_id: 0,
    };
    let (executor, handles) = executor(true, Some((failing, Injected::Fail)));
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let first = open_batch(&manager, 1);
    submit(&first, &credits, 1, 1);
    let release = handles.release.as_ref().expect("gated executor");

    // The failing request is held inside the executor, so the batch below is
    // admitted while the failure is in flight.
    handles
        .started
        .recv_timeout(TIMEOUT)
        .expect("the failing request starts");
    let late = open_batch(&manager, 2);
    submit(&late, &credits, 2, 1);
    release
        .send_timeout((), TIMEOUT)
        .expect("the failing request is released");

    let reason = await_failure(&first.events, "batch 1");
    assert!(reason.contains(INJECTED_FAILURE), "{reason}");
    let late_reason = await_failure(&late.events, "admitted late batch");
    assert_eq!(late_reason, reason);
    await_closure(&first.events, "batch 1");
    await_closure(&late.events, "admitted late batch");

    drop(first);
    drop(late);
    with_timeout("shutdown after failure", move || drop(manager));
    credits.assert_returned();
}

/// The failure lands first: submission must be refused by the submitting thread
/// itself, naming the failure that ended the manager.
#[test]
fn a_batch_submitted_after_the_failure_is_refused_with_the_original_reason() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let failing = Identity {
        batch_id: 1,
        sequence_id: 0,
    };
    let (executor, _handles) = executor(false, Some((failing, Injected::Fail)));
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let first = open_batch(&manager, 1);
    submit(&first, &credits, 1, 1);
    let reason = await_failure(&first.events, "batch 1");
    assert!(reason.contains(INJECTED_FAILURE), "{reason}");

    let late = open_batch(&manager, 2);
    let late_reason = await_failure(&late.events, "late batch");
    assert_eq!(late_reason, reason);
    await_closure(&late.events, "late batch");

    drop(first);
    drop(late);
    with_timeout("shutdown after failure", move || drop(manager));
    credits.assert_returned();
}

/// Neither ordering forced: a submission and the failure are released from one
/// barrier, so whichever wins, the batch must still learn its fate.
#[test]
fn a_batch_submitted_concurrently_with_the_failure_is_never_dropped_silently() {
    for round in 0..16 {
        with_timeout("submit versus failure race", move || {
            let worker = Arc::new(Worker::new_with_num_threads(2));
            let credits = Credits::new();
            let failing = Identity {
                batch_id: 1,
                sequence_id: 0,
            };
            let (executor, handles) = executor(true, Some((failing, Injected::Fail)));
            let manager = CpuManager::try_new(worker, executor).unwrap();
            let first = open_batch(&manager, 1);
            submit(&first, &credits, 1, 1);
            handles
                .started
                .recv_timeout(TIMEOUT)
                .expect("the failing request starts");
            let release = handles.release.as_ref().expect("gated executor");

            let barrier = Barrier::new(2);
            let (handle_sender, handle_receiver) = bounded(1);
            thread::scope(|scope| {
                scope.spawn(|| {
                    barrier.wait();
                    let late = open_batch(&manager, 2);
                    // Not `submit`: in a race against the failure the manager
                    // may already have refused the batch, and a rejected send
                    // only means the request never entered the system.
                    let _ = late.requests.send(WorkRequest::SetupInitialization(
                        SetupInitializationRequest {
                            batch_id: 2,
                            circuit_type: CircuitType::Unrolled(
                                UnrolledCircuitType::InitsAndTeardowns,
                            ),
                            sequence_id: 0,
                            precomputations: credits.owner(),
                            security_level: SecurityLevel::Sec100,
                        },
                    ));
                    handle_sender.send(late).expect("late batch handed back");
                });
                barrier.wait();
                release
                    .send_timeout((), TIMEOUT)
                    .expect("the failing request is released");
            });

            let late = handle_receiver
                .recv_timeout(TIMEOUT)
                .expect("late batch handle");
            assert_told_before_closing(&first.events, &format!("round {round} batch 1"));
            assert_told_before_closing(&late.events, &format!("round {round} late batch"));

            drop(first);
            drop(late);
            drop(manager);
            credits.assert_returned();
        });
    }
}

#[test]
fn an_executor_panic_is_reported_as_a_terminal_failure() {
    let worker = Arc::new(Worker::new_with_num_threads(2));
    let credits = Credits::new();
    let panicking = Identity {
        batch_id: 3,
        sequence_id: 0,
    };
    let (executor, handles) = executor(false, Some((panicking, Injected::Panic)));
    let manager = CpuManager::try_new(worker, executor).unwrap();
    let batch = open_batch(&manager, 3);
    submit(&batch, &credits, 3, 2);

    let reason = await_failure(&batch.events, "batch 3");
    assert!(reason.contains("panicked"), "{reason}");
    assert!(reason.contains(INJECTED_FAILURE), "{reason}");
    await_closure(&batch.events, "batch 3");
    assert_eq!(manager.terminal_reason(), Some(reason));

    drop(batch);
    let dropped = handles.dropped.clone();
    with_timeout("shutdown after panic", move || drop(manager));
    assert!(dropped.load(Ordering::SeqCst));
    credits.assert_returned();
}
