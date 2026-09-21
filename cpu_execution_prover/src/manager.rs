//! The CPU manager: one coordinator, one request-driving thread, one pool.
//!
//! The CPU has one compute resource, so the only scheduling decision left is
//! *when* a request may start, and that is a rendezvous: the coordinator's
//! offer completes only when the request thread is waiting for one. Nothing
//! else in the loop blocks, so batches, requests and completions keep being
//! processed while a request runs.
//!
//! Retirement is the other half of liveness. The shared collector iterates
//! until every result sender is dropped, so a batch's sender is dropped exactly
//! when its input has closed, no accepted request is outstanding, and every
//! completion has been forwarded.

use crossbeam_channel::{bounded, unbounded, Receiver, Select, Sender};
use execution_prover::messages::{
    BackendFailure, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};
use execution_prover_model::allocator::HostTraceAllocator;
use log::{error, trace, warn};
use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::io;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};
use std::thread::{self, JoinHandle};
use worker::Worker;

/// Executes one request to completion on the proving pool.
///
/// Injected, so the manager's lifecycle is testable without real proving. An
/// implementation may block for as long as the proof takes.
pub trait RequestExecutor<A: HostTraceAllocator, P>: Send + Sync + 'static {
    fn execute(&self, request: WorkRequest<A, P>, worker: &Worker)
        -> Result<WorkResult<A>, String>;
}

type Outcome<A> = Result<WorkResult<A>, String>;

struct BatchState<A: HostTraceAllocator> {
    sender: Sender<WorkerResult<A>>,
    input_closed: bool,
    /// Accepted requests whose completion has not been forwarded yet: queued,
    /// running, or completed but not yet sent.
    outstanding: usize,
}

impl<A: HostTraceAllocator> BatchState<A> {
    fn is_retired(&self) -> bool {
        self.input_closed && self.outstanding == 0
    }
}

/// The first failure a manager raised. A failure ends the instance, and every
/// later submission is refused naming that failure rather than a generic
/// "closed".
type TerminalReason = Arc<OnceLock<String>>;

/// A submitted batch the coordinator has not taken into service yet.
///
/// Its `Drop` reports the batch to its own caller, so no path can dispose of a
/// batch silently. Closing the result sender is *not* a failure notification:
/// the caller's collector ends only once every sender is gone, and its
/// producers hold their own clones while blocked on trace credits.
struct PendingBatch<A: HostTraceAllocator, P> {
    batch: Option<WorkBatch<A, P>>,
    terminal: TerminalReason,
}

impl<A: HostTraceAllocator, P> PendingBatch<A, P> {
    fn new(batch: WorkBatch<A, P>, terminal: TerminalReason) -> Self {
        Self {
            batch: Some(batch),
            terminal,
        }
    }

    fn batch_id(&self) -> u64 {
        self.batch
            .as_ref()
            .expect("pending batch is present")
            .batch_id
    }

    /// Take the batch into service. From here its own bookkeeping reports it.
    fn accept(mut self) -> WorkBatch<A, P> {
        self.batch.take().expect("pending batch is present")
    }

    fn refuse(mut self, reason: &str) {
        if let Some(batch) = self.batch.take() {
            report_refusal(batch, reason);
        }
    }
}

impl<A: HostTraceAllocator, P> Drop for PendingBatch<A, P> {
    fn drop(&mut self) {
        if let Some(batch) = self.batch.take() {
            let reason = self.terminal.get().map_or(MANAGER_STOPPED, String::as_str);
            report_refusal(batch, reason);
        }
    }
}

/// The submission gate; `sender` is `None` once admission has closed.
///
/// Submission holds the lock across the enqueue and closing holds it across the
/// mark-and-drop, so a batch either lands early enough for the coordinator's
/// drain to see it or is refused by the submitting thread itself.
struct Admission<A: HostTraceAllocator, P> {
    sender: Mutex<Option<Sender<PendingBatch<A, P>>>>,
    terminal: TerminalReason,
}

impl<A: HostTraceAllocator, P> Admission<A, P> {
    fn lock(&self) -> MutexGuard<'_, Option<Sender<PendingBatch<A, P>>>> {
        self.sender
            .lock()
            .expect("admission gate is never poisoned")
    }

    fn submit(&self, batch: WorkBatch<A, P>) {
        let sender = self.lock();
        let Some(sender) = sender.as_ref() else {
            let reason = self.terminal.get().map_or(MANAGER_STOPPED, String::as_str);
            report_refusal(batch, reason);
            return;
        };
        // The channel is unbounded, so holding the gate across the enqueue
        // cannot block a caller behind the coordinator.
        let pending = PendingBatch::new(batch, self.terminal.clone());
        let _ = sender.send(pending);
    }

    /// Close admission, recording `reason` if this is the first failure.
    fn close(&self, reason: Option<&str>) {
        let mut sender = self.lock();
        if let Some(reason) = reason {
            // Keeps the first reason: anything after it is a consequence.
            let _ = self.terminal.set(reason.to_owned());
        }
        *sender = None;
    }
}

pub struct CpuManager<A: HostTraceAllocator, P> {
    admission: Arc<Admission<A, P>>,
    coordinator: Option<JoinHandle<()>>,
    driver: Option<JoinHandle<()>>,
}

/// Spawn-failure injection for the startup-unwind test. Process-global, so a
/// test using it must own its process.
#[cfg(any(test, feature = "test_utils"))]
pub mod spawn_injection {
    use std::sync::atomic::{AtomicUsize, Ordering};

    static ALLOWED_SPAWNS: AtomicUsize = AtomicUsize::new(usize::MAX);

    /// Let `successes` manager spawns through, then fail every later one.
    pub fn fail_spawn_after(successes: usize) {
        ALLOWED_SPAWNS.store(successes, Ordering::SeqCst);
    }

    pub fn clear() {
        ALLOWED_SPAWNS.store(usize::MAX, Ordering::SeqCst);
    }

    pub(super) fn should_fail() -> bool {
        let mut current = ALLOWED_SPAWNS.load(Ordering::SeqCst);
        loop {
            if current == usize::MAX {
                return false;
            }
            if current == 0 {
                return true;
            }
            match ALLOWED_SPAWNS.compare_exchange(
                current,
                current - 1,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return false,
                Err(observed) => current = observed,
            }
        }
    }
}

#[cfg(not(any(test, feature = "test_utils")))]
mod spawn_injection {
    pub(super) fn should_fail() -> bool {
        false
    }
}

fn spawn_named(name: &str, stack: impl FnOnce() + Send + 'static) -> io::Result<JoinHandle<()>> {
    if spawn_injection::should_fail() {
        return Err(io::Error::other(format!(
            "injected spawn failure for the {name} thread"
        )));
    }
    thread::Builder::new().name(name.to_owned()).spawn(stack)
}

impl<A: HostTraceAllocator + 'static, P: Send + 'static> CpuManager<A, P> {
    /// Start the coordinator and the request thread. `worker` is the proving
    /// pool one request computes on, not the shared auxiliary pool. A thread
    /// that will not start is reported, and a driver that already started is
    /// joined before returning rather than left detached.
    pub fn try_new<E: RequestExecutor<A, P>>(worker: Arc<Worker>, executor: E) -> io::Result<Self> {
        let (batches_sender, batches_receiver) = unbounded();
        // Zero capacity: a dispatch completes only when the request thread is
        // waiting for work, so "the worker is idle" needs no separate flag and
        // cannot go stale.
        let (dispatch_sender, dispatch_receiver) = bounded(0);
        let (outcome_sender, outcome_receiver) = unbounded();
        let admission = Arc::new(Admission {
            sender: Mutex::new(Some(batches_sender)),
            terminal: Arc::new(OnceLock::new()),
        });
        let coordinator_admission = admission.clone();
        let driver = spawn_named("cpu-exec-request", move || {
            drive_requests(worker, executor, dispatch_receiver, outcome_sender)
        })?;
        let coordinator = match spawn_named("cpu-exec-coordinator", move || {
            coordinate(
                batches_receiver,
                dispatch_sender,
                outcome_receiver,
                coordinator_admission,
            )
        }) {
            Ok(coordinator) => coordinator,
            Err(error) => {
                // The dispatch sender moved into the closure that never ran,
                // so it is dropped with it and the driver's `recv` ends.
                let _ = driver.join();
                return Err(error);
            }
        };
        Ok(Self {
            admission,
            coordinator: Some(coordinator),
            driver: Some(driver),
        })
    }

    pub fn send_batch(&self, batch: WorkBatch<A, P>) {
        self.admission.submit(batch);
    }
}

#[cfg(any(test, feature = "test_utils"))]
impl<A: HostTraceAllocator, P> CpuManager<A, P> {
    pub fn terminal_reason(&self) -> Option<String> {
        self.admission.terminal.get().cloned()
    }
}

const MANAGER_STOPPED: &str = "CPU execution manager is no longer running";

/// Report a batch's refusal through its own result channel, then drop it: a
/// silent drop turns a refusal into a wait for work that will never start.
fn report_refusal<A: HostTraceAllocator, P>(batch: WorkBatch<A, P>, reason: &str) {
    let batch_id = batch.batch_id;
    error!("BATCH[{batch_id}] CPU_MANAGER refused the batch: {reason}");
    let _ = batch
        .sender
        .send(WorkerResult::BackendFailure(BackendFailure {
            batch_id,
            reason: reason.to_owned(),
        }));
}

impl<A: HostTraceAllocator, P> Drop for CpuManager<A, P> {
    fn drop(&mut self) {
        // Closing admission first lets the coordinator finish the work it has
        // already accepted; it then drops the dispatch channel, which is what
        // ends the request thread.
        self.admission.close(None);
        for (name, handle) in [
            ("coordinator", self.coordinator.take()),
            ("request", self.driver.take()),
        ] {
            if let Some(handle) = handle {
                if handle.join().is_err() {
                    error!("CPU_MANAGER {name} thread panicked");
                }
            }
        }
    }
}

fn coordinate<A: HostTraceAllocator, P>(
    batches_receiver: Receiver<PendingBatch<A, P>>,
    dispatch_sender: Sender<WorkRequest<A, P>>,
    outcome_receiver: Receiver<Outcome<A>>,
    admission: Arc<Admission<A, P>>,
) {
    let mut batches_receiver = Some(batches_receiver);
    let mut batch_receivers: HashMap<u64, Receiver<WorkRequest<A, P>>> = HashMap::new();
    let mut batches: HashMap<u64, BatchState<A>> = HashMap::new();
    let mut ready: VecDeque<WorkRequest<A, P>> = VecDeque::new();
    let mut busy = false;
    loop {
        let mut select = Select::new();
        let batches_index = batches_receiver.as_ref().map(|r| select.recv(r));
        let request_indexes: HashMap<usize, u64> = batch_receivers
            .iter()
            .map(|(&batch_id, receiver)| (select.recv(receiver), batch_id))
            .collect();
        let outcome_index = select.recv(&outcome_receiver);
        let dispatch_index = (!busy && !ready.is_empty()).then(|| select.send(&dispatch_sender));
        let op = select.select();
        let index = op.index();
        if batches_index == Some(index) {
            match op.recv(batches_receiver.as_ref().unwrap()) {
                Ok(pending) => {
                    let batch_id = pending.batch_id();
                    if batches.contains_key(&batch_id) {
                        // The batch already being served keeps its id: taking
                        // it over would drop the sender its caller is
                        // collecting on. The arriving batch is refused instead.
                        pending.refuse(&format!("batch id {batch_id} is already active"));
                    } else {
                        trace!("BATCH[{batch_id}] CPU_MANAGER received new batch");
                        let WorkBatch {
                            batch_id,
                            receiver,
                            sender,
                        } = pending.accept();
                        batch_receivers.insert(batch_id, receiver);
                        batches.insert(
                            batch_id,
                            BatchState {
                                sender,
                                input_closed: false,
                                outstanding: 0,
                            },
                        );
                    }
                }
                Err(_) => {
                    trace!("CPU_MANAGER batches channel closed");
                    batches_receiver = None;
                }
            }
        } else if let Some(&batch_id) = request_indexes.get(&index) {
            match op.recv(&batch_receivers[&batch_id]) {
                Ok(request) => {
                    assert_eq!(request.batch_id(), batch_id);
                    trace!(
                        "BATCH[{batch_id}] CPU_MANAGER received {} request for circuit {:?}[{}]",
                        request.kind_name(),
                        request.circuit_type(),
                        request.sequence_id()
                    );
                    let state = batches
                        .get_mut(&batch_id)
                        .expect("request for a batch that is not active");
                    state.outstanding += 1;
                    ready.push_back(request);
                }
                Err(_) => {
                    trace!("BATCH[{batch_id}] CPU_MANAGER work request channel closed");
                    batch_receivers.remove(&batch_id);
                    let state = batches
                        .get_mut(&batch_id)
                        .expect("closure of a batch that is not active");
                    state.input_closed = true;
                    if state.is_retired() {
                        trace!("BATCH[{batch_id}] CPU_MANAGER batch completed");
                        batches.remove(&batch_id);
                    }
                }
            }
        } else if index == outcome_index {
            busy = false;
            match op.recv(&outcome_receiver) {
                Ok(Ok(result)) => {
                    let batch_id = result.batch_id();
                    trace!(
                        "BATCH[{batch_id}] CPU_MANAGER received completion for circuit {:?}[{}]",
                        result.circuit_type(),
                        result.sequence_id()
                    );
                    let state = batches
                        .get_mut(&batch_id)
                        .expect("completion for a batch that is not active");
                    if state
                        .sender
                        .send(WorkerResult::BackendWorkResult(result))
                        .is_err()
                    {
                        // Nothing can be delivered any more, but the batch must
                        // still retire or this loop would never finish.
                        warn!("BATCH[{batch_id}] CPU_MANAGER result channel closed early");
                    }
                    state.outstanding -= 1;
                    if state.is_retired() {
                        trace!("BATCH[{batch_id}] CPU_MANAGER batch completed");
                        batches.remove(&batch_id);
                    }
                }
                Ok(Err(reason)) => {
                    fail(&admission, &batches, &mut batches_receiver, &reason);
                    return;
                }
                Err(_) => {
                    fail(&admission, &batches, &mut batches_receiver, DRIVER_STOPPED);
                    return;
                }
            }
        } else if dispatch_index == Some(index) {
            let request = ready.pop_front().expect("dispatch with an empty queue");
            let batch_id = request.batch_id();
            trace!(
                "BATCH[{batch_id}] CPU_MANAGER dispatching {} request for circuit {:?}[{}]",
                request.kind_name(),
                request.circuit_type(),
                request.sequence_id()
            );
            if op.send(&dispatch_sender, request).is_err() {
                fail(&admission, &batches, &mut batches_receiver, DRIVER_STOPPED);
                return;
            }
            busy = true;
        } else {
            unreachable!("select returned an unregistered operation");
        }
        if batches_receiver.is_none() && batches.is_empty() {
            break;
        }
    }
    trace!("CPU_MANAGER finished");
}

const DRIVER_STOPPED: &str = "CPU execution request thread stopped";

/// Raise a terminal failure: mark the instance, tell every caller still being
/// served, and refuse whatever arrived alongside the failure — all before
/// returning, because returning is what drops the queued requests and their
/// channels. Abandoned requests are dropped rather than recycled: a pool that
/// insists on unique ownership would panic over the top of the real error.
fn fail<A: HostTraceAllocator, P>(
    admission: &Admission<A, P>,
    batches: &HashMap<u64, BatchState<A>>,
    batches_receiver: &mut Option<Receiver<PendingBatch<A, P>>>,
    reason: &str,
) {
    // Closing admission under the gate is what makes the drain below complete:
    // afterwards a submission is refused by its own thread, and everything that
    // was admitted before it is already in the channel.
    admission.close(Some(reason));
    error!("CPU_MANAGER terminating: {reason}");
    for (&batch_id, state) in batches {
        let _ = state
            .sender
            .send(WorkerResult::BackendFailure(BackendFailure {
                batch_id,
                reason: reason.to_owned(),
            }));
    }
    if let Some(receiver) = batches_receiver.take() {
        for pending in receiver.try_iter() {
            pending.refuse(reason);
        }
    }
}

fn drive_requests<A: HostTraceAllocator, P: Send, E: RequestExecutor<A, P>>(
    worker: Arc<Worker>,
    executor: E,
    dispatch: Receiver<WorkRequest<A, P>>,
    outcomes: Sender<Outcome<A>>,
) {
    while let Ok(request) = dispatch.recv() {
        // The coordinator waits for exactly one outcome per dispatch, so a
        // panicking executor has to become a reported failure rather than an
        // unwind. The request is dropped by the unwind, returning its traces.
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            worker.pool.install(|| executor.execute(request, &worker))
        }))
        .unwrap_or_else(|payload| Err(panic_reason(payload)));
        if outcomes.send(outcome).is_err() {
            break;
        }
    }
}

fn panic_reason(payload: Box<dyn Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        format!("request execution panicked: {message}")
    } else if let Some(message) = payload.downcast_ref::<String>() {
        format!("request execution panicked: {message}")
    } else {
        "request execution panicked".to_owned()
    }
}
