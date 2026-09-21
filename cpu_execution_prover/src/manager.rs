//! Receive batches and return completions while one CPU request runs.

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

pub(crate) trait RequestExecutor<A: HostTraceAllocator, P>: Send + Sync + 'static {
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

// Hold the gate across both submission and terminal failure drainage: every
// accepted batch must be notified before its result sender drops.
struct Admission<A: HostTraceAllocator, P> {
    sender: Mutex<Option<Sender<WorkBatch<A, P>>>>,
    terminal: OnceLock<String>,
}

impl<A: HostTraceAllocator, P> Admission<A, P> {
    fn lock(&self) -> MutexGuard<'_, Option<Sender<WorkBatch<A, P>>>> {
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
        if let Err(rejected) = sender.send(batch) {
            let reason = self.terminal.get().map_or(MANAGER_STOPPED, String::as_str);
            report_refusal(rejected.into_inner(), reason);
        }
    }

    /// Close admission. Afterwards a submission is refused by its own thread.
    fn close(&self) {
        *self.lock() = None;
    }
}

pub(crate) struct CpuManager<A: HostTraceAllocator, P> {
    admission: Arc<Admission<A, P>>,
    coordinator: Option<JoinHandle<()>>,
    driver: Option<JoinHandle<()>>,
}

impl<A: HostTraceAllocator + 'static, P: Send + 'static> CpuManager<A, P> {
    pub(crate) fn try_new<E: RequestExecutor<A, P>>(
        worker: Arc<Worker>,
        executor: E,
    ) -> io::Result<Self> {
        let (batches_sender, batches_receiver) = unbounded();
        // The coordinator remains responsive while the request thread is occupied.
        let (dispatch_sender, dispatch_receiver) = bounded(0);
        let (outcome_sender, outcome_receiver) = unbounded();
        let admission = Arc::new(Admission {
            sender: Mutex::new(Some(batches_sender)),
            terminal: OnceLock::new(),
        });
        let coordinator_admission = admission.clone();
        let driver = thread::Builder::new()
            .name("cpu-exec-request".to_owned())
            .spawn(move || drive_requests(worker, executor, dispatch_receiver, outcome_sender))?;
        let coordinator = match thread::Builder::new()
            .name("cpu-exec-coordinator".to_owned())
            .spawn(move || {
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

    pub(crate) fn send_batch(&self, batch: WorkBatch<A, P>) {
        self.admission.submit(batch);
    }
}

const MANAGER_STOPPED: &str = "CPU execution manager is no longer running";

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
        // The coordinator drains accepted work before closing the request channel.
        self.admission.close();
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
    batches_receiver: Receiver<WorkBatch<A, P>>,
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
                Ok(batch) => {
                    let batch_id = batch.batch_id;
                    match batches.entry(batch_id) {
                        std::collections::hash_map::Entry::Occupied(_) => {
                            report_refusal(
                                batch,
                                &format!("batch id {batch_id} is already active"),
                            );
                        }
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            trace!("BATCH[{batch_id}] CPU_MANAGER received new batch");
                            batch_receivers.insert(batch_id, batch.receiver);
                            entry.insert(BatchState {
                                sender: batch.sender,
                                input_closed: false,
                                outstanding: 0,
                            });
                        }
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

fn fail<A: HostTraceAllocator, P>(
    admission: &Admission<A, P>,
    batches: &HashMap<u64, BatchState<A>>,
    batches_receiver: &mut Option<Receiver<WorkBatch<A, P>>>,
    reason: &str,
) {
    error!("CPU_MANAGER terminating: {reason}");
    {
        let mut gate = admission.lock();
        let _ = admission.terminal.set(reason.to_owned());
        *gate = None;
        if let Some(receiver) = batches_receiver.take() {
            for batch in receiver.try_iter() {
                report_refusal(batch, reason);
            }
        }
    }
    for (&batch_id, state) in batches {
        let _ = state
            .sender
            .send(WorkerResult::BackendFailure(BackendFailure {
                batch_id,
                reason: reason.to_owned(),
            }));
    }
}

fn drive_requests<A: HostTraceAllocator, P: Send, E: RequestExecutor<A, P>>(
    worker: Arc<Worker>,
    executor: E,
    dispatch: Receiver<WorkRequest<A, P>>,
    outcomes: Sender<Outcome<A>>,
) {
    while let Ok(request) = dispatch.recv() {
        // A panic must still deliver the outcome the coordinator is waiting for.
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

#[cfg(test)]
mod tests;
