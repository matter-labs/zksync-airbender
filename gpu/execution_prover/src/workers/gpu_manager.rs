use crate::errors::{await_startup_aggregate, collect_worker_acknowledgements, GpuBackendError};
use crate::host_storage::GpuTraceAllocator;
use crate::precomputations::CircuitPrecomputations;
use crate::workers::gpu::get_gpu_worker_func;
use execution_prover::messages::{
    BackendFailure, WorkBatch, WorkRequest, WorkResult, WorkerResult,
};

/// The shared protocol types, specialized to this backend once.
pub(crate) type GpuWorkBatch = WorkBatch<GpuTraceAllocator, CircuitPrecomputations>;
pub(crate) type GpuWorkRequest = WorkRequest<GpuTraceAllocator, CircuitPrecomputations>;
pub(crate) type GpuWorkResult = WorkResult<GpuTraceAllocator>;
pub(crate) type GpuWorkerResult = WorkerResult<GpuTraceAllocator>;
use crossbeam_channel::{bounded, unbounded, Receiver, RecvError, Select, Sender};
use crossbeam_utils::sync::WaitGroup;
use crossbeam_utils::thread::{scope, Scope};
use era_cudart::device::get_device_count;
use gpu_prover_context::ProverContextConfig;
use itertools::Itertools;
use log::{error, info, trace};
use std::collections::{HashMap, HashSet, VecDeque};
use std::thread;

/// A batch in transit to the manager, which notifies its caller if it is never
/// accepted.
///
/// Closing the batch's sender is NOT notification: the simulation and replay
/// threads hold their own `WorkerResult` sender clones while blocked on trace
/// credits, so a silently dropped batch leaves the caller's collector waiting
/// forever. Notifying from `Drop` covers every way admission can lose a batch
/// (closed channel, manager return, unwind) without enumerating them.
pub(crate) struct PendingBatch {
    batch: Option<GpuWorkBatch>,
}

impl PendingBatch {
    fn new(batch: GpuWorkBatch) -> Self {
        Self { batch: Some(batch) }
    }

    /// Take the batch into service; the envelope then notifies nobody.
    fn accept(mut self) -> GpuWorkBatch {
        self.batch.take().expect("a pending batch is accepted once")
    }

    fn batch_id(&self) -> u64 {
        self.batch
            .as_ref()
            .expect("a pending batch is inspected before acceptance")
            .batch_id
    }
}

impl Drop for PendingBatch {
    fn drop(&mut self) {
        if let Some(batch) = self.batch.take() {
            let _ = batch
                .sender
                .send(WorkerResult::BackendFailure(BackendFailure {
                    batch_id: batch.batch_id,
                    reason: "the GPU manager stopped before accepting this batch".to_string(),
                }));
        }
    }
}

pub(crate) struct GpuManager {
    wait_group: Option<WaitGroup>,
    batches_sender: Option<Sender<PendingBatch>>,
}

impl GpuManager {
    /// Start the manager and its per-device workers, returning once every
    /// worker has acknowledged its device context — successfully or not. The
    /// acknowledgement carries a `Result`, so a device-side initialization
    /// failure is observable at construction rather than later.
    pub fn try_new(prover_context_config: ProverContextConfig) -> Result<Self, GpuBackendError> {
        let (batches_sender, batches_receiver) = unbounded();
        let (startup_sender, startup_receiver) = unbounded();
        trace!("GPU_MANAGER spawning");
        let wait_group = WaitGroup::new();
        let wait_group_clone = wait_group.clone();
        thread::spawn(move || {
            scope(|s| gpu_manager(startup_sender, prover_context_config, batches_receiver, s))
                .unwrap();
            drop(wait_group_clone);
        });
        if let Err(error) = await_startup_aggregate(&startup_receiver) {
            // Close admission and join before returning, so a failed startup
            // leaves no detached workers behind.
            drop(batches_sender);
            wait_group.wait();
            return Err(error);
        }
        Ok(Self {
            wait_group: Some(wait_group),
            batches_sender: Some(batches_sender),
        })
    }

    /// Hand a batch to the manager. Infallible by contract: a batch that
    /// cannot be served is reported through its own result channel by the
    /// envelope's `Drop`, never by panicking here.
    pub fn send_batch(&self, batch: GpuWorkBatch) {
        let pending = PendingBatch::new(batch);
        let Some(sender) = self.batches_sender.as_ref() else {
            return;
        };
        if let Err(error) = sender.send(pending) {
            // `SendError` hands the envelope back; dropping it notifies.
            drop(error.into_inner());
        }
    }
}

impl Drop for GpuManager {
    fn drop(&mut self) {
        drop(self.batches_sender.take().unwrap());
        trace!("GPU_MANAGER waiting for all workers to finish");
        self.wait_group.take().unwrap().wait();
        trace!("GPU_MANAGER all workers finished");
    }
}

/// Report a dead worker to everyone who could still be waiting on it.
///
/// A caller blocked on a trace credit is not waiting on these senders, so it
/// only learns to cancel its producers from the message itself; closing the
/// senders on the way out would not wake it. Batches still queued behind the
/// registered ones notify from their envelope's `Drop` as they are drained.
fn report_worker_failure(
    worker_id: usize,
    error: &GpuBackendError,
    batch_senders: &HashMap<u64, Sender<GpuWorkerResult>>,
    batches_receiver: Option<&Receiver<PendingBatch>>,
) {
    error!("GPU_MANAGER worker {worker_id} failed: {error}");
    for (batch_id, sender) in batch_senders.iter() {
        let _ = sender.send(WorkerResult::BackendFailure(BackendFailure {
            batch_id: *batch_id,
            reason: error.to_string(),
        }));
    }
    if let Some(receiver) = batches_receiver {
        for pending in receiver.try_iter() {
            drop(pending);
        }
    }
}

/// Runs the GPU manager's event loop: a 4-way `crossbeam` [`Select`] over new
/// batches, new work requests, worker results, and idle workers, plus an
/// eager-dispatch drain after every event. Each `match op.index()` arm
/// delegates its bookkeeping to a named handler below so this function reads
/// as an orchestration skeleton; the `op.recv`/`op.send` calls themselves
/// stay inline because `SelectedOperation` must be consumed with the exact
/// channel reference it was registered against.
fn gpu_manager(
    startup_sender: Sender<Result<(), GpuBackendError>>,
    prover_context_config: ProverContextConfig,
    batches_receiver: Receiver<PendingBatch>,
    scope: &Scope,
) {
    let device_count = match get_device_count() {
        Ok(count) => count as usize,
        Err(error) => {
            let _ = startup_sender.send(Err(GpuBackendError::cuda(
                "CUDA device count query failed",
                error,
            )));
            return;
        }
    };
    info!("GPU_MANAGER found {} CUDA capable device(s)", device_count);
    if device_count == 0 {
        let _ = startup_sender.send(Err(GpuBackendError::new("no CUDA capable devices found")));
        return;
    }
    let (worker_initialized_sender, worker_initialized_receiver) = bounded(device_count);
    let mut worker_senders = Vec::with_capacity(device_count);
    let mut worker_receivers = Vec::with_capacity(device_count);
    let mut worker_queues = Vec::with_capacity(device_count);
    for device_id in 0..device_count as i32 {
        let (request_sender, request_receiver) = bounded(0);
        let (result_sender, result_receiver) = bounded(0);
        worker_senders.push(request_sender);
        worker_receivers.push(result_receiver);
        worker_queues.push(VecDeque::from([None, None]));
        let gpu_worker_func = get_gpu_worker_func(
            device_id,
            prover_context_config,
            worker_initialized_sender.clone(),
            request_receiver,
            result_sender,
        );
        trace!("GPU_MANAGER spawning GPU worker {device_id}");
        scope.spawn(move |_| gpu_worker_func());
    }
    drop(worker_initialized_sender);
    let startup = collect_worker_acknowledgements(
        device_count,
        worker_initialized_receiver.iter().collect::<Vec<_>>(),
    );
    let started = startup.is_ok();
    let _ = startup_sender.send(startup);
    drop(startup_sender);
    if !started {
        // The request channels drop here, so the workers that did start exit
        // their loops and the scope joins them.
        return;
    }
    trace!("GPU_MANAGER all GPU workers initialized");
    let mut batches_receiver = Some(batches_receiver);
    let mut batch_receivers = HashMap::new();
    let mut batch_senders = HashMap::new();
    let mut work_queue = VecDeque::new();
    let mut batches_to_flush = HashSet::new();
    loop {
        let mut select = Select::new();
        let batches_index = batches_receiver.as_ref().map(|r| select.recv(r));
        let batch_receiver_indexes: HashMap<_, _> = batch_receivers
            .iter()
            .map(|(&batch_id, r)| (select.recv(r), batch_id))
            .collect();
        let worker_receivers_indexes: HashMap<_, _> = worker_receivers
            .iter()
            .enumerate()
            .map(|(worker_id, r)| (select.recv(r), worker_id))
            .collect();
        let worker_senders_indexes: HashMap<_, _> = worker_senders
            .iter()
            .enumerate()
            .filter_map(|(worker_id, s)| {
                let worker_queue = &worker_queues[worker_id];
                let advance = worker_queue.len() == 2
                    && worker_queue[0].is_none()
                    && worker_queue[1].is_some();
                let flush = worker_queue
                    .iter()
                    .any(|item| item.is_some_and(|batch_id| batches_to_flush.contains(&batch_id)));
                if !work_queue.is_empty() || advance || flush {
                    Some((select.send(s), worker_id))
                } else {
                    None
                }
            })
            .collect();
        let op = select.select();
        match op.index() {
            index if batches_index == Some(index) => {
                let received = op.recv(batches_receiver.as_ref().unwrap());
                handle_new_batch(
                    received,
                    &mut batches_receiver,
                    &mut batch_receivers,
                    &mut batch_senders,
                );
            }
            index if batch_receiver_indexes.contains_key(&index) => {
                let batch_id = batch_receiver_indexes[&index];
                let received = op.recv(&batch_receivers[&batch_id]);
                handle_new_request(
                    batch_id,
                    received,
                    &mut work_queue,
                    &mut batch_receivers,
                    &mut batches_to_flush,
                );
            }
            index if worker_receivers_indexes.contains_key(&index) => {
                let worker_id = worker_receivers_indexes[&index];
                // A disconnect means the worker exited without reporting. A
                // panic here would reach no caller, and a caller blocked on a
                // trace credit still has to be told.
                let received = match op.recv(&worker_receivers[worker_id]) {
                    Ok(received) => received,
                    Err(_) => Err(GpuBackendError::new(format!(
                        "GPU worker {worker_id} exited without reporting a result"
                    ))),
                };
                match received {
                    Ok(result) => handle_worker_result(
                        worker_id,
                        result,
                        &mut worker_queues,
                        &work_queue,
                        &mut batch_senders,
                        &mut batches_to_flush,
                    ),
                    Err(error) => {
                        report_worker_failure(
                            worker_id,
                            &error,
                            &batch_senders,
                            batches_receiver.as_ref(),
                        );
                        return;
                    }
                }
            }
            index if worker_senders_indexes.contains_key(&index) => {
                let worker_id = worker_senders_indexes[&index];
                let (request, batch_id) = handle_worker_ready(
                    worker_id,
                    &mut work_queue,
                    &worker_queues,
                    &batches_to_flush,
                );
                // `Select` can pick this send in the same round as the
                // worker's results channel closing, so a worker that dies with
                // work routed to it lands here instead of the recv arm above.
                if op.send(&worker_senders[worker_id], request).is_err() {
                    let error = GpuBackendError::new(format!(
                        "GPU worker {worker_id} exited without reporting a result"
                    ));
                    report_worker_failure(
                        worker_id,
                        &error,
                        &batch_senders,
                        batches_receiver.as_ref(),
                    );
                    return;
                }
                worker_queues[worker_id].push_back(batch_id);
            }
            _ => unreachable!(),
        };
        drain_eager_dispatch(&mut work_queue, &mut worker_queues, &worker_senders);
        if batches_receiver.is_none() && batch_senders.is_empty() {
            break;
        }
    }
    trace!("GPU_MANAGER finished");
}

/// Handles a receive on `batches_receiver` (the intake-batch arm): records a
/// newly arrived batch's request/result channels, or — on channel closure —
/// marks the batches channel as permanently exhausted.
fn handle_new_batch(
    received: Result<PendingBatch, RecvError>,
    batches_receiver: &mut Option<Receiver<PendingBatch>>,
    batch_receivers: &mut HashMap<u64, Receiver<GpuWorkRequest>>,
    batch_senders: &mut HashMap<u64, Sender<GpuWorkerResult>>,
) {
    match received {
        Ok(pending) => {
            let batch_id = pending.batch_id();
            let GpuWorkBatch {
                batch_id: _,
                receiver: requests,
                sender: results,
            } = pending.accept();
            trace!("BATCH[{batch_id}] GPU_MANAGER received new batch");
            assert!(batch_receivers.insert(batch_id, requests).is_none());
            assert!(batch_senders.insert(batch_id, results).is_none());
        }
        Err(_) => {
            trace!("GPU_MANAGER batches channel closed");
            *batches_receiver = None;
        }
    }
}

/// Handles a receive on batch `batch_id`'s request channel (the new-request
/// arm): enqueues the request for dispatch, or — on channel closure —
/// removes the batch's request receiver and marks the batch for flush-out.
fn handle_new_request(
    batch_id: u64,
    received: Result<GpuWorkRequest, RecvError>,
    work_queue: &mut VecDeque<GpuWorkRequest>,
    batch_receivers: &mut HashMap<u64, Receiver<GpuWorkRequest>>,
    batches_to_flush: &mut HashSet<u64>,
) {
    match received {
        Ok(request) => {
            assert_eq!(request.batch_id(), batch_id);
            let circuit_type = request.circuit_type();
            let sequence_id = request.sequence_id();
            match &request {
                WorkRequest::MemoryCommitment(_) => trace!(
                    "BATCH[{batch_id}] GPU_MANAGER received memory commitment request for circuit {circuit_type:?}[{sequence_id}]"
                ),
                WorkRequest::Proof(_) => {
                    trace!("BATCH[{batch_id}] GPU_MANAGER received proof request for circuit {circuit_type:?}[{sequence_id}]")
                }
                WorkRequest::SetupInitialization(_) => trace!(
                    "BATCH[{batch_id}] GPU_MANAGER received setup initialization request for circuit {circuit_type:?}[{sequence_id}]"
                ),
            };
            work_queue.push_back(request);
        }
        Err(_) => {
            trace!("BATCH[{batch_id}] GPU_MANAGER work request channel closed");
            assert!(batch_receivers.remove(&batch_id).is_some());
            assert!(batches_to_flush.insert(batch_id));
        }
    }
}

/// Handles a receive on GPU worker `worker_id`'s result channel (the
/// worker-result arm): pops the worker's in-flight queue slot, forwards a
/// real result to its batch's result channel, and — if that was the batch's
/// last outstanding item during a flush — completes the batch's bookkeeping.
/// A `None` result (advance/flush no-op cycle) still consumes the queue slot
/// but otherwise does nothing, matching the original arm.
fn handle_worker_result(
    worker_id: usize,
    result: Option<GpuWorkResult>,
    worker_queues: &mut [VecDeque<Option<u64>>],
    work_queue: &VecDeque<GpuWorkRequest>,
    batch_senders: &mut HashMap<u64, Sender<GpuWorkerResult>>,
    batches_to_flush: &mut HashSet<u64>,
) {
    let item = worker_queues[worker_id].pop_front().unwrap();
    if let Some(result) = result {
        let batch_id = item.unwrap();
        let circuit_type = result.circuit_type();
        let sequence_id = result.sequence_id();
        match &result {
            WorkResult::MemoryCommitment(result) => {
                assert_eq!(result.batch_id, batch_id);
                trace!("BATCH[{batch_id}] GPU_MANAGER received memory commitment for circuit {circuit_type:?}[{sequence_id}] from GPU_WORKER[{worker_id}]");
            }
            WorkResult::Proof(result) => {
                assert_eq!(result.batch_id, batch_id);
                trace!("BATCH[{batch_id}] GPU_MANAGER received proof from GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]");
            }
            WorkResult::SetupInitialization(result) => {
                assert_eq!(result.batch_id, batch_id);
                trace!("BATCH[{batch_id}] GPU_MANAGER received setup initialization for circuit {circuit_type:?}[{sequence_id}] from GPU_WORKER[{worker_id}]");
            }
        };
        let result = WorkerResult::BackendWorkResult(result);
        batch_senders[&batch_id]
            .send(result)
            .expect("GPU manager result channel closed before batch completion");
        if batches_to_flush.contains(&batch_id)
            && !work_queue
                .iter()
                .any(|request| request.batch_id() == batch_id)
            && !worker_queues
                .iter()
                .flatten()
                .any(|item| item.is_some_and(|id| id == batch_id))
        {
            trace!("BATCH[{batch_id}] GPU_MANAGER batch completed");
            assert!(batches_to_flush.remove(&batch_id));
            batch_senders.remove(&batch_id);
        }
    }
}

/// Decides what to hand GPU worker `worker_id` for the idle-worker-dispatch
/// arm: the next queued request (popping `work_queue`), or `(None, None)` if
/// the queue is empty and the worker is merely being cycled through an
/// advance/flush no-op (asserting that's indeed why it was selected). The
/// caller is left to perform the actual `op.send` and push the returned
/// `batch_id` onto the worker's in-flight queue, since both must happen
/// after this decision and in that order.
fn handle_worker_ready(
    worker_id: usize,
    work_queue: &mut VecDeque<GpuWorkRequest>,
    worker_queues: &[VecDeque<Option<u64>>],
    batches_to_flush: &HashSet<u64>,
) -> (Option<GpuWorkRequest>, Option<u64>) {
    if work_queue.is_empty() {
        let worker_queue = &worker_queues[worker_id];
        let advance =
            worker_queue.len() == 2 && worker_queue[0].is_none() && worker_queue[1].is_some();
        let flush = worker_queue
            .iter()
            .any(|item| item.is_some_and(|batch_id| batches_to_flush.contains(&batch_id)));
        assert!(advance || flush);
        trace!(
            "GPU_MANAGER {} queue for GPU_WORKER[{worker_id}]",
            if advance { "advancing" } else { "flushing" }
        );
        (None, None)
    } else {
        let request = work_queue.pop_front().unwrap();
        let batch_id = request.batch_id();
        let circuit_type = request.circuit_type();
        let sequence_id = request.sequence_id();
        trace!(
            "BATCH[{batch_id}] GPU_MANAGER sending {} request to GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]",
            match &request {
                WorkRequest::MemoryCommitment(_) => "memory commitment",
                WorkRequest::Proof(_) => "proof",
                WorkRequest::SetupInitialization(_) => "setup initialization",
            }
        );
        (Some(request), Some(batch_id))
    }
}

/// Drains `work_queue` after every main-loop event by eagerly handing
/// requests to whichever idle GPU worker is ready to accept them (biased
/// toward the workers with the shortest in-flight queues), without waiting
/// for the main loop to cycle back around to the idle-worker-dispatch arm.
fn drain_eager_dispatch(
    work_queue: &mut VecDeque<GpuWorkRequest>,
    worker_queues: &mut [VecDeque<Option<u64>>],
    worker_senders: &[Sender<Option<GpuWorkRequest>>],
) {
    while !work_queue.is_empty() {
        let mut select = Select::new_biased();
        let worker_senders_indexes: HashMap<_, _> = worker_queues
            .iter()
            .enumerate()
            .sorted_by_key(|(_, q)| *q)
            .map(|(worker_id, _)| (select.send(&worker_senders[worker_id]), worker_id))
            .collect();
        match select.try_select() {
            Ok(op) => {
                let op_index = op.index();
                let worker_id = worker_senders_indexes[&op_index];
                let request = work_queue.pop_front().unwrap();
                let batch_id = request.batch_id();
                let circuit_type = request.circuit_type();
                let sequence_id = request.sequence_id();
                match &request {
                    WorkRequest::MemoryCommitment(_) => trace!("BATCH[{batch_id}] GPU_MANAGER sending memory commitment request to GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]"),
                    WorkRequest::Proof(_) => trace!("BATCH[{batch_id}] GPU_MANAGER sending proof request to GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]"),
                    WorkRequest::SetupInitialization(_) => trace!("BATCH[{batch_id}] GPU_MANAGER sending setup initialization request to GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]"),
                };
                op.send(&worker_senders[worker_id], Some(request))
                    .expect("GPU manager failed to eagerly queue work for GPU worker");
                worker_queues[worker_id].push_back(Some(batch_id));
            }
            Err(_) => break,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use execution_prover::messages::WorkBatch;

    /// A batch wired to live channels. The request sender is returned rather
    /// than dropped, so the batch looks like one whose producers still run.
    fn batch(
        batch_id: u64,
    ) -> (
        GpuWorkBatch,
        Sender<GpuWorkRequest>,
        Receiver<GpuWorkerResult>,
    ) {
        let (request_sender, request_receiver) = unbounded();
        let (result_sender, result_receiver) = unbounded();
        (
            WorkBatch {
                batch_id,
                receiver: request_receiver,
                sender: result_sender,
            },
            request_sender,
            result_receiver,
        )
    }

    fn failure_reason(result: GpuWorkerResult) -> String {
        match result {
            WorkerResult::BackendFailure(failure) => failure.reason,
            _ => panic!("expected a backend failure"),
        }
    }

    /// A batch that is never accepted must be told, not silently dropped: the
    /// caller's collector ends only when every `WorkerResult` sender is gone,
    /// and blocked producers hold clones of their own.
    #[test]
    fn cpu_unaccepted_batch_is_notified_when_dropped() {
        let (batch, _requests, results) = batch(7);

        drop(PendingBatch::new(batch));

        let reason = failure_reason(results.recv().expect("the caller must be told"));
        assert!(
            reason.contains("stopped before accepting"),
            "the rejection must say the batch was never accepted; got: {reason}"
        );
    }

    /// An accepted batch's envelope notifies nobody — the manager owns it now.
    #[test]
    fn cpu_accepted_batch_is_not_notified() {
        let (batch, _requests, results) = batch(9);

        let pending = PendingBatch::new(batch);
        assert_eq!(pending.batch_id(), 9);
        let accepted = pending.accept();
        assert_eq!(accepted.batch_id, 9);

        assert!(
            results.try_recv().is_err(),
            "an accepted batch is not failed"
        );
        drop(accepted);
        assert!(results.try_recv().is_err());
    }

    /// The "manager returned with batches still queued" path: its receiver
    /// goes away, and every queued envelope reports on its way out.
    #[test]
    fn cpu_queued_batches_are_notified_when_the_manager_receiver_drops() {
        let (sender, receiver) = unbounded::<PendingBatch>();
        let (first, _first_requests, first_results) = batch(1);
        let (second, _second_requests, second_results) = batch(2);
        sender.send(PendingBatch::new(first)).unwrap();
        sender.send(PendingBatch::new(second)).unwrap();

        drop(receiver);
        drop(sender);

        for results in [first_results, second_results] {
            let reason = failure_reason(results.recv().expect("every queued batch must be told"));
            assert!(reason.contains("stopped before accepting"));
        }
    }

    /// `ExecutionBackend::submit` is infallible by contract, so a `send_batch`
    /// after the manager has gone must report on the batch's own result
    /// channel rather than panic.
    #[test]
    fn cpu_send_after_shutdown_reports_instead_of_panicking() {
        let (sender, receiver) = unbounded::<PendingBatch>();
        drop(receiver);
        // A fresh `WaitGroup` with no outstanding clones, so the real `Drop`
        // runs unmodified instead of being leaked past.
        let manager = GpuManager {
            wait_group: Some(WaitGroup::new()),
            batches_sender: Some(sender),
        };
        let (batch, _requests, results) = batch(3);

        manager.send_batch(batch);

        let reason = failure_reason(results.recv().expect("a refused batch must be told"));
        assert!(reason.contains("stopped before accepting"));
        drop(manager);
    }
}
