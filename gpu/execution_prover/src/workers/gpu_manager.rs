use crate::messages::{GpuWorkBatch, GpuWorkRequest, GpuWorkResult, WorkerResult};
use crate::workers::gpu::get_gpu_worker_func;
use crate::A;
use crossbeam_channel::{bounded, unbounded, Receiver, RecvError, Select, Sender};
use crossbeam_utils::sync::WaitGroup;
use crossbeam_utils::thread::{scope, Scope};
use era_cudart::device::get_device_count;
use era_cudart::result::CudaResult;
use gpu_circuit_prover::prover::ProverContextConfig;
use itertools::Itertools;
use log::{error, info, trace};
use std::collections::{HashMap, HashSet, VecDeque};
use std::process::exit;
use std::thread;

pub(crate) struct GpuManager {
    wait_group: Option<WaitGroup>,
    batches_sender: Option<Sender<GpuWorkBatch>>,
}

impl GpuManager {
    pub fn new(
        initialized_wait_group: WaitGroup,
        prover_context_config: ProverContextConfig,
    ) -> Self {
        let (batches_sender, batches_receiver) = unbounded();
        trace!("GPU_MANAGER spawning");
        let wait_group = WaitGroup::new();
        let wait_group_clone = wait_group.clone();
        thread::spawn(move || {
            let result = scope(|s| {
                gpu_manager(
                    initialized_wait_group,
                    prover_context_config,
                    batches_receiver,
                    s,
                )
            })
            .unwrap();
            if let Err(e) = result {
                error!("GPU_MANAGER encountered an error: {e}");
                exit(1);
            }
            drop(wait_group_clone);
        });
        Self {
            wait_group: Some(wait_group),
            batches_sender: Some(batches_sender),
        }
    }

    pub fn send_batch(&self, batch: GpuWorkBatch) {
        self.batches_sender
            .as_ref()
            .expect("GPU manager batch sender must exist before shutdown")
            .send(batch)
            .expect("GPU manager batch channel closed before all work was submitted")
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

/// Runs the GPU manager's event loop: a 4-way `crossbeam` [`Select`] over new
/// batches, new work requests, worker results, and idle workers, plus an
/// eager-dispatch drain after every event. Each `match op.index()` arm
/// delegates its bookkeeping to a named handler below so this function reads
/// as an orchestration skeleton; the `op.recv`/`op.send` calls themselves
/// stay inline because `SelectedOperation` must be consumed with the exact
/// channel reference it was registered against.
fn gpu_manager(
    initialized_wait_group: WaitGroup,
    prover_context_config: ProverContextConfig,
    batches_receiver: Receiver<GpuWorkBatch>,
    scope: &Scope,
) -> CudaResult<()> {
    let device_count = get_device_count()? as usize;
    info!("GPU_MANAGER found {} CUDA capable device(s)", device_count);
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
            prover_context_config.clone(),
            worker_initialized_sender.clone(),
            request_receiver,
            result_sender,
        );
        trace!("GPU_MANAGER spawning GPU worker {device_id}");
        scope.spawn(move |_| gpu_worker_func());
    }
    drop(worker_initialized_sender);
    assert_eq!(worker_initialized_receiver.iter().count(), device_count);
    drop(initialized_wait_group);
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
                let result = op.recv(&worker_receivers[worker_id]).unwrap();
                handle_worker_result(
                    worker_id,
                    result,
                    &mut worker_queues,
                    &work_queue,
                    &mut batch_senders,
                    &mut batches_to_flush,
                );
            }
            index if worker_senders_indexes.contains_key(&index) => {
                let worker_id = worker_senders_indexes[&index];
                let (request, batch_id) = handle_worker_ready(
                    worker_id,
                    &mut work_queue,
                    &worker_queues,
                    &batches_to_flush,
                );
                op.send(&worker_senders[worker_id], request)
                    .expect("GPU manager failed to send work to GPU worker");
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
    Ok(())
}

/// Handles a receive on `batches_receiver` (the intake-batch arm): records a
/// newly arrived batch's request/result channels, or — on channel closure —
/// marks the batches channel as permanently exhausted.
fn handle_new_batch(
    received: Result<GpuWorkBatch, RecvError>,
    batches_receiver: &mut Option<Receiver<GpuWorkBatch>>,
    batch_receivers: &mut HashMap<u64, Receiver<GpuWorkRequest<A>>>,
    batch_senders: &mut HashMap<u64, Sender<WorkerResult<A>>>,
) {
    match received {
        Ok(batch) => {
            let GpuWorkBatch {
                batch_id,
                receiver: requests,
                sender: results,
            } = batch;
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
    received: Result<GpuWorkRequest<A>, RecvError>,
    work_queue: &mut VecDeque<GpuWorkRequest<A>>,
    batch_receivers: &mut HashMap<u64, Receiver<GpuWorkRequest<A>>>,
    batches_to_flush: &mut HashSet<u64>,
) {
    match received {
        Ok(request) => {
            assert_eq!(request.batch_id(), batch_id);
            let circuit_type = request.circuit_type();
            let sequence_id = request.sequence_id();
            match &request {
                GpuWorkRequest::MemoryCommitment(_) => trace!(
                    "BATCH[{batch_id}] GPU_MANAGER received memory commitment request for circuit {circuit_type:?}[{sequence_id}]"
                ),
                GpuWorkRequest::Proof(_) => {
                    trace!("BATCH[{batch_id}] GPU_MANAGER received proof request for circuit {circuit_type:?}[{sequence_id}]")
                }
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
    result: Option<GpuWorkResult<A>>,
    worker_queues: &mut [VecDeque<Option<u64>>],
    work_queue: &VecDeque<GpuWorkRequest<A>>,
    batch_senders: &mut HashMap<u64, Sender<WorkerResult<A>>>,
    batches_to_flush: &mut HashSet<u64>,
) {
    let item = worker_queues[worker_id].pop_front().unwrap();
    if let Some(result) = result {
        let batch_id = item.unwrap();
        let circuit_type = result.circuit_type();
        let sequence_id = result.sequence_id();
        match &result {
            GpuWorkResult::MemoryCommitment(result) => {
                assert_eq!(result.batch_id, batch_id);
                trace!("BATCH[{batch_id}] GPU_MANAGER received memory commitment for circuit {circuit_type:?}[{sequence_id}] from GPU_WORKER[{worker_id}]");
            }
            GpuWorkResult::Proof(result) => {
                assert_eq!(result.batch_id, batch_id);
                trace!("BATCH[{batch_id}] GPU_MANAGER received proof from GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]");
            }
        };
        let result = WorkerResult::GpuWorkResult(result);
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
    work_queue: &mut VecDeque<GpuWorkRequest<A>>,
    worker_queues: &[VecDeque<Option<u64>>],
    batches_to_flush: &HashSet<u64>,
) -> (Option<GpuWorkRequest<A>>, Option<u64>) {
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
                GpuWorkRequest::MemoryCommitment(_) => "memory commitment",
                GpuWorkRequest::Proof(_) => "proof",
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
    work_queue: &mut VecDeque<GpuWorkRequest<A>>,
    worker_queues: &mut [VecDeque<Option<u64>>],
    worker_senders: &[Sender<Option<GpuWorkRequest<A>>>],
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
                    GpuWorkRequest::MemoryCommitment(_) => trace!("BATCH[{batch_id}] GPU_MANAGER sending memory commitment request to GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]"),
                    GpuWorkRequest::Proof(_) => trace!("BATCH[{batch_id}] GPU_MANAGER sending proof request to GPU_WORKER[{worker_id}] for circuit {circuit_type:?}[{sequence_id}]"),
                };
                op.send(&worker_senders[worker_id], Some(request))
                    .expect("GPU manager failed to eagerly queue work for GPU worker");
                worker_queues[worker_id].push_back(Some(batch_id));
            }
            Err(_) => break,
        }
    }
}
