use crate::gpu_worker::{get_gpu_worker_func, GpuWorkRequest};
use crate::messages::WorkerResult;
use crossbeam_channel::internal::SelectHandle;
use crossbeam_channel::{bounded, unbounded, Receiver, Select, Sender};
use fft::GoodAllocator;
use gpu_prover::cudart::device::{get_device_count, get_device_properties, set_device};
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{ProverContext, ProverContextConfig};
use itertools::Itertools;
use log::{error, info};
use std::alloc::Global;
use std::collections::{HashMap, HashSet, VecDeque};
use std::ffi::CStr;
use std::process::exit;
use std::sync::OnceLock;

pub struct GpuWorkBatch<A: GoodAllocator, B: GoodAllocator = Global> {
    pub batch_id: u64,
    pub receiver: Receiver<GpuWorkRequest<A, B>>,
    pub sender: Sender<WorkerResult<A>>,
}

pub struct GpuManager<C: ProverContext, A: GoodAllocator + 'static = Global> {
    is_initialized_receiver: Receiver<usize>,
    workers_count: OnceLock<usize>,
    batches_sender: Sender<GpuWorkBatch<C::HostAllocator, A>>,
}

impl<C: ProverContext, A: GoodAllocator + 'static> GpuManager<C, A> {
    pub fn new(scope: &rayon::Scope) -> Self {
        let (is_initialized_sender, is_initialized_receiver) = bounded(1);
        let (batches_sender, batches_receiver) = unbounded();
        info!("GPU_MANAGER spawning");
        scope.spawn(move |scope| {
            let result = gpu_manager::<C>(is_initialized_sender, batches_receiver, scope);
            if let Err(e) = result {
                error!("GPU_MANAGER encountered an error: {e}");
                exit(1);
            }
        });
        Self {
            is_initialized_receiver,
            workers_count: OnceLock::new(),
            batches_sender,
        }
    }

    pub fn send_batch(&self, batch: GpuWorkBatch<C::HostAllocator, A>) {
        self.batches_sender.send(batch).unwrap()
    }

    pub fn is_initialized(&self) -> bool {
        self.workers_count.get().is_some()
    }

    pub fn wait_for_initialization(&self) {
        if self.workers_count.get().is_some() {
            return;
        }
        let count = self.is_initialized_receiver.recv().unwrap();
        self.workers_count.set(count).unwrap();
    }

    pub fn get_workers_count(&self) -> usize {
        self.wait_for_initialization();
        *self.workers_count.get().unwrap()
    }
}

fn gpu_manager<C: ProverContext>(
    is_initialized: Sender<usize>,
    batches_receiver: Receiver<GpuWorkBatch<C::HostAllocator, impl GoodAllocator + 'static>>,
    scope: &rayon::Scope<'_>,
) -> CudaResult<()> {
    let device_count = get_device_count()? as usize;
    info!("GPU_MANAGER found {} CUDA capable devices", device_count);
    let prover_context_config = {
        let mut c = ProverContextConfig::default();
        c.allocation_block_log_size = 22;
        c
    };
    let (worker_initialized_sender, worker_initialized_receiver) = bounded(device_count);
    let mut worker_senders = Vec::with_capacity(device_count);
    let mut worker_receivers = Vec::with_capacity(device_count);
    let mut worker_queues = Vec::with_capacity(device_count);
    for device_id in 0..device_count as i32 {
        set_device(device_id)?;
        let props = get_device_properties(device_id)?;
        let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
        info!(
            "GPU_MANAGER Device {}: {} ({} SMs, {} GB memory)",
            device_id,
            name,
            props.multiProcessorCount,
            props.totalGlobalMem as f32 / 1024.0 / 1024.0 / 1024.0
        );
        let (request_sender, request_receiver) = bounded(0);
        let (result_sender, result_receiver) = bounded(0);
        worker_senders.push(request_sender);
        worker_receivers.push(result_receiver);
        worker_queues.push(VecDeque::from([None, None]));
        let gpu_worker_func = get_gpu_worker_func::<C>(
            device_id,
            prover_context_config,
            worker_initialized_sender.clone(),
            request_receiver,
            result_sender,
        );
        info!("GPU_MANAGER spawning GPU worker {device_id}");
        scope.spawn(move |_| gpu_worker_func());
    }
    drop(worker_initialized_sender);
    assert_eq!(worker_initialized_receiver.iter().count(), device_count);
    info!("GPU_MANAGER all GPU workers initialized");
    is_initialized.send(device_count).unwrap();
    drop(is_initialized);
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
        let op = select.select();
        match op.index() {
            index if batches_index == Some(index) => {
                match op.recv(batches_receiver.as_ref().unwrap()) {
                    Ok(batch) => {
                        let GpuWorkBatch {
                            batch_id,
                            receiver: requests,
                            sender: results,
                        } = batch;
                        info!("GPU_MANAGER received new batch with id {batch_id}");
                        batch_receivers.insert(batch_id, requests);
                        batch_senders.insert(batch_id, results);
                    }
                    Err(_) => {
                        info!("GPU_MANAGER batches channel closed");
                        batches_receiver = None;
                    }
                };
            }
            index if batch_receiver_indexes.contains_key(&index) => {
                let batch_id = batch_receiver_indexes[&index];
                match op.recv(&batch_receivers[&batch_id]) {
                    Ok(request) => {
                        assert_eq!(request.batch_id(), batch_id);
                        match &request {
                            GpuWorkRequest::MemoryCommitment(_) => info!(
                                "BATCH[{batch_id}] GPU_MANAGER received memory commitment request"
                            ),
                            GpuWorkRequest::Proof(_) => {
                                info!("BATCH[{batch_id}] GPU_MANAGER received proof request")
                            }
                        };
                        work_queue.push_back(request);
                    }
                    Err(_) => {
                        info!("BATCH[{batch_id}] GPU_MANAGER work request channel closed");
                        batch_receivers.remove(&batch_id);
                        batches_to_flush.insert(batch_id);
                    }
                };
            }
            index if worker_receivers_indexes.contains_key(&index) => {
                let worker_id = worker_receivers_indexes[&index];
                let result = op.recv(&worker_receivers[worker_id]).unwrap();
                let item = worker_queues[worker_id].pop_front().unwrap();
                if let Some(result) = result {
                    let batch_id = item.unwrap();
                    match &result {
                        WorkerResult::MemoryCommitment(result) => {
                            assert_eq!(result.batch_id, batch_id);
                            info!("BATCH[{batch_id}] GPU_MANAGER received memory commitment from worker id {}", worker_id);
                        }
                        WorkerResult::Proof(result) => {
                            assert_eq!(result.batch_id, batch_id);
                            info!(
                                "BATCH[{batch_id}] GPU_MANAGER received proof from worker id {}",
                                worker_id
                            );
                        }
                        _ => unreachable!(),
                    };
                    batch_senders[&batch_id].send(result).unwrap();
                    if !batch_receivers.contains_key(&batch_id)
                        && !work_queue
                            .iter()
                            .any(|request| request.batch_id() == batch_id)
                        && !worker_queues
                            .iter()
                            .flatten()
                            .any(|item| item.is_some_and(|id| id == batch_id))
                    {
                        info!("BATCH[{batch_id}] GPU_MANAGER batch completed");
                        batch_senders.remove(&batch_id);
                    }
                }
            }
            _ => unreachable!(),
        };
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
                    match &request {
                        GpuWorkRequest::MemoryCommitment(_) => info!(
                            "BATCH[{batch_id}] GPU_MANAGER sending memory commitment request to worker id {worker_id}"
                        ),
                        GpuWorkRequest::Proof(_) => info!(
                            "BATCH[{batch_id}] GPU_MANAGER sending proof request to worker id {worker_id}"
                        ),
                    };
                    op.send(&worker_senders[worker_id], Some(request)).unwrap();
                    worker_queues[worker_id].push_back(Some(batch_id));
                }
                Err(_) => break,
            }
        }
        if work_queue.is_empty() {
            for (worker_id, queue) in worker_queues.iter_mut().enumerate() {
                if queue.len() == 2 && queue[0].is_none() && queue[1].is_some() {
                    info!("GPU_MANAGER advancing queue for worker id {worker_id}");
                    worker_senders[worker_id].send(None).unwrap();
                    queue.push_back(None);
                }
            }
        }
        if !batches_to_flush.is_empty() {
            for batch_id in batches_to_flush.clone().into_iter() {
                if !worker_queues
                    .iter()
                    .flatten()
                    .any(|&id| id == Some(batch_id))
                {
                    batches_to_flush.remove(&batch_id);
                    info!("BATCH[{batch_id}] GPU_MANAGER batch flushed");
                }
            }
        }
        if !batches_to_flush.is_empty() {
            for (worker_id, sender) in worker_senders.iter().enumerate() {
                if sender.is_ready()
                    && worker_queues[worker_id].iter().any(|item| {
                        item.is_some_and(|batch_id| batches_to_flush.contains(&batch_id))
                    })
                {
                    info!("GPU_MANAGER flushing worker id {worker_id}");
                    sender.send(None).unwrap();
                    worker_queues[worker_id].push_back(None);
                }
            }
        }
        if batches_receiver.is_none() && batch_senders.is_empty() {
            break;
        }
    }
    info!("GPU_MANAGER finished");
    Ok(())
}
