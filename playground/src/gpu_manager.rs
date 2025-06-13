use crate::gpu_worker::{get_gpu_worker_func, GpuWorkRequest};
use crate::messages::WorkerResult;
use crossbeam_channel::internal::SelectHandle;
use crossbeam_channel::{bounded, unbounded, Receiver, Select, Sender};
use fft::GoodAllocator;
use gpu_prover::cudart::device::{get_device_count, get_device_properties, set_device};
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{ProverContext, ProverContextConfig};
use itertools::Itertools;
use log::info;
use std::alloc::Global;
use std::collections::{HashMap, HashSet, VecDeque};
use std::ffi::CStr;
use std::sync::OnceLock;

pub struct GpuWorkBatch<A: GoodAllocator, B: GoodAllocator = Global> {
    pub receiver: Receiver<GpuWorkRequest<A, B>>,
    pub sender: Sender<WorkerResult<A>>,
}

pub struct GpuManager<C: ProverContext, A: GoodAllocator + 'static = Global> {
    is_initialized_receiver: Receiver<usize>,
    workers_count: OnceLock<usize>,
    batches_sender: Sender<GpuWorkBatch<C::HostAllocator, A>>,
}

impl<C: ProverContext, A: GoodAllocator + 'static> GpuManager<C, A> {
    pub fn new(
        host_allocations_count: usize,
        log_host_allocation_size: usize,
        scope: &rayon::Scope,
    ) -> Self {
        let (is_initialized_sender, is_initialized_receiver) = bounded(1);
        let (batches_sender, batches_receiver) = unbounded();
        info!("GPU MANAGER spawning");
        scope.spawn(move |scope| {
            let result = gpu_manager::<C>(
                host_allocations_count,
                log_host_allocation_size,
                is_initialized_sender,
                batches_receiver,
                scope,
            );
            if let Err(e) = result {
                panic!("GPU MANAGER encountered an error: {e}");
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
    host_allocations_count: usize,
    log_host_allocation_size: usize,
    is_initialized: Sender<usize>,
    batches_receiver: Receiver<GpuWorkBatch<C::HostAllocator, impl GoodAllocator + 'static>>,
    scope: &rayon::Scope<'_>,
) -> CudaResult<()> {
    assert!(log_host_allocation_size >= 22);
    info!("GPU MANAGER initializing host allocator with {host_allocations_count} allocations of size 2^{log_host_allocation_size} bytes each");
    C::initialize_host_allocator(
        host_allocations_count,
        1 << (log_host_allocation_size - 22),
        22,
    )?;
    let device_count = get_device_count()? as usize;
    info!("GPU MANAGER found {} CUDA capable devices", device_count);
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
            "GPU MANAGER Device {}: {} ({} SMs, {} GB memory)",
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
        info!("GPU MANAGER spawning GPU worker {device_id}");
        scope.spawn(move |_| gpu_worker_func());
    }
    drop(worker_initialized_sender);
    assert_eq!(worker_initialized_receiver.iter().count(), device_count);
    info!("GPU MANAGER all GPU workers initialized");
    is_initialized.send(device_count).unwrap();
    drop(is_initialized);
    let mut next_batch_id = 0;
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
            .map(|(&id, r)| (select.recv(r), id))
            .collect();
        let worker_receivers_indexes: HashMap<_, _> = worker_receivers
            .iter()
            .enumerate()
            .map(|(i, r)| (select.recv(r), i))
            .collect();
        let op = select.select();
        match op.index() {
            index if batches_index == Some(index) => {
                match op.recv(batches_receiver.as_ref().unwrap()) {
                    Ok(batch) => {
                        let GpuWorkBatch {
                            receiver: requests,
                            sender: results,
                        } = batch;
                        let id = next_batch_id;
                        next_batch_id += 1;
                        info!("GPU MANAGER received new batch with id {}", id);
                        batch_receivers.insert(id, requests);
                        batch_senders.insert(id, results);
                    }
                    Err(_) => {
                        info!("GPU MANAGER batches channel closed");
                        batches_receiver = None;
                    }
                };
            }
            index if batch_receiver_indexes.contains_key(&index) => {
                let batch_id = batch_receiver_indexes[&index];
                match op.recv(&batch_receivers[&batch_id]) {
                    Ok(request) => {
                        info!("GPU MANAGER received work request for batch id {batch_id}");
                        work_queue.push_back((batch_id, request));
                    }
                    Err(_) => {
                        info!("GPU MANAGER batch request channel with id {batch_id} closed");
                        batch_receivers.remove(&batch_id);
                        batches_to_flush.insert(batch_id);
                    }
                };
            }
            index if worker_receivers_indexes.contains_key(&index) => {
                let worker_id = worker_receivers_indexes[&index];
                let result = op.recv(&worker_receivers[worker_id]).unwrap();
                let batch_id: Option<usize> = worker_queues[worker_id].pop_front().unwrap();
                if let Some(result) = result {
                    let batch_id = batch_id.unwrap();
                    info!(
                        "GPU MANAGER received work result from worker id {worker_id} fo batch id {batch_id}",
                    );
                    batch_senders[&batch_id].send(result).unwrap();
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
                .map(|(index, _)| (select.send(&worker_senders[index]), index))
                .collect();
            match select.try_select() {
                Ok(op) => {
                    let op_index = op.index();
                    let worker_id = worker_senders_indexes[&op_index];
                    let (batch_id, request) = work_queue.pop_front().unwrap();
                    info!("GPU MANAGER sending work request from batch id {batch_id} to worker id {worker_id}");
                    op.send(&worker_senders[worker_id], Some(request)).unwrap();
                    worker_queues[worker_id].push_back(Some(batch_id));
                }
                Err(_) => break,
            }
        }
        if work_queue.is_empty() {
            for (worker_id, queue) in worker_queues.iter_mut().enumerate() {
                if queue.len() == 2 && queue[0].is_none() && queue[1].is_some() {
                    info!("GPU MANAGER advancing queue for worker id {worker_id}");
                    worker_senders[worker_id].send(None).unwrap();
                    queue.push_back(None);
                }
            }
        }
        if !batches_to_flush.is_empty() {
            for batch_id in batches_to_flush.clone().into_iter() {
                if worker_queues
                    .iter()
                    .flatten()
                    .all(|&id| id != Some(batch_id))
                {
                    batches_to_flush.remove(&batch_id);
                    batch_senders.remove(&batch_id);
                    info!("GPU MANAGER batch id {batch_id} flushed");
                }
            }
        }
        if !batches_to_flush.is_empty() {
            for (i, sender) in worker_senders.iter().enumerate() {
                if sender.is_ready()
                    && worker_queues[i]
                        .iter()
                        .any(|q| q.is_some_and(|x| batches_to_flush.contains(&x)))
                {
                    info!("GPU MANAGER flushing worker id {i}");
                    sender.send(None).unwrap();
                    worker_queues[i].push_back(None);
                }
            }
        }
        if batches_receiver.is_none() && batch_receivers.is_empty() && batches_to_flush.is_empty() {
            break;
        }
    }
    info!("GPU MANAGER finished");
    Ok(())
}
