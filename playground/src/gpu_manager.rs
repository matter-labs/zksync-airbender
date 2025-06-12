use crate::gpu_worker::{get_gpu_worker_func, GpuWorkRequest};
use crate::logger::LOCAL_LOGGER;
use crate::messages::WorkerResult;
use crossbeam_channel::internal::SelectHandle;
use crossbeam_channel::{bounded, Receiver, Select, Sender};
use fft::GoodAllocator;
use gpu_prover::cudart::device::{get_device_count, get_device_properties, set_device};
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{ProverContext, ProverContextConfig};
use itertools::Itertools;
use std::collections::{HashMap, HashSet, VecDeque};
use std::ffi::CStr;
use std::time::Instant;

pub struct GpuWorkBatch<A: GoodAllocator, B: GoodAllocator> {
    pub receiver: Receiver<GpuWorkRequest<A, B>>,
    pub sender: Sender<WorkerResult<B>>,
}

pub fn get_gpu_manager_func<C: ProverContext>(
    timer: Instant,
    is_initialized: Sender<()>,
    timer_reset: Receiver<Instant>,
    batches: Receiver<GpuWorkBatch<impl GoodAllocator + 'static, C::HostAllocator>>,
) -> impl FnOnce(&rayon::Scope) {
    move |_| {
        rayon::scope(|s| gpu_manager::<C>(timer, is_initialized, timer_reset, batches, s).unwrap())
    }
}

fn gpu_manager<C: ProverContext>(
    timer: Instant,
    is_initialized: Sender<()>,
    timer_reset: Receiver<Instant>,
    batches_receiver: Receiver<GpuWorkBatch<impl GoodAllocator + 'static, C::HostAllocator>>,
    scope: &rayon::Scope<'_>,
) -> CudaResult<()> {
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.name = "GPU[M]".to_string();
        l.timer = timer;
    });
    C::initialize_host_allocator(8, 1 << 8, 22)?;
    let device_count = get_device_count()? as usize;
    log::info!("found {} CUDA capable devices", device_count);
    let prover_context_config = {
        let mut c = ProverContextConfig::default();
        c.allocation_block_log_size = 22;
        c
    };
    let (worker_initialized_sender, worker_initialized_receiver) = bounded(device_count);
    let (worker_timer_reset_sender, worker_timer_reset_receiver) = bounded(device_count);
    let mut worker_senders = Vec::with_capacity(device_count);
    let mut worker_receivers = Vec::with_capacity(device_count);
    let mut worker_queues = Vec::with_capacity(device_count);
    for device_id in 0..device_count as i32 {
        set_device(device_id)?;
        let props = get_device_properties(device_id)?;
        let name = unsafe { CStr::from_ptr(props.name.as_ptr()).to_string_lossy() };
        log::info!(
            "Device {}: {} ({} SMs, {} GB memory)",
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
            timer,
            device_id,
            prover_context_config,
            worker_initialized_sender.clone(),
            worker_timer_reset_receiver.clone(),
            request_receiver,
            result_sender,
        );
        log::info!("spawning GPU worker {device_id}");
        scope.spawn(move |_| gpu_worker_func());
    }
    drop(worker_initialized_sender);
    assert_eq!(worker_initialized_receiver.iter().count(), device_count);
    log::info!("all GPU workers initialized");
    is_initialized.send(()).unwrap();
    drop(is_initialized);
    let timer = timer_reset.recv().unwrap();
    drop(timer_reset);
    LOCAL_LOGGER.with_borrow_mut(|l| {
        l.timer = timer;
    });
    log::info!("timer reset");
    for _ in 0..device_count {
        worker_timer_reset_sender.send(timer).unwrap();
    }
    drop(worker_timer_reset_sender);
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
                        log::info!("received new batch with id {}", id);
                        batch_receivers.insert(id, requests);
                        batch_senders.insert(id, results);
                    }
                    Err(_) => {
                        log::info!("batches channel closed");
                        batches_receiver = None;
                    }
                };
            }
            index if batch_receiver_indexes.contains_key(&index) => {
                let batch_id = batch_receiver_indexes[&index];
                match op.recv(&batch_receivers[&batch_id]) {
                    Ok(request) => {
                        log::info!("received work request for batch id {batch_id}");
                        work_queue.push_back((batch_id, request));
                    }
                    Err(_) => {
                        log::info!("batch request channel with id {batch_id} closed");
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
                    log::info!(
                        "received work result from worker id {worker_id} fo batch id {batch_id}",
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
                    log::info!("sending work request from batch id {batch_id} to worker id {worker_id}");
                    op.send(&worker_senders[worker_id], Some(request)).unwrap();
                    worker_queues[worker_id].push_back(Some(batch_id));
                }
                Err(_) => break,
            }
        }
        if work_queue.is_empty() {
            for (worker_id, queue) in worker_queues.iter_mut().enumerate() {
                if queue.len() == 2 && queue[0].is_none() && queue[1].is_some() {
                    log::info!("advancing queue for worker id {worker_id}");
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
                    log::info!("batch id {batch_id} flushed");
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
                    log::info!("flushing worker id {i}");
                    sender.send(None).unwrap();
                    worker_queues[i].push_back(None);
                }
            }
        }
        if batches_receiver.is_none() && batch_receivers.is_empty() && batches_to_flush.is_empty() {
            break;
        }
    }
    log::info!("GPU manager finished");
    Ok(())
}
