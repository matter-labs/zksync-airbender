//! One thread that serves whichever active batch has a ready request.

use crate::jobs::CpuJobs;
use crate::precomputations::CpuCircuitPrecomputations;
use crossbeam_channel::{unbounded, Receiver, Select, Sender};
use execution_prover::messages::{WorkBatch, WorkRequest, WorkerResult};
use execution_prover::spawn_abort_on_panic;
use execution_prover_model::allocator::CpuTraceAllocator;
use std::collections::HashMap;
use std::sync::Arc;
use std::thread::JoinHandle;
use worker::Worker;

type Batch = WorkBatch<CpuTraceAllocator, CpuCircuitPrecomputations>;
type Request = WorkRequest<CpuTraceAllocator, CpuCircuitPrecomputations>;
type Completion = WorkerResult<CpuTraceAllocator>;

pub(crate) struct CpuManager {
    batches: Option<Sender<Batch>>,
    thread: Option<JoinHandle<()>>,
}

impl CpuManager {
    pub(crate) fn new(worker: Arc<Worker>) -> Self {
        let (sender, receiver) = unbounded();
        let thread = spawn_abort_on_panic("cpu-exec-manager".to_owned(), move || {
            serve(worker, receiver)
        });
        Self {
            batches: Some(sender),
            thread: Some(thread),
        }
    }

    pub(crate) fn send_batch(&self, batch: Batch) {
        self.batches
            .as_ref()
            .expect("CPU manager batch sender must exist before shutdown")
            .send(batch)
            .expect("CPU manager batch channel closed before all work was submitted");
    }
}

impl Drop for CpuManager {
    fn drop(&mut self) {
        drop(self.batches.take().unwrap());
        self.thread.take().unwrap().join().unwrap();
    }
}

fn serve(worker: Arc<Worker>, batches: Receiver<Batch>) {
    let mut jobs = CpuJobs::default();
    let mut batches = Some(batches);
    let mut active: HashMap<u64, (Receiver<Request>, Sender<Completion>)> = HashMap::new();
    while batches.is_some() || !active.is_empty() {
        let mut select = Select::new();
        let batches_index = batches.as_ref().map(|receiver| select.recv(receiver));
        let request_indexes: HashMap<usize, u64> = active
            .iter()
            .map(|(&batch_id, (receiver, _))| (select.recv(receiver), batch_id))
            .collect();
        let op = select.select();
        let index = op.index();
        if batches_index == Some(index) {
            match op.recv(batches.as_ref().unwrap()) {
                Ok(batch) => {
                    let batch_id = batch.batch_id;
                    let previous = active.insert(batch_id, (batch.receiver, batch.sender));
                    assert!(previous.is_none(), "batch {batch_id} is already active");
                }
                Err(_) => batches = None,
            }
            continue;
        }
        let batch_id = request_indexes[&index];
        match op.recv(&active[&batch_id].0) {
            Ok(request) => {
                let result = worker.pool.install(|| jobs.execute(request, &worker));
                active[&batch_id]
                    .1
                    .send(WorkerResult::BackendWorkResult(result))
                    .expect("CPU manager result channel closed before the batch retired");
            }
            Err(_) => {
                active.remove(&batch_id);
            }
        }
    }
}
