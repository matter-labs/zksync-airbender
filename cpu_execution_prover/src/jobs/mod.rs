//! The CPU request handlers, one module per request kind.

pub(crate) mod memory;
pub(crate) mod proof;
pub(crate) mod setup;

use crate::adapters::inits_and_teardowns::{self, TeardownColumns};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{Backend, DefaultBabyBearBackend, DefaultBabyBearGKRBackend, BF, E4};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::messages::{WorkRequest, WorkResult};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::InitsAndTeardownsTraceHost;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use worker::Worker;

type CpuTwiddles = <DefaultBabyBearBackend as Backend<BF, E4>>::TwiddleSet;

#[derive(Default)]
pub(crate) struct CpuJobs {
    pub(crate) backend: DefaultBabyBearBackend,
    pub(crate) gkr_backend: DefaultBabyBearGKRBackend,
    twiddles: Mutex<HashMap<usize, Arc<CpuTwiddles>>>,
}

impl CpuJobs {
    pub(crate) fn execute<A: HostTraceAllocator>(
        &self,
        request: WorkRequest<A, CpuCircuitPrecomputations>,
        worker: &Worker,
    ) -> WorkResult<A> {
        match request {
            WorkRequest::SetupInitialization(request) => {
                WorkResult::SetupInitialization(setup::run(self, request, worker))
            }
            WorkRequest::MemoryCommitment(request) => {
                WorkResult::MemoryCommitment(memory::run(self, request, worker))
            }
            WorkRequest::Proof(request) => WorkResult::Proof(proof::run(self, request, worker)),
        }
    }

    /// The twiddle set for `trace_len`, built once and handed out behind an
    /// `Arc` so a commitment runs without holding the cache lock.
    pub(crate) fn twiddles(&self, trace_len: usize, worker: &Worker) -> Arc<CpuTwiddles> {
        let mut cache = self
            .twiddles
            .lock()
            .expect("twiddle cache mutex is never poisoned");
        cache
            .entry(trace_len)
            .or_insert_with(|| {
                Arc::new(<DefaultBabyBearBackend as Backend<BF, E4>>::make_twiddles(
                    &self.backend,
                    trace_len,
                    worker,
                ))
            })
            .clone()
    }
}

/// The circuit's teardown sets, expanded from the instance's packed pages or
/// zero-filled when the instance carries none.
pub(crate) fn teardown_sets<A: HostTraceAllocator>(
    precomputations: &CpuCircuitPrecomputations,
    trace: Option<&InitsAndTeardownsTraceHost<A>>,
) -> Vec<TeardownColumns> {
    let num_sets = precomputations
        .compiled_circuit()
        .memory_layout
        .teardown_sets
        .len();
    match trace {
        Some(trace) => {
            inits_and_teardowns::expand(trace, num_sets, precomputations.trace_len_log2() as u32)
        }
        None => inits_and_teardowns::zero_sets(num_sets, precomputations.trace_len),
    }
}

#[cfg(test)]
mod tests;
