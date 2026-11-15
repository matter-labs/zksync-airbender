pub(super) mod memory;
pub(super) mod proof;

use super::inits_and_teardowns::{self, TeardownColumns};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{Backend, DefaultBabyBearBackend, DefaultBabyBearGKRBackend, BF, E4};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::InitsAndTeardownsTraceHost;
use std::collections::HashMap;
use std::sync::Arc;
use worker::Worker;

type CpuTwiddles = <DefaultBabyBearBackend as Backend<BF, E4>>::TwiddleSet;

#[derive(Default)]
pub(super) struct BabyBearJobs {
    backend: DefaultBabyBearBackend,
    gkr_backend: DefaultBabyBearGKRBackend,
    twiddles: HashMap<usize, Arc<CpuTwiddles>>,
}

impl BabyBearJobs {
    pub(super) fn initialize_setup(
        &mut self,
        precomputations: &CpuCircuitPrecomputations,
        worker: &Worker,
    ) {
        let message_size_log2 = precomputations.max_whir_message_size_log2();
        let twiddles = self.twiddles(1usize << message_size_log2, worker);
        precomputations.initialize_setup(&*twiddles, worker);
    }

    fn twiddles(&mut self, message_len: usize, worker: &Worker) -> Arc<CpuTwiddles> {
        self.twiddles
            .entry(message_len)
            .or_insert_with(|| {
                Arc::new(<DefaultBabyBearBackend as Backend<BF, E4>>::make_twiddles(
                    &self.backend,
                    message_len,
                    worker,
                ))
            })
            .clone()
    }
}

fn teardown_sets<A: HostTraceAllocator>(
    precomputations: &CpuCircuitPrecomputations,
    trace: Option<&InitsAndTeardownsTraceHost<A>>,
) -> Vec<TeardownColumns<BF>> {
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
