use execution_prover::ProofProfile;
mod caps;
mod inits_and_teardowns;
mod l1_wrap;
mod memory;
mod proof;

use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    Backend, DefaultBabyBearBackend, DefaultBabyBearGKRBackend, WhirOracleStorage, BF, E4,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::messages::{
    SetupInitializationRequest, SetupInitializationResult, WorkRequest, WorkResult,
};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{ChunkedTraceHolder, InitsAndTeardownsTraceHost};
use inits_and_teardowns::TeardownColumns;
use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;
use worker::Worker;

type CpuTwiddles = <DefaultBabyBearBackend as Backend<BF, E4>>::TwiddleSet;

#[derive(Default)]
pub(crate) struct CpuJobs {
    backend: DefaultBabyBearBackend,
    gkr_backend: DefaultBabyBearGKRBackend,
    twiddles: HashMap<usize, Arc<CpuTwiddles>>,
}

impl CpuJobs {
    pub(crate) fn execute<A: HostTraceAllocator>(
        &mut self,
        request: WorkRequest<A, CpuCircuitPrecomputations>,
        worker: &Worker,
    ) -> WorkResult<A> {
        match request {
            WorkRequest::L1WrapProof(request) => {
                WorkResult::L1WrapProof(l1_wrap::run(request, worker))
            }
            WorkRequest::SetupInitialization(request) => {
                WorkResult::SetupInitialization(self.initialize_setup(request, worker))
            }
            WorkRequest::MemoryCommitment(request) => {
                WorkResult::MemoryCommitment(memory::run(self, request, worker))
            }
            WorkRequest::Proof(request) => WorkResult::Proof(proof::run(self, request, worker)),
        }
    }

    fn initialize_setup(
        &mut self,
        request: SetupInitializationRequest<CpuCircuitPrecomputations>,
        worker: &Worker,
    ) -> SetupInitializationResult {
        let SetupInitializationRequest {
            batch_id,
            circuit_type,
            sequence_id,
            precomputations,
            security_level,
        } = request;
        if circuit_type == CircuitType::L1Wrap {
            precomputations
                .l1_wrap()
                .initialize_setup(security_level, worker);
        } else {
            let twiddles = self.twiddles(precomputations.trace_len, worker);
            precomputations.initialize_setup(security_level, &*twiddles, worker);
        }
        SetupInitializationResult {
            batch_id,
            circuit_type,
            sequence_id,
        }
    }

    fn twiddles(&mut self, trace_len: usize, worker: &Worker) -> Arc<CpuTwiddles> {
        self.twiddles
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

fn whir_storage(profile: ProofProfile) -> WhirOracleStorage {
    if profile == ProofProfile::L1Feeder {
        WhirOracleStorage::recompute_base_materialized_intermediates()
    } else {
        WhirOracleStorage::fully_in_memory()
    }
}

fn rows<T: Clone, A: HostTraceAllocator>(holder: &ChunkedTraceHolder<T, A>) -> Cow<'_, [T]> {
    match holder.chunks.as_slice() {
        [] => Cow::Borrowed(&[]),
        [single] => Cow::Borrowed(single.as_slice()),
        chunks => {
            let mut flattened = Vec::with_capacity(holder.len());
            for chunk in chunks {
                flattened.extend_from_slice(chunk);
            }
            Cow::Owned(flattened)
        }
    }
}

fn teardown_sets<A: HostTraceAllocator>(
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
