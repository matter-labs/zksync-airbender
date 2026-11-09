use execution_prover::ProofProfile;
mod baby_bear;
mod caps;
mod inits_and_teardowns;
mod proth120;

#[cfg(any(test, feature = "test-support"))]
pub(crate) use proth120::evaluate_witness;

use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::WhirOracleStorage;
use execution_prover::messages::{
    SetupInitializationRequest, SetupInitializationResult, WorkRequest, WorkResult,
};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::ChunkedTraceHolder;
use std::borrow::Cow;
use worker::Worker;

#[derive(Default)]
pub(crate) struct CpuJobs {
    baby_bear: baby_bear::BabyBearJobs,
}

impl CpuJobs {
    pub(crate) fn execute<A: HostTraceAllocator>(
        &mut self,
        request: WorkRequest<A, CpuCircuitPrecomputations>,
        worker: &Worker,
    ) -> WorkResult<A> {
        match request {
            WorkRequest::L1WrapProof(request) => {
                WorkResult::L1WrapProof(proth120::run(request, worker))
            }
            WorkRequest::SetupInitialization(request) => {
                WorkResult::SetupInitialization(self.initialize_setup(request, worker))
            }
            WorkRequest::MemoryCommitment(request) => WorkResult::MemoryCommitment(
                baby_bear::memory::run(&mut self.baby_bear, request, worker),
            ),
            WorkRequest::Proof(request) => {
                WorkResult::Proof(baby_bear::proof::run(&mut self.baby_bear, request, worker))
            }
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
        } = request;
        if circuit_type.is_l1_wrap() {
            let l1_wrap = precomputations.l1_wrap();
            l1_wrap.initialize_setup(worker);
        } else {
            self.baby_bear.initialize_setup(&precomputations, worker);
        }
        SetupInitializationResult {
            batch_id,
            circuit_type,
            sequence_id,
        }
    }
}

fn whir_storage(
    profile: ProofProfile,
    config: &crate::upstream::ProverConfig,
) -> WhirOracleStorage {
    if profile.is_compression() {
        WhirOracleStorage::recompute_base_materialized_intermediates()
    } else if config.pack_log2() > 0 {
        WhirOracleStorage::fully_recompute()
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
