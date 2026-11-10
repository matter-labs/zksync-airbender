mod baby_bear;
pub mod inputs;
mod job;
pub mod memory_policy;
mod orchestration;
pub(crate) mod pipeline;

use era_cudart::result::CudaResult;
use gpu_prover_context::ProverContext;

pub use baby_bear::{BabyBearProofRequest, GpuGKRProofJob};
pub use job::{ProofJob, ProofResult};

pub(crate) mod sealed {
    pub trait Sealed {}
    pub trait ResultSealed {}
}

/// A concrete proof request; implementations are sealed to the two field pipelines.
pub trait ProofRequest: sealed::Sealed + Sized {
    type Job;
    #[doc(hidden)]
    fn enqueue(self, context: &ProverContext) -> CudaResult<Self::Job>;
    #[doc(hidden)]
    fn collect_stage_snapshots(self) -> Self;
}

/// Enqueue the shared proof phase order with static field dispatch.
pub fn prove<P: ProofRequest>(request: P, context: &ProverContext) -> CudaResult<P::Job> {
    request.enqueue(context)
}

#[doc(hidden)]
pub fn prove_stagewise<P: ProofRequest>(request: P, context: &ProverContext) -> CudaResult<P::Job> {
    prove(request.collect_stage_snapshots(), context)
}
