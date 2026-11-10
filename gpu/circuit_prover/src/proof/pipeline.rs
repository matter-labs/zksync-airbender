use era_cudart::result::CudaResult;
use gpu_prover_context::ProverContext;

pub(crate) trait ProofPipeline: super::sealed::Sealed + Sized {
    type Joined;
    type Committed;
    type Challenged;
    type Gkr;
    type Whir;
    type Job;

    fn join(self, context: &ProverContext) -> CudaResult<Self::Joined>;
    fn witness_commit(state: Self::Joined, context: &ProverContext) -> CudaResult<Self::Committed>;
    fn challenges(state: Self::Committed, context: &ProverContext) -> CudaResult<Self::Challenged>;
    fn gkr(state: Self::Challenged, context: &ProverContext) -> CudaResult<Self::Gkr>;
    fn whir(state: Self::Gkr, context: &ProverContext) -> CudaResult<Self::Whir>;
    fn readback(state: Self::Whir, context: &ProverContext) -> CudaResult<Self::Job>;
}

pub(crate) fn prove<P: ProofPipeline>(request: P, context: &ProverContext) -> CudaResult<P::Job> {
    let joined = request.join(context)?;
    let committed = P::witness_commit(joined, context)?;
    let challenged = P::challenges(committed, context)?;
    let gkr = P::gkr(challenged, context)?;
    let whir = P::whir(gkr, context)?;
    P::readback(whir, context)
}

pub(crate) struct ProofWork<'a, T: super::job::ProofResult> {
    pub callbacks: gpu_core::primitives::callbacks::Callbacks<'a>,
    pub result: Box<Option<T>>,
    pub ranges: Vec<gpu_core::primitives::device_tracing::Range>,
    pub proof_range: gpu_core::primitives::device_tracing::Range,
}

impl<T: super::job::ProofResult> ProofWork<'_, T> {
    pub(crate) fn new(name: &str, context: &ProverContext) -> CudaResult<Self> {
        let callbacks = gpu_core::primitives::callbacks::Callbacks::new();
        let result = Box::new(None);
        let ranges = Vec::new();
        let proof_range = gpu_core::primitives::device_tracing::Range::new(name)?;
        proof_range.start(context.get_exec_stream())?;
        Ok(Self {
            callbacks,
            result,
            ranges,
            proof_range,
        })
    }
}
