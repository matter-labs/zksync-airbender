use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;
use gpu_prover_context::ProverContext;

mod generated;
pub(crate) use generated::{policy, ARENA_BYTES};

pub(crate) fn validate_device_budget(context: &ProverContext) -> CudaResult<()> {
    if context.get_mem_size() < ARENA_BYTES {
        return Err(CudaError::ErrorMemoryAllocation);
    }
    Ok(())
}
