use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceVariable;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

/// Transcript words for query bits, including the skipped header and one
/// complete eight-word squeeze block at a time (Blake2s and Keccak).
pub(crate) fn query_words(queries: usize, query_domain_log2: u32) -> usize {
    ((queries * query_domain_log2 as usize).div_ceil(32) + 1).next_multiple_of(8)
}

pub(crate) fn schedule_running_powers<T: gpu_ops::powers::GetPowersByRef>(
    base: &DeviceVariable<T>,
    queries: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    let mut powers = context.alloc(queries + 1, AllocationPlacement::BestFit)?;
    gpu_ops::powers::get_powers_by_ref(base, 1, &mut powers, context.get_exec_stream())?;
    Ok(powers)
}
