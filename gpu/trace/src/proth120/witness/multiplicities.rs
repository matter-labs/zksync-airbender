use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_ops::simple::set_to_zero;
use gpu_prover_context::ProverContext;

crate::witness::multiplicities::define_lookup_multiplicities!(
    PR,
    u32,
    u32::MAX as usize,
    allocate_counter_storage,
    ab_pr_count_multiplicities_kernel,
    ab_pr_reduce_convert_multiplicities_kernel
);

fn allocate_counter_storage(
    counter_storage_len: usize,
    _multiplicities_len: usize,
    context: &ProverContext,
) -> CudaResult<Option<DeviceAllocation<u32>>> {
    let mut storage = context.alloc(counter_storage_len, AllocationPlacement::BestFit)?;
    set_to_zero(&mut storage, context.get_exec_stream())?;
    Ok(Some(storage))
}
