use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::DeviceMatrixMutImpl;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_ops::simple::set_to_zero;
use gpu_prover_context::ProverContext;

const COUNTER_REPLICAS: usize = 8;

cuda_kernel!(CountProth120Multiplicities,
    ab_pr_count_multiplicities_kernel(
        lookup_mapping: *mut u32,
        lookup_mapping_size: u32,
        counter_shards: *mut u32,
        active_counts_len: u32,
        counter_replicas: u32,
    )
);

cuda_kernel!(ReduceConvertProth120Multiplicities,
    ab_pr_reduce_convert_multiplicities_kernel(
        counter_shards: *const u32,
        multiplicities: *mut PR,
        active_counts_len: u32,
        counter_replicas: u32,
    )
);

pub fn generate_lookup_multiplicities(
    mapping: &mut impl DeviceMatrixMutImpl<u32>,
    multiplicities: &mut impl DeviceMatrixMutImpl<PR>,
    active_counts_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let stride = mapping.stride();
    assert!(stride.is_power_of_two());
    assert_eq!(stride, multiplicities.stride());
    let mapping_len = mapping.slice().len();
    let multiplicities_len = multiplicities.slice().len();
    let stream = context.get_exec_stream();
    set_to_zero(multiplicities.slice_mut(), stream)?;
    if mapping_len == 0 {
        return Ok(());
    }
    assert!(mapping_len < u32::MAX as usize);
    assert!(active_counts_len > 0);
    assert!(active_counts_len <= multiplicities_len);
    let counter_storage_len = active_counts_len * COUNTER_REPLICAS;
    assert!(counter_storage_len <= u32::MAX as usize);

    let mapping_len = mapping_len as u32;
    let active_counts_len = active_counts_len as u32;
    let counter_replicas = COUNTER_REPLICAS as u32;
    let mut counter_shards: DeviceAllocation<u32> =
        context.alloc(counter_storage_len, AllocationPlacement::BestFit)?;
    set_to_zero(&mut counter_shards, stream)?;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, mapping_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = CountProth120MultiplicitiesArguments::new(
        mapping.as_mut_ptr(),
        mapping_len,
        counter_shards.as_mut_ptr(),
        active_counts_len,
        counter_replicas,
    );
    CountProth120MultiplicitiesFunction::default().launch(&config, &args)?;

    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, active_counts_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ReduceConvertProth120MultiplicitiesArguments::new(
        counter_shards.as_ptr(),
        multiplicities.as_mut_ptr(),
        active_counts_len,
        counter_replicas,
    );
    ReduceConvertProth120MultiplicitiesFunction::default().launch(&config, &args)
}
