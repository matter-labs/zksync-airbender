use era_cudart::memory::memory_copy_async;

use super::*;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContextConfig;

// Local test-context builder for the `gpu_trace` suites. Mirrors the apex
// `prover::test_utils::make_test_context` minus its GKR `configure_kernel_
// attributes()` call, which only sets shared-memory carveout on the
// `ab_gkr_main_round*` flat kernels and is unreachable from this crate.
const TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

fn make_test_context(
    device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
) -> ProverContext {
    let default_block_log_size = ProverContextConfig::default().allocator_block_log_size;
    let arena_bytes = device_allocation_blocks_count << default_block_log_size;
    let test_blocks_count = arena_bytes >> TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let mut config = ProverContextConfig {
        allocator_block_log_size: TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
        device_allocation_blocks_count: Some(test_blocks_count),
        ..Default::default()
    };
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (host_pool_size_mb * 1024 * 1024) / host_block_size;
    // Disable the small sub-allocator when the block size is too small for it.
    if config
        .small_allocator_log_chunk_size
        .is_some_and(|s| s >= TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE)
    {
        config.small_allocator_log_chunk_size = None;
    }
    ProverContext::new(&config).unwrap()
}

#[test]
fn padded_raw_backing_preserves_prefix_and_zeros_recycled_tail_before_transfer() {
    use gpu_prover_context::transfer::Transfer;

    let context = make_test_context(64, 16);
    let baseline = context.get_used_mem_current();
    let rows = 1 << 8;
    let mut dirty = context
        .alloc::<u32>(8 * rows, AllocationPlacement::Bottom)
        .unwrap();
    let recycled_ptr = dirty.as_ptr();
    memory_set_async(
        // SAFETY: this exclusive allocation consists entirely of initialized-size u32 storage.
        unsafe { dirty.transmute_mut::<u8>() },
        0xff,
        context.get_exec_stream(),
    )
    .unwrap();
    drop(dirty);
    let mut holder = TraceHolder::<u32>::new_without_cosets_padded(
        8,
        1,
        1,
        3,
        5,
        2,
        TreesCacheMode::CacheNone,
        &context,
    )
    .unwrap();
    assert_eq!(holder.padded_hypercube_evals().as_ptr(), recycled_ptr);
    assert_eq!(holder.padded_hypercube_evals().len(), 8 * rows);
    assert_eq!(holder.get_hypercube_evals().len(), 5 * rows);
    assert_eq!(holder.get_uninit_hypercube_evals_mut().len(), 5 * rows);
    let source: Vec<u32> = (0..5 * rows).map(|i| i as u32 + 1).collect();
    let mut transfer = Transfer::new().unwrap();
    transfer.record_allocated(&context).unwrap();
    transfer.stage(&source, holder.get_uninit_hypercube_evals_mut());
    transfer.record_transferred(&context).unwrap();
    transfer.ensure_transferred(&context).unwrap();
    let mut actual = vec![u32::MAX; 8 * rows];
    memory_copy_async(
        &mut actual,
        holder.padded_hypercube_evals(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(&actual[..5 * rows], source.as_slice());
    assert!(actual[5 * rows..].iter().all(|&value| value == 0));
    drop(transfer);
    drop(holder);
    assert_eq!(context.get_used_mem_current(), baseline);
}
