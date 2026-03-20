use crate::primitives::context::{ProverContext, ProverContextConfig};

pub(crate) fn make_test_context(
    max_device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
) -> ProverContext {
    make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        host_pool_size_mb,
        ProverContextConfig::default().allocator_block_log_size,
    )
}

pub(crate) fn make_test_context_with_device_allocator_block_log_size(
    max_device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
    device_allocator_block_log_size: u32,
) -> ProverContext {
    let mut config = ProverContextConfig::default();
    config.allocator_block_log_size = device_allocator_block_log_size;
    config.max_device_allocation_blocks_count = Some(max_device_allocation_blocks_count);
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (host_pool_size_mb * 1024 * 1024) / host_block_size;
    ProverContext::new(&config).unwrap()
}
