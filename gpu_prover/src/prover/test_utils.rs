use crate::primitives::context::{ProverContext, ProverContextConfig};

pub(crate) fn make_test_context(
    max_device_allocation_blocks_count: usize,
    host_allocator_blocks_count: usize,
) -> ProverContext {
    let mut config = ProverContextConfig::default();
    config.max_device_allocation_blocks_count = Some(max_device_allocation_blocks_count);
    config.host_allocator_blocks_count = host_allocator_blocks_count;
    ProverContext::new(&config).unwrap()
}
