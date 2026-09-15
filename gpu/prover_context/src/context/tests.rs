use super::*;
use era_cudart_sys::CudaError;

#[test]
fn cpu_exact_arena_rejects_invalid_block_counts_before_cuda() {
    let config = ProverContextConfig::default();
    let wrapping_blocks = (usize::MAX >> config.allocator_block_log_size) + 1;
    for (blocks, message) in [
        (0, "device arena must contain at least one block"),
        (15, "small allocator pool requires 16"),
        (wrapping_blocks, "device arena size overflows usize"),
    ] {
        let panic = std::panic::catch_unwind(|| {
            let _ = ProverContext::new(&ProverContextConfig {
                device_allocation_blocks_count: Some(blocks),
                ..config
            });
        })
        .expect_err("invalid arena must panic before calling CUDA");
        let message_actual = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(message_actual.contains(message), "{message_actual}");
    }
}

fn small_context_config() -> ProverContextConfig {
    ProverContextConfig {
        host_allocator_blocks_count: 128,
        device_slack_static_bytes: 1 << 20,
        device_slack_per_thread_bytes: 0,
        ..Default::default()
    }
}

#[test]
fn exact_budget_includes_small_pool_and_enforces_boundary() {
    let config = small_context_config();
    let budget = 64 << 20;
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(budget >> config.allocator_block_log_size),
        ..config
    })
    .unwrap();
    assert_eq!(context.get_mem_size(), budget);
    let large_bytes =
        budget - (config.small_allocator_pool_blocks << config.allocator_block_log_size);
    let large = context
        .alloc::<u8>(large_bytes, AllocationPlacement::BestFit)
        .unwrap();
    assert!(matches!(
        context.alloc::<u8>(1 << 20, AllocationPlacement::BestFit),
        Err(CudaError::ErrorMemoryAllocation)
    ));
    drop(large);
    assert_eq!(context.get_used_mem_current(), 0);
    context
        .alloc::<u8>(large_bytes, AllocationPlacement::BestFit)
        .unwrap();
}

#[test]
fn exact_budget_does_not_shrink_on_driver_oom() {
    let config = small_context_config();
    let (_, total) = memory_get_info().unwrap();
    let block_size = 1usize << config.allocator_block_log_size;
    let oversized_blocks = total / block_size + 1;
    assert!(matches!(
        ProverContext::new(&ProverContextConfig {
            device_allocation_blocks_count: Some(oversized_blocks),
            ..config
        }),
        Err(CudaError::ErrorMemoryAllocation)
    ));
}
