use super::*;

#[test]
fn cpu_exact_budget_rejects_invalid_sizes_before_cuda() {
    let config = ProverContextConfig::default();
    for bytes in [0, 1, (1 << 20) + 1, 15 << 20] {
        assert!(matches!(
            ProverContext::new(&ProverContextConfig {
                device_arena_budget_bytes: Some(bytes),
                ..config
            }),
            Err(CudaError::ErrorInvalidValue)
        ));
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
        device_arena_budget_bytes: Some(budget),
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
    let oversized = (total / block_size + 1) * block_size;
    assert!(matches!(
        ProverContext::new(&ProverContextConfig {
            device_arena_budget_bytes: Some(oversized),
            ..config
        }),
        Err(CudaError::ErrorMemoryAllocation)
    ));
}
