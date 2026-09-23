use super::*;
use era_cudart_sys::CudaError;

#[test]
fn cpu_exact_arena_rejects_invalid_block_counts_before_cuda() {
    let config = ProverContextConfig::default();
    let wrapping_blocks = (usize::MAX >> config.allocator_block_log_size) + 1;
    for (blocks, message) in [
        (0, "device arena must contain at least one block"),
        (31, "small allocator pools require 32"),
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
    let context = ProverContext::new_with_auto_arena_size(
        &ProverContextConfig {
            device_allocation_blocks_count: Some(budget >> config.allocator_block_log_size),
            ..config
        },
        |_| panic!("explicit arena must bypass automatic selection"),
    )
    .unwrap();
    assert_eq!(context.get_mem_size(), budget);
    let large_bytes =
        budget - ((2 * config.small_allocator_pool_blocks) << config.allocator_block_log_size);
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
fn automatic_arena_uses_selected_size() {
    let budget = 64 << 20;
    let context = ProverContext::new_with_auto_arena_size(&small_context_config(), |available| {
        assert!(available >= budget);
        budget
    })
    .unwrap();
    assert_eq!(context.get_mem_size(), budget);
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

#[test]
fn allocation_modes_place_within_their_side() {
    let config = small_context_config();
    let block = 1usize << config.allocator_block_log_size;
    let reserve = 8 * block;
    let mut context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(64),
        inputs_reserve_bytes: reserve,
        ..config
    })
    .unwrap();
    let Range { start, end } = context.arena.clone();
    let addr = |allocation: &DeviceAllocation<u8>| allocation.as_ptr() as usize;

    context.set_allocation_mode(AllocationMode::Inputs(AllocationSide::Low));
    let low_input = context
        .alloc::<u8>(block, AllocationPlacement::Top)
        .unwrap();
    assert_eq!(addr(&low_input), start);
    context.set_allocation_mode(AllocationMode::Inputs(AllocationSide::High));
    let high_input = context
        .alloc::<u8>(block, AllocationPlacement::Bottom)
        .unwrap();
    assert_eq!(addr(&high_input), end - block);

    context.set_allocation_mode(AllocationMode::Proof(AllocationSide::Low));
    let low_top = context
        .alloc::<u8>(block, AllocationPlacement::Top)
        .unwrap();
    let low_bottom = context
        .alloc::<u8>(block, AllocationPlacement::Bottom)
        .unwrap();
    assert_eq!(addr(&low_top), end - reserve - block);
    assert_eq!(addr(&low_bottom), start + block);
    let low_small = context
        .alloc::<u8>(64, AllocationPlacement::Bottom)
        .unwrap();

    context.set_allocation_mode(AllocationMode::Proof(AllocationSide::High));
    let high_top = context
        .alloc::<u8>(block, AllocationPlacement::Top)
        .unwrap();
    let high_bottom = context
        .alloc::<u8>(block, AllocationPlacement::Bottom)
        .unwrap();
    assert_eq!(addr(&high_top), start + reserve);
    assert_eq!(addr(&high_bottom), end - 2 * block);
    let high_small = context
        .alloc::<u8>(64, AllocationPlacement::Bottom)
        .unwrap();

    assert!(addr(&low_small) < start && addr(&high_small) >= end);
    drop((
        low_input,
        high_input,
        low_top,
        low_bottom,
        low_small,
        high_top,
        high_bottom,
        high_small,
    ));
    assert_eq!(context.get_used_mem_current(), 0);
}

#[test]
fn proof_mode_never_enters_the_far_reserve() {
    let config = small_context_config();
    let block = 1usize << config.allocator_block_log_size;
    let reserve = 8 * block;
    let mut context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(64),
        inputs_reserve_bytes: reserve,
        ..config
    })
    .unwrap();
    let proof_room = context.arena.len() - reserve;
    context.set_allocation_mode(AllocationMode::Proof(AllocationSide::Low));
    let all = context
        .alloc::<u8>(proof_room, AllocationPlacement::BestFit)
        .unwrap();
    assert!(matches!(
        context.alloc::<u8>(block, AllocationPlacement::Top),
        Err(CudaError::ErrorMemoryAllocation)
    ));
    context.set_allocation_mode(AllocationMode::Inputs(AllocationSide::High));
    let input = context
        .alloc::<u8>(reserve, AllocationPlacement::Top)
        .unwrap();
    drop((all, input));
}

#[test]
#[should_panic(expected = "input bundle exceeds the 8388608-byte next-inputs reserve")]
fn inputs_mode_panics_past_the_reserve() {
    let config = small_context_config();
    let block = 1usize << config.allocator_block_log_size;
    let mut context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(64),
        inputs_reserve_bytes: 8 * block,
        ..config
    })
    .unwrap();
    context.set_allocation_mode(AllocationMode::Inputs(AllocationSide::Low));
    let _ = context.alloc::<u8>(9 * block, AllocationPlacement::Bottom);
}
