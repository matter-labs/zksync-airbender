use super::*;
use crate::upstream::{lde_coset_lazy_r8, precompute_twiddles_for_fft, Field, Worker};
use era_cudart::memory::memory_copy_async;
use era_cudart_sys::CudaError;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use gpu_core::primitives::field::PR;

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

fn reserved_context(reserve: usize) -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(64),
        inputs_reserve_bytes: reserve,
        ..small_context_config()
    })
    .unwrap()
}

#[test]
fn allocation_modes_place_within_their_side() {
    use AllocationDirection::{Ascending, Descending};
    use AllocationMode::{Inputs, Proof};
    use AllocationPlacement::{BestFit, Bottom, Top};
    let block = 1usize << small_context_config().allocator_block_log_size;
    let reserve = 8 * block;
    let mut context = reserved_context(reserve);
    let Range { start, end } = context.arena.clone();
    let mut live = Vec::new();
    let mut alloc = |mode, bytes, placement| {
        context.set_allocation_mode(mode);
        let allocation = context.alloc::<u8>(bytes, placement).unwrap();
        let addr = allocation.as_ptr() as usize;
        live.push(allocation);
        addr
    };
    assert_eq!(alloc(Inputs(Ascending), block, Top), start);
    assert_eq!(alloc(Inputs(Descending), block, Top), end - block);
    assert_eq!(alloc(Proof(Ascending), block, Top), end - reserve - block);
    assert_eq!(alloc(Proof(Descending), block, Top), start + reserve);
    assert_eq!(alloc(Proof(Ascending), block, BestFit), start + block);
    assert_eq!(alloc(Proof(Descending), block, BestFit), end - 2 * block);
    assert!(alloc(Proof(Ascending), 64, Bottom) < start);
    assert!(alloc(Proof(Descending), 64, Bottom) >= end);
    drop(live);
    assert_eq!(context.get_used_mem_current(), 0);
}

#[test]
#[should_panic(
    expected = "9437184-byte input does not fit the 8388608-byte Ascending inputs reserve"
)]
fn inputs_mode_panics_past_the_reserve() {
    let block = 1usize << small_context_config().allocator_block_log_size;
    let mut context = reserved_context(8 * block);
    context.set_allocation_mode(AllocationMode::Inputs(AllocationDirection::Ascending));
    let _ = context.alloc::<u8>(9 * block, AllocationPlacement::Bottom);
}

fn assert_proth120_context(context: &ProverContext) {
    let proth120_context = context.proth120_ntt_device_context();
    assert_eq!(proth120_context.log_max_domain(), 31);
    let _: gpu_ntt::proth120::TwiddleDescriptor = proth120_context.descriptor();
    assert_eq!(
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
        27
    );
    let n = 256usize;
    let input: Vec<PR> = (0..n).map(|i| PR::new(7 * i as u128 + 1)).collect();
    let worker = Worker::new_with_num_threads(1);
    let twiddles = precompute_twiddles_for_fft::<PR, std::alloc::Global, false>(n, &worker);
    let expected = lde_coset_lazy_r8(&input, PR::ONE, &twiddles);
    let stream = context.get_exec_stream();
    let mut device_input = era_cudart::memory::DeviceAllocation::<PR>::alloc(n).unwrap();
    let mut device_output = era_cudart::memory::DeviceAllocation::<PR>::alloc(n).unwrap();
    let mut device_offset = era_cudart::memory::DeviceAllocation::<PR>::alloc(1).unwrap();
    let offset = [PR::ONE];
    memory_copy_async(&mut device_input, &input, stream).unwrap();
    memory_copy_async(&mut device_offset, &offset, stream).unwrap();
    gpu_ntt::proth120::lde_coset(
        proth120_context,
        &DeviceMatrixChunk::new(&device_input[..], n, 0, n),
        &mut DeviceMatrixChunkMut::new(&mut device_output[..], n, 0, n),
        &device_offset,
        stream,
    )
    .unwrap();
    let mut actual = vec![PR::ZERO; n];
    memory_copy_async(&mut actual, &device_output, stream).unwrap();
    stream.synchronize().unwrap();
    let actual: Vec<u128> = actual.iter().map(|value| value.0).collect();
    let expected: Vec<u128> = expected.iter().map(|value| value.0).collect();
    assert_eq!(actual, expected);
}

#[test]
fn proth120_optional_context() {
    let config = small_context_config();
    let budget = 64 << 20;
    let explicit = ProverContextConfig {
        device_allocation_blocks_count: Some(budget >> config.allocator_block_log_size),
        ..config
    };
    let context = ProverContext::new(&explicit).unwrap();
    assert!(context._proth120_device_context.is_none());
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        context.proth120_ntt_device_context();
    }))
    .expect_err("an unconfigured Proth120 NTT context must panic");
    let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap();
    assert_eq!(message, "Proth120 NTT context is not configured");
    drop(context);
    let context = ProverContext::new(&ProverContextConfig {
        proth120_ntt_log_max_domain: Some(31),
        ..explicit
    })
    .unwrap();
    assert_eq!(context.get_mem_size(), budget);
    assert_proth120_context(&context);
    drop(context);
    let context = ProverContext::new_with_auto_arena_size(
        &ProverContextConfig {
            proth120_ntt_log_max_domain: Some(31),
            ..config
        },
        |available| {
            assert!(available >= budget);
            budget
        },
    )
    .unwrap();
    assert_eq!(context.get_mem_size(), budget);
    assert_proth120_context(&context);
}
