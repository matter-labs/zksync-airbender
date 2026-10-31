//! Crate-local test-context builder.
//!
//! `gpu_whir`'s own unit tests need a `ProverContext`; the apex crate's
//! `prover::test_utils::make_test_context` stays in `gpu_circuit_prover` (it is
//! shared by the apex e2e suite and can't move down without dragging the proof
//! layer). This self-contained copy mirrors that helper.

use gpu_prover_context::{ProverContext, ProverContextConfig};
use prover::definitions::SecurityLevel;
use prover::gkr::prover_config::ProofProfile;

const TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

pub(crate) fn make_test_context(
    device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
) -> ProverContext {
    let default_block_log_size = ProverContextConfig::default().allocator_block_log_size;
    let arena_bytes = device_allocation_blocks_count << default_block_log_size;
    let test_blocks_count = arena_bytes >> TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    make_test_context_with_device_allocator_block_log_size(
        test_blocks_count,
        host_pool_size_mb,
        TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
    )
}

pub(crate) fn make_test_context_with_device_allocator_block_log_size(
    device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
    device_allocator_block_log_size: u32,
) -> ProverContext {
    let mut config = ProverContextConfig {
        allocator_block_log_size: device_allocator_block_log_size,
        device_allocation_blocks_count: Some(device_allocation_blocks_count),
        ..Default::default()
    };
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (host_pool_size_mb * 1024 * 1024) / host_block_size;
    // Disable the small sub-allocator when the block size is too small for it.
    if config
        .small_allocator_log_chunk_size
        .is_some_and(|s| s >= device_allocator_block_log_size)
    {
        config.small_allocator_log_chunk_size = None;
    }
    ProverContext::new(&config).unwrap()
}

/// The intermediate WHIR oracles of the 2^22 L1 feeder, from its config:
/// `(log_n, log_v, lde_factor, cap_size)` per oracle.
pub(crate) fn l1_feeder_oracle_shapes() -> Vec<(u32, u32, usize, usize)> {
    let config = ProofProfile::L1Feeder.prover_config(22, SecurityLevel::Sec100);
    let schedule = &config.whir_schedule;
    let steps = &schedule.fold_steps();
    assert_eq!(steps.len(), schedule.intermediate_lde_factors().len() + 1);
    let mut log_n = config.trace_len_log2 as u32;
    schedule
        .intermediate_lde_factors()
        .iter()
        .enumerate()
        .map(|(round, &lde_factor)| {
            log_n -= steps[round] as u32;
            (
                log_n,
                steps[round + 1] as u32,
                lde_factor,
                schedule.cap_size,
            )
        })
        .collect()
}
