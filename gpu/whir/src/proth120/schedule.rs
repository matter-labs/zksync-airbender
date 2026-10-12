use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_gkr::gkr_ops::assemble_query_indexes;
use gpu_hash::keccak256::{keccak256_pow, transcript_draw_fields, transcript_draw_u32};
use gpu_ntt::proth120::{update_eq_poly, EqSample};
use gpu_ops::powers::get_powers_by_ref;
use gpu_prover_context::ProverContext;

use super::state::L1WhirState;

pub(crate) fn query_words(queries: usize, query_domain_log2: u32) -> usize {
    ((queries * query_domain_log2 as usize).div_ceil(32) + 1).next_multiple_of(8)
}

pub(crate) fn schedule_pow_and_query_indexes(
    seed: &mut DeviceSlice<u8>,
    queries: usize,
    pow_bits: u32,
    query_domain_log2: u32,
    nonce_dst: &mut DeviceVariable<u64>,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<u32>> {
    assert!(
        queries > 0 && (1..=32).contains(&query_domain_log2),
        "Proth120 WHIR: query phase geometry invalid"
    );
    let stream = context.get_exec_stream();
    keccak256_pow(seed, pow_bits, nonce_dst, stream)?;
    let mut raw = context.alloc(
        query_words(queries, query_domain_log2),
        AllocationPlacement::BestFit,
    )?;
    transcript_draw_u32(seed, &mut raw, stream)?;
    let mut indexes = context.alloc(queries, AllocationPlacement::BestFit)?;
    assemble_query_indexes(&raw, &mut indexes, query_domain_log2, stream)?;
    Ok(indexes)
}

pub(crate) fn schedule_delinearization(
    seed: &mut DeviceSlice<u8>,
    queries: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<PR>> {
    let stream = context.get_exec_stream();
    let mut delta = context.alloc(1, AllocationPlacement::BestFit)?;
    transcript_draw_fields(seed, &mut delta, stream)?;
    let mut powers = context.alloc(queries + 1, AllocationPlacement::BestFit)?;
    get_powers_by_ref(
        unsafe { DeviceVariable::from_raw_parts(delta.as_ptr()) },
        1,
        &mut powers,
        stream,
    )?;
    Ok(powers)
}

pub(crate) fn schedule_eq_update(
    state: &mut L1WhirState,
    ood_point: &DeviceSlice<PR>,
    weight: &DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        ood_point.len() == 1 && weight.len() == 1,
        "Proth120 WHIR: eq update sample lengths invalid"
    );
    let stream = context.get_exec_stream();
    let mut sample = context.alloc::<EqSample>(1, AllocationPlacement::BestFit)?;
    let slots: &mut DeviceSlice<PR> = unsafe { sample.transmute_mut() };
    memory_copy_async(&mut slots[0..1], ood_point, stream)?;
    memory_copy_async(&mut slots[1..2], weight, stream)?;
    let len = state.current_len;
    update_eq_poly(&mut state.eq[..len], &sample, &sample[..0], stream)
}
