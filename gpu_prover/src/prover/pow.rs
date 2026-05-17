use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::{
    assemble_query_indexes, blake2s_pow, transcript_commit, transcript_squeeze, STATE_SIZE,
};
use crate::primitives::context::{DeviceAllocation, ProverContext};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};

/// Device buffers produced by [`schedule_pow_verify_and_query_indexes`]. The
/// rolling `device_seed` is owned by the WHIR scheduler and threaded in by the
/// caller; it does not appear here. The PoW nonce is written directly into the
/// caller-supplied slab slot, so it is not retained here either.
pub(crate) struct PowAndQueryIndexesState {
    #[allow(dead_code)]
    pub(crate) d_raw_bits: Option<DeviceAllocation<u32>>,
    #[allow(dead_code)]
    pub(crate) d_indexes: DeviceAllocation<u32>,
}

/// Fused device-side PoW search + transcript `verify_pow` + query index
/// assembly that advances a caller-owned rolling `device_seed` in place.
///
/// 1. (if `pow_bits > 0`) run `ab_blake2s_pow_kernel` against `device_seed` to
///    search a nonce; write the nonce directly into the caller-supplied
///    `nonce_slab_dst` slot inside the proof slab.
/// 2. (if `pow_bits > 0`) `transcript_commit(device_seed, [nonce_lo, nonce_hi])`
///    advances the seed to match the post-`verify_pow` state. The nonce words
///    are read from the same slab slot.
/// 3. `transcript_squeeze(device_seed, d_raw_bits)` produces the padded random
///    u32 buffer.
/// 4. `assemble_query_indexes(d_raw_bits, d_indexes)` builds the query
///    indexes on device.
///
/// The prover's own PoW search kernel guarantees the POW validity invariant
/// that `verify_pow` formerly asserted, so the host-side sanity check is
/// intentionally elided on this path.
pub(crate) fn schedule_pow_verify_and_query_indexes(
    device_seed: &mut DeviceSlice<u32>,
    num_queries: usize,
    pow_bits: u32,
    query_domain_log2: usize,
    nonce_slab_dst: &mut DeviceVariable<u64>,
    context: &ProverContext,
) -> CudaResult<PowAndQueryIndexesState> {
    let stream = context.get_exec_stream();
    assert_eq!(device_seed.len(), STATE_SIZE);
    assert!(num_queries > 0);
    assert!(query_domain_log2 > 0 && query_domain_log2 <= 32);

    let mut d_indexes: DeviceAllocation<u32> =
        context.alloc(num_queries, AllocationPlacement::BestFit)?;

    // PoW search (GPU) → nonce, written directly into the slab slot. For
    // pow_bits == 0 we emulate `nonce = 0` and skip the transcript commit
    // (the host `verify_pow` is a no-op in that case too).
    if pow_bits > 0 {
        blake2s_pow(device_seed, pow_bits, u64::MAX, nonce_slab_dst, stream)?;
    } else {
        // SAFETY: `memory_set_async` is byte-granular; zeroing the 8-byte
        // `u64` slab slot through a `u8` view writes the canonical all-zero
        // `nonce = 0` bit pattern expected by the `pow_bits == 0` fast path.
        unsafe {
            era_cudart::memory::memory_set_async(nonce_slab_dst.transmute_mut::<u8>(), 0, stream)?;
        }
    }

    // verify_pow on device: hash device_seed || [nonce_lo, nonce_hi] → new seed.
    if pow_bits > 0 {
        // SAFETY: the slab slot is a single `u64` (8 bytes, align 8) viewable
        // as 2 little-endian `u32` words — the layout `transcript_commit`
        // consumes (and the host `verify_pow` convention it replaces). The
        // read is stream-ordered on the same `exec_stream` as the preceding
        // `blake2s_pow` write into this same slot.
        let nonce_as_u32: &DeviceSlice<u32> = unsafe { nonce_slab_dst.transmute::<u32>() };
        let nonce_words = &nonce_as_u32[..2];
        transcript_commit(device_seed, nonce_words, stream)?;
    }

    // Squeeze enough random u32 words to cover the first PoW header word plus
    // `num_queries * query_domain_log2` bits of query material, padded up to a
    // multiple of STATE_SIZE (the squeeze kernel's chunk granularity).
    let total_bits = 32usize + num_queries * query_domain_log2;
    let required_words = total_bits.div_ceil(32);
    let padded_words = (required_words + 1).next_multiple_of(STATE_SIZE);
    let mut d_raw_bits: DeviceAllocation<u32> =
        context.alloc(padded_words, AllocationPlacement::BestFit)?;
    transcript_squeeze(device_seed, &mut d_raw_bits, stream)?;

    // Assemble query indexes on device. The caller decides whether to D2H
    // them (current path) or route them directly into slab + gather kernels
    // (Phase 3/4).
    assemble_query_indexes(
        &d_raw_bits,
        &mut d_indexes,
        query_domain_log2 as u32,
        stream,
    )?;

    Ok(PowAndQueryIndexesState {
        d_raw_bits: Some(d_raw_bits),
        d_indexes,
    })
}
