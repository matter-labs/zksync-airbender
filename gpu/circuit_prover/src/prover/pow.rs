use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::{
    blake2s_pow, reduce_raw_words_to_e4, transcript_commit, transcript_squeeze, STATE_SIZE,
};
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::E4;
use crate::prover::ProverContext;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use gpu_gkr::gkr_ops::assemble_query_indexes;

/// Device buffers produced by [`schedule_pow_verify_and_query_indexes`]. The
/// rolling `device_seed` is owned by the WHIR scheduler and threaded in by the
/// caller; it does not appear here. The PoW nonce is written directly into the
/// caller-supplied slab slot, so it is not retained here either.
pub(crate) struct PowAndQueryIndexesState {
    #[allow(dead_code)]
    pub(crate) d_raw_bits: Option<DeviceAllocation<u32>>,
    pub(crate) d_indexes: DeviceAllocation<u32>,
}

/// Fused device-side PoW search + transcript `verify_pow` + query index
/// assembly that advances a caller-owned rolling `device_seed` in place.
///
/// 1. run `ab_blake2s_pow_kernel` against `device_seed` to search a nonce and
///    write it into the caller-supplied `nonce_slab_dst` slot inside the proof
///    slab (at `pow_bits == 0` the nonce is 0, matching the host `search_pow`).
/// 2. `transcript_commit(device_seed, [nonce_lo, nonce_hi])` advances the seed
///    to match the post-`verify_pow` state. Runs for EVERY bit count: the host
///    `verify_pow` hashes `seed || nonce` and updates the seed even at
///    `pow_bits == 0` (nonce 0), so this must not be skipped.
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
    query_domain_log2: u32,
    nonce_slab_dst: &mut DeviceVariable<u64>,
    context: &ProverContext,
) -> CudaResult<PowAndQueryIndexesState> {
    let stream = context.get_exec_stream();
    assert_eq!(device_seed.len(), STATE_SIZE);
    assert!(num_queries > 0);
    assert!(query_domain_log2 > 0 && query_domain_log2 <= 32);

    let mut d_indexes: DeviceAllocation<u32> =
        context.alloc(num_queries, AllocationPlacement::BestFit)?;

    // PoW search (GPU) → nonce, written directly into the slab slot. At
    // pow_bits == 0 the nonce is 0 (the host `search_pow` also returns 0), but
    // the seed is STILL advanced by the commit below.
    if pow_bits > 0 {
        blake2s_pow(device_seed, pow_bits, nonce_slab_dst, stream)?;
    } else {
        // SAFETY: `memory_set_async` is byte-granular; zeroing the 8-byte
        // `u64` slab slot through a `u8` view writes the canonical all-zero
        // `nonce = 0` bit pattern.
        unsafe {
            era_cudart::memory::memory_set_async(nonce_slab_dst.transmute_mut::<u8>(), 0, stream)?;
        }
    }

    // verify_pow on device: hash device_seed || [nonce_lo, nonce_hi] → new seed.
    // ALWAYS runs, including at pow_bits == 0: the host `verify_pow` (which
    // `search_pow` funnels through for every bit count) advances the seed even
    // for a 0-bit / nonce-0 draw, so skipping this would diverge from the CPU
    // transcript on the next challenge. Every `whir_pow_schedule` entry is
    // currently non-zero, so the 0-bit case is not exercised today, but the two
    // paths must agree (and it mirrors `schedule_draw_e4_challenges_with_pow`).
    // SAFETY: the slab slot is a single `u64` (8 bytes, align 8) viewable as 2
    // little-endian `u32` words — the layout `transcript_commit` consumes (the
    // host `verify_pow` nonce encoding). The read is stream-ordered on the same
    // `exec_stream` as the `blake2s_pow` / `memory_set_async` write above.
    let nonce_as_u32: &DeviceSlice<u32> = unsafe { nonce_slab_dst.transmute::<u32>() };
    let nonce_words = &nonce_as_u32[..2];
    transcript_commit(device_seed, nonce_words, stream)?;

    // Squeeze enough random u32 words to cover `num_queries * query_domain_log2`
    // bits of query material plus the first PoW header word that the index
    // assembly skips, padded up to a multiple of STATE_SIZE (the squeeze
    // kernel's chunk granularity). This must match the CPU transcript exactly
    // (`draw_query_bits`): `(ceil(query_bits / 32) + 1).next_multiple_of(8)`,
    // where the `+ 1` — NOT an extra 32 bits folded into `total_bits` — is the
    // skipped header word. Double-counting the header word (adding both `32 +`
    // and `+ 1`) over-squeezes by a digest block whenever `ceil(query_bits/32)
    // + 1` already lands on a multiple of 8, advancing the transcript past the
    // CPU and diverging every subsequent Fiat-Shamir challenge (e.g. the WHIR
    // delinearization challenge) for that round.
    let query_bits = num_queries * query_domain_log2 as usize;
    let required_words = query_bits.div_ceil(32);
    let padded_words = (required_words + 1).next_multiple_of(STATE_SIZE);
    let mut d_raw_bits: DeviceAllocation<u32> =
        context.alloc(padded_words, AllocationPlacement::BestFit)?;
    transcript_squeeze(device_seed, &mut d_raw_bits, stream)?;

    // Assemble query indexes on device; the caller D2Hs them.
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

/// Device-side `draw_random_field_els_with_pow::<BF, E4>(seed, count, pow_bits)` —
/// the PoW-gated E4 challenge draw used for the lookup challenges and the WHIR
/// batching challenge. Mirrors the query-index sibling above and the host
/// `draw_random_field_els_with_pow` (`prover::gkr::prover::transcript_utils`) exactly:
///
/// 1. (`pow_bits > 0`) `blake2s_pow` searches a nonce against `device_seed`, written
///    into `nonce_slab_dst`; otherwise the slot is set to the canonical `nonce = 0`.
/// 2. `transcript_commit(device_seed, [nonce_lo, nonce_hi])` advances the seed to the
///    post-`verify_pow` state — ALWAYS, including at `pow_bits == 0`: the host
///    `verify_pow` hashes `seed || nonce` and updates the seed for every bit count.
/// 3. `transcript_squeeze` draws `(count*4 + 1)` raw words padded to `STATE_SIZE`
///    (the `+1` is the PoW header word), advancing the seed; `reduce_raw_words_to_e4`
///    then skips that header word (`&raw[1..]`) and reduces the rest into the `count`
///    E4 challenges. This matches the host draw's `(count*DEGREE + 1)
///    .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)` sizing and skip-first-word.
///
/// The nonce is written into the caller-supplied proof-slab slot (0 at Sec80),
/// read back with the rest of the slab and assembled into `GKRProof` by `finish`.
pub(crate) fn schedule_draw_e4_challenges_with_pow(
    device_seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<E4>,
    pow_bits: u32,
    nonce_slab_dst: &mut DeviceVariable<u64>,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();
    assert_eq!(device_seed.len(), STATE_SIZE);
    let count = output.len();
    assert!(count > 0);

    // PoW search (GPU) → nonce into the slab slot. For pow_bits == 0 we emulate
    // nonce = 0 (the host `search_pow` also returns nonce 0 there).
    if pow_bits > 0 {
        blake2s_pow(device_seed, pow_bits, nonce_slab_dst, stream)?;
    } else {
        // SAFETY: `memory_set_async` is byte-granular; zeroing the 8-byte `u64`
        // slab slot through a `u8` view writes the canonical all-zero nonce = 0.
        unsafe {
            era_cudart::memory::memory_set_async(nonce_slab_dst.transmute_mut::<u8>(), 0, stream)?;
        }
    }

    // Advance the seed by committing the nonce words — ALWAYS, including at
    // pow_bits == 0. The host `verify_pow` (which `search_pow` funnels through
    // for every bit count) hashes `seed || nonce` and updates the seed even for
    // a 0-bit / nonce-0 draw, so skipping this at 0 bits would diverge from the
    // CPU transcript on the very next challenge.
    // SAFETY: the slab slot is a single `u64` (8 bytes, align 8) viewable as 2
    // little-endian `u32` words — the layout `transcript_commit` consumes (the
    // host `verify_pow` nonce encoding). The read is stream-ordered on the same
    // `exec_stream` as the `blake2s_pow` / `memory_set_async` write above.
    let nonce_as_u32: &DeviceSlice<u32> = unsafe { nonce_slab_dst.transmute::<u32>() };
    transcript_commit(device_seed, &nonce_as_u32[..2], stream)?;

    let e4_words = count * 4;
    let padded_words = (e4_words + 1).next_multiple_of(STATE_SIZE);
    let mut d_raw: DeviceAllocation<u32> =
        context.alloc(padded_words, AllocationPlacement::BestFit)?;
    transcript_squeeze(device_seed, &mut d_raw, stream)?;
    reduce_raw_words_to_e4(&d_raw[1..1 + e4_words], output, stream)?;

    Ok(())
}
