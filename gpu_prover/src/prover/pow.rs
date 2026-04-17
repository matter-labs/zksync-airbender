use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::{
    assemble_query_indexes, blake2s_pow, transcript_commit, transcript_squeeze, STATE_SIZE,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use prover::transcript::Seed;
use std::slice;

/// Device-side keepalives produced by
/// [`schedule_pow_verify_and_query_indexes`]. Must outlive the stream work the
/// caller queued afterwards (they're freed on drop).
pub(crate) struct PowAndQueryIndexesKeepalives {
    #[allow(dead_code)]
    pub(crate) d_seed: DeviceAllocation<u32>,
    #[allow(dead_code)]
    pub(crate) d_nonce: DeviceAllocation<u64>,
    #[allow(dead_code)]
    pub(crate) d_raw_bits: Option<DeviceAllocation<u32>>,
    #[allow(dead_code)]
    pub(crate) d_indexes: DeviceAllocation<u32>,
    pub(crate) h_seed_mirror: HostAllocation<[u32]>,
}

/// Fused device-side PoW search + transcript `verify_pow` + query index
/// assembly.
///
/// Replaces the host-side callback chain (`verify_pow` →
/// `draw_query_bits_after_verified_pow` → `assemble_query_index`) with a
/// straight-line device kernel sequence:
///   1. H2D the current host seed.
///   2. (if `pow_bits > 0`) run `ab_blake2s_pow_kernel` to search a nonce;
///      D2H the nonce into `nonce_host`.
///   3. (if `pow_bits > 0`) `transcript_commit(d_seed, [nonce_lo, nonce_hi])`
///      updates `d_seed` to match the post-`verify_pow` state.
///   4. `transcript_squeeze(d_seed, d_raw_bits)` produces the padded random
///      u32 buffer.
///   5. `assemble_query_indexes(d_raw_bits, d_indexes)` builds the query
///      indexes on device.
///   6. D2H `d_indexes` into `query_indexes_host` and `d_seed` into
///      `PowAndQueryIndexesKeepalives::h_seed_mirror`. No host callback is
///      scheduled — the caller is expected to schedule one fused callback
///      that reads the mirror and writes back `seed_host`, alongside any
///      other post-PoW host-side work (e.g. populating
///      `proof.pow_nonces[idx]`).
///
/// The prover's own PoW search kernel guarantees the POW validity invariant
/// that `verify_pow` formerly asserted, so the host-side sanity check is
/// intentionally elided on this path.
pub(crate) fn schedule_pow_verify_and_query_indexes(
    seed_host: &mut HostAllocation<Seed>,
    nonce_host: &mut HostAllocation<u64>,
    query_indexes_host: &mut HostAllocation<[u32]>,
    num_queries: usize,
    pow_bits: u32,
    query_domain_log2: usize,
    context: &ProverContext,
) -> CudaResult<PowAndQueryIndexesKeepalives> {
    let stream = context.get_exec_stream();
    assert!(num_queries > 0);
    assert!(query_domain_log2 > 0 && query_domain_log2 <= 32);

    let nonce_accessor = nonce_host.get_mut_accessor();
    let seed_accessor = seed_host.get_mut_accessor();

    // Allocate device buffers.
    let mut d_seed: DeviceAllocation<u32> = context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
    let mut d_nonce: DeviceAllocation<u64> = context.alloc(1, AllocationPlacement::BestFit)?;
    let mut d_indexes: DeviceAllocation<u32> =
        context.alloc(num_queries, AllocationPlacement::BestFit)?;

    // H2D the current host seed.
    memory_copy_async(&mut d_seed, unsafe { &seed_accessor.get().0 }, &stream)?;

    // PoW search (GPU) → nonce. For pow_bits == 0 we emulate `nonce = 0` and
    // skip the transcript commit (the host `verify_pow` is a no-op in that
    // case too).
    if pow_bits > 0 {
        blake2s_pow(&d_seed, pow_bits, u64::MAX, &mut d_nonce[0], stream)?;
    } else {
        unsafe {
            era_cudart::memory::memory_set_async(d_nonce.transmute_mut::<u8>(), 0, stream)?;
        }
    }

    // D2H nonce — needed on host for proof assembly and for the test fixture
    // that snapshots per-round nonces. Scheduled early so it overlaps with
    // the downstream kernels.
    memory_copy_async(
        slice::from_mut::<u64>(unsafe { nonce_accessor.get_mut() }),
        &d_nonce,
        &stream,
    )?;

    // verify_pow on device: hash seed || [nonce_lo, nonce_hi] → new seed.
    if pow_bits > 0 {
        // Treat the u64 nonce as 2 LE u32 words on device — transcript_commit
        // consumes a DeviceSlice<u32>.
        let nonce_as_u32: &DeviceSlice<u32> = unsafe { d_nonce.transmute::<u32>() };
        let nonce_words = &nonce_as_u32[..2];
        transcript_commit(&mut d_seed, nonce_words, stream)?;
    }

    // Squeeze enough random u32 words to cover the first PoW header word plus
    // `num_queries * query_domain_log2` bits of query material, padded up to a
    // multiple of STATE_SIZE (the squeeze kernel's chunk granularity).
    let total_bits = 32usize + num_queries * query_domain_log2;
    let required_words = total_bits.div_ceil(32);
    let padded_words = (required_words + 1).next_multiple_of(STATE_SIZE);
    let mut d_raw_bits: DeviceAllocation<u32> =
        context.alloc(padded_words, AllocationPlacement::BestFit)?;
    transcript_squeeze(&mut d_seed, &mut d_raw_bits, stream)?;

    // Assemble query indexes on device and D2H them.
    assemble_query_indexes(&d_raw_bits, &mut d_indexes, query_domain_log2 as u32, stream)?;
    memory_copy_async(query_indexes_host, &d_indexes, &stream)?;

    // Mirror the advanced seed back to host-pinned memory so subsequent
    // host-side draws (delinearization challenge, etc.) can see the
    // post-squeeze state. The caller is responsible for scheduling a single
    // fused callback that reads this mirror plus the nonce and performs all
    // post-PoW host bookkeeping in one stall.
    let _ = seed_accessor; // not used here, but retained as a compile-time
                           // reminder that the caller owns the copy-back.
    let _ = nonce_accessor;
    let mut h_seed_mirror = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
    memory_copy_async(&mut h_seed_mirror, &d_seed, &stream)?;

    Ok(PowAndQueryIndexesKeepalives {
        d_seed,
        d_nonce,
        d_raw_bits: Some(d_raw_bits),
        d_indexes,
        h_seed_mirror,
    })
}

