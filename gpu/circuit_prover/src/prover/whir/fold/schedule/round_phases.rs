use super::super::*;

use crate::ops::blake2s::{transcript_commit, transcript_squeeze_e4};
use crate::ops::powers::get_powers_by_ref;
use crate::ops::squaring::squaring_sequence_e4;

/// Commits the next WHIR extension oracle: builds it from `state.sumchecked_poly_monomial_form`,
/// gathering its unified device cap directly into the slab at `oracle_idx`, then advances
/// the rolling device transcript seed via `transcript_commit` reading the same slab range.
/// Production proof assembly sources `intermediate_whir_oracles[oracle_idx].commitment.cap`
/// from the slab via `parse_whir_proof`.
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_commit_next_oracle_phase(
    state: &GpuWhirState,
    oracle_idx: usize,
    lde_factor: usize,
    next_folding_steps: usize,
    tree_cap_size: usize,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    device_seed: &mut DeviceSlice<u32>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<GpuWhirExtensionOracle> {
    // SAFETY: `ProofLayout` returns a live, non-overlapping mutable region for
    // this intermediate cap inside the slab allocation.
    let (cap_ptr, cap_len_u32) = unsafe {
        proof_layout.whir_intermediate_cap_device_mut(proof_slab.as_ptr() as *mut u8, oracle_idx)
    };
    assert!(
        cap_len_u32 > 0,
        "intermediate cap slab range must be non-empty"
    );
    // SAFETY: `cap_ptr` is 4-byte-aligned (the slab `.cap` range is `u32`-typed
    // and aligned by `ProofLayout`) and points at a disjoint region inside the
    // pool-backed `proof_slab` allocation. The gather kernel scheduled by
    // `schedule_from_device_monomial_coeffs_into_slab` writes it exclusively
    // on `exec_stream`; the subsequent `transcript_commit` reborrows it as a
    // shared `*const u32` view, stream-ordered after the gather.
    let mut cap_dst_u32 =
        unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(cap_ptr, cap_len_u32) };
    let oracle = GpuWhirExtensionOracle::schedule_from_device_monomial_coeffs_into_slab(
        &state.sumchecked_poly_monomial_form,
        state.current_len,
        lde_factor,
        1 << next_folding_steps,
        tree_cap_size,
        &mut cap_dst_u32,
        context,
    )?;
    // Device transcript commit: hash the slab-resident cap (viewed as a flat
    // u32 stream) into `device_seed`. Reads from the same slab range the
    // gather kernel just wrote.
    // SAFETY: the slab cap range is read-only here, after the gather kernel
    // scheduled above on the same `exec_stream`.
    let cap_view = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts(cap_ptr as *const u32, cap_len_u32)
    };
    transcript_commit(device_seed, cap_view, stream)?;
    Ok(oracle)
}

/// Draws an OOD sample point on device, schedules the monomial-eval reduction
/// for the current state's folded polynomial, D2D-copies the resulting reduced
/// E4 into the slab's `whir.ood_samples[oracle_idx]`, then advances the rolling
/// transcript seed via `transcript_commit` of the slab slot. Pushes the
/// device-resident OOD point into `ood_point_devices` so the caller's
/// delinearization phase can read it without a host round-trip.
///
/// Range tracking is the caller's responsibility.
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_ood_sample_phase(
    state: &mut GpuWhirState,
    oracle_idx: usize,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    device_seed: &mut DeviceSlice<u32>,
    ood_point_devices: &mut Vec<DeviceAllocation<E4>>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<()> {
    let mut ood_point_device: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::BestFit)?;
    transcript_squeeze_e4(device_seed, &mut ood_point_device, stream)?;
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the OOD-sample array inside the slab allocation.
    let (dst_ptr, dst_len) =
        unsafe { proof_layout.whir_ood_samples_device_mut(proof_slab.as_ptr() as *mut u8) };
    assert!(
        oracle_idx < dst_len,
        "oracle_idx {oracle_idx} out of slab ood_samples range (len {dst_len})",
    );
    // SAFETY: `dst_ptr.add(oracle_idx)` is a 16-byte-aligned, live, disjoint
    // single-`E4` slot inside the pool-backed `proof_slab` allocation. The CUB
    // `reduce` write below and the subsequent transcript_commit read are both
    // stream-ordered on `exec_stream`, so they observe each other's updates
    // without an explicit barrier.
    let slab_slot: &mut era_cudart::slice::DeviceVariable<E4> =
        unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(dst_ptr.add(oracle_idx)) };
    schedule_monomial_eval_device_impl(state, &ood_point_device, slab_slot, context)?;
    // SAFETY: same slab slot, viewed as 4 LE u32 words for transcript_commit.
    let slot_as_u32 = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts(
            dst_ptr.add(oracle_idx) as *const u32,
            EXT4_DEGREE,
        )
    };
    transcript_commit(device_seed, slot_as_u32, stream)?;
    ood_point_devices.push(ood_point_device);
    Ok(())
}

/// Schedules the PoW verify + query-index draw for one WHIR round driven by the
/// rolling device transcript seed. The nonce is written directly into the
/// slab's `whir.pow_nonces[pow_round_idx]` slot by `blake2s_pow`, and the
/// transcript_commit that consumes the nonce as u32 words reads from that same
/// slab slot — no intermediate `d_nonce` allocation, no D2D copy.
///
/// Returns a per-round callbacks container (currently empty; retained for
/// future per-round callback wiring).
#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_pow_and_query_indexes_phase(
    device_seed: &mut DeviceSlice<u32>,
    num_queries: usize,
    pow_bits: u32,
    pow_round_idx: usize,
    query_domain_log2: usize,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    pow_round_state: &mut Vec<PowAndQueryIndexesState>,
    _stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<Callbacks<'static>> {
    let query_index_callbacks_for_round = Callbacks::new();

    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the PoW-nonce array inside the slab allocation.
    let (pow_nonces_ptr, pow_nonces_len) =
        unsafe { proof_layout.whir_pow_nonces_device_mut(proof_slab.as_ptr() as *mut u8) };
    assert!(
        pow_round_idx < pow_nonces_len,
        "pow_round_idx {pow_round_idx} out of slab pow_nonces range (len {pow_nonces_len})",
    );
    // SAFETY: `pow_nonces_ptr.add(pow_round_idx)` is an 8-byte-aligned, live,
    // disjoint single-`u64` slot inside the pool-backed `proof_slab`
    // allocation. The subsequent kernel write + transcript_commit read are
    // both stream-ordered on `exec_stream`, so they observe each other's
    // updates without an explicit barrier.
    let nonce_slab_dst: &mut era_cudart::slice::DeviceVariable<u64> = unsafe {
        era_cudart::slice::DeviceVariable::from_raw_parts_mut(pow_nonces_ptr.add(pow_round_idx))
    };

    let pow_round_state_entry = schedule_pow_verify_and_query_indexes(
        device_seed,
        num_queries,
        pow_bits,
        query_domain_log2,
        nonce_slab_dst,
        context,
    )?;
    pow_round_state.push(pow_round_state_entry);
    Ok(query_index_callbacks_for_round)
}

/// Schedules the running-powers buffer `[x, x^2, ..., x^(num_queries + 1)]`
/// fully on device and writes the OOD anchor squaring sequence
/// `[ood, ood^2, ood^4, ..., ood^(2^(log_n - 1))]` into the caller-provided
/// `anchor_out` slot.
///
/// The eq accumulation that consumes these is deferred to the caller so it
/// can fuse the OOD contribution (challenge = power index 0, claim_point =
/// anchor) with the batched per-query contributions (challenges = power
/// indices 1..N+1, claim_points = per_query_pows) into a single
/// `schedule_accumulate_eq_samples_batched` call. Used by base and
/// intermediate rounds; the final round has no delinearization step.
pub(super) fn schedule_delinearization_running_powers_phase(
    state: &mut GpuWhirState,
    num_queries: usize,
    ood_point_device: &DeviceSlice<E4>,
    anchor_out: &mut DeviceSlice<E4>,
    device_seed: &mut DeviceSlice<u32>,
    device_keepalives: &mut Vec<DeviceAllocation<E4>>,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E4>> {
    let stream = context.get_exec_stream();
    let log_n = state.current_len.trailing_zeros() as usize;
    assert_eq!(anchor_out.len(), log_n);
    // Draw the delinearization base challenge on device.
    let mut delin_base: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::BestFit)?;
    transcript_squeeze_e4(device_seed, &mut delin_base, stream)?;
    // Materialize [base^1, base^2, ..., base^(num_queries + 1)] on device.
    let count = num_queries + 1;
    let mut delinearization_device: DeviceAllocation<E4> =
        context.alloc(count, AllocationPlacement::BestFit)?;
    get_powers_by_ref(
        &delin_base[0],
        1,
        false,
        &mut delinearization_device[..],
        stream,
    )?;
    // Materialize the OOD anchor squaring sequence directly into the caller's
    // slot (slot 0 of the fused claim_points buffer).
    squaring_sequence_e4(&ood_point_device[0], anchor_out, stream)?;
    device_keepalives.push(delin_base);
    Ok(delinearization_device)
}
