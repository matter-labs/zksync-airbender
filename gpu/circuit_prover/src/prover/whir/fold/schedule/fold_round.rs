use super::super::*;

/// Schedules one fold-round group: `num_folding_steps` sumcheck/fold iterations
/// driven by a rolling device-resident seed buffer threaded by the caller.
/// Each fold round advances `device_seed` via `whir_fold_round_update`, which
/// writes its `[E4; 3]` sumcheck-poly coefficients directly into the slab's
/// `whir.sumcheck_polys` region; no intermediate device buffer and no D2D is
/// needed, and no host-side transcript bookkeeping is required.
///
/// `scheduled_sumcheck_poly_idx` is read at entry to compute the group's slab
/// offset and advanced once per inner round so the next group starts at the
/// correct slab/proof index. The per-group device challenge allocation is
/// pushed into `keepalives` so the caller can keep it alive on the returned
/// `GpuWhirFoldScheduledExecution`.
pub(super) fn schedule_fold_round(
    num_folding_steps: usize,
    state: &mut GpuWhirState,
    scheduled_sumcheck_poly_idx: &mut usize,
    keepalives: &mut FoldRoundGroupKeepalives,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    device_seed: &mut DeviceSlice<u32>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<()> {
    if num_folding_steps == 0 {
        return Ok(());
    }

    // Resolve the slab destination for this group's `[E4; 3]` per-round
    // coefficients. The slab range is flat `total_sumcheck_polys * 3` `E4`
    // values in schedule order, so each round writes 3 consecutive E4s
    // starting at `(group_start_idx + round) * 3`.
    let group_start_idx = *scheduled_sumcheck_poly_idx;
    let (slab_sumcheck_base_ptr, slab_sumcheck_total_len) =
        unsafe { proof_layout.whir_sumcheck_polys_device_mut(proof_slab.as_ptr() as *mut u8) };
    assert!(
        group_start_idx * 3 + num_folding_steps * 3 <= slab_sumcheck_total_len,
        "sumcheck_polys slab range overflow: {}+{} > {}",
        group_start_idx * 3,
        num_folding_steps * 3,
        slab_sumcheck_total_len,
    );

    // Per-group device challenge buffer: overwritten each round
    // (stream-ordered, so safe to reuse).
    let mut d_challenge: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::BestFit)?;

    for round in 0..num_folding_steps {
        // Compute the 3 reductions into state.reduce_out (on device).
        schedule_special_three_point_eval_device_compute(state, context)?;

        // SAFETY: `slab_sumcheck_base_ptr` points into the live proof slab;
        // the offset is 16-byte-aligned (slab base is, and `E4` is 16 bytes
        // so every element index is aligned); the 3-element destination
        // sub-range is disjoint from other slab fields and from other
        // fold-round groups, and within this group rounds are issued in
        // schedule order on a single stream, so the writes are
        // non-overlapping and stream-ordered.
        let round_offset = (group_start_idx + round) * 3;
        let slab_round_dst = unsafe {
            era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                slab_sumcheck_base_ptr.add(round_offset),
                3,
            )
        };

        // Fused kernel: reads reduce_out + device_seed, writes the round's
        // 3 coefficients straight into the slab, plus d_challenge and the
        // advanced device_seed — all device-side, no host roundtrip.
        crate::ops::gkr_ops::whir_fold_round_update(
            &state.reduce_out[..3],
            device_seed,
            slab_round_dst,
            &mut d_challenge,
            stream,
        )?;

        let current_len = state.current_len;
        let next_len = current_len / 2;
        whir_fold_split_half_in_place_vectorized(
            &mut state.sumchecked_poly_monomial_form,
            &d_challenge[0],
            next_len,
            stream,
        )?;
        whir_fold_split_half_in_place_pair(
            &mut state.sumchecked_poly_evaluation_form[..current_len],
            &mut state.eq_poly[..current_len],
            &d_challenge[0],
            stream,
        )?;
        state.current_len = next_len;
        *scheduled_sumcheck_poly_idx += 1;
    }

    keepalives.device_challenges.push(d_challenge);
    Ok(())
}
