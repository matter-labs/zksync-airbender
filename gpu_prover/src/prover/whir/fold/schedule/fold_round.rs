use super::super::*;

/// Schedules one fold-round group: `num_folding_steps` sumcheck/fold iterations
/// sharing a device-side seed, plus the slab D2D, the bulk D2H of packed
/// coefficients, and the rehydration callback that publishes them into
/// `proof.sumcheck_polys` and mirrors the device seed back into the host
/// transcript seed.
///
/// `scheduled_sumcheck_poly_idx` is read at entry to compute the group's slab
/// offset and advanced once per inner round so the next group starts at the
/// correct slab/proof index. Per-group device and host allocations are
/// `push`ed into `keepalives` so the caller can keep them alive on the
/// returned `GpuWhirFoldScheduledExecution`.
pub(super) fn schedule_fold_round(
    num_folding_steps: usize,
    state: &mut GpuWhirState,
    scheduled_sumcheck_poly_idx: &mut usize,
    keepalives: &mut FoldRoundGroupKeepalives,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    shared_state_handle: UnsafeMutAccessor<ScheduledWhirProofState>,
    seed_accessor: UnsafeMutAccessor<Seed>,
    stream: &era_cudart::stream::CudaStream,
    context: &ProverContext,
) -> CudaResult<()> {
    if num_folding_steps == 0 {
        return Ok(());
    }

    // Allocate persistent per-round-group device buffers: seed is
    // threaded round-to-round, challenge is overwritten each round
    // (stream-ordered, so safe to reuse), coeffs are packed into one
    // contiguous [3 * num_folding_steps] block for bulk readback.
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
    let mut d_challenge: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::BestFit)?;
    let mut d_coeffs_all: DeviceAllocation<E4> =
        context.alloc(3 * num_folding_steps, AllocationPlacement::BestFit)?;

    // Seed upload: stage the host seed into a pinned buffer via a
    // pre-kernel callback, then H2D copy into d_seed.
    let mut h_seed_staging = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
    let mut upload_callbacks = Callbacks::new();
    let staging_accessor = h_seed_staging.get_mut_accessor();
    upload_callbacks.schedule(
        move || unsafe {
            staging_accessor
                .get_mut()
                .copy_from_slice(&seed_accessor.get().0);
        },
        stream,
    )?;
    memory_copy_async(&mut d_seed, &h_seed_staging, stream)?;

    let group_start_idx = *scheduled_sumcheck_poly_idx;
    for round in 0..num_folding_steps {
        // Compute the 3 reductions into state.reduce_out (on device).
        schedule_special_three_point_eval_device_compute(state, context)?;

        // Fused kernel: reads reduce_out + d_seed, writes
        // d_coeffs[round*3..round*3+3], d_challenge, and the advanced
        // d_seed — all device-side, no host roundtrip.
        let coeff_range = (round * 3)..((round + 1) * 3);
        crate::ops::blake2s::whir_fold_round_update(
            &state.reduce_out[..3],
            &mut d_seed,
            &mut d_coeffs_all[coeff_range],
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
        whir_fold_split_half_in_place(
            &mut state.sumchecked_poly_evaluation_form[..current_len],
            &d_challenge[0],
            stream,
        )?;
        whir_fold_split_half_in_place(&mut state.eq_poly[..current_len], &d_challenge[0], stream)?;
        state.current_len = next_len;
        *scheduled_sumcheck_poly_idx += 1;
    }

    // Phase 3 slab routing: before the host-directed D2H, D2D-copy the
    // packed `d_coeffs_all` (the `[E4; 3]` sumcheck-round coefficients
    // for every round in this group) into the slab's
    // `whir.sumcheck_polys[group_start_idx * 3 .. (group_start_idx +
    // num_folding_steps) * 3]` region. The slab range is flat
    // `total_sumcheck_polys * 3` `E4` values in schedule order, which
    // matches `d_coeffs_all`'s packing exactly.
    if let Some(slab) = proof_slab {
        let (dst_base_ptr, dst_total_len) =
            unsafe { proof_layout.whir_sumcheck_polys_device_mut(slab.as_ptr() as *mut u8) };
        let dst_offset = group_start_idx * 3;
        let dst_len = num_folding_steps * 3;
        assert!(
            dst_offset + dst_len <= dst_total_len,
            "sumcheck_polys slab range overflow: {}+{} > {}",
            dst_offset,
            dst_len,
            dst_total_len,
        );
        // SAFETY: offset is 16-byte-aligned (slab base is, and
        // `E4` is 16 bytes so every element index is aligned);
        // the destination sub-range is disjoint from other slab
        // fields and from other fold-round groups.
        let dst = unsafe {
            era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                dst_base_ptr.add(dst_offset),
                dst_len,
            )
        };
        memory_copy_async(dst, &d_coeffs_all[..dst_len], stream)?;
    }

    // Bulk D2H: all coeffs for this group, plus the updated seed.
    // Schedule a final callback that rehydrates both into the shared
    // proof state and the host seed (which subsequent host-side
    // transcript ops — oracle commit, OOD, pow, queries — rely on).
    let mut h_coeffs_all = unsafe { context.alloc_host_uninit_slice::<E4>(3 * num_folding_steps) };
    memory_copy_async(&mut h_coeffs_all, &d_coeffs_all, stream)?;
    let mut h_seed_mirror = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
    memory_copy_async(&mut h_seed_mirror, &d_seed, stream)?;
    let h_coeffs_accessor = h_coeffs_all.get_accessor();
    let h_seed_mirror_accessor = h_seed_mirror.get_accessor();
    // Rehydration callback goes into the same per-group Callbacks
    // container as the upload callback; their stream-order is decided
    // by scheduling position, not by the Callbacks object they belong
    // to. Keeping it local avoids a mutable borrow conflict with the
    // outer `final_callbacks` (which the surrounding scope also
    // writes to).
    upload_callbacks.schedule(
        move || unsafe {
            let all = h_coeffs_accessor.get();
            let proof_state = shared_state_handle.get_mut();
            let proof = proof_state
                .proof
                .as_mut()
                .expect("proof must be initialized");
            for i in 0..num_folding_steps {
                let base = i * 3;
                proof.sumcheck_polys[group_start_idx + i] =
                    [all[base], all[base + 1], all[base + 2]];
            }
            // Mirror the device seed back into the host transcript
            // seed for subsequent host-side transcript operations.
            let new_seed = h_seed_mirror_accessor.get();
            seed_accessor.get_mut().0.copy_from_slice(new_seed);
        },
        stream,
    )?;

    keepalives.device_seeds.push(d_seed);
    keepalives.device_challenges.push(d_challenge);
    keepalives.device_coeffs.push(d_coeffs_all);
    keepalives.host_seed_stagings.push(h_seed_staging);
    keepalives.host_seed_mirrors.push(h_seed_mirror);
    keepalives.host_coeffs.push(h_coeffs_all);
    keepalives.upload_callbacks.push(upload_callbacks);
    Ok(())
}
