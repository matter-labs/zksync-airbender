use std::collections::BTreeMap;
use std::ptr::{null, null_mut};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};

use super::kernels::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::cub::device_reduce::Reduce;
use crate::ops::simple::{BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::proof_layout::ProofLayout;
use crate::prover::ProverContext;
use crate::upstream::{Field, FieldExtension, GKRAddress, Seed};

impl<B: 'static, E: 'static> GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    E: Field + FieldExtension<BF> + Reduce + crate::prover::gkr::BackwardKernels,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn batch_challenge_base_ptr(&self) -> *const E {
        if let Some(ptr) = self.batch_challenge_base_override_ptr {
            return ptr;
        }
        // SAFETY: `round_scratch.claim_point` always has `folding_steps + 1`
        // entries in the host-driven path, so the batching-challenge slot at
        // `folding_steps` exists.
        unsafe {
            // SAFETY: the host-driven claim-point scratch buffer is only
            // re-viewed to read its concrete `E` batching-challenge slot.
            self.round_scratch
                .claim_point
                .as_ptr()
                .add(self.folding_steps)
        }
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round0_batch_template_compact;
        batch.eq_low = self.round_scratch.eq_low_group.as_ptr();
        batch.eq_sizes = self.eq_sizes;
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        launch_dim_reducing_round0_batched_compact(&batch, acc_size, context)
    }

    fn launch_round1_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round1_batch_template_compact;
        batch.eq_low = self.round_scratch.eq_low_group.as_ptr();
        batch.eq_sizes = self.eq_sizes;
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round1_batched_compact(&batch, null(), acc_size, context)
    }

    fn launch_continuation_kernels_from_symbol(
        &mut self,
        step: usize,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.continuation_batch_template_compact;
        batch.eq_low = self.round_scratch.eq_low_group.as_ptr();
        batch.eq_sizes = self.eq_sizes;
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.explicit_form = explicit_form;
        launch_dim_reducing_continuation_batched_compact(&batch, null(), acc_size, step, context)
    }

    /// Fused-tail dispatcher: after the round kernel wrote
    /// `acc[0..2*acc_size)`, this replaces the unfused 5-launch sequence
    /// (2× CUB reduce + fold_eq + round_update) with either a single
    /// combined launch (when acc_size <= BLOCK_THREADS) or a two-stage
    /// block-reduce + mega-finalize pair. The active eq slot is folded
    /// inside the same kernel as the round update.
    ///
    /// E is generic but E4-only in this build; pointer casts below are safe
    /// (both `Field` and `E4` are `#[repr(C)]` with identical layouts).
    /// `fold_eq == false` is the #320 final round: the round still reduces its
    /// univariate monomial, commits it, and draws the folding challenge, but it
    /// must NOT fold the factored eq for a next round (there is none — the
    /// factored eq is already fully consumed by the preceding `folding_steps-1`
    /// rounds and is the identity at `acc_size == 1`). Passing
    /// `active_eq_size_before_fold = 0` makes `mega_finalize_block` skip the
    /// fold branch, and we skip `record_active_eq_slot_fold` to avoid a `u32`
    /// underflow of the already-zero eq sizes.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_fused_tail(
        &mut self,
        acc_size: usize,
        prev_claim_coord: *const E,
        seed: *mut u32,
        claim: *mut E,
        eq_prefactor: *mut E,
        coeffs_out: *mut E,
        challenge_out: *mut E,
        fold_eq: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let prev_e4 = prev_claim_coord as *const E4;
        let claim_e4 = claim as *mut E4;
        let eq_pref_e4 = eq_prefactor as *mut E4;
        let coeffs_e4 = coeffs_out as *mut E4;
        let chal_e4 = challenge_out as *mut E4;
        let acc_ptr = self.round_scratch.accumulator.as_ptr() as *const E4;
        let eq_low_ptr = self.round_scratch.eq_low_group.as_mut_ptr() as *mut E4;
        let partials_ptr = self.round_scratch.partials.as_mut_ptr() as *mut E4;

        let (slot_base, slot_size_before_fold) = if fold_eq {
            super::kernels::resolve_active_eq_slot(&self.eq_sizes, eq_low_ptr)
        } else {
            // Final round: identity eq, no fold. `slot_base` is a valid pointer
            // but `mega_finalize_block` never dereferences it when size == 0.
            (eq_low_ptr, 0u32)
        };

        let num_blocks = super::kernels::dual_reduce_num_stage1_blocks(acc_size);
        if num_blocks == 0 {
            super::kernels::launch_backward_dual_finalize_from_acc(
                acc_ptr,
                acc_size,
                prev_e4,
                seed,
                claim_e4,
                eq_pref_e4,
                coeffs_e4,
                chal_e4,
                slot_base,
                slot_size_before_fold,
                context,
            )?;
        } else {
            super::kernels::launch_backward_dual_reduce_blockwise(
                acc_ptr,
                acc_size,
                partials_ptr,
                context,
            )?;
            super::kernels::launch_backward_dual_finalize_from_partials(
                partials_ptr as *const E4,
                num_blocks,
                prev_e4,
                seed,
                claim_e4,
                eq_pref_e4,
                coeffs_e4,
                chal_e4,
                slot_base,
                slot_size_before_fold,
                context,
            )?;
        }

        if fold_eq {
            super::kernels::record_active_eq_slot_fold(&mut self.eq_sizes);
        }
        Ok(())
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let sources = match last_step {
                1 => &kernel.round1_prepared.extension_field_inputs,
                2 => {
                    &kernel
                        .round2_prepared
                        .as_ref()
                        .expect("round 2 storage must be prepared")
                        .extension_field_inputs
                }
                step => {
                    &kernel
                        .round3_and_beyond_prepared
                        .iter()
                        .find(|prepared| prepared.step == step)
                        .unwrap_or_else(|| {
                            panic!("missing prepared round 3+ storage for step {step}")
                        })
                        .prepared
                        .extension_field_inputs
                }
            };
            for (address, source) in kernel.inputs.inputs_in_extension.iter().zip(sources.iter()) {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching<E>,
        device_claims_in: DeviceAllocation<E>,
        claim_layout: &ClaimBufferLayout,
        // Per-round kernels write coeffs directly into the slab's
        // `internal_round_coefficients` range for `layer_slot` and the
        // per-address gather writes directly into `final_step_evaluations`
        // (B1 + B2).
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        mirror_layer_to_host: bool,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        const DIMENSION_REDUCING_LAYER_RANGE_MIN_FOLDING_STEPS: usize = 19;

        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let last_step = self.folding_steps - 1;
        let mut layer_range = if self.folding_steps
            >= DIMENSION_REDUCING_LAYER_RANGE_MIN_FOLDING_STEPS
        {
            let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
            let range = Range::new(layer_name)?;
            range.start(stream)?;
            Some(range)
        } else {
            None
        };
        // Compute the per-layer combined_claim `(exp, claim_idx)` descriptor
        // consumed by `build_combined_claim`. Passed inline as kernel-arg
        // (`__grid_constant__`) — no device buffer, no per-layer H2D. The
        // audit-locked ceiling `GKR_COMBINED_CLAIM_MAX_PAIRS` is enforced
        // inside `build_combined_claim`.
        let mut desc_pairs: Vec<u32> = Vec::with_capacity(
            self.kernel_plans
                .iter()
                .map(|kernel| kernel.inputs.outputs_in_extension.len() * 2)
                .sum(),
        );
        for kernel in self.kernel_plans.iter() {
            for (j, output) in kernel.inputs.outputs_in_extension.iter().enumerate() {
                desc_pairs.push((kernel.batch_challenge_offset + j) as u32);
                desc_pairs.push(claim_layout.claim_idx(output));
            }
        }
        let mut shared_state = Box::new(ScheduledDimensionReducingLayerExecutionState {
            seed: Seed::default(),
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        // `device_seed` is owned by the orchestrator across all backward
        // layers (initialized from the post-forward device seed produced in
        // proof.rs). The fused per-round kernel and the end-of-layer device
        // transcript work mutate it in place; the scheduler returns it via
        // `Execution::device_seed` so the next layer can thread it in.
        let mut device_claim: DeviceAllocation<E> = context.alloc(1, AllocationPlacement::Top)?;
        let mut device_eq_prefactor: DeviceAllocation<E> =
            context.alloc(1, AllocationPlacement::Top)?;
        // #320: every round — including the last (acc_size == 1) — now emits a
        // univariate monomial, so `internal_round_coefficients` has
        // `folding_steps` entries (was `folding_steps - 1`). Must match the
        // `ProofLayout` allocation (`sumcheck_num_rounds * 4`).
        let coeffs_total_len = self.folding_steps * 4;
        // B1: per-round kernels write coeffs straight into the slab range for
        // this layer — no standalone allocation and no post-loop slab D2D. The
        // kernels are stream-ordered against the terminal D2H of the slab in
        // `prove()`, so the slab is self-consistent on `exec_stream`.
        let coeffs_buffer_ptr: *mut E = if coeffs_total_len > 0 {
            // SAFETY: `layer_slot` selects this layer's slab segment and the
            // returned region is validated against `coeffs_total_len` below.
            let (dst_ptr, dst_len) = unsafe {
                proof_layout
                    .backward_internal_coeffs_device_mut(proof_slab.as_ptr() as *mut u8, layer_slot)
            };
            debug_assert_eq!(
                dst_len, coeffs_total_len,
                "slab internal_round_coefficients range must match layer's coeffs_total_len",
            );
            dst_ptr as *mut E
        } else {
            null_mut()
        };

        // The `[claim_point || batching_challenge]` input is consumed
        // directly from `device_claim_point_in` — no D2D into a per-layer
        // `round_scratch.claim_point` buffer. Per-round kernels read it for
        // `prev_coord_slice`; `launch_build_eq_high_and_low_groups_from_point`
        // reads the suffix `[1..folding_steps]`. The launch_round*_kernels path reads
        // the batching challenge slot via `batch_challenge_base_ptr()`, so
        // point that at `device_claim_point_in[folding_steps]` for the
        // duration of this layer's scheduling.
        let claim_point_and_batching_len = self.folding_steps + 1;
        assert_eq!(
            device_claim_point_in.len(),
            claim_point_and_batching_len,
            "device claim_point input size must match this layer's folding_steps + 1",
        );
        // SAFETY: the validated `device_claim_point_in` length is
        // `folding_steps + 1`, so the final batching-challenge slot exists.
        self.batch_challenge_base_override_ptr =
            Some(unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) });
        schedule_dim_reducing_batch_challenge_table_prelude(
            self.batch_challenge_base_ptr() as *const E4,
            context,
        )?;
        // Build the factored eq representation (high slabs in the
        // `ab_gkr_eq_high` __constant__ symbol + `eq_low_group` buffer in
        // global memory) directly from the device claim_point (using coords
        // `[1..folding_steps]` — the suffix that `fill_round0_eq_pair_values`
        // used to expand on host). Dim-reducing consumer kernels compute eq
        // per-row inline from `(eq_low, eq_sizes)` via the inline-eq helper
        // (high slabs read from the __constant__ symbol).
        let challenge_count = self.folding_steps.saturating_sub(1);
        launch_build_eq_high_and_low_groups_from_point::<E>(
            device_claim_point_in.as_ptr(),
            1,
            challenge_count,
            get_eq_high_constant_device_ptr() as *mut E,
            self.round_scratch.eq_low_group.as_mut_ptr(),
            context,
        )?;
        // Host-side bookkeeping for the per-round factored-eq sizes. Mutated
        // in place by `fold_eq_values_for_next_round` between sumcheck rounds.
        self.eq_sizes = make_eq_sizes(challenge_count);

        assert_eq!(
            device_claims_in.len(),
            claim_layout.len(),
            "device claims buffer must match claim layout length",
        );

        {
            // SAFETY: every instantiation uses `E = E4`, so these are
            // byte-for-byte views of live device buffers with matching layout.
            let claims_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claims_in[..claim_layout.len()].transmute::<E4>() };
            // SAFETY: the last slot of `device_claim_point_in` is the batching
            // challenge and exists because its length is `folding_steps + 1`.
            let batching_slice = unsafe { device_claim_point_in.slice(self.folding_steps, 1) };
            // SAFETY: same concrete-layout reinterpret as the claims buffer.
            let batching_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { batching_slice.transmute::<E4>() };
            // SAFETY: the one-element outputs are allocated as `E` and viewed
            // at the concrete `E4` layout used by the helper kernel.
            let claim_out_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claim[..].transmute_mut::<E4>() };
            let eq_out_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_eq_prefactor[..].transmute_mut::<E4>() };
            crate::ops::gkr_ops::build_combined_claim(
                claims_e4,
                batching_e4,
                &desc_pairs,
                claim_out_e4,
                eq_out_e4,
                stream,
            )?;
        }

        // Hoisted: `device_claim_point_out` holds the next layer's
        // `[claim_point || batching_challenge]` buffer. Slots `[0..folding_steps - 1]`
        // are written in-place by the per-round update kernels (replacing
        // the old `round_challenge_storage` + post-loop D2D pack), and
        // slots `[folding_steps - 1..folding_steps + 2]` are written by the
        // post-loop transcript squeeze (replacing the old `d_layer_challenges`
        // allocation + post-loop D2D pack).
        let next_claim_point_and_batching_len = self.folding_steps + 2;
        assert!(
            next_claim_point_and_batching_len <= MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN,
            "dim-reducing layer claim point length {} exceeds __constant__ symbol capacity {}",
            next_claim_point_and_batching_len,
            MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN
        );
        // SAFETY: the constant-buffer symbol is provisioned for
        // `MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN`; the checked length above
        // keeps the mutable view in bounds.
        let mut device_claim_point_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                get_dim_reducing_layer_claim_point_device_ptr() as *mut E,
                next_claim_point_and_batching_len,
            )
        };

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            // Variant-agnostic round-kernel head (V_combined will replace
            // this with a cooperative-launch single kernel in Task 9).
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels_from_symbol(acc_size, false, context)?,
                    step => self
                        .launch_continuation_kernels_from_symbol(step, acc_size, false, context)?,
                }
            }

            // SAFETY: `step < last_step <= folding_steps`, so the one-element
            // slice lies within the immutable input claim-point buffer.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(step, 1) };
            // SAFETY: `coeffs_buffer_ptr` points either into `proof_slab`
            // (held alive by `_proof_slab` keepalive in `prove()`) or into
            // `fallback_device_coeffs` (dropped at end of this function,
            // after every kernel that writes through this pointer is
            // scheduled). The 4-element window is in-bounds for both
            // (`coeffs_total_len = last_step * 4`).
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            // SAFETY: `device_claim_point_out` is length `folding_steps + 2`,
            // and `step < last_step <= folding_steps - 1`, so this output slot
            // is in bounds and uniquely written by this iteration.
            let challenge_slice = unsafe { device_claim_point_out.slice_mut(step, 1) };

            // Unfused round-kernel head + fused tail (reduce + round-update +
            // fold-eq in one kernel; -0.9 ms vs the unfused 5-launch tail on this
            // fixture). These `folding_steps - 1` rounds each fold the factored
            // eq for the next round (`fold_eq = true`).
            self.dispatch_fused_tail(
                acc_size,
                prev_coord_slice.as_ptr(),
                device_seed.as_mut_ptr(),
                device_claim.as_mut_ptr(),
                device_eq_prefactor.as_mut_ptr(),
                coeffs_round_slice.as_mut_ptr(),
                challenge_slice.as_mut_ptr(),
                true,
                context,
            )?;
        }

        // #320 final round (step == last_step == folding_steps - 1, acc_size == 1).
        // The factored eq is now fully consumed (identity), so the round kernel
        // runs in monomial form (`explicit_form = false`) — exactly the CPU
        // `evaluate::<_, false>` last round — and the fused tail emits the
        // `last_step`-th monomial into the coeff slab and draws `r_before_last`
        // into `device_claim_point_out[last_step]`, WITHOUT folding eq again.
        // The `[E;4]` last-round line is still read from the round storage by
        // `final_evaluation_sources_for_last_step(last_step)` below (the
        // explicit-form flag never affected that storage fold).
        match last_step {
            1 => self.launch_round1_kernels_from_symbol(1, false, context)?,
            step => self.launch_continuation_kernels_from_symbol(step, 1, false, context)?,
        }
        {
            // SAFETY: `last_step == folding_steps - 1 < folding_steps + 1`, so
            // this input claim-point coordinate (`z_{last_step}`) exists.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(last_step, 1) };
            // SAFETY: `coeffs_total_len = folding_steps * 4`, so the
            // `last_step`-th 4-element window is in-bounds.
            let coeffs_round_slice = unsafe {
                DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(last_step * 4), 4)
            };
            // SAFETY: `device_claim_point_out` is length `folding_steps + 2`;
            // slot `last_step = folding_steps - 1` (= `r_before_last`) is in
            // bounds and uniquely written here.
            let challenge_slice = unsafe { device_claim_point_out.slice_mut(last_step, 1) };
            self.dispatch_fused_tail(
                1,
                prev_coord_slice.as_ptr(),
                device_seed.as_mut_ptr(),
                device_claim.as_mut_ptr(),
                device_eq_prefactor.as_mut_ptr(),
                coeffs_round_slice.as_mut_ptr(),
                challenge_slice.as_mut_ptr(),
                false,
                context,
            )?;
        }

        // B1: coeffs already landed in the slab via the per-round kernels
        // (or in `fallback_device_coeffs` for test paths). No post-loop
        // slab D2D needed.

        // Device-side inter-layer transcript (#320). The `[E;4]` last-round
        // bilinear line is gathered from the round storage into a TEMP device
        // buffer, then reduced over the last-output coordinate at
        // `r_before_last` (drawn in-loop at `claim_point_out[last_step]`) into
        // the `[E;2]` LSB line that is sent in the proof and committed to the
        // transcript. We then squeeze the 2 remaining challenges
        // `[r_last, next_batching_challenge]`. The TEMP `[E;4]` buffer still
        // feeds `backward_new_claims_two_var` (whose value equals the CPU
        // `interp(interp(v0,v2,rbl), interp(v1,v3,rbl), r_last)`).
        let transcript_input_sources = self.final_evaluation_sources_for_last_step(last_step);
        let num_addresses = transcript_input_sources.len();
        let last_evals_len = num_addresses * 4;
        let final_step_evals_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();

        // TEMP `[E;4]` gather target. The slab now holds the reduced `[E;2]`
        // LSB lines (degree 2), so the raw 4-evals can no longer live there.
        let mut device_last_evals: DeviceAllocation<E> =
            context.alloc(last_evals_len.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            let src_ptrs: Vec<u64> = transcript_input_sources
                .values()
                .map(|p| *p as u64)
                .collect();
            // SAFETY: `device_last_evals` holds `last_evals_len` ext elements;
            // the E4 view matches the only instantiated extension layout.
            let dst = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    device_last_evals.as_mut_ptr() as *mut E4,
                    last_evals_len,
                )
            };
            crate::ops::blake2s::gather_e_addresses(&src_ptrs, dst, 4, stream)?;
        }

        // Slab destination for the `[E;2]` LSB lines = `final_step_evaluations`
        // (degree 2; BTreeMap key order matches `final_step_eval_addresses`
        // stored by `build_proof_layout_inputs`).
        let final_step_evals_buffer_ptr: *mut E = if final_step_evals_len > 0 {
            // SAFETY: `layer_slot` selects this layer's slab segment; the region
            // is validated against `final_step_evals_len` immediately below.
            let (dst_ptr, dst_len) = unsafe {
                proof_layout.backward_final_step_evals_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    layer_slot,
                )
            };
            debug_assert_eq!(
                dst_len, final_step_evals_len,
                "slab final_step_evaluations range must match num_addresses * 2",
            );
            dst_ptr as *mut E
        } else {
            null_mut()
        };

        // #320: reduce the `[E;4]` line over the last-output coordinate at
        // `r_before_last` into the `[E;2]` LSB line, written into the slab.
        if num_addresses > 0 {
            // SAFETY: TEMP `[E;4]` buffer, E = E4 layout, alive through launch.
            let last_evals_e4 = unsafe {
                DeviceSlice::from_raw_parts(
                    device_last_evals.as_ptr() as *const E4,
                    last_evals_len,
                )
            };
            // SAFETY: `claim_point_out[last_step]` is `r_before_last`, drawn by
            // the in-loop final round; reading one E4 challenge.
            let rbl_view = unsafe {
                DeviceSlice::from_raw_parts(
                    device_claim_point_out.as_ptr().add(last_step) as *const E4,
                    1,
                )
            };
            // SAFETY: slab final-step region, E = E4 layout, `2 * num_addresses`.
            let lsb_out = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    final_step_evals_buffer_ptr as *mut E4,
                    final_step_evals_len,
                )
            };
            crate::ops::gkr_ops::backward_dim_reducing_lsb_lines(
                last_evals_e4,
                rbl_view,
                lsb_out,
                stream,
            )?;
        }

        // Commit the `[E;2]` LSB lines (matches host `commit_field_els::<BF, E4>`
        // over the final-step evaluations).
        // SAFETY: slab final-step region is alive through the launch; E = E4 so
        // the u32 view matches the host byte layout. Empty when 0 addresses.
        let final_step_evals_e_slice = unsafe {
            DeviceSlice::from_raw_parts(
                final_step_evals_buffer_ptr as *const E,
                final_step_evals_len,
            )
        };
        let d_final_step_evals_u32 = unsafe { final_step_evals_e_slice.transmute::<u32>() };
        crate::ops::blake2s::transcript_commit(&mut device_seed, d_final_step_evals_u32, stream)?;

        // Squeeze the 2 remaining layer challenges
        // `[r_last, next_batching_challenge]` into
        // `claim_point_out[folding_steps..folding_steps + 2]`. `r_before_last`
        // was drawn in-loop at `claim_point_out[folding_steps - 1]`.
        // SAFETY: `folding_steps + 2 = next_claim_point_and_batching_len`, so the
        // range is in-bounds, and only this scheduling site writes it.
        {
            let layer_challenges_dst =
                unsafe { device_claim_point_out.slice_mut(self.folding_steps, 2) };
            // SAFETY: E = E4; the transmute is a byte-level no-op matching host
            // `draw_random_field_els::<BF, E4>`.
            let layer_challenges_dst_e4 = unsafe { layer_challenges_dst.transmute_mut::<E4>() };
            crate::ops::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst_e4,
                stream,
            )?;
        }

        // Device-side per-address `new_claims` evaluator. Consumes the TEMP
        // `[E;4]` last-round line and `[r_before_last, r_last]` to produce N E
        // per-address next-layer claims. `r_before_last` is at
        // `claim_point_out[last_step]` (in-loop) and `r_last` at
        // `claim_point_out[last_step + 1] = claim_point_out[folding_steps]`
        // (squeeze) — contiguous, so the 2-element read is unchanged.
        let mut device_new_claims: DeviceAllocation<E> =
            context.alloc(num_addresses.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: E = E4 in every instantiation; the transmutes match the
            // kernel's `e4` view of both the packed evals and the challenges.
            // The TEMP eval buffer is alive through the kernel launch.
            let transcript_inputs_e_view = unsafe {
                DeviceSlice::from_raw_parts(device_last_evals.as_ptr() as *const E, last_evals_len)
            };
            // SAFETY: the packed eval buffer is laid out as `E4` elements in
            // this scheduler instantiation.
            let transcript_inputs_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { transcript_inputs_e_view.transmute::<E4>() };
            // SAFETY: layer-challenge slots `[last_step..last_step + 2]` hold
            // `[r_before_last, r_last]` (in-loop draw + post-loop squeeze).
            let challenges_view = unsafe {
                DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr().add(last_step), 2)
            };
            // SAFETY: the just-squeezed challenge tail is stored in the same
            // concrete `E4` layout that the kernel helper expects.
            let challenges_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { challenges_view.transmute::<E4>() };
            // SAFETY: `device_new_claims` was allocated as `E` and is viewed at
            // the concrete `E4` layout used by the kernel helper.
            let new_claims_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_new_claims[..num_addresses].transmute_mut::<E4>() };
            crate::ops::gkr_ops::backward_new_claims_two_var(
                transcript_inputs_e4,
                challenges_e4,
                new_claims_e4,
                stream,
            )?;
        }

        // `device_claim_point_out` is already populated in place — slots
        // `[0..last_step]` by the per-round update kernels and slots
        // `[last_step..last_step + 3]` by the transcript squeeze. No post-loop
        // pack copies needed.

        let next_claim_layout =
            ClaimBufferLayout::from_addresses(transcript_input_addresses.clone());
        let callback_addresses = next_claim_layout.addresses.clone();
        let mut final_readback_callbacks = Callbacks::new();
        if mirror_layer_to_host {
            // Fork exec -> d2h: every D2H source below has been written on exec by this point
            // (d_layer_challenges via `transcript_squeeze_e4`, device_new_claims via
            // `backward_new_claims_two_var`, device_seed/round_challenge_storage from earlier
            // work in this layer; coeffs and packed last-evals are now slab-direct via B1/B2
            // and not D2H'd here). The join lets exec wait for the per-layer D2Hs before
            // scheduling the final-readback callback and dropping the source allocations.
            // #320: `r_before_last` is now drawn in-loop and lives among the
            // folding challenges `claim_point_out[0..folding_steps]`; only
            // `[r_last, next_batching_challenge]` are squeezed post-loop.
            let folding_steps = self.folding_steps;
            // SAFETY: these pinned host buffers are used only as D2H
            // destinations before the callback reads them.
            let mut layer_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(2) };
            let layer_challenges_accessor = layer_challenges_host.get_accessor();
            let mut new_claims_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(num_addresses.max(1)) };
            let new_claims_accessor = new_claims_host.get_accessor();
            // SAFETY: this pinned host buffer is also a pure D2H destination
            // before the final callback consumes it.
            let mut final_seed_host = unsafe { context.alloc_host_uninit_slice(STATE_SIZE) };
            let final_seed_accessor = final_seed_host.get_accessor();
            let mut final_folding_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(folding_steps.max(1)) };
            let final_folding_challenges_accessor = final_folding_challenges_host.get_accessor();
            crate::prover::transfer::fork_join_exec_to_d2h(
                stream,
                context.get_d2h_stream(),
                |d2h_stream| {
                    // SAFETY: `[folding_steps..folding_steps + 2] = [r_last,
                    // next_batching_challenge]` was just written by the transcript
                    // squeeze on `stream`; d2h_stream waits on the fork event
                    // before this read.
                    let layer_challenges_src = unsafe {
                        DeviceSlice::from_raw_parts(
                            device_claim_point_out.as_ptr().add(folding_steps),
                            2,
                        )
                    };
                    memory_copy_async(
                        &mut layer_challenges_host,
                        layer_challenges_src,
                        d2h_stream,
                    )?;

                    // Single D2H of device-computed new_claims. Replaces N per-address
                    // D2Hs (one per address × 4 E) + the host
                    // `evaluate_with_two_variable_eq_ext` loop.
                    if num_addresses > 0 {
                        memory_copy_async(
                            &mut new_claims_host,
                            &device_new_claims[..num_addresses],
                            d2h_stream,
                        )?;
                    }

                    // Bulk D2H the on-device per-layer state that the final readback
                    // callback needs to advance the workflow (seed + folding challenges
                    // for WHIR host setup; coeffs and packed last-evaluations stay on
                    // device and flow through the proof slab via B1/B2).
                    memory_copy_async(&mut final_seed_host, &device_seed, d2h_stream)?;
                    if folding_steps > 0 {
                        // SAFETY: `[0..folding_steps]` are written in-place by the
                        // per-round update kernels — slots `[0..folding_steps - 1]`
                        // by the loop rounds and `[folding_steps - 1]` (=
                        // `r_before_last`) by the in-loop final round.
                        let folding_src = unsafe {
                            DeviceSlice::from_raw_parts(
                                device_claim_point_out.as_ptr(),
                                folding_steps,
                            )
                        };
                        memory_copy_async(
                            &mut final_folding_challenges_host,
                            folding_src,
                            d2h_stream,
                        )?;
                    }
                    Ok(())
                },
            )?;

            let shared_state_for_callback = shared_state_handle;
            let workflow_state_for_callback = workflow_state;
            let layer_idx = self.layer_idx;
            final_readback_callbacks.schedule(
                // SAFETY: every accessor captured here points to host buffers
                // filled earlier on the same stream, and the callback runs only
                // after the fork/join D2H sequence has completed.
                move || unsafe {
                    // Populate the rolling state from the D2H'd device state. The
                    // seed captured here is already post-commit+squeeze (advanced
                    // on-device), so no host `commit_field_els`/`draw_random_field_els`
                    // is needed — the 2 post-loop challenges live in
                    // `layer_challenges_host` and `r_before_last` is already among
                    // the folding challenges.
                    let state = shared_state_for_callback.get_mut();
                    state.seed = Seed(
                        <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                            .expect("seed readback has STATE_SIZE words")
                            .to_owned(),
                    );
                    state.folding_challenges.clear();
                    if folding_steps > 0 {
                        // Includes `r_before_last` at index `folding_steps - 1`.
                        state.folding_challenges.extend_from_slice(
                            &final_folding_challenges_accessor.get()[..folding_steps],
                        );
                    }

                    let [r_last, next_batching_challenge]: [E; 2] = layer_challenges_accessor
                        .get()
                        .try_into()
                        .expect("layer challenges D2H has length 2");
                    let mut new_claim_point = state.folding_challenges.clone();
                    new_claim_point.push(r_last);

                    // Rebuild `new_claims` from the D2H'd device-computed per-
                    // address buffer + the same address list. The host loop that
                    // used to evaluate `eq_ext(values, r_before_last, r_last)` per
                    // address is gone — the kernel already did it.
                    let new_claims_slice = new_claims_accessor.get();
                    let new_claims: BTreeMap<GKRAddress, E> = callback_addresses
                        .iter()
                        .enumerate()
                        .map(|(i, addr)| (*addr, new_claims_slice[i]))
                        .collect();

                    {
                        let workflow_state = workflow_state_for_callback.get_mut();
                        workflow_state.current_claims = new_claims.clone();
                        workflow_state.current_claim_point = new_claim_point.clone();
                        workflow_state.current_batching_challenge = next_batching_challenge;
                        workflow_state.seed = state.seed;
                        workflow_state
                            .claims_for_layers
                            .insert(layer_idx, new_claims.clone());
                        workflow_state
                            .points_for_claims_at_layer
                            .insert(layer_idx, new_claim_point.clone());
                    }
                },
                stream,
            )?;
        }
        if let Some(layer_range) = layer_range.take() {
            layer_range.end(stream)?;
            tracing_ranges.push(layer_range);
        }

        drop(device_claim);
        drop(device_eq_prefactor);
        // TEMP `[E;4]` gather buffer: freed (stream-ordered) after the
        // lsb-lines + new_claims kernels that read it have been scheduled.
        drop(device_last_evals);
        drop(device_claim_point_in);
        drop(device_claims_in);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            start_callbacks: Callbacks::new(),
            final_readback: final_readback_callbacks,
            shared_state,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(device_claim_point_out),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
            _phantom: std::marker::PhantomData,
        })
    }
}
