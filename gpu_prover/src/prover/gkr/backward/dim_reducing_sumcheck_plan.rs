use std::collections::BTreeMap;
use std::ptr::{null, null_mut};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};

use super::kernels::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::cub::device_reduce::{reduce, Reduce, ReduceOperation};
use crate::ops::simple::{BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_structures::DeviceVectorChunk;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::proof::layout::ProofLayout;
use crate::upstream::{Field, FieldExtension, GKRAddress, Seed};

impl<B: 'static, E: 'static> GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    E: Field + FieldExtension<BF> + Reduce + crate::prover::gkr::GpuKernels,
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

    fn fold_eq_values_for_next_round(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        debug_assert!(acc_size.is_power_of_two());
        debug_assert!(acc_size >= 2);
        launch_fold_eq_values_in_place(
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size / 2,
            context,
        )
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round0_batch_template_compact;
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
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
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
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
        batch.eq_values = self.round_scratch.eq_values.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.explicit_form = explicit_form;
        launch_dim_reducing_continuation_batched_compact(&batch, null(), acc_size, step, context)
    }

    /// Runs the two CUB reductions for a round's sumcheck accumulator without
    /// copying the result back to the host. Used by the on-device per-round
    /// update path where the reduction output stays on the GPU and is consumed
    /// by `launch_backward_sumcheck_round_update` directly.
    fn run_round_coefficients_reduction_device(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        let stream = context.get_exec_stream();
        // SAFETY: `reduction_temp_storage` owns a live device allocation sized
        // exactly to its backing buffer; this temporary mutable view is used
        // only by the reductions below.
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        {
            let low_half = DeviceVectorChunk::new(&self.round_scratch.accumulator, 0, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &low_half,
                &mut self.round_scratch.reduction_output[0],
                stream,
            )?;
        }
        {
            let high_half =
                DeviceVectorChunk::new(&self.round_scratch.accumulator, acc_size, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &high_half,
                &mut self.round_scratch.reduction_output[1],
                stream,
            )?;
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
        // When `Some` (production), per-round kernels write coeffs directly
        // into the slab's `internal_round_coefficients` range for `layer_slot`
        // and the per-address gather writes directly into
        // `final_step_evaluations` (B1 + B2). When `None` (test paths with
        // placeholder layouts), per-layer fallback device buffers are
        // allocated so the kernels still have valid destinations.
        proof_slab: Option<&DeviceAllocation<E4>>,
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
        let coeffs_total_len = last_step * 4;
        // B1: per-round kernels write coeffs straight into the slab range for
        // this layer when `proof_slab` is provided — no standalone allocation
        // and no post-loop slab D2D. The kernels are stream-ordered against
        // the terminal D2H of the slab in `prove()`, so the slab is
        // self-consistent on `exec_stream`. Test paths fall back to a
        // per-layer device buffer.
        let mut fallback_device_coeffs: Option<DeviceAllocation<E>> = None;
        let coeffs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if coeffs_total_len > 0 {
                // SAFETY: `layer_slot` selects this layer's slab segment and the
                // returned region is validated against `coeffs_total_len` below.
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_internal_coeffs_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, coeffs_total_len,
                    "slab internal_round_coefficients range must match layer's coeffs_total_len",
                );
                dst_ptr as *mut E
            } else {
                null_mut()
            }
        } else {
            let alloc: DeviceAllocation<E> =
                context.alloc(coeffs_total_len.max(1), AllocationPlacement::Top)?;
            let ptr = alloc.as_ptr() as *mut E;
            fallback_device_coeffs = Some(alloc);
            ptr
        };

        // The `[claim_point || batching_challenge]` input is consumed
        // directly from `device_claim_point_in` — no D2D into a per-layer
        // `round_scratch.claim_point` buffer. Per-round kernels read it for
        // `prev_coord_slice`; `launch_build_eq_values_from_point` reads the
        // suffix `[1..folding_steps]`. The launch_round*_kernels path reads
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
        // Build `eq_group_tables` + `eq_values` directly from the device
        // claim_point (using coords `[1..folding_steps]` — the suffix that
        // `fill_round0_eq_pair_values` used to expand on host). Replaces the
        // `eq_pair_values_host` H2D + `build_round0_eq_values_from_pairs`
        // kernel chain with a single on-device builder.
        let challenge_count = self.folding_steps.saturating_sub(1);
        let acc_size = 1usize << challenge_count;
        launch_build_eq_values_from_point(
            device_claim_point_in.as_ptr(),
            1,
            challenge_count,
            self.round_scratch.eq_group_tables.as_mut_ptr(),
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )?;

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
            crate::ops::blake2s::build_combined_claim(
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
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels_from_symbol(acc_size, false, context)?,
                    step => self
                        .launch_continuation_kernels_from_symbol(step, acc_size, false, context)?,
                }
            }

            // Device-only reduction: sums accumulator halves into
            // `round_scratch.reduction_output` (2 E4 values) without any D2H.
            self.run_round_coefficients_reduction_device(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;

            // Fused on-device per-round update: reads the reduction output and
            // current (seed, claim, eq_prefactor) state, derives the 4
            // univariate coefficients, commits them to the transcript, extracts
            // the next folding challenge, and folds claim/eq_prefactor — all in
            // one single-thread kernel. The challenge lands directly in
            // `device_claim_point_out[step]`, ready for the next round's
            // kernel to read and for the next layer to consume.
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
            E::launch_backward_sumcheck_round_update(
                &self.round_scratch.reduction_output,
                prev_coord_slice,
                &mut device_seed,
                &mut device_claim,
                &mut device_eq_prefactor,
                coeffs_round_slice,
                challenge_slice,
                stream,
            )?;
        }

        match last_step {
            1 => self.launch_round1_kernels_from_symbol(1, true, context)?,
            step => self.launch_continuation_kernels_from_symbol(step, 1, true, context)?,
        }

        // B1: coeffs already landed in the slab via the per-round kernels
        // (or in `fallback_device_coeffs` for test paths). No post-loop
        // slab D2D needed.

        // Device-side inter-layer transcript: pack the flattened last-round
        // evaluations into a packed E buffer (D2D from each address's 4-E
        // source slot) — written **directly into the slab** via B2 in the
        // production path. Absorbed into device_seed via transcript_commit,
        // then squeezed into 3 E4 challenges
        // `[r_before_last, r_last, next_batching_challenge]` via
        // transcript_squeeze_e4. The same packed buffer feeds the on-device
        // `backward_new_claims_two_var` kernel.
        let transcript_input_sources = self.final_evaluation_sources_for_last_step(last_step);
        let num_addresses = transcript_input_sources.len();
        let transcript_inputs_len = num_addresses * 4;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();
        // Per-address gather writes straight into the slab's
        // `final_step_evaluations` range when `proof_slab` is provided. Test
        // paths fall back to a per-layer device buffer. The flat layout (4 E
        // per address, in BTreeMap key order from
        // `final_evaluation_sources_for_last_step`) matches what
        // `build_proof_layout_inputs` stored in
        // `ProofLayout.backward[slot].final_step_eval_addresses`.
        let mut fallback_d_layer_transcript_inputs: Option<DeviceAllocation<E>> = None;
        let transcript_inputs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if transcript_inputs_len > 0 {
                // SAFETY: `layer_slot` selects this layer's slab segment and
                // the returned region is validated against
                // `transcript_inputs_len` immediately below.
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_final_step_evals_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, transcript_inputs_len,
                    "slab final_step_evaluations range must match layer's transcript_inputs_len",
                );
                dst_ptr as *mut E
            } else {
                null_mut()
            }
        } else {
            let alloc: DeviceAllocation<E> =
                context.alloc(transcript_inputs_len.max(1), AllocationPlacement::Top)?;
            let ptr = alloc.as_ptr() as *mut E;
            fallback_d_layer_transcript_inputs = Some(alloc);
            ptr
        };
        // B7: per-address gather kernel — single launch replaces the
        // num_addresses-element D2D loop. Source pointers are scheduling-
        // time-known and now ride inline in the kernel-arg struct
        // (`GpuGatherEAddressesDesc`), so the previous SchedulerHostAllocation
        // + per-launch H2D of the pointer table is gone. The slab/fallback
        // `transcript_inputs_e_slice` below is still held alive by
        // `_proof_slab` (slab path) or `fallback_d_layer_transcript_inputs`
        // (test path) for the duration of the gather launch.
        if num_addresses > 0 {
            let src_ptrs: Vec<u64> = transcript_input_sources
                .values()
                .map(|p| *p as u64)
                .collect();
            // SAFETY: the slab/fallback transcript-input buffer was allocated
            // for `transcript_inputs_len` ext elements; viewing it as `E4`
            // matches the only instantiated extension layout.
            let dst = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    transcript_inputs_buffer_ptr as *mut E4,
                    transcript_inputs_len,
                )
            };
            crate::ops::blake2s::gather_e_addresses(&src_ptrs, dst, 4, stream)?;
        }

        // SAFETY: E = E4 in every instantiation of this scheduler; the u32
        // view matches the host `commit_field_els::<BF, E4>` byte layout
        // (covered by `ops::blake2s::tests::transcript_squeeze_e4_parity_*`).
        // The slab/fallback memory is alive through the kernel launch, and
        // `transcript_commit` only reads from this slice.
        let transcript_inputs_e_slice = unsafe {
            DeviceSlice::from_raw_parts(
                transcript_inputs_buffer_ptr as *const E,
                transcript_inputs_len,
            )
        };
        // SAFETY: `E = E4` in this scheduler, so the transcript input slice is
        // byte-identical to the `u32` view that `transcript_commit` expects.
        let d_transcript_inputs_u32 = unsafe { transcript_inputs_e_slice.transmute::<u32>() };
        crate::ops::blake2s::transcript_commit(&mut device_seed, d_transcript_inputs_u32, stream)?;

        // Squeeze the 3 layer challenges directly into the tail of
        // `device_claim_point_out` — slots
        // `[last_step..last_step + 3] = [r_before_last, r_last, next_batching_challenge]`.
        // SAFETY: `last_step + 3 = folding_steps + 2 = next_claim_point_and_batching_len`,
        // so the range is in-bounds, and only this scheduling site writes
        // it (see write-exclusivity below).
        {
            let layer_challenges_dst = unsafe { device_claim_point_out.slice_mut(last_step, 3) };
            // SAFETY: E = E4 in every instantiation; the transmute is a no-op at
            // the byte level and matches host `draw_random_field_els::<BF, E4>`.
            let layer_challenges_dst_e4 = unsafe { layer_challenges_dst.transmute_mut::<E4>() };
            crate::ops::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst_e4,
                stream,
            )?;
        }

        // Device-side per-address `new_claims` evaluator. Consumes the packed
        // last-round evaluations (4 E per address) and the just-squeezed
        // `[r_before_last, r_last]` to produce N E per-address next-layer
        // claims. Replaces the host loop inside the final readback callback.
        // The kernel is stream-ordered after the transcript squeeze and
        // before the subsequent D2H of the result.
        let mut device_new_claims: DeviceAllocation<E> =
            context.alloc(num_addresses.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: E = E4 in every instantiation; the transmutes match the
            // kernel's `e4` view of both the packed evals and the challenges.
            // The packed evals slab/fallback memory is alive through the
            // kernel launch.
            let transcript_inputs_e_view = unsafe {
                DeviceSlice::from_raw_parts(
                    transcript_inputs_buffer_ptr as *const E,
                    transcript_inputs_len,
                )
            };
            // SAFETY: the packed eval buffer is laid out as `E4` elements in
            // this scheduler instantiation.
            let transcript_inputs_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { transcript_inputs_e_view.transmute::<E4>() };
            // SAFETY: layer-challenge tail lives at
            // `claim_point_out[last_step..last_step + 3]`; reading the first
            // two (`r_before_last`, `r_last`) for the kernel.
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
            crate::ops::blake2s::backward_new_claims_two_var(
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
            // SAFETY: these pinned host buffers are used only as D2H
            // destinations before the callback reads them.
            let mut layer_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(3) };
            let layer_challenges_accessor = layer_challenges_host.get_accessor();
            let mut new_claims_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(num_addresses.max(1)) };
            let new_claims_accessor = new_claims_host.get_accessor();
            // SAFETY: this pinned host buffer is also a pure D2H destination
            // before the final callback consumes it.
            let mut final_seed_host = unsafe { context.alloc_host_uninit_slice(STATE_SIZE) };
            let final_seed_accessor = final_seed_host.get_accessor();
            let mut final_folding_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(last_step.max(1)) };
            let final_folding_challenges_accessor = final_folding_challenges_host.get_accessor();
            crate::primitives::transfer::fork_join_exec_to_d2h(
                stream,
                context.get_d2h_stream(),
                |d2h_stream| {
                    // SAFETY: `[last_step..last_step + 3]` was just written by the
                    // transcript squeeze on `stream`; d2h_stream waits on the fork event
                    // before this read.
                    let layer_challenges_src = unsafe {
                        DeviceSlice::from_raw_parts(
                            device_claim_point_out.as_ptr().add(last_step),
                            3,
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
                    if last_step > 0 {
                        // SAFETY: `[0..last_step]` are written in-place by the
                        // per-round update kernels.
                        let folding_src = unsafe {
                            DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr(), last_step)
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
                    // is needed — the 3 challenges live in `layer_challenges_host`.
                    let state = shared_state_for_callback.get_mut();
                    state.seed = Seed(
                        <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                            .expect("seed readback has STATE_SIZE words")
                            .to_owned(),
                    );
                    state.folding_challenges.clear();
                    if last_step > 0 {
                        state.folding_challenges.extend_from_slice(
                            &final_folding_challenges_accessor.get()[..last_step],
                        );
                    }

                    let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                        layer_challenges_accessor
                            .get()
                            .try_into()
                            .expect("layer challenges D2H has length 3");
                    let mut new_claim_point = state.folding_challenges.clone();
                    new_claim_point.push(r_before_last);
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

        drop(fallback_d_layer_transcript_inputs);
        drop(device_claim);
        drop(device_eq_prefactor);
        drop(fallback_device_coeffs);
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
