use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use crate::GpuGKRStorage;

use super::super::kernels::*;
use super::super::window::binding::{launch_window_program, BWD_WINDOW_COORDINATES};
use super::super::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use super::extras::{schedule_main_layer_extras_eval, MainLayerExtrasKeepalive};
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

impl GpuGKRMainLayerSumcheckLayerPlan {
    fn dispatch_warp_partial_tail(
        &mut self,
        acc_size: usize,
        prev_claim_coord: *const E4,
        seed: *mut u32,
        claim: *mut E4,
        eq_prefactor: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let eq_low_ptr_mut = self.round_scratch.eq_low_group.as_mut_ptr();
        let (slot_base, slot_size_before_fold) =
            super::super::kernels::resolve_active_eq_slot(&self.eq_sizes, eq_low_ptr_mut);
        self.dispatch_warp_partial_tail_inner(
            acc_size,
            (slot_base, slot_size_before_fold),
            prev_claim_coord,
            seed,
            claim,
            eq_prefactor,
            coeffs_out,
            challenge_out,
            context,
        )?;
        super::super::kernels::record_active_eq_slot_fold(&mut self.eq_sizes);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn dispatch_warp_partial_tail_inner(
        &mut self,
        acc_size: usize,
        eq_slot: (*mut E4, u32),
        prev_claim_coord: *const E4,
        seed: *mut u32,
        claim: *mut E4,
        eq_prefactor: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let partials_ptr = self.round_scratch.partials.as_mut_ptr();
        let num_partials = super::super::kernels::warp_partial_count(acc_size);
        let (slot_base, slot_size_before_fold) = eq_slot;
        super::super::kernels::launch_backward_dual_finalize_from_partials(
            partials_ptr,
            num_partials,
            prev_claim_coord,
            seed,
            claim,
            eq_prefactor,
            coeffs_out,
            challenge_out,
            slot_base,
            slot_size_before_fold,
            context,
        )
    }

    /// The windowed arm's rounds 0-2, in the order Task 4 fixed: window-plan
    /// bank fill -> window kernel -> ext-recipe bank refill -> tail. The window
    /// kernel's coefficient reads must be enqueued before the refill overwrites
    /// the shared output bank.
    fn schedule_windowed_rounds_0_2(
        &mut self,
        external_challenges: *const E4,
        lookup_multiplicative: *const E4,
        lookup_additive: *const E4,
        claim_batching: *const E4,
        prev_claim_coords: *const E4,
        seed: *mut u32,
        claim: *mut E4,
        eq_prefactor: *mut E4,
        coeffs_out: *mut E4,
        challenges_out: *mut E4,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let MainLayerR0Binding::Windowed(windowed) = &mut self.bwd_vm_r0 else {
            panic!("the windowed prologue requires a windowed R0 binding");
        };
        super::super::vm::production_bind::schedule_bwd_vm_window_bank_fill(
            &mut windowed.bank,
            external_challenges,
            lookup_multiplicative,
            lookup_additive,
            claim_batching,
            context,
        )?;
        launch_window_program(&windowed.window, context)?;
        let tail_arm = windowed.tail_arm;
        let row_tiles = windowed.window.row_tiles;
        let reduced_tensor = windowed.window.reduced_tensor;
        super::super::vm::production_bind::schedule_bwd_vm_ext_bank_fill(
            &mut self.bwd_vm_ext,
            external_challenges,
            lookup_multiplicative,
            lookup_additive,
            claim_batching,
            context,
        )?;
        let eq_low_ptr_mut = self.round_scratch.eq_low_group.as_mut_ptr();
        let (active_eq_slot_base, active_eq_size_before_fold) =
            super::super::kernels::resolve_active_eq_slot(&self.eq_sizes, eq_low_ptr_mut);
        let state = WindowTailState {
            partials: self.round_scratch.partials.as_ptr(),
            row_tiles,
            reduced_tensor,
            prev_claim_coords,
            seed,
            claim,
            eq_prefactor,
            coeffs_out,
            challenges_out,
            active_eq_slot_base,
            active_eq_size_before_fold,
        };
        launch_window_tensor_round_tail(tail_arm, &state, context)?;
        // The tail folds the active slot exactly once, for the three rounds it
        // played; round 3's descriptor was lowered against the same one-fold
        // drain of the same built schedule.
        super::super::kernels::record_active_eq_slot_fold(&mut self.eq_sizes);
        assert_eq!(
            self.eq_sizes,
            super::super::vm::production_bind::drained_eq_sizes(
                make_eq_sizes(self.folding_steps - BWD_WINDOW_COORDINATES),
                1,
            ),
            "the tail's physical eq state must match the round-3 descriptor's drain"
        );
        Ok(())
    }

    pub(crate) fn schedule_execute_main_layer(
        &mut self,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching,
        device_claims_in: DeviceAllocation<E4>,
        claim_layout: &ClaimBufferLayout,
        device_lookup_challenges_ptr: *const E4,
        device_external_challenges_ptr: *const E4,
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        storage: &mut GpuGKRStorage<BF, E4>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.main.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name)?;
        layer_range.start(stream)?;
        assert!(self.folding_steps >= 4);
        let last_step = self.folding_steps - 1;
        let mut desc_pairs: Vec<u32> = Vec::new();
        for &(batch_offset, output) in &self.claim_terms {
            desc_pairs.push(batch_offset as u32);
            desc_pairs.push(claim_layout.claim_idx(&output));
        }
        let mut device_claim: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top)?;
        let mut device_eq_prefactor: DeviceAllocation<E4> =
            context.alloc(1, AllocationPlacement::Top)?;
        let coeffs_total_len = self.folding_steps * 4;
        // SAFETY: `layer_slot` selects this layer's slab segment.
        let (coeffs_buffer_ptr, coeffs_buffer_len) = unsafe {
            proof_layout
                .backward_internal_coeffs_device_mut(proof_slab.as_ptr() as *mut u8, layer_slot)
        };
        assert_eq!(coeffs_buffer_len, coeffs_total_len);
        let coeffs_buffer_ptr = coeffs_buffer_ptr as *mut E4;
        let claim_point_and_batching_len = self.folding_steps + 1;
        assert_eq!(
            device_claim_point_in.len(),
            claim_point_and_batching_len,
            "device claim_point input size must match this layer's folding_steps + 1",
        );
        // The eq table is built over the coordinates the arm's first sumcheck
        // launch still carries: everything past round 0 for the per-round arm,
        // everything past the window's three rounds for the windowed arm.
        // `first_ext_round` is the first round the continuation VM plays;
        // `first_round_in_loop` is the first round the per-round loop below
        // plays, which for the per-round arm is round 0 on the R0 VM.
        let (first_ext_round, first_round_in_loop) = match &self.bwd_vm_r0 {
            MainLayerR0Binding::PerRound(_) => (1, 0),
            MainLayerR0Binding::Windowed(_) => (BWD_WINDOW_COORDINATES, BWD_WINDOW_COORDINATES),
        };
        let challenge_count = self.folding_steps - first_ext_round;
        launch_build_eq_high_and_low_groups_from_point(
            device_claim_point_in.as_ptr(),
            first_ext_round,
            challenge_count,
            get_eq_high_constant_device_ptr() as *mut E4,
            self.round_scratch.eq_low_group.as_mut_ptr(),
            context,
        )?;
        self.eq_sizes = make_eq_sizes(challenge_count);

        assert_eq!(
            device_claims_in.len(),
            claim_layout.claim_count(),
            "device claims buffer must match claim layout length",
        );

        {
            let batching = device_claim_point_in.slice(self.folding_steps, 1);
            crate::gkr_ops::build_combined_claim(
                &device_claims_in[..claim_layout.claim_count()],
                batching,
                &desc_pairs,
                &mut device_claim[..],
                &mut device_eq_prefactor[..],
                stream,
            )?;
        }

        let cont_batch_base_ptr = unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) };
        let cont_lookup_mul_ptr = device_lookup_challenges_ptr;
        let cont_lookup_add_ptr = unsafe { device_lookup_challenges_ptr.add(1) };
        let next_claim_point_and_batching_len = self.folding_steps + 1;
        assert!(
            next_claim_point_and_batching_len <= MAX_MAIN_LAYER_CLAIM_POINT_LEN,
            "main-layer claim point length {} exceeds __constant__ symbol capacity {}",
            next_claim_point_and_batching_len,
            MAX_MAIN_LAYER_CLAIM_POINT_LEN
        );
        // SAFETY: the capacity check keeps the symbol-backed view in bounds.
        let mut device_claim_point_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                get_main_layer_claim_point_device_ptr() as *mut E4,
                next_claim_point_and_batching_len,
            )
        };
        if matches!(self.bwd_vm_r0, MainLayerR0Binding::Windowed(_)) {
            let coeffs_out = coeffs_buffer_ptr;
            let challenges_out = device_claim_point_out
                .slice_mut(0, BWD_WINDOW_COORDINATES)
                .as_mut_ptr();
            self.schedule_windowed_rounds_0_2(
                device_external_challenges_ptr,
                cont_lookup_mul_ptr,
                cont_lookup_add_ptr,
                cont_batch_base_ptr,
                device_claim_point_in.as_ptr(),
                device_seed.as_mut_ptr(),
                device_claim.as_mut_ptr(),
                device_eq_prefactor.as_mut_ptr(),
                coeffs_out,
                challenges_out,
                context,
            )?;
            storage.purge_up_to_layer(self.layer_idx);
        }

        for step in first_round_in_loop..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                let MainLayerR0Binding::PerRound(round0) = &mut self.bwd_vm_r0 else {
                    panic!("step 0 runs the per-round R0 VM");
                };
                super::super::vm::production_bind::schedule_bwd_vm_round0(
                    round0,
                    device_external_challenges_ptr,
                    cont_lookup_mul_ptr,
                    cont_lookup_add_ptr,
                    cont_batch_base_ptr,
                    acc_size as u32,
                    context,
                )?;
            } else {
                if step == 1 {
                    super::super::vm::production_bind::schedule_bwd_vm_ext_bank_fill(
                        &mut self.bwd_vm_ext,
                        device_external_challenges_ptr,
                        cont_lookup_mul_ptr,
                        cont_lookup_add_ptr,
                        cont_batch_base_ptr,
                        context,
                    )?;
                }
                super::super::vm::production_bind::schedule_bwd_vm_ext_round(
                    &mut self.bwd_vm_ext,
                    step as u32,
                    acc_size as u32,
                    context,
                )?;
            }

            if step == 0 {
                storage.purge_up_to_layer(self.layer_idx);
            }

            let prev_coord_slice = device_claim_point_in.slice(step, 1);
            // SAFETY: `step < folding_steps`, and every round owns four slab elements.
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            let challenge_slot = device_claim_point_out.slice_mut(step, 1);

            self.dispatch_warp_partial_tail(
                acc_size,
                prev_coord_slice.as_ptr(),
                device_seed.as_mut_ptr(),
                device_claim.as_mut_ptr(),
                device_eq_prefactor.as_mut_ptr(),
                coeffs_round_slice.as_mut_ptr(),
                challenge_slot.as_mut_ptr(),
                context,
            )?;
        }
        super::super::vm::production_bind::schedule_bwd_vm_ext_round(
            &mut self.bwd_vm_ext,
            last_step as u32,
            1,
            context,
        )?;
        {
            let prev_coord_slice = device_claim_point_in.slice(last_step, 1);
            // SAFETY: `last_step < folding_steps`, and every round owns four slab elements.
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(last_step * 4), 4) };
            let challenge_slot = device_claim_point_out.slice_mut(last_step, 1);
            let eq_low_ptr = self.round_scratch.eq_low_group.as_mut_ptr();
            self.dispatch_warp_partial_tail_inner(
                1,
                (eq_low_ptr, 0),
                prev_coord_slice.as_ptr(),
                device_seed.as_mut_ptr(),
                device_claim.as_mut_ptr(),
                device_eq_prefactor.as_mut_ptr(),
                coeffs_round_slice.as_mut_ptr(),
                challenge_slot.as_mut_ptr(),
                context,
            )?;
        }

        let mut transcript_input_sources: BTreeMap<GKRAddress, *const E4> = self
            .folding_evaluation_sources
            .iter()
            .map(|address| (*address, std::ptr::null()))
            .collect();
        self.bwd_vm_ext
            .repoint_final_evaluations(&mut transcript_input_sources);
        let num_addresses = transcript_input_sources.len();
        let last_evals_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();

        let mut device_last_evals: DeviceAllocation<E4> =
            context.alloc(last_evals_len.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            let src_ptrs: Vec<u64> = transcript_input_sources
                .values()
                .map(|p| *p as u64)
                .collect();
            gpu_hash::blake2s::gather_e_addresses(
                &src_ptrs,
                &mut device_last_evals[..last_evals_len],
                stream,
            )?;
        }

        let final_step_evals_buffer_ptr: *mut E4 = if num_addresses > 0 {
            // SAFETY: `layer_slot` selects this layer's slab segment; validated
            // against `num_addresses` immediately below.
            let (dst_ptr, dst_len) = unsafe {
                proof_layout.backward_final_step_evals_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    layer_slot,
                )
            };
            assert_eq!(
                dst_len, num_addresses,
                "slab final_step_evaluations range must match main-layer num_addresses (degree 1)",
            );
            dst_ptr as *mut E4
        } else {
            std::ptr::null_mut()
        };

        if num_addresses > 0 {
            let last_r_view = device_claim_point_out.slice(last_step, 1);
            // SAFETY: the proof layout returned a live region of `num_addresses` elements.
            let final_step_e4 = unsafe {
                DeviceSlice::from_raw_parts_mut(final_step_evals_buffer_ptr, num_addresses)
            };
            crate::gkr_ops::backward_new_claims_linear(
                &device_last_evals[..last_evals_len],
                last_r_view,
                final_step_e4,
                stream,
            )?;
        }

        // Transcript order is final evaluations followed by cached dependencies.
        let extra_addresses: Vec<GKRAddress> = proof_layout.backward[layer_slot]
            .extra_evaluations_addresses
            .clone();
        let extra_count = extra_addresses.len();
        let total_new_claims_len = num_addresses + extra_count;
        assert!(total_new_claims_len > 0);

        let mut device_new_claims: DeviceAllocation<E4> =
            context.alloc(total_new_claims_len, AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: slab final-step region holds `num_addresses` live E4 evals.
            let final_step_src = unsafe {
                DeviceSlice::from_raw_parts(final_step_evals_buffer_ptr as *const E4, num_addresses)
            };
            memory_copy_async(
                &mut device_new_claims[..num_addresses],
                final_step_src,
                stream,
            )?;
        }

        let extras_keepalive: Option<MainLayerExtrasKeepalive> = if extra_count > 0 {
            let folding_point_ptr = device_claim_point_out.as_ptr();
            let trace_len = 1usize << self.folding_steps;
            // SAFETY: `device_new_claims` includes the `extra_count`-element tail.
            let extras_dst_ptr = unsafe { device_new_claims.as_mut_ptr().add(num_addresses) };
            Some(schedule_main_layer_extras_eval(
                self.layer_idx,
                &extra_addresses,
                storage,
                folding_point_ptr,
                self.folding_steps,
                trace_len,
                extras_dst_ptr,
                proof_slab,
                proof_layout,
                layer_slot,
                context,
            )?)
        } else {
            None
        };

        let transcript_inputs_e = &device_new_claims[..total_new_claims_len];
        // SAFETY: E4 is four packed BF limbs, matching transcript word order.
        let transcript_inputs_u32 = unsafe { transcript_inputs_e.transmute::<u32>() };
        gpu_hash::blake2s::transcript_commit(&mut device_seed, transcript_inputs_u32, stream)?;

        {
            let layer_challenges_dst = device_claim_point_out.slice_mut(self.folding_steps, 1);
            gpu_hash::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst,
                stream,
            )?;
        }

        let mut combined_addresses = transcript_input_addresses;
        combined_addresses.extend(extra_addresses.iter().copied());
        let next_claim_layout = ClaimBufferLayout::from_addresses(combined_addresses);
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(device_claim);
        drop(device_eq_prefactor);
        drop(device_last_evals);
        drop(device_claim_point_in);
        drop(device_claims_in);
        // Release extras scratch immediately after its last queued use.
        drop(extras_keepalive);
        let r0_bank_staging = match &mut self.bwd_vm_r0 {
            MainLayerR0Binding::PerRound(round0) => round0.take_bank_staging(),
            MainLayerR0Binding::Windowed(windowed) => windowed.bank.take_bank_staging(),
        };
        let coeff_bank_staging = [r0_bank_staging, self.bwd_vm_ext.take_bank_staging()]
            .into_iter()
            .flatten()
            .collect();
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(device_claim_point_out),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
            coeff_bank_staging,
        })
    }
}
