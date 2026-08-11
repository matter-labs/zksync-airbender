use std::collections::BTreeMap;

use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};

use super::{dim_reducing_encoder, kernels::*};
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

impl GpuGKRDimensionReducingSumcheckLayerPlan {
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

    fn launch_round1_kernels(
        &mut self,
        mut batch: GpuGKRDimensionReducingContinuationBatchCompact<E4>,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        batch.eq_low = self.round_scratch.eq_low_group.as_ptr();
        batch.eq_sizes = self.eq_sizes;
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        launch_dim_reducing_round1_batched_compact(&batch, acc_size, context)
    }

    fn launch_continuation_kernels(
        &mut self,
        mut batch: GpuGKRDimensionReducingContinuationBatchCompact<E4>,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        batch.eq_low = self.round_scratch.eq_low_group.as_ptr();
        batch.eq_sizes = self.eq_sizes;
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        launch_dim_reducing_continuation_batched_compact(&batch, acc_size, step, context)
    }

    #[allow(clippy::too_many_arguments)]
    fn dispatch_fused_tail(
        &mut self,
        acc_size: usize,
        prev_claim_coord: *const E4,
        seed: *mut u32,
        claim: *mut E4,
        eq_prefactor: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        fold_eq: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let acc_ptr = self.round_scratch.accumulator.as_ptr();
        let eq_low_ptr = self.round_scratch.eq_low_group.as_mut_ptr();
        let partials_ptr = self.round_scratch.partials.as_mut_ptr();

        let (slot_base, slot_size_before_fold) = if fold_eq {
            super::kernels::resolve_active_eq_slot(&self.eq_sizes, eq_low_ptr)
        } else {
            (eq_low_ptr, 0u32)
        };

        let num_blocks = super::kernels::dual_reduce_num_stage1_blocks(acc_size);
        if num_blocks == 0 {
            super::kernels::launch_backward_dual_finalize_from_acc(
                acc_ptr,
                acc_size,
                prev_claim_coord,
                seed,
                claim,
                eq_prefactor,
                coeffs_out,
                challenge_out,
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
                partials_ptr,
                num_blocks,
                prev_claim_coord,
                seed,
                claim,
                eq_prefactor,
                coeffs_out,
                challenge_out,
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
        storage: &GpuGKRStorage<BF, E4>,
        folding: &DeviceAllocation<E4>,
        per_poly_len: usize,
    ) -> BTreeMap<GKRAddress, *const E4> {
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            for address in kernel.inputs.inputs_in_extension.iter() {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                let canonical = storage
                    .layout
                    .as_ref()
                    .and_then(|layout| layout.aliases.get(address))
                    .copied()
                    .unwrap_or(*address);
                let poly_idx = self
                    .folding_addresses
                    .binary_search(&canonical)
                    .expect("final folding source missing from dense arena");
                let pointer = unsafe { folding.as_ptr().add(poly_idx * per_poly_len) };
                result.insert(*address, pointer);
            }
        }

        result
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer(
        &mut self,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching,
        device_claims_in: DeviceAllocation<E4>,
        claim_layout: &ClaimBufferLayout,
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        storage: &mut GpuGKRStorage<BF, E4>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution> {
        const DIMENSION_REDUCING_LAYER_RANGE_MIN_FOLDING_STEPS: usize = 19;

        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        assert!(self.folding_steps >= 2);
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
        let batch_challenge_base_ptr =
            unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) };
        schedule_dim_reducing_batch_challenge_table_prelude(batch_challenge_base_ptr, context)?;
        let challenge_count = self.folding_steps - 1;
        launch_build_eq_high_and_low_groups_from_point(
            device_claim_point_in.as_ptr(),
            1,
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

        let next_claim_point_and_batching_len = self.folding_steps + 2;
        assert!(
            next_claim_point_and_batching_len <= MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN,
            "dim-reducing layer claim point length {} exceeds __constant__ symbol capacity {}",
            next_claim_point_and_batching_len,
            MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN
        );
        // SAFETY: the capacity check keeps the symbol-backed view in bounds.
        let mut device_claim_point_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                get_dim_reducing_layer_claim_point_device_ptr() as *mut E4,
                next_claim_point_and_batching_len,
            )
        };
        let folding_poly_count = self.folding_addresses.len();
        let mut folding_current: Option<DeviceAllocation<E4>> = None;
        let mut folding_current_len = 0usize;

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                let destination_len = self.trace_len_after_reduction >> (step - 1);
                let destination: DeviceAllocation<E4> = context.alloc(
                    folding_poly_count * destination_len,
                    AllocationPlacement::Top,
                )?;
                let destination_binding = FoldingArenaBinding::new(
                    destination.as_ptr() as *const u8,
                    destination_len.trailing_zeros(),
                );
                if step == 1 {
                    let batch = dim_reducing_encoder::build_round1_batch_compact_for_arena(
                        &self.kernel_plans,
                        storage,
                        &self.folding_addresses,
                        destination_binding,
                    );
                    self.launch_round1_kernels(batch, acc_size, context)?;
                } else {
                    let current = folding_current
                        .as_ref()
                        .expect("continuation round requires current folding arena");
                    let current_binding = FoldingArenaBinding::new(
                        current.as_ptr() as *const u8,
                        folding_current_len.trailing_zeros(),
                    );
                    let batch = dim_reducing_encoder::build_continuation_batch_compact_for_arenas(
                        &self.kernel_plans,
                        storage,
                        &self.folding_addresses,
                        current_binding,
                        destination_binding,
                    );
                    self.launch_continuation_kernels(batch, step, acc_size, context)?;
                }
                folding_current = Some(destination);
                folding_current_len = destination_len;
            }

            if step == 0 {
                storage.purge_up_to_layer(self.layer_idx);
            }

            let prev_coord_slice = device_claim_point_in.slice(step, 1);
            // SAFETY: `step < folding_steps`, and every round owns four slab elements.
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            let challenge_slice = device_claim_point_out.slice_mut(step, 1);

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

        let destination_len = self.trace_len_after_reduction >> (last_step - 1);
        let destination: DeviceAllocation<E4> = context.alloc(
            folding_poly_count * destination_len,
            AllocationPlacement::Top,
        )?;
        let destination_binding = FoldingArenaBinding::new(
            destination.as_ptr() as *const u8,
            destination_len.trailing_zeros(),
        );
        if last_step == 1 {
            let batch = dim_reducing_encoder::build_round1_batch_compact_for_arena(
                &self.kernel_plans,
                storage,
                &self.folding_addresses,
                destination_binding,
            );
            self.launch_round1_kernels(batch, 1, context)?;
        } else {
            let current = folding_current
                .as_ref()
                .expect("final continuation round requires current folding arena");
            let current_binding = FoldingArenaBinding::new(
                current.as_ptr() as *const u8,
                folding_current_len.trailing_zeros(),
            );
            let batch = dim_reducing_encoder::build_continuation_batch_compact_for_arenas(
                &self.kernel_plans,
                storage,
                &self.folding_addresses,
                current_binding,
                destination_binding,
            );
            self.launch_continuation_kernels(batch, last_step, 1, context)?;
        }
        folding_current = Some(destination);
        folding_current_len = destination_len;
        {
            let prev_coord_slice = device_claim_point_in.slice(last_step, 1);
            // SAFETY: `last_step < folding_steps`, and every round owns four slab elements.
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(last_step * 4), 4) };
            let challenge_slice = device_claim_point_out.slice_mut(last_step, 1);
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

        let transcript_input_sources = self.final_evaluation_sources_for_last_step(
            storage,
            folding_current
                .as_ref()
                .expect("final folding arena must be present"),
            folding_current_len,
        );
        let num_addresses = transcript_input_sources.len();
        assert!(
            num_addresses > 0,
            "dimension-reducing layer must produce a next-layer claim"
        );
        let last_evals_len = num_addresses * 4;
        let final_step_evals_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();

        let mut device_last_evals: DeviceAllocation<E4> =
            context.alloc(last_evals_len, AllocationPlacement::Top)?;
        let src_ptrs: Vec<u64> = transcript_input_sources
            .values()
            .map(|p| *p as u64)
            .collect();
        gpu_hash::blake2s::gather_e_addresses(
            &src_ptrs,
            &mut device_last_evals[..last_evals_len],
            stream,
        )?;
        drop(folding_current);

        // SAFETY: `layer_slot` selects this layer's slab segment.
        let (final_step_evals_buffer_ptr, final_step_evals_buffer_len) = unsafe {
            proof_layout
                .backward_final_step_evals_device_mut(proof_slab.as_ptr() as *mut u8, layer_slot)
        };
        assert_eq!(final_step_evals_buffer_len, final_step_evals_len);
        let final_step_evals_buffer_ptr = final_step_evals_buffer_ptr as *mut E4;

        let rbl_view = device_claim_point_out.slice(last_step, 1);
        // SAFETY: the proof layout returned `final_step_evals_len` live elements.
        let lsb_out = unsafe {
            DeviceSlice::from_raw_parts_mut(final_step_evals_buffer_ptr, final_step_evals_len)
        };
        crate::gkr_ops::backward_dim_reducing_lsb_lines(
            &device_last_evals[..last_evals_len],
            rbl_view,
            lsb_out,
            stream,
        )?;

        // SAFETY: the slab region is live, and E4 is four packed BF limbs.
        let final_step_evals_e_slice = unsafe {
            DeviceSlice::from_raw_parts(
                final_step_evals_buffer_ptr as *const E4,
                final_step_evals_len,
            )
        };
        let d_final_step_evals_u32 = unsafe { final_step_evals_e_slice.transmute::<u32>() };
        gpu_hash::blake2s::transcript_commit(&mut device_seed, d_final_step_evals_u32, stream)?;

        {
            let layer_challenges_dst = device_claim_point_out.slice_mut(self.folding_steps, 2);
            gpu_hash::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst,
                stream,
            )?;
        }

        let mut device_new_claims: DeviceAllocation<E4> =
            context.alloc(num_addresses, AllocationPlacement::Top)?;
        let challenges = device_claim_point_out.slice(last_step, 2);
        crate::gkr_ops::backward_new_claims_two_var(
            &device_last_evals[..last_evals_len],
            challenges,
            &mut device_new_claims[..],
            stream,
        )?;

        let next_claim_layout = ClaimBufferLayout::from_addresses(transcript_input_addresses);
        if let Some(layer_range) = layer_range.take() {
            layer_range.end(stream)?;
            tracing_ranges.push(layer_range);
        }

        drop(device_claim);
        drop(device_eq_prefactor);
        drop(device_last_evals);
        drop(device_claim_point_in);
        drop(device_claims_in);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(device_claim_point_out),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
        })
    }
}
