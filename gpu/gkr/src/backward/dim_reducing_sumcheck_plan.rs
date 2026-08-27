use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};

use super::dr_tail::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc, DrTailSlot, DR_TAIL_MAX_SOURCES,
    DR_TAIL_SLOTS,
};
use super::kernels::*;
use super::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use super::window_dr::{
    launch_dr_window_continuation, launch_dr_window_r0, resolve_dr_global_active_eq_slot,
    DrWindowBindError,
};
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

fn unwrap_dr_window<T>(result: Result<T, DrWindowBindError>) -> CudaResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(DrWindowBindError::Cuda(error)) => Err(error),
        Err(error) => panic!("DR window invariant failed: {error:?}"),
    }
}

impl GpuGKRDimensionReducingSumcheckLayerPlan {
    fn final_evaluation_sources_for_last_step(
        &self,
        storage: &GpuGKRStorage<BF, E4>,
        folding: &DeviceAllocation<E4>,
        per_poly_len: usize,
    ) -> BTreeMap<GKRAddress, *const E4> {
        let mut result = BTreeMap::new();
        for address in self.layer_slots.input_addresses() {
            if result.contains_key(&address) {
                continue;
            }
            let canonical = storage
                .layout
                .as_ref()
                .and_then(|layout| layout.aliases.get(&address))
                .copied()
                .unwrap_or(address);
            let poly_idx = self
                .folding_addresses
                .binary_search(&canonical)
                .expect("final folding source missing from dense arena");
            let pointer = unsafe { folding.as_ptr().add(poly_idx * per_poly_len) };
            result.insert(address, pointer);
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
        let stream = context.get_exec_stream();
        let dr_execution_plan = self.dr_execution_plan;
        let dr_tail_capacity = dr_execution_plan.capacity();
        let mut tracing_ranges = Vec::new();
        assert!(self.folding_steps >= 2);
        let last_step = self.folding_steps - 1;
        let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
        let layer_range = {
            let range = Range::new(layer_name)?;
            range.start(stream)?;
            Some(range)
        };
        // Exponents come from the same slot table the kernels read, so the claim
        // combination and the per-output kernel weights cannot disagree.
        let mut desc_pairs: Vec<u32> = Vec::new();
        for (_, slot) in self.layer_slots.iter_enabled() {
            for (output, batch_exp) in slot.outputs.iter().zip(slot.batch_exp.iter()) {
                desc_pairs.push(u32::from(*batch_exp));
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
        // The combined-claim kernel is the final exec-stream use of the
        // previous layer's claim buffer.  Dropping its handle here permits
        // stream-ordered pool reuse before the next-layer claim allocation;
        // all queued pointer uses remain valid under the scheduling contract.
        drop(device_claims_in);

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
        let prepared = self
            .dr_window
            .take()
            .expect("DR window preparation must be consumed exactly once");
        let mut hook =
            unwrap_dr_window(prepared.activate(storage, device_claim_point_out.as_ptr(), context))?;
        assert_eq!(
            hook.continuation_launches.len(),
            dr_execution_plan.continuation_window_count(),
        );
        assert_eq!(
            hook.megakernel_entry_round,
            dr_execution_plan.megakernel_entry_round(),
        );
        assert_eq!(
            dr_tail_capacity.entry_round(),
            dr_execution_plan.megakernel_entry_round(),
        );
        assert_eq!(
            hook.continuation_projection.canonical_sources(),
            self.folding_addresses,
        );
        let canonical_sources = unwrap_dr_window(hook.megakernel_source_pointers(storage))?;
        assert_eq!(canonical_sources.len(), folding_poly_count);
        assert!(folding_poly_count <= DR_TAIL_MAX_SOURCES);
        let mut source_ptrs = [std::ptr::null(); DR_TAIL_MAX_SOURCES];
        source_ptrs[..folding_poly_count].copy_from_slice(&canonical_sources);

        let mut slots = [DrTailSlot::default(); DR_TAIL_SLOTS];
        for (slot_idx, slot) in self.layer_slots.iter_enabled() {
            let mut encoded = DrTailSlot::default();
            for (input_idx, address) in slot.inputs.iter().copied().enumerate() {
                let canonical = storage
                    .layout
                    .as_ref()
                    .and_then(|layout| layout.aliases.get(&address))
                    .copied()
                    .unwrap_or(address);
                let source_idx = self
                    .folding_addresses
                    .binary_search(&canonical)
                    .expect("DR-tail source must be in the canonical publication");
                encoded.input_source[input_idx] = source_idx as u16;
            }
            encoded.batch_exp = slot.batch_exp;
            slots[slot_idx] = encoded;
        }

        memory_copy_async(
            device_claim_point_out.slice_mut(0, self.folding_steps),
            device_claim_point_in.slice(0, self.folding_steps),
            stream,
        )?;

        launch_dr_window_r0(&hook, device_claim_point_out.as_ptr(), context)?;
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_active_eq_slot(&hook.r0_eq.eq_sizes, hook.r0_eq.eq_low.as_mut_ptr());
        launch_window_tensor_round_tail(
            &WindowTailState {
                partials: hook.r0_launch.binding.partials,
                row_tiles: hook.r0_launch.row_tiles,
                reduced_tensor: hook.r0_launch.reduced_tensor,
                prev_claim_coords: device_claim_point_out.as_ptr(),
                seed: device_seed.as_mut_ptr(),
                claim: device_claim.as_mut_ptr(),
                eq_prefactor: device_eq_prefactor.as_mut_ptr(),
                coeffs_out: coeffs_buffer_ptr,
                challenges_out: device_claim_point_out.as_mut_ptr(),
                active_eq_slot_base,
                active_eq_size_before_fold,
            },
            context,
        )?;
        storage.purge_up_to_layer(self.layer_idx);

        for pass in &hook.continuation_launches {
            launch_dr_window_continuation(&pass.launch, context)?;
            let (active_eq_slot_base, active_eq_size_before_fold) =
                resolve_dr_global_active_eq_slot(&pass.eq_entry);
            let start_round = pass.geometry.start_round;
            // SAFETY: the preflighted pass lies within the layer point and slab.
            let point = unsafe { device_claim_point_out.as_mut_ptr().add(start_round) };
            let coeffs_out = unsafe { coeffs_buffer_ptr.add(4 * start_round) };
            launch_window_tensor_round_tail(
                &WindowTailState {
                    partials: pass.launch.binding.partials,
                    row_tiles: pass.launch.row_tiles,
                    reduced_tensor: pass.launch.reduced_tensor,
                    prev_claim_coords: point.cast_const(),
                    seed: device_seed.as_mut_ptr(),
                    claim: device_claim.as_mut_ptr(),
                    eq_prefactor: device_eq_prefactor.as_mut_ptr(),
                    coeffs_out,
                    challenges_out: point,
                    active_eq_slot_base,
                    active_eq_size_before_fold,
                },
                context,
            )?;
        }

        let mut dr_tail_output: DeviceAllocation<E4> =
            context.alloc(folding_poly_count * 4, AllocationPlacement::Top)?;
        launch_dr_tail_megakernel_e4(
            DrTailMegakernelDesc {
                enabled_mask: self.layer_slots.enabled_mask(),
                folding_steps: self.folding_steps as u32,
                entry_round: hook.megakernel_entry_round as u32,
                source_count: folding_poly_count as u32,
                source_ptrs,
                final_sources: dr_tail_output.as_mut_ptr(),
                tau: device_claim_point_in.as_ptr(),
                seed: device_seed.as_mut_ptr(),
                claim: device_claim.as_mut_ptr(),
                eq_prefactor: device_eq_prefactor.as_mut_ptr(),
                coeffs_out: coeffs_buffer_ptr,
                challenges_out: device_claim_point_out.as_mut_ptr(),
                slots,
            },
            &dr_tail_capacity,
            context,
        )?;
        let transcript_input_sources =
            self.final_evaluation_sources_for_last_step(storage, &dr_tail_output, 4);
        let num_addresses = transcript_input_sources.len();
        assert!(
            num_addresses > 0,
            "dimension-reducing layer must produce a next-layer claim"
        );
        let last_evals_len = num_addresses * 4;
        let final_step_evals_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();

        // The transcript follows raw address order even when aliases share storage.
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
        drop(dr_tail_output);

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

        let device_next_claim_point = schedule_dim_reducing_next_layer_claim_point(
            &device_claim_point_out,
            self.folding_steps,
            context,
        )?;

        let next_claim_layout = ClaimBufferLayout::from_addresses(transcript_input_addresses);
        if let Some(layer_range) = layer_range {
            layer_range.end(stream)?;
            tracing_ranges.push(layer_range);
        }

        drop(device_claim);
        drop(device_eq_prefactor);
        drop(device_last_evals);
        drop(device_claim_point_in);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(DeviceClaimPointAndBatching::from_allocation(
                device_next_claim_point,
            )),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
        })
    }
}

/// Materializes the claim point handed to the next backward layer in plain
/// variable order (coordinate 0 first).
///
/// CPU authority: `prover/src/gkr/prover/sumcheck_loop/mod.rs:306-310` builds
/// `folding_challenges` as `[r_last, r_0, .., r_{n-1}]` — the end-of-layer
/// challenge `r_last` binds the gate bit, which is coordinate 0 of the polys
/// the next layer reads ("r_last actually binds a bit 0 in enumeration"), so it
/// LEADS the point and the round challenges follow. The next layer then consumes
/// the point untouched (`let tau: &[E] = &prev_challenges[..]`, same file).
///
/// `layer_out` is the shared `ab_gkr_dim_reducing_layer_claim_point` view this
/// layer wrote in DRAW order (`[r_0, .., r_{n-1}, r_last, batching]`), which is
/// the layout the continuation kernels require — they read round `step`'s
/// challenge from `ab_gkr_dim_reducing_layer_claim_point[step - 1]`
/// (`native/gkr/support/lookup_helpers.cuh:288`). The coordinate order is
/// therefore established on the way OUT, into a separate buffer no round writes.
pub(crate) fn schedule_dim_reducing_next_layer_claim_point(
    layer_out: &DeviceClaimPointAndBatching,
    folding_steps: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E4>> {
    let len = folding_steps + 2;
    assert_eq!(
        layer_out.len(),
        len,
        "layer output view must be [round challenges | end-of-layer challenge | batching]",
    );
    let stream = context.get_exec_stream();
    let mut next: DeviceAllocation<E4> = context.alloc(len, AllocationPlacement::Top)?;
    memory_copy_async(&mut next[..1], layer_out.slice(folding_steps, 1), stream)?;
    memory_copy_async(
        &mut next[1..1 + folding_steps],
        layer_out.slice(0, folding_steps),
        stream,
    )?;
    memory_copy_async(
        &mut next[1 + folding_steps..],
        layer_out.slice(folding_steps + 1, 1),
        stream,
    )?;
    Ok(next)
}
