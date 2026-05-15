use std::collections::BTreeMap;
use std::ptr::{null, null_mut};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use crate::prover::gkr::GpuGKRStorage;

use super::super::kernels::*;
use super::super::packed_main_layer_batch_challenge_len;
use super::super::{compact, flat};
use super::extras::{schedule_main_layer_extras_eval, MainLayerExtrasKeepalive};
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

impl<E: 'static> GpuGKRMainLayerSumcheckLayerPlan<E>
where
    E: Field + FieldExtension<BF> + Reduce + crate::prover::gkr::GpuKernels,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn schedule_batch_challenge_buffer_on_device(
        &self,
        device_claim_point_in: &DeviceClaimPointAndBatching<E>,
        context: &ProverContext,
    ) -> CudaResult<(ScheduledChallengeStorage<E>, ScheduledChallengeBuffer<E>)> {
        let len = packed_main_layer_batch_challenge_len(&self.kernel_plans);
        assert!(
            len > 0,
            "main-layer batched execution requires at least one packed batch challenge"
        );
        // Static-blueprint main-layer plans never pre-populate `batch_challenges`;
        // every packed slot is `base^(offset + k)` for the single device-resident
        // batching challenge `base`. Assert so callers can't silently lose
        // pre-drawn values.
        assert!(
            self.kernel_plans
                .iter()
                .all(|k| k.batch_challenges.is_empty()),
            "schedule_batch_challenge_buffer_on_device requires static-blueprint specs",
        );
        let mut storage =
            ScheduledChallengeStorage::new(context.alloc(len, AllocationPlacement::Top)?);
        // Fill the packed buffer with powers of the device-resident batching
        // challenge — the last slot of the orchestrator-owned
        // `device_claim_point_in`.
        // SAFETY: `device_claim_point_in` has length `folding_steps + 1`, so the
        // final slot exists and is the batching challenge by construction.
        let batching_slice = unsafe { device_claim_point_in.slice(self.folding_steps, 1) };
        // SAFETY: `storage.device` was just allocated with capacity `len` and
        // no other view into it exists yet; the `&mut DeviceSlice` is dropped
        // before `storage.device_accessor()` is called below. The subsequent
        // `get_powers_by_ref` launch is stream-ordered on `exec_stream`, so the
        // buffer is populated before any downstream consumer reads it.
        unsafe {
            // SAFETY: the freshly allocated challenge buffer is only re-viewed
            // at the concrete `E4` layout used by this scheduler.
            let dst_slice = storage.device.slice_mut(0, len);
            let dst_e4 = dst_slice.transmute_mut::<E4>();
            let batching_e4 = batching_slice.transmute::<E4>();
            crate::ops::powers::get_powers_by_ref::<E4>(
                &batching_e4[0],
                0,
                false,
                dst_e4,
                context.get_exec_stream(),
            )?;
        }
        let buffer = ScheduledChallengeBuffer {
            device: storage.device_accessor(),
            offset: 0,
            len,
        };
        Ok((storage, buffer))
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
        assert!(
            self.flat_recipe_desc.is_some(),
            "flat round 0 recipe descriptor must be scheduled"
        );
        let plan_compact = self
            .flat_round0_template_compact
            .as_ref()
            .expect("compact flat round 0 plan must be built");
        if self.flat_use_constant {
            compact::launch_main_round0_constant(
                &plan_compact.static_desc,
                self.round_scratch.eq_values.as_ptr(),
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else {
            compact::launch_main_round0(
                &plan_compact.static_desc,
                self.flat_coeff_device_buf.as_ref().unwrap().as_ptr(),
                self.round_scratch.eq_values.as_ptr(),
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        }
    }

    fn launch_round1_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some(),
            "flat continuation recipe descriptor must be scheduled"
        );
        let sizes = self
            .flat_round1_size_check()
            .resolve(acc_size)
            .expect("flat round 1 size check must be consistent");
        let compact_desc = self
            .flat_round1_unified_desc_compact
            .as_ref()
            .expect("flat round 1 compact desc must be built");
        compact::launch_main_round1_unified(
            compact_desc,
            null(),
            sizes.fold_stride,
            sizes.next_layer_size,
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.accumulator.as_mut_ptr(),
            acc_size as u32,
            context,
        )
    }

    fn launch_round2_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some(),
            "flat continuation recipe descriptor must be scheduled"
        );
        let sizes = self
            .flat_round2_size_check()
            .resolve(acc_size)
            .expect("flat round 2 size check must be consistent");
        let compact_desc = self
            .flat_round2_unified_desc_compact
            .as_ref()
            .expect("flat round 2 compact desc must be built");
        compact::launch_main_round2_unified(
            compact_desc,
            compact::get_main_layer_claim_point_device_ptr() as *const E,
            sizes.fold_stride,
            sizes.next_layer_size,
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.accumulator.as_mut_ptr(),
            acc_size as u32,
            context,
        )
    }

    fn launch_round3_kernels_from_symbol(
        &mut self,
        step: usize,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some(),
            "flat continuation recipe descriptor must be scheduled"
        );
        let sizes = self
            .flat_round3_size_check(step)
            .resolve(acc_size)
            .unwrap_or_else(|| {
                panic!("flat round 3 size check must be consistent for step {step}")
            });
        let (_, compact_desc) = self
            .flat_continuation_unified_descs_compact
            .iter()
            .find(|(s, _)| *s == step)
            .unwrap_or_else(|| {
                panic!("flat continuation compact desc must be built for step {step}")
            });
        compact::launch_main_round3_unified(
            compact_desc,
            null(),
            sizes.fold_stride,
            sizes.next_layer_size,
            (step - 1) as u32,
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.accumulator.as_mut_ptr(),
            acc_size as u32,
            explicit_form,
            context,
        )
    }

    /// Main-layer variant of the device-only sumcheck accumulator reduction.
    fn run_round_coefficients_reduction_device(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let challenge_offset = step + 1;
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        let _ = (challenge_offset, challenge_count);
        let stream = context.get_exec_stream();
        // SAFETY: `reduction_temp_storage` owns a live device allocation sized
        // exactly to its backing buffer; this creates a temporary mutable view
        // for the two reductions below and no aliasing mutable view escapes it.
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

    /// Schedule eval_recipes on the GPU. Each challenge is read from its own
    /// existing device-resident pointer:
    ///   - batch_base = `device_claim_point_in[folding_steps]` (last slot,
    ///     advanced on-device by the previous layer's end-of-round squeeze);
    ///   - lookup_mul = `device_lookup_and_constraint_ptr[0]`;
    ///   - lookup_add = `device_lookup_and_constraint_ptr[1]`.
    /// Replaces the prior per-layer 3-element scratch buffer + 2 D2Ds; the
    /// kernel now reads each scalar through its own pointer.
    fn schedule_flat_eval_recipes(
        &mut self,
        device_claim_point_in: &DeviceClaimPointAndBatching<E>,
        device_lookup_and_constraint_ptr: *const E,
        external_challenges_ptr: *const E,
        context: &ProverContext,
    ) -> CudaResult<Callbacks<'static>> {
        let desc = match self.flat_recipe_desc {
            Some(ref desc) => desc,
            None => return Ok(Callbacks::new()),
        };
        let stream = context.get_exec_stream();

        // SAFETY: `device_claim_point_in` outlives this scheduling call (held
        // by the orchestrator across the full layer); `device_lookup_and_constraint_ptr`
        // points to 2 device-resident `E` scalars owned by the workflow scope
        // and stays allocated until all scheduled reads have completed on GPU.
        let batch_base_ptr =
            unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) } as *const E4;
        let lookup_mul_ptr = device_lookup_and_constraint_ptr as *const E4;
        // SAFETY: `device_lookup_and_constraint_ptr` points to two contiguous
        // `E` scalars; offset 1 is the additive lookup challenge.
        let lookup_add_ptr = unsafe { device_lookup_and_constraint_ptr.add(1) } as *const E4;
        let external_challenges_ptr = external_challenges_ptr as *const E4;

        // Determine output pointer for eval_recipes.
        let coeff_out_ptr: *mut E4 = if self.flat_use_constant {
            flat::get_constant_coefficients_device_ptr()
        } else {
            self.flat_coeff_device_buf
                .as_mut()
                .unwrap()
                .as_mut_ptr()
                .cast()
        };

        crate::prover::gkr::eval_recipes::eval_recipes_e4(
            batch_base_ptr,
            lookup_mul_ptr,
            lookup_add_ptr,
            external_challenges_ptr,
            desc,
            self.flat_recipe_count,
            coeff_out_ptr,
            stream,
        )?;

        Ok(Callbacks::new())
    }

    /// Schedule eval_recipes for continuation coefficients (rounds 3+).
    /// Reuses the round 0 challenges buffer (same 4 challenge values).
    /// Must be called AFTER schedule_flat_eval_recipes so the challenges
    /// buffer is already populated on the stream.
    fn schedule_flat_continuation_eval_recipes(
        &mut self,
        batch_base_ptr: *const E4,
        lookup_mul_ptr: *const E4,
        lookup_add_ptr: *const E4,
        external_challenges_ptr: *const E4,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let desc = match self.flat_cont_recipe_desc {
            Some(ref desc) => desc,
            None => return Ok(()),
        };

        let coeff_out_ptr: *mut E4 = flat::get_constant_continuation_coefficients_device_ptr();

        flat::eval_continuation_recipes_e4(
            batch_base_ptr,
            lookup_mul_ptr,
            lookup_add_ptr,
            external_challenges_ptr,
            desc,
            self.flat_cont_recipe_count,
            coeff_out_ptr,
            context.get_exec_stream(),
        )?;

        Ok(())
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        assert!(last_step >= 3, "main-layer final step must be in round 3+");
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let prepared = &kernel
                .round3_and_beyond_prepared
                .iter()
                .find(|prepared| prepared.step == last_step)
                .unwrap_or_else(|| panic!("missing round 3+ prepared storage for step {last_step}"))
                .prepared;
            for (address, source) in kernel
                .inputs
                .inputs_in_base
                .iter()
                .zip(prepared.base_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
            for (address, source) in kernel
                .inputs
                .inputs_in_extension
                .iter()
                .zip(prepared.extension_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    pub(crate) fn schedule_execute_main_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching<E>,
        device_claims_in: DeviceAllocation<E>,
        claim_layout: &ClaimBufferLayout,
        device_lookup_and_constraint_ptr: *const E,
        device_external_challenges_ptr: *const E,
        // Same pattern as the dim-reducing scheduler — when `Some` (production),
        // per-round kernels write coeffs directly into the slab's
        // `internal_round_coefficients` range and the per-address gather
        // writes directly into `final_step_evaluations` (B1 + B2). When
        // `None` (test paths), per-layer fallback device buffers are used.
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        mirror_layer_to_host: bool,
        // Read-only handle to the consolidated GKR storage. Used by the
        // main-layer extras eval path to resolve orphan output addresses
        // (`outputs[layer-1] − inputs[layer]`) to their backing
        // pointers without forcing additional allocations. Test paths
        // that don't exercise extras can pass `None` to skip extras work
        // entirely; production callers always pass `Some`.
        storage: Option<&GpuGKRStorage<BF, E>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.main.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        // Compute the per-layer combined_claim `(exp, claim_idx)` descriptor
        // consumed by `build_combined_claim`. Passed inline as kernel-arg
        // (`__grid_constant__`) — no device buffer, no per-layer H2D.
        // `EnforceConstraintsMaxQuadratic` kernels contribute no term (see
        // `compute_combined_claim`).
        let mut desc_pairs: Vec<u32> = Vec::new();
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            for (j, output) in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
                .enumerate()
            {
                desc_pairs.push((kernel.batch_challenge_offset + j) as u32);
                desc_pairs.push(claim_layout.claim_idx(output));
            }
        }
        let mut shared_state = Box::new(ScheduledMainLayerExecutionState {
            seed: Seed::default(),
            folding_challenges: Vec::with_capacity(self.folding_steps),
        });
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        // `device_seed` is owned by the orchestrator across all backward
        // layers; the fused per-round kernel + end-of-layer device transcript
        // mutate it in place. Returned via `Execution::device_seed` for the
        // next layer.
        let mut device_claim: DeviceAllocation<E> = context.alloc(1, AllocationPlacement::Top)?;
        let mut device_eq_prefactor: DeviceAllocation<E> =
            context.alloc(1, AllocationPlacement::Top)?;
        let coeffs_total_len = last_step * 4;
        // B1: per-round kernels write coeffs straight into the slab's
        // `internal_round_coefficients` range for this layer when `proof_slab`
        // is provided — no standalone allocation, no post-loop slab D2D. Test
        // paths fall back to a per-layer buffer.
        let mut fallback_device_coeffs: Option<DeviceAllocation<E>> = None;
        let coeffs_buffer_ptr: *mut E = if let Some(slab) = proof_slab {
            if coeffs_total_len > 0 {
                // SAFETY: `layer_slot` selects this layer's slab segment and
                // the returned region is validated against `coeffs_total_len`
                // immediately below.
                let (dst_ptr, dst_len) = unsafe {
                    proof_layout
                        .backward_internal_coeffs_device_mut(slab.as_ptr() as *mut u8, layer_slot)
                };
                debug_assert_eq!(
                    dst_len, coeffs_total_len,
                    "slab internal_round_coefficients range must match main-layer coeffs_total_len",
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
        // Consume `[claim_point || batching_challenge]` directly from the
        // orchestrator-owned `device_claim_point_in`; build `eq_group_tables`
        // + `eq_values` from it (offset 1, count folding_steps - 1) — same
        // pattern as the dim-reducing twin.
        let claim_point_and_batching_len = self.folding_steps + 1;
        assert_eq!(
            device_claim_point_in.len(),
            claim_point_and_batching_len,
            "device claim_point input size must match this layer's folding_steps + 1",
        );
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
            // SAFETY: every instantiation uses `E = E4`, so these reinterprets
            // are byte-for-byte views over live device buffers with identical
            // ext-field layout.
            let claims_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_claims_in[..claim_layout.len()].transmute::<E4>() };
            // SAFETY: the last slot of `device_claim_point_in` is the batching
            // challenge and exists because its length is `folding_steps + 1`.
            let batching_slice = unsafe { device_claim_point_in.slice(self.folding_steps, 1) };
            // SAFETY: same concrete-layout reinterpret as the claims buffer.
            let batching_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { batching_slice.transmute::<E4>() };
            // SAFETY: the one-element outputs are allocated as `E` and viewed
            // at the concrete `E4` layout used by the kernel helper.
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

        let (batch_challenge_storage, batch_challenge_buffer) =
            self.schedule_batch_challenge_buffer_on_device(&device_claim_point_in, context)?;
        let flat_coeff_callbacks = self.schedule_flat_eval_recipes(
            &device_claim_point_in,
            device_lookup_and_constraint_ptr,
            device_external_challenges_ptr,
            context,
        )?;
        // Continuation kernel reads the same 3 challenges via per-element
        // pointers as the round-0 kernel above.
        // SAFETY: the validated input length is `folding_steps + 1`, so the
        // last slot still exists for the continuation path.
        let cont_batch_base_ptr =
            unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) } as *const E4;
        let cont_lookup_mul_ptr = device_lookup_and_constraint_ptr as *const E4;
        // SAFETY: same invariant as the round-0 path above: the additive
        // lookup challenge is the second scalar in this contiguous pair.
        let cont_lookup_add_ptr = unsafe { device_lookup_and_constraint_ptr.add(1) } as *const E4;
        self.schedule_flat_continuation_eval_recipes(
            cont_batch_base_ptr,
            cont_lookup_mul_ptr,
            cont_lookup_add_ptr,
            device_external_challenges_ptr as *const E4,
            context,
        )?;
        // Hoisted: `device_claim_point_out` holds the next layer's
        // `[claim_point || batching_challenge]` buffer. Slots `[0..folding_steps - 1]`
        // are written in-place by the per-round update kernels; slots
        // `[folding_steps - 1..folding_steps + 1]` are written by the
        // post-loop transcript squeeze.
        //
        // Round-N kernels read directly from `device_claim_point_out`:
        // - round 1 reads `[0..1]` (= c_0)
        // - round 2 reads `[0..2]` (= c_0, c_1) — the prior round's contiguous prefix
        // - round ≥ 3 reads `[step - 1..step]` (= c_{step - 1}, the just-produced challenge)
        // No packing buffer or per-round D2D needed.
        let next_claim_point_and_batching_len = self.folding_steps + 1;
        assert!(
            next_claim_point_and_batching_len <= compact::MAX_MAIN_LAYER_CLAIM_POINT_LEN,
            "main-layer claim point length {} exceeds __constant__ symbol capacity {}",
            next_claim_point_and_batching_len,
            compact::MAX_MAIN_LAYER_CLAIM_POINT_LEN
        );
        // SAFETY: the constant-buffer symbol is provisioned for
        // `MAX_MAIN_LAYER_CLAIM_POINT_LEN`; the checked length above keeps the
        // mutable view in bounds for the whole layer.
        let mut device_claim_point_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                compact::get_main_layer_claim_point_device_ptr() as *mut E,
                next_claim_point_and_batching_len,
            )
        };

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels_from_symbol(acc_size, context)?,
                    2 => self.launch_round2_kernels_from_symbol(acc_size, context)?,
                    step => {
                        self.launch_round3_kernels_from_symbol(step, acc_size, false, context)?
                    }
                }
            }

            // Device-only reduction into round_scratch.reduction_output.
            self.run_round_coefficients_reduction_device(step, acc_size, context)?;
            self.fold_eq_values_for_next_round(acc_size, context)?;

            // Fused per-round update: reads (seed, claim, eq_prefactor) +
            // (e, c) reduction output + prev_coord; writes updated state,
            // pushes the round's 4 coefficients into device_coeffs at
            // [step*4..step*4+4], and emits the next folding challenge
            // directly into `claim_point_out[step]`.
            // SAFETY: `step < last_step <= folding_steps`, so the single-element
            // read lies inside the immutable input claim-point buffer.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(step, 1) };
            // SAFETY: see the dim-reducing twin — the coeffs buffer is either
            // a slab subslice (held alive by `_proof_slab` keepalive) or
            // `fallback_device_coeffs` (dropped after every kernel that writes
            // through this pointer is scheduled). The 4-element window is
            // in-bounds (`coeffs_total_len = last_step * 4`).
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            // SAFETY: `device_claim_point_out` was created with length
            // `folding_steps + 1`, and `step < last_step <= folding_steps`, so
            // this one-element output slot is in bounds and uniquely written by
            // this iteration.
            let challenge_slot = unsafe { device_claim_point_out.slice_mut(step, 1) };
            E::launch_backward_sumcheck_round_update(
                &self.round_scratch.reduction_output,
                prev_coord_slice,
                &mut device_seed,
                &mut device_claim,
                &mut device_eq_prefactor,
                coeffs_round_slice,
                challenge_slot,
                stream,
            )?;
        }
        self.launch_round3_kernels_from_symbol(last_step, 1, true, context)?;

        // B1: coeffs already landed in the slab via the per-round kernels
        // (or in `fallback_device_coeffs` for test paths). No post-loop slab
        // D2D needed.

        // Device-side inter-layer transcript (main-layer variant): pack the
        // flattened last-round evaluations (2 E per address, vs 4 in dim-
        // reducing) — written **directly into the slab** via B2. Absorbed
        // into device_seed via transcript_commit, then squeezed into 2 E4
        // challenges `[last_r, next_batching_challenge]`. The same packed
        // buffer feeds `backward_new_claims_linear`.
        let transcript_input_sources = self.final_evaluation_sources_for_last_step(last_step);
        let num_addresses = transcript_input_sources.len();
        let transcript_inputs_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();
        // B2: per-address gather writes straight into the slab's
        // `final_step_evaluations` range. Flat layout (2 E per address, in
        // BTreeMap key order from `final_evaluation_sources_for_last_step`)
        // matches what `build_proof_layout_inputs` stored in
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
                    "slab final_step_evaluations range must match main-layer transcript_inputs_len",
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
        // B7: per-address gather kernel for the main-layer variant (2 E per
        // address). Pointer table rides inline in the kernel-arg struct; see
        // the dim-reducing twin for context.
        if num_addresses > 0 {
            let src_ptrs: Vec<u64> = transcript_input_sources
                .values()
                .map(|p| *p as u64)
                .collect();
            // SAFETY: the slab/fallback transcript-input buffer was allocated
            // for `transcript_inputs_len` ext elements; reinterpreting it as an
            // `E4` slice matches the only instantiated extension layout.
            let dst = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    transcript_inputs_buffer_ptr as *mut E4,
                    transcript_inputs_len,
                )
            };
            crate::ops::blake2s::gather_e_addresses(&src_ptrs, dst, 2, stream)?;
        }

        // SAFETY: E = E4 in every instantiation of this scheduler. The
        // slab/fallback memory is alive through the kernel launch, and
        // `transcript_commit` only reads.
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

        // Squeeze the 2 layer challenges directly into the tail of
        // `device_claim_point_out` — slots
        // `[last_step..last_step + 2] = [last_r, next_batching_challenge]`.
        // SAFETY: `last_step + 2 = folding_steps + 1 = next_claim_point_and_batching_len`,
        // so the range is in-bounds, and only this scheduling site writes it.
        {
            let layer_challenges_dst = unsafe { device_claim_point_out.slice_mut(last_step, 2) };
            // SAFETY: E = E4 in every instantiation; matches host `draw_random_field_els::<BF, E4>`.
            let layer_challenges_dst_e4 = unsafe { layer_challenges_dst.transmute_mut::<E4>() };
            crate::ops::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst_e4,
                stream,
            )?;
        }

        // Look up orphan addresses for this layer's slot. These are
        // `outputs[layer_idx - 1] − inputs[layer_idx]` (i.e., layer-(L-1)
        // kernel outputs that L's kernels do NOT consume) and must be
        // explicitly evaluated at the just-produced folding point so
        // L-1's `desc_pairs` build can resolve them in its IN claim
        // layout. See [backward.rs] `compute_main_layer_orphan_output_addresses_per_layer`
        // for the producer side. Empty for `layer_idx == 0` and for
        // any layer that consumes every immediate-child output.
        let orphan_addresses: Vec<GKRAddress> = proof_layout.backward[layer_slot]
            .extra_evaluations_addresses
            .clone();
        let orphan_count = orphan_addresses.len();
        if orphan_count > 0 {
            assert!(
                storage.is_some(),
                "main-layer extras eval requires a storage handle; production callers must pass Some(&storage)"
            );
        }
        let total_new_claims_len = num_addresses + orphan_count;

        // Device-side per-address `new_claims` evaluator (main-layer variant:
        // interpolate `v0, v1` at `last_r`). Replaces the host loop inside the
        // final readback callback. Allocation extends by `orphan_count` so
        // the on-device extras kernel can write extras into the tail.
        let mut device_new_claims: DeviceAllocation<E> =
            context.alloc(total_new_claims_len.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: E = E4 in every instantiation; transmutes match the
            // kernel's `e4` view of the packed evals and challenges. The
            // slab/fallback memory is alive through the kernel launch.
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
            // `claim_point_out[last_step..last_step + 2]`; reading the first
            // element (`last_r`) for the kernel.
            let challenges_view = unsafe {
                DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr().add(last_step), 1)
            };
            // SAFETY: the just-squeezed challenge tail is stored in the same
            // concrete `E4` layout that the kernel helper expects.
            let challenges_e4: &era_cudart::slice::DeviceSlice<E4> =
                unsafe { challenges_view.transmute::<E4>() };
            // SAFETY: `device_new_claims` was allocated as `E` and is viewed at
            // the concrete `E4` layout used by the kernel helper.
            let new_claims_e4: &mut era_cudart::slice::DeviceSlice<E4> =
                unsafe { device_new_claims[..num_addresses].transmute_mut::<E4>() };
            crate::ops::blake2s::backward_new_claims_linear(
                transcript_inputs_e4,
                challenges_e4,
                new_claims_e4,
                stream,
            )?;
        }

        // Schedule on-device evaluation of orphan output polys at the
        // full folding point `[r_0..r_{last_step-1}, last_r]`
        // (= `device_claim_point_out[0..self.folding_steps]`). Each
        // orphan's claim is written into:
        //   - `device_new_claims[num_addresses..num_addresses + orphan_count]`
        //     (tail) so the next layer's IN claim buffer carries it; and
        //   - `proof_layout.backward[layer_slot].extra_evaluations` slab
        //     range so the verifier can read the explicit at-point evals.
        // Returns a keepalive that holds eq_values, block_partials,
        // reduction_temp, and the orphan poly views (Arc-clones of the
        // consolidated backings) until exec_stream has finished every
        // kernel reading them. Drop happens at end of scheduler — same
        // pattern as `fallback_d_layer_transcript_inputs`.
        let extras_keepalive: Option<MainLayerExtrasKeepalive<BF, E>> = if orphan_count > 0 {
            // SAFETY: device_claim_point_out is `MAX_MAIN_LAYER_CLAIM_POINT_LEN`
            // long; `[0..folding_steps]` is in-bounds. The orphan eval
            // tail starts at `device_new_claims[num_addresses]`.
            let folding_point_ptr = device_claim_point_out.as_ptr();
            let trace_len = 1usize << self.folding_steps;
            // SAFETY: `device_new_claims` was allocated with
            // `num_addresses + orphan_count` slots, so the orphan tail starts
            // at `num_addresses` and has capacity for exactly `orphan_count`
            // outputs.
            let extras_dst_ptr = unsafe { device_new_claims.as_mut_ptr().add(num_addresses) };
            Some(schedule_main_layer_extras_eval::<E>(
                self.layer_idx,
                &orphan_addresses,
                storage.expect("extras eval requires storage handle"),
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

        // `device_claim_point_out` is already populated in place — slots
        // `[0..last_step]` by the per-round update kernels (folding challenges)
        // and slots `[last_step..last_step + 2]` by the transcript squeeze
        // (`last_r`, `next_batching_challenge`). No post-loop pack copies.

        // Combined claim layout = transcript inputs (in BTreeMap key order)
        // followed by orphans (in BTreeSet order). Orphans are disjoint from
        // transcript inputs by construction (orphan = layer-(L-1) output not
        // consumed by L), so the combined Vec has no duplicates.
        let mut combined_addresses = transcript_input_addresses.clone();
        combined_addresses.extend(orphan_addresses.iter().copied());
        let next_claim_layout = ClaimBufferLayout::from_addresses(combined_addresses);
        let callback_addresses = next_claim_layout.addresses.clone();
        let mut final_readback_callbacks = Callbacks::new();
        if mirror_layer_to_host {
            // Fork exec -> d2h then join. Every D2H source below has been written on exec by
            // this point (d_layer_challenges via `transcript_squeeze_e4`, device_new_claims
            // via `backward_new_claims_linear`, device_seed/device_folding_challenges from
            // earlier work in this layer; coeffs and packed last-evals are now slab-direct
            // via B1/B2 and not D2H'd here). The join lets exec wait for the per-layer D2Hs
            // before scheduling the final-readback callback and dropping the source
            // allocations at end of this function.
            // SAFETY: these pinned host buffers are written by the D2H copies
            // below before any host callback reads them.
            let mut layer_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(2) };
            let layer_challenges_accessor = layer_challenges_host.get_accessor();
            let mut new_claims_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(total_new_claims_len.max(1)) };
            let new_claims_accessor = new_claims_host.get_accessor();
            // SAFETY: same D2H-destination invariant as above for the seed and
            // folding-challenge mirrors.
            let mut final_seed_host = unsafe { context.alloc_host_uninit_slice(STATE_SIZE) };
            let final_seed_accessor = final_seed_host.get_accessor();
            // SAFETY: this pinned host buffer is also a pure D2H destination
            // before the final callback consumes it.
            let mut final_folding_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(last_step) };
            let final_folding_challenges_accessor = final_folding_challenges_host.get_accessor();
            crate::primitives::transfer::fork_join_exec_to_d2h(
                stream,
                context.get_d2h_stream(),
                |d2h_stream| {
                    // SAFETY: `[last_step..last_step + 2]` were just written by the
                    // transcript squeeze on `stream`; d2h_stream waits on the fork event
                    // before this read.
                    let layer_challenges_src = unsafe {
                        DeviceSlice::from_raw_parts(
                            device_claim_point_out.as_ptr().add(last_step),
                            2,
                        )
                    };
                    memory_copy_async(
                        &mut layer_challenges_host,
                        layer_challenges_src,
                        d2h_stream,
                    )?;

                    // Single D2H of device-computed new_claims, including any orphan
                    // extras the on-device extras kernel appended at
                    // `[num_addresses..num_addresses + orphan_count]`.
                    if total_new_claims_len > 0 {
                        memory_copy_async(
                            &mut new_claims_host,
                            &device_new_claims[..total_new_claims_len],
                            d2h_stream,
                        )?;
                    }

                    // D2H the on-device per-layer state that the final readback needs to
                    // advance the workflow (seed + folding challenges for WHIR host
                    // setup; coeffs and packed last-evaluations stay on device and flow
                    // through the proof slab via B1/B2).
                    memory_copy_async(&mut final_seed_host, &device_seed, d2h_stream)?;
                    // SAFETY: `[0..last_step]` were written in-place by the per-round
                    // update kernels.
                    let folding_src = unsafe {
                        DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr(), last_step)
                    };
                    memory_copy_async(&mut final_folding_challenges_host, folding_src, d2h_stream)?;
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
                    // seed captured here is already post-commit+squeeze; the 2
                    // challenges live in `layer_challenges_host`.
                    let state = shared_state_for_callback.get_mut();
                    state.seed = Seed(
                        <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                            .expect("seed readback has STATE_SIZE words")
                            .to_owned(),
                    );
                    state.folding_challenges.clear();
                    state
                        .folding_challenges
                        .extend_from_slice(final_folding_challenges_accessor.get());

                    let [last_r, next_batching_challenge]: [E; 2] = layer_challenges_accessor
                        .get()
                        .try_into()
                        .expect("layer challenges D2H has length 2");
                    let mut new_claim_point = state.folding_challenges.clone();
                    new_claim_point.push(last_r);
                    // Rebuild `new_claims` from the D2H'd device-computed buffer
                    // (host `interpolate_linear` loop is now a kernel).
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
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(fallback_d_layer_transcript_inputs);
        drop(device_claim);
        drop(device_eq_prefactor);
        drop(fallback_device_coeffs);
        drop(device_claim_point_in);
        drop(device_claims_in);
        // Stream-ordered drop: every scheduled extras-eval kernel +
        // memcpy has been issued by this point, so the temporary
        // device buffers (eq_values, block_partials, reduction_temp)
        // and the orphan view Arc-clones can release here. The pool
        // defers the underlying free until exec_stream has progressed
        // past the writes.
        drop(extras_keepalive);
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            start_callbacks: Callbacks::new(),
            batch_challenge_storage,
            batch_challenge_buffer,
            final_readback: final_readback_callbacks,
            flat_coeff_callbacks,
            recipe_upload_callbacks: std::mem::replace(
                &mut self.recipe_upload_callbacks,
                Callbacks::new(),
            ),
            shared_state,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(device_claim_point_out),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
        })
    }
}
