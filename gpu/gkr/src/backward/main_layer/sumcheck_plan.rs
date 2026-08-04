use std::collections::BTreeMap;
use std::ptr::null_mut;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use crate::GpuGKRStorage;

use super::super::kernels::*;
use super::super::packed_main_layer_batch_challenge_len;
use super::super::{compact, flat};
use super::extras::{schedule_main_layer_extras_eval, MainLayerExtrasKeepalive};
use crate::proof_layout::ProofLayout;
use crate::upstream::{Field, FieldExtension, GKRAddress, Seed};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation};
use gpu_core::primitives::device_structures::DeviceVectorChunk;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_cub::cub::device_reduce::{reduce, Reduce, ReduceOperation};
use gpu_hash::blake2s::STATE_SIZE;
use gpu_ops::simple::{BinaryOp, Mul};
use gpu_prover_context::ProverContext;

impl<E: 'static> GpuGKRMainLayerSumcheckLayerPlan<E>
where
    // `GpuKernels` (not the sealed `BackwardKernels`): see ../../gpu_kernels.rs.
    E: Field + FieldExtension<BF> + Reduce + crate::GpuKernels,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn schedule_batch_challenge_buffer_on_device(
        &self,
        device_claim_point_in: &DeviceClaimPointAndBatching<E>,
        context: &ProverContext,
    ) -> CudaResult<ScheduledChallengeStorage<E>> {
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
        // at the end of this block. The subsequent `get_powers_by_ref` launch
        // is stream-ordered on `exec_stream`, so the buffer is populated before
        // any downstream consumer reads it.
        unsafe {
            // SAFETY: the freshly allocated challenge buffer is only re-viewed
            // at the concrete `E4` layout used by this scheduler.
            let dst_slice = storage
                .device
                .as_deref_mut()
                .expect("challenge storage device just allocated")
                .slice_mut(0, len);
            let dst_e4 = dst_slice.transmute_mut::<E4>();
            let batching_e4 = batching_slice.transmute::<E4>();
            gpu_ops::powers::get_powers_by_ref::<E4>(
                &batching_e4[0],
                0,
                dst_e4,
                context.get_exec_stream(),
            )?;
        }
        Ok(storage)
    }

    fn fold_eq_values_for_next_round(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        debug_assert!(acc_size.is_power_of_two());
        debug_assert!(acc_size >= 2);
        fold_factored_eq_one_round::<E>(
            &mut self.eq_sizes,
            self.round_scratch.eq_low_group.as_mut_ptr(),
            context,
        )
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_recipe_desc.is_some() || self.flat_recipe_desc_device.is_some(),
            "flat round 0 recipe descriptor must be scheduled"
        );
        let plan_compact = self
            .flat_round0_template_compact
            .as_ref()
            .expect("compact flat round 0 plan must be built");
        if self.flat_use_constant {
            compact::launch_main_round0_constant(
                &plan_compact.static_desc,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else {
            compact::launch_main_round0(
                &plan_compact.static_desc,
                self.flat_coeff_device_buf.as_ref().unwrap().as_ptr(),
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
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
            self.flat_cont_recipe_desc.is_some() || self.flat_cont_recipe_desc_device.is_some(),
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
        if let Some((devptr, bufs)) = self.flat_round1_terms_device.as_ref() {
            // Stage 3b device-terms path (terms/tiles + coeffs from device).
            compact::launch_main_round1_unified_devptr_terms(
                devptr,
                sizes.fold_stride,
                sizes.next_layer_size,
                self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr(),
                bufs.tables,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else if self.flat_cont_use_constant {
            compact::launch_main_round1_unified(
                compact_desc,
                sizes.fold_stride,
                sizes.next_layer_size,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else {
            compact::launch_main_round1_unified_devptr(
                compact_desc,
                sizes.fold_stride,
                sizes.next_layer_size,
                self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr(),
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        }
    }

    fn launch_round2_kernels_from_symbol(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some() || self.flat_cont_recipe_desc_device.is_some(),
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
        if let Some((devptr, bufs)) = self.flat_round2_terms_device.as_ref() {
            // Stage 3b device-terms path (terms/tiles + coeffs from device).
            compact::launch_main_round2_unified_devptr_terms(
                devptr,
                compact::get_main_layer_claim_point_device_ptr() as *const E,
                sizes.fold_stride,
                sizes.next_layer_size,
                self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr(),
                bufs.tables,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else if self.flat_cont_use_constant {
            compact::launch_main_round2_unified(
                compact_desc,
                compact::get_main_layer_claim_point_device_ptr() as *const E,
                sizes.fold_stride,
                sizes.next_layer_size,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        } else {
            compact::launch_main_round2_unified_devptr(
                compact_desc,
                compact::get_main_layer_claim_point_device_ptr() as *const E,
                sizes.fold_stride,
                sizes.next_layer_size,
                self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr(),
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                context,
            )
        }
    }

    fn launch_round3_kernels_from_symbol(
        &mut self,
        step: usize,
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.flat_cont_recipe_desc.is_some() || self.flat_cont_recipe_desc_device.is_some(),
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
        if let Some((_, devptr, bufs)) = self
            .flat_continuation_terms_device
            .iter()
            .find(|(s, _, _)| *s == step)
        {
            // Stage 3b device-terms path (terms/tiles + coeffs from device).
            return compact::launch_main_round3_unified_devptr_terms(
                devptr,
                sizes.fold_stride,
                sizes.next_layer_size,
                (step - 1) as u32,
                self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr(),
                bufs.tables,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                explicit_form,
                context,
            );
        }
        if self.flat_cont_use_constant {
            compact::launch_main_round3_unified(
                compact_desc,
                sizes.fold_stride,
                sizes.next_layer_size,
                (step - 1) as u32,
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                explicit_form,
                context,
            )
        } else {
            compact::launch_main_round3_unified_devptr(
                compact_desc,
                sizes.fold_stride,
                sizes.next_layer_size,
                (step - 1) as u32,
                self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr(),
                self.round_scratch.eq_low_group.as_ptr(),
                &self.eq_sizes,
                self.round_scratch.accumulator.as_mut_ptr(),
                acc_size as u32,
                explicit_form,
                context,
            )
        }
    }

    /// Warp-partial round-kernel launcher. `step == 0` uses the round-0
    /// warp-partial kernel; `step >= 1` uses the continuation warp-partial
    /// kernel for the matching round family (rounds 3+ all share the
    /// round-3 kernel). Requires `acc_size >= 32` — the warp shfl_xor
    /// inside the kernel uses a full 0xFFFFFFFF mask and would deadlock
    /// with dead lanes.
    fn launch_round_kernel_warp_partial(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        debug_assert!(acc_size >= 32);
        let partials_ptr = self.round_scratch.partials.as_mut_ptr() as *mut E4;
        let eq_low_ptr = self.round_scratch.eq_low_group.as_ptr() as *const E4;

        if step == 0 {
            // Round 0's warp-partial kernel only has a constant-coefficient
            // variant. A round-0 coefficient overflow is handled by the
            // unfused device-buffer path (`launch_main_round0`), not here.
            assert!(
                self.flat_use_constant,
                "warp-partial round-0 dispatch only supports the constant-coefficient path"
            );
            let plan_compact = self
                .flat_round0_template_compact
                .as_ref()
                .expect("compact flat round 0 plan must be built");
            return super::super::kernels::launch_main_round0_constant_warp_partial(
                &plan_compact.static_desc,
                eq_low_ptr,
                &self.eq_sizes,
                partials_ptr,
                acc_size as u32,
                context,
            );
        }

        match step {
            1 => {
                let sizes = self
                    .flat_round1_size_check()
                    .resolve(acc_size)
                    .expect("flat round 1 size check must be consistent");
                let compact_desc = self
                    .flat_round1_unified_desc_compact
                    .as_ref()
                    .expect("flat round 1 compact desc must be built");
                if let Some((devptr, bufs)) = self.flat_round1_terms_device.as_ref() {
                    super::super::kernels::launch_main_round1_unified_warp_partial_devptr_terms(
                        devptr,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr() as *const E4,
                        bufs.tables,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                } else if self.flat_cont_use_constant {
                    super::super::kernels::launch_main_round1_unified_warp_partial(
                        compact_desc,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                } else {
                    super::super::kernels::launch_main_round1_unified_warp_partial_devptr(
                        compact_desc,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr() as *const E4,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                }
            }
            2 => {
                let sizes = self
                    .flat_round2_size_check()
                    .resolve(acc_size)
                    .expect("flat round 2 size check must be consistent");
                let compact_desc = self
                    .flat_round2_unified_desc_compact
                    .as_ref()
                    .expect("flat round 2 compact desc must be built");
                if let Some((devptr, bufs)) = self.flat_round2_terms_device.as_ref() {
                    super::super::kernels::launch_main_round2_unified_warp_partial_devptr_terms(
                        devptr,
                        super::super::compact::get_main_layer_claim_point_device_ptr() as *const E4,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr() as *const E4,
                        bufs.tables,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                } else if self.flat_cont_use_constant {
                    super::super::kernels::launch_main_round2_unified_warp_partial(
                        compact_desc,
                        super::super::compact::get_main_layer_claim_point_device_ptr() as *const E4,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                } else {
                    super::super::kernels::launch_main_round2_unified_warp_partial_devptr(
                        compact_desc,
                        super::super::compact::get_main_layer_claim_point_device_ptr() as *const E4,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr() as *const E4,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                }
            }
            step => {
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
                if let Some((_, devptr, bufs)) = self
                    .flat_continuation_terms_device
                    .iter()
                    .find(|(s, _, _)| *s == step)
                {
                    return super::super::kernels::launch_main_round3_unified_warp_partial_devptr_terms(
                        devptr,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        (step - 1) as u32,
                        self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr() as *const E4,
                        bufs.tables,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    );
                }
                if self.flat_cont_use_constant {
                    super::super::kernels::launch_main_round3_unified_warp_partial(
                        compact_desc,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        (step - 1) as u32,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                } else {
                    super::super::kernels::launch_main_round3_unified_warp_partial_devptr(
                        compact_desc,
                        sizes.fold_stride,
                        sizes.next_layer_size,
                        (step - 1) as u32,
                        self.flat_cont_coeff_device_buf.as_ref().unwrap().as_ptr() as *const E4,
                        eq_low_ptr,
                        &self.eq_sizes,
                        partials_ptr,
                        acc_size as u32,
                        context,
                    )
                }
            }
        }
    }

    /// Fused-tail dispatcher for the warp-partial round kernels. The round
    /// kernel — round 0 or continuation — wrote `acc_size / 32` partial
    /// pairs to `partials[]`; this stage runs the mega-finalize-from-partials
    /// kernel to reduce + round-update + fold-eq.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_warp_partial_tail(
        &mut self,
        acc_size: usize,
        prev_claim_coord: *const E,
        seed: *mut u32,
        claim: *mut E,
        eq_prefactor: *mut E,
        coeffs_out: *mut E,
        challenge_out: *mut E,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let prev_e4 = prev_claim_coord as *const E4;
        let claim_e4 = claim as *mut E4;
        let eq_pref_e4 = eq_prefactor as *mut E4;
        let coeffs_e4 = coeffs_out as *mut E4;
        let chal_e4 = challenge_out as *mut E4;
        let eq_low_ptr_mut = self.round_scratch.eq_low_group.as_mut_ptr() as *mut E4;
        let partials_ptr = self.round_scratch.partials.as_mut_ptr() as *mut E4;
        let num_partials = super::super::kernels::warp_partial_count(acc_size);
        let (slot_base, slot_size_before_fold) =
            super::super::kernels::resolve_active_eq_slot(&self.eq_sizes, eq_low_ptr_mut);
        super::super::kernels::launch_backward_dual_finalize_from_partials(
            partials_ptr as *const E4,
            num_partials,
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
        super::super::kernels::record_active_eq_slot_fold(&mut self.eq_sizes);
        Ok(())
    }

    /// Main-layer variant of the device-only sumcheck accumulator reduction.
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
    ///   - lookup_add = `device_lookup_and_constraint_ptr[1]`;
    ///   - external = `external_challenges_ptr`.
    fn schedule_flat_eval_recipes(
        &mut self,
        device_claim_point_in: &DeviceClaimPointAndBatching<E>,
        device_lookup_and_constraint_ptr: *const E,
        external_challenges_ptr: *const E,
        context: &ProverContext,
    ) -> CudaResult<Callbacks<'static>> {
        // Either an inline descriptor or a device-pointer descriptor is present
        // (mutually exclusive; Stage 3c). No recipes at all => nothing to launch.
        if self.flat_recipe_desc.is_none() && self.flat_recipe_desc_device.is_none() {
            return Ok(Callbacks::new());
        }
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

        // Route to the device-pointer eval-recipes kernel when the recipe tables
        // overflowed the inline caps (Stage 3c); otherwise use the inline desc.
        if let Some(ref desc_device) = self.flat_recipe_desc_device {
            crate::eval_recipes::eval_recipes_e4_devptr(
                batch_base_ptr,
                lookup_mul_ptr,
                lookup_add_ptr,
                external_challenges_ptr,
                &desc_device.desc,
                self.flat_recipe_count,
                coeff_out_ptr,
                stream,
            )?;
        } else {
            let desc = self.flat_recipe_desc.as_ref().unwrap();
            crate::eval_recipes::eval_recipes_e4(
                batch_base_ptr,
                lookup_mul_ptr,
                lookup_add_ptr,
                external_challenges_ptr,
                desc,
                self.flat_recipe_count,
                coeff_out_ptr,
                stream,
            )?;
        }

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
        // Inline or device-pointer descriptor (mutually exclusive; Stage 3c). No
        // continuation recipes at all => nothing to launch.
        if self.flat_cont_recipe_desc.is_none() && self.flat_cont_recipe_desc_device.is_none() {
            return Ok(());
        }

        // Route the continuation coefficients to the `__constant__` symbol when
        // the count fits, else to the device buffer read by the devptr kernels.
        let coeff_out_ptr: *mut E4 = if self.flat_cont_use_constant {
            flat::get_constant_coefficients_device_ptr()
        } else {
            self.flat_cont_coeff_device_buf
                .as_mut()
                .unwrap()
                .as_mut_ptr()
                .cast()
        };
        let stream = context.get_exec_stream();

        // Route to the device-pointer eval-recipes kernel when the recipe tables
        // overflowed the inline caps (Stage 3c); otherwise use the inline desc.
        if let Some(ref desc_device) = self.flat_cont_recipe_desc_device {
            flat::eval_continuation_recipes_e4_devptr(
                batch_base_ptr,
                lookup_mul_ptr,
                lookup_add_ptr,
                external_challenges_ptr,
                &desc_device.desc,
                self.flat_cont_recipe_count,
                coeff_out_ptr,
                stream,
            )?;
        } else {
            let desc = self.flat_cont_recipe_desc.as_ref().unwrap();
            flat::eval_continuation_recipes_e4(
                batch_base_ptr,
                lookup_mul_ptr,
                lookup_add_ptr,
                external_challenges_ptr,
                desc,
                self.flat_cont_recipe_count,
                coeff_out_ptr,
                stream,
            )?;
        }

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

    // `device_lookup_and_constraint_ptr`/`device_external_challenges_ptr` are
    // opaque device pointers (into GPU memory the caller allocated): this
    // function only does host-side pointer arithmetic (`.add`) to derive
    // kernel-argument offsets, the same as the offsets it hands to
    // `KernelFunction::launch`. They are never dereferenced on the host, so
    // marking this `unsafe` would misrepresent the contract — the actual
    // safety precondition (a valid, sufficiently-large device allocation)
    // is on the GPU side, enforced by the kernels these offsets feed.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn schedule_execute_main_layer_from_workflow_state(
        &mut self,
        workflow_state: ScheduledBackwardWorkflowStateHandle<E>,
        mut device_seed: DeviceAllocation<u32>,
        device_claim_point_in: DeviceClaimPointAndBatching<E>,
        device_claims_in: DeviceAllocation<E>,
        claim_layout: &ClaimBufferLayout,
        device_lookup_and_constraint_ptr: *const E,
        device_external_challenges_ptr: *const E,
        // Same pattern as the dim-reducing scheduler: per-round kernels write
        // coeffs directly into the slab's `internal_round_coefficients` range
        // and the per-address gather writes directly into
        // `final_step_evaluations`.
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
        layer_slot: usize,
        mirror_layer_to_host: bool,
        // Read-only handle to the consolidated GKR storage. Used by the
        // main-layer extras eval path to resolve missing cached-relation
        // dependencies to their backing
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
            gpu_core::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());

        // `device_seed` is owned by the orchestrator across all backward
        // layers; the fused per-round kernel + end-of-layer device transcript
        // mutate it in place. Returned via `Execution::device_seed` for the
        // next layer.
        let mut device_claim: DeviceAllocation<E> = context.alloc(1, AllocationPlacement::Top)?;
        let mut device_eq_prefactor: DeviceAllocation<E> =
            context.alloc(1, AllocationPlacement::Top)?;
        // Every round — including the last (acc_size == 1) — emits a
        // univariate monomial, so `internal_round_coefficients` has
        // `folding_steps` entries. Matches the
        // `ProofLayout` allocation (`sumcheck_num_rounds * 4`).
        let coeffs_total_len = self.folding_steps * 4;
        // Per-round kernels write coeffs straight into the slab's
        // `internal_round_coefficients` range for this layer — no standalone
        // allocation, no post-loop slab D2D.
        let coeffs_buffer_ptr: *mut E = if coeffs_total_len > 0 {
            // SAFETY: `layer_slot` selects this layer's slab segment and
            // the returned region is validated against `coeffs_total_len`
            // immediately below.
            let (dst_ptr, dst_len) = unsafe {
                proof_layout
                    .backward_internal_coeffs_device_mut(proof_slab.as_ptr() as *mut u8, layer_slot)
            };
            debug_assert_eq!(
                dst_len, coeffs_total_len,
                "slab internal_round_coefficients range must match main-layer coeffs_total_len",
            );
            dst_ptr as *mut E
        } else {
            null_mut()
        };
        // Consume `[claim_point || batching_challenge]` directly from the
        // orchestrator-owned `device_claim_point_in`; build the factored eq
        // representation (high slabs in the `ab_gkr_eq_high` __constant__
        // symbol + `eq_low_group` buffer in global memory) from it (offset 1,
        // count folding_steps - 1). The main-layer flat compact consumer
        // kernels compute eq per-row inline from `(eq_low, eq_sizes)` via the
        // inline-eq helper (high slabs read from the __constant__ symbol).
        let claim_point_and_batching_len = self.folding_steps + 1;
        assert_eq!(
            device_claim_point_in.len(),
            claim_point_and_batching_len,
            "device claim_point input size must match this layer's folding_steps + 1",
        );
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
            crate::gkr_ops::build_combined_claim(
                claims_e4,
                batching_e4,
                &desc_pairs,
                claim_out_e4,
                eq_out_e4,
                stream,
            )?;
        }

        let batch_challenge_storage =
            self.schedule_batch_challenge_buffer_on_device(&device_claim_point_in, context)?;
        let flat_coeff_callbacks = self.schedule_flat_eval_recipes(
            &device_claim_point_in,
            device_lookup_and_constraint_ptr,
            device_external_challenges_ptr,
            context,
        )?;
        // Continuation kernel reads the same 4 challenges (batch-base, lookup
        // mul/add, external) via per-element pointers as the round-0 kernel above.
        // SAFETY: the validated input length is `folding_steps + 1`, so the
        // last slot still exists for the continuation path.
        let cont_batch_base_ptr =
            unsafe { device_claim_point_in.as_ptr().add(self.folding_steps) } as *const E4;
        let cont_lookup_mul_ptr = device_lookup_and_constraint_ptr as *const E4;
        // SAFETY: same invariant as the round-0 path above: the additive
        // lookup challenge is the second scalar in this contiguous pair.
        let cont_lookup_add_ptr = unsafe { device_lookup_and_constraint_ptr.add(1) } as *const E4;
        // Continuation eval_recipes is scheduled *inside* the sumcheck loop
        // after `launch_round0_kernels`: round-0 and continuation share the
        // `ab_gkr_flat_coefficients` __constant__ symbol, so scheduling the
        // continuation write here would clobber round-0's coefficients
        // before round-0's kernel reads them (both ops are stream-ordered
        // on `exec_stream`).
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
            // Warp-partial round kernel + fused tail when the block can
            // fill a full warp's worth of gids; otherwise reduce-fold-update
            // fallback. The warp shfl_xor in the warp-partial kernel uses a
            // full 0xFFFFFFFF mask, so `acc_size < 32` would deadlock with
            // dead lanes — late rounds run the unfused 5-launch path.
            //
            // Round 0's warp-partial kernel has only a constant-coefficient
            // variant. When round-0 coefficients overflow the `__constant__`
            // symbol (large delegations → `flat_use_constant == false`), fall
            // back to the unfused round-0 path (`launch_round0_kernels`), which
            // supports the device-buffer coeff loader. Fast-path circuits keep
            // the warp-partial path (their round-0 fits `__constant__`).
            let use_warp_partial = (self.flat_use_constant || step != 0) && acc_size >= 32;

            // Round-kernel launch.
            if use_warp_partial {
                self.launch_round_kernel_warp_partial(step, acc_size, context)?;
                if step == 0 {
                    self.schedule_flat_continuation_eval_recipes(
                        cont_batch_base_ptr,
                        cont_lookup_mul_ptr,
                        cont_lookup_add_ptr,
                        device_external_challenges_ptr as *const E4,
                        context,
                    )?;
                }
            } else if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
                // Round-0 kernel reads are now ordered before this point on
                // `exec_stream`; the continuation eval_recipes write can
                // safely target the shared `ab_gkr_flat_coefficients`
                // __constant__ symbol without clobbering round-0's input.
                self.schedule_flat_continuation_eval_recipes(
                    cont_batch_base_ptr,
                    cont_lookup_mul_ptr,
                    cont_lookup_add_ptr,
                    device_external_challenges_ptr as *const E4,
                    context,
                )?;
            } else {
                match step {
                    1 => self.launch_round1_kernels_from_symbol(acc_size, context)?,
                    2 => self.launch_round2_kernels_from_symbol(acc_size, context)?,
                    step => {
                        self.launch_round3_kernels_from_symbol(step, acc_size, false, context)?
                    }
                }
            }

            // SAFETY: `step < last_step <= folding_steps`, so the single-element
            // read lies inside the immutable input claim-point buffer.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(step, 1) };
            // SAFETY: `coeffs_buffer_ptr` is a subslice of the proof slab (via
            // `backward_internal_coeffs_device_mut`). The 4-element window is
            // in-bounds (`coeffs_total_len = folding_steps * 4`).
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4) };
            // SAFETY: `device_claim_point_out` was created with length
            // `folding_steps + 1`, and `step < last_step <= folding_steps`, so
            // this one-element output slot is in bounds and uniquely written by
            // this iteration.
            let challenge_slot = unsafe { device_claim_point_out.slice_mut(step, 1) };

            if use_warp_partial {
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
            } else {
                // Unfused reduce-fold-update fallback (small acc_size only).
                self.run_round_coefficients_reduction_device(step, acc_size, context)?;
                self.fold_eq_values_for_next_round(acc_size, context)?;
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
        }
        // Final round (step == last_step == folding_steps - 1, acc_size == 1).
        // The factored eq is fully consumed (identity), so the round runs in
        // monomial form (`explicit_form = false`) — the CPU `evaluate::<_, false>`
        // last round — and emits the `last_step`-th monomial + draws `last_r`
        // into `device_claim_point_out[last_step]`, WITHOUT folding eq again
        // (skip `fold_eq_values_for_next_round`). The `[E;2]` last-round line is
        // still read from the round storage by
        // `final_evaluation_sources_for_last_step(last_step)` below.
        self.launch_round3_kernels_from_symbol(last_step, 1, false, context)?;
        {
            // SAFETY: `last_step == folding_steps - 1`, so this input claim-point
            // coordinate (`z_{last_step}`) exists.
            let prev_coord_slice = unsafe { device_claim_point_in.slice(last_step, 1) };
            // SAFETY: `coeffs_total_len = folding_steps * 4`, so the
            // `last_step`-th 4-element window is in-bounds.
            let coeffs_round_slice =
                unsafe { DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(last_step * 4), 4) };
            // SAFETY: `device_claim_point_out` is length `folding_steps + 1`;
            // slot `last_step = folding_steps - 1` (= `last_r`) is in bounds and
            // uniquely written here.
            let challenge_slot = unsafe { device_claim_point_out.slice_mut(last_step, 1) };
            // No `fold_eq_values_for_next_round`: there is no next round and the
            // factored eq is the identity at `acc_size == 1`.
            self.run_round_coefficients_reduction_device(last_step, 1, context)?;
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

        // Coeffs already landed in the slab via the per-round kernels; no
        // post-loop slab D2D needed.

        // Device-side inter-layer transcript (main-layer variant). The
        // last round now emits its monomial + draws `last_r` in-loop; the
        // `[E;2]` last-round line is gathered into a TEMP buffer and reduced at
        // `last_r` into the single at-point evaluation that is BOTH the
        // next-layer claim and the degree-1 `final_step_evaluations` (written to
        // the slab, committed, and sent in the proof). We then squeeze the 1
        // remaining challenge `[next_batching_challenge]`.
        let transcript_input_sources = self.final_evaluation_sources_for_last_step(last_step);
        let num_addresses = transcript_input_sources.len();
        let last_evals_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();

        // TEMP `[E;2]` gather target (the slab now holds the degree-1 at-point
        // evals, not the raw line).
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
            gpu_hash::blake2s::gather_e_addresses(&src_ptrs, dst, stream)?;
        }

        // Slab destination for the degree-1 `final_step_evaluations` (BTreeMap
        // key order matches `final_step_eval_addresses`).
        let final_step_evals_buffer_ptr: *mut E = if num_addresses > 0 {
            // SAFETY: `layer_slot` selects this layer's slab segment; validated
            // against `num_addresses` immediately below.
            let (dst_ptr, dst_len) = unsafe {
                proof_layout.backward_final_step_evals_device_mut(
                    proof_slab.as_ptr() as *mut u8,
                    layer_slot,
                )
            };
            debug_assert_eq!(
                dst_len, num_addresses,
                "slab final_step_evaluations range must match main-layer num_addresses (degree 1)",
            );
            dst_ptr as *mut E
        } else {
            null_mut()
        };

        // Reduce the `[E;2]` line at `last_r` (drawn in-loop,
        // `claim_point_out[last_step]`) into the single at-point evaluation,
        // written directly into the slab final-step range.
        if num_addresses > 0 {
            // SAFETY: TEMP `[E;2]` buffer, E = E4, alive through the launch.
            let last_evals_e4 = unsafe {
                DeviceSlice::from_raw_parts(device_last_evals.as_ptr() as *const E4, last_evals_len)
            };
            // SAFETY: `claim_point_out[last_step]` is `last_r` (in-loop draw).
            let last_r_view = unsafe {
                DeviceSlice::from_raw_parts(
                    device_claim_point_out.as_ptr().add(last_step) as *const E4,
                    1,
                )
            };
            // SAFETY: slab final-step region, E = E4, `num_addresses` elements.
            let final_step_e4 = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    final_step_evals_buffer_ptr as *mut E4,
                    num_addresses,
                )
            };
            crate::gkr_ops::backward_new_claims_linear(
                last_evals_e4,
                last_r_view,
                final_step_e4,
                stream,
            )?;
        }

        // The CPU transcript commits one logical payload containing the
        // degree-1 final-step evaluations followed by every missing
        // cached-relation dependency, then squeezes the next batching
        // challenge. The proof layout carries the schedule-time address set in
        // that same BTreeMap order, including layer-0 base dependencies.
        let extra_addresses: Vec<GKRAddress> = proof_layout.backward[layer_slot]
            .extra_evaluations_addresses
            .clone();
        let extra_count = extra_addresses.len();
        if extra_count > 0 {
            assert!(
                storage.is_some(),
                "main-layer extras eval requires a storage handle; production callers must pass Some(&storage)"
            );
        }
        let total_new_claims_len = num_addresses + extra_count;

        // Device-side per-address `new_claims`: final-step evaluations first,
        // then cached-relation extras. Besides feeding the next layer, this
        // contiguous buffer is the exact logical transcript payload.
        let mut device_new_claims: DeviceAllocation<E> =
            context.alloc(total_new_claims_len.max(1), AllocationPlacement::Top)?;
        if num_addresses > 0 {
            // SAFETY: slab final-step region holds `num_addresses` live E evals.
            let final_step_src = unsafe {
                DeviceSlice::from_raw_parts(final_step_evals_buffer_ptr as *const E, num_addresses)
            };
            memory_copy_async(
                &mut device_new_claims[..num_addresses],
                final_step_src,
                stream,
            )?;
        }

        // Evaluate every missing cached-relation dependency at the full
        // folding point. The helper also writes the proof-slab extras range in
        // the same deterministic address order.
        let extras_keepalive: Option<MainLayerExtrasKeepalive<BF, E>> = if extra_count > 0 {
            // SAFETY: device_claim_point_out is `MAX_MAIN_LAYER_CLAIM_POINT_LEN`
            // long; `[0..folding_steps]` is in-bounds. The extras tail starts
            // at `device_new_claims[num_addresses]` and has `extra_count`
            // slots.
            let folding_point_ptr = device_claim_point_out.as_ptr();
            let trace_len = 1usize << self.folding_steps;
            let extras_dst_ptr = unsafe { device_new_claims.as_mut_ptr().add(num_addresses) };
            Some(schedule_main_layer_extras_eval::<E>(
                self.layer_idx,
                &extra_addresses,
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

        // SAFETY: E = E4 in every instantiation; the contiguous claim buffer
        // is byte-identical to the host `Vec<E4>` payload passed to
        // `commit_field_els`.
        let transcript_inputs_e = &device_new_claims[..total_new_claims_len];
        let transcript_inputs_u32 = unsafe { transcript_inputs_e.transmute::<u32>() };
        gpu_hash::blake2s::transcript_commit(&mut device_seed, transcript_inputs_u32, stream)?;

        // Squeeze the 1 remaining challenge `[next_batching_challenge]` into
        // `device_claim_point_out[folding_steps]`. `last_r` was drawn in-loop at
        // `claim_point_out[folding_steps - 1]`.
        // SAFETY: `folding_steps + 1 = next_claim_point_and_batching_len`, so the
        // slot is in-bounds, and only this scheduling site writes it.
        {
            let layer_challenges_dst =
                unsafe { device_claim_point_out.slice_mut(self.folding_steps, 1) };
            // SAFETY: E = E4 in every instantiation; matches host `draw_random_field_els::<BF, E4>`.
            let layer_challenges_dst_e4 = unsafe { layer_challenges_dst.transmute_mut::<E4>() };
            gpu_hash::blake2s::transcript_squeeze_e4(
                &mut device_seed,
                layer_challenges_dst_e4,
                stream,
            )?;
        }

        // `device_claim_point_out` is already populated in place — slots
        // `[0..last_step]` by the per-round update kernels (folding challenges)
        // and slots `[last_step..last_step + 2]` by the transcript squeeze
        // (`last_r`, `next_batching_challenge`). No post-loop pack copies.

        // Combined claim layout matches the transcript payload: final-step
        // inputs followed by missing cached-relation dependencies. The sets
        // are disjoint by construction.
        let mut combined_addresses = transcript_input_addresses.clone();
        combined_addresses.extend(extra_addresses.iter().copied());
        let next_claim_layout = ClaimBufferLayout::from_addresses(combined_addresses);
        let callback_addresses = next_claim_layout.addresses.clone();
        let mut final_readback_callbacks = Callbacks::new();
        if mirror_layer_to_host {
            // Fork exec -> d2h then join. Every D2H source below has been written on exec by
            // this point (d_layer_challenges via `transcript_squeeze_e4`, device_new_claims
            // via `backward_new_claims_linear`, device_seed/device_folding_challenges from
            // earlier work in this layer; coeffs and packed last-evals are now slab-direct
            // and not D2H'd here). The join lets exec wait for the per-layer D2Hs
            // before scheduling the final-readback callback and dropping the source
            // allocations at end of this function.
            // `last_r` is now drawn in-loop and lives among the folding
            // challenges `claim_point_out[0..folding_steps]`; only
            // `[next_batching_challenge]` is squeezed post-loop.
            let folding_steps = self.folding_steps;
            // SAFETY: these pinned host buffers are written by the D2H copies
            // below before any host callback reads them.
            let mut layer_challenges_host: HostAllocation<[E]> =
                unsafe { context.alloc_host_uninit_slice(1) };
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
                unsafe { context.alloc_host_uninit_slice(folding_steps) };
            let final_folding_challenges_accessor = final_folding_challenges_host.get_accessor();
            gpu_prover_context::transfer::fork_join_exec_to_d2h(
                stream,
                context.get_d2h_stream(),
                |d2h_stream| {
                    // SAFETY: `[folding_steps] = next_batching_challenge` was just
                    // written by the transcript squeeze on `stream`; d2h_stream
                    // waits on the fork event before this read.
                    let layer_challenges_src = unsafe {
                        DeviceSlice::from_raw_parts(
                            device_claim_point_out.as_ptr().add(folding_steps),
                            1,
                        )
                    };
                    memory_copy_async(
                        &mut layer_challenges_host,
                        layer_challenges_src,
                        d2h_stream,
                    )?;

                    // Single D2H of device-computed new_claims, including any
                    // cached-relation extras appended after the final-step
                    // evaluations.
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
                    // through the proof slab).
                    memory_copy_async(&mut final_seed_host, &device_seed, d2h_stream)?;
                    // SAFETY: `[0..folding_steps]` were written in-place by the
                    // per-round update kernels — slots `[0..folding_steps - 1]` by
                    // the loop rounds and `[folding_steps - 1]` (= `last_r`) by the
                    // in-loop final round.
                    let folding_src = unsafe {
                        DeviceSlice::from_raw_parts(device_claim_point_out.as_ptr(), folding_steps)
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
                    // seed captured here is already post-commit+squeeze; the 1
                    // post-loop challenge lives in `layer_challenges_host` and
                    // `last_r` is already among the folding challenges.
                    let state = shared_state_for_callback.get_mut();
                    state.seed = Seed(
                        <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                            .expect("seed readback has STATE_SIZE words")
                            .to_owned(),
                    );
                    state.folding_challenges.clear();
                    // Includes `last_r` at index `folding_steps - 1`.
                    state
                        .folding_challenges
                        .extend_from_slice(final_folding_challenges_accessor.get());

                    let [next_batching_challenge]: [E; 1] = layer_challenges_accessor
                        .get()
                        .try_into()
                        .expect("layer challenges D2H has length 1");
                    // `last_r` is already the last folding challenge — no push.
                    let new_claim_point = state.folding_challenges.clone();
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

        drop(device_claim);
        drop(device_eq_prefactor);
        // TEMP `[E;2]` gather buffer: freed (stream-ordered) after the
        // at-point reduce kernel that reads it has been scheduled.
        drop(device_last_evals);
        drop(device_claim_point_in);
        drop(device_claims_in);
        // Stream-ordered drop: every scheduled extras-eval kernel +
        // memcpy has been issued by this point, so the temporary
        // device buffers (eq_values, block_partials, reduction_temp)
        // and the extra-polynomial view Arc-clones can release here. The pool
        // defers the underlying free until exec_stream has progressed
        // past the writes.
        drop(extras_keepalive);
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            start_callbacks: Callbacks::new(),
            batch_challenge_storage,
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
