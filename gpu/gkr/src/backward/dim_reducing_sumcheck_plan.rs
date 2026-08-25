use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};

use super::dr_tail::resources::DrTailScheduleError;
use super::dr_tail::{
    launch_dr_tail_megakernel_e4, DrTailCapacityDecision, DrTailMegakernelDesc, DrTailSlot,
    DR_TAIL_MAX_SOURCES, DR_TAIL_SLOTS,
};
use super::window::tail::{launch_window_tensor_round_tail, WindowTailArm, WindowTailState};
use super::window_dr::{
    launch_dr_window_continuation, launch_dr_window_r0, resolve_dr_global_active_eq_slot,
    validate_dr_window_final_publication_stride, DrWindowBindError, DrWindowContinuationReadiness,
    DrWindowLayerCompositionHook,
};
use super::{dim_reducing_encoder, kernels::*};
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrLayerExecutionStage {
    R0,
    Continuation(usize),
    Megakernel,
    LegacyDiagnostic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrLayerExecutionSelection {
    CompleteNewChain { continuation_count: usize },
    LegacyDiagnostic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DrFinalPublicationContract {
    owner_log2_stride: u32,
    planned_log2_stride: u32,
    planned_per_poly_len: usize,
    selected_log2_stride: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrLayerExecutionContract {
    common_eq_owner_count: usize,
    final_publication: Option<DrFinalPublicationContract>,
}

impl DrLayerExecutionContract {
    fn from_hook(hook: &DrWindowLayerCompositionHook) -> Self {
        let final_publication = hook.continuation_launches.last().map(|last| {
            let owner = hook
                .continuation_arenas
                .get(last.geometry.destination)
                .expect("the final continuation destination must remain owned");
            DrFinalPublicationContract {
                owner_log2_stride: owner.binding().log2_stride,
                planned_log2_stride: last.geometry.log2_stride,
                planned_per_poly_len: last.geometry.per_poly_len,
                selected_log2_stride: last.geometry.log2_stride,
            }
        });
        Self {
            common_eq_owner_count: hook.r0_eq.owner_count,
            final_publication,
        }
    }

    fn validate(self) -> Result<(), DrTailScheduleError> {
        if self.common_eq_owner_count != 1 {
            return Err(DrTailScheduleError::DuplicateEqOwner {
                observed: self.common_eq_owner_count,
            });
        }
        if let Some(final_publication) = self.final_publication {
            validate_dr_window_final_publication_stride(
                final_publication.owner_log2_stride,
                final_publication.planned_log2_stride,
                final_publication.planned_per_poly_len,
                final_publication.selected_log2_stride,
            )
            .map_err(dr_window_schedule_error)?;
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) const fn minimal_valid_for_test() -> Self {
        Self {
            common_eq_owner_count: 1,
            final_publication: None,
        }
    }
}

struct DrLayerExecutionStages {
    selection: DrLayerExecutionSelection,
    next: usize,
}

impl DrLayerExecutionStages {
    fn new(selection: DrLayerExecutionSelection) -> Self {
        Self { selection, next: 0 }
    }
}

impl Iterator for DrLayerExecutionStages {
    type Item = DrLayerExecutionStage;

    fn next(&mut self) -> Option<Self::Item> {
        let stage = match self.selection {
            DrLayerExecutionSelection::CompleteNewChain { continuation_count } => {
                if self.next == 0 {
                    Some(DrLayerExecutionStage::R0)
                } else if self.next <= continuation_count {
                    Some(DrLayerExecutionStage::Continuation(self.next - 1))
                } else if self.next == continuation_count + 1 {
                    Some(DrLayerExecutionStage::Megakernel)
                } else {
                    None
                }
            }
            DrLayerExecutionSelection::LegacyDiagnostic => {
                (self.next == 0).then_some(DrLayerExecutionStage::LegacyDiagnostic)
            }
        };
        self.next += usize::from(stage.is_some());
        stage
    }
}

pub(crate) fn schedule_dr_layer_execution<E: From<DrTailScheduleError>>(
    contract: Option<&DrLayerExecutionContract>,
    selection: DrLayerExecutionSelection,
    #[cfg(test)] mut observer: Option<&mut dyn FnMut(DrLayerExecutionStage)>,
    mut launch: impl FnMut(DrLayerExecutionStage) -> Result<(), E>,
) -> Result<(), E> {
    if matches!(
        selection,
        DrLayerExecutionSelection::CompleteNewChain { .. }
    ) {
        contract
            .ok_or(DrTailScheduleError::MissingCompleteChainContract)
            .and_then(|contract| contract.validate())
            .map_err(E::from)?;
    }
    for stage in DrLayerExecutionStages::new(selection) {
        #[cfg(test)]
        if let Some(observer) = observer.as_deref_mut() {
            observer(stage);
        }
        launch(stage)?;
    }
    Ok(())
}

fn dr_window_schedule_error(error: DrWindowBindError) -> DrTailScheduleError {
    match error {
        DrWindowBindError::Cuda(error) => DrTailScheduleError::Cuda(error),
        DrWindowBindError::FinalPublicationStrideMismatch {
            owner_log2_stride,
            planned_log2_stride,
            planned_per_poly_len,
            selected_log2_stride,
        } => DrTailScheduleError::FinalPublicationStrideMismatch {
            owner_log2_stride,
            planned_log2_stride,
            planned_per_poly_len,
            selected_log2_stride,
        },
        error => DrTailScheduleError::WindowBinding {
            detail: format!("{error:?}"),
        },
    }
}

#[cfg(test)]
mod stage_dispatch_tests {
    use super::*;

    use crate::backward::window_dr::plan_dr_window_continuations;

    fn production_contract() -> DrLayerExecutionContract {
        let passes = plan_dr_window_continuations(24, 4, 15).unwrap();
        let last = passes.last().unwrap();
        let owner = passes
            .iter()
            .find(|pass| pass.destination == last.destination)
            .unwrap();
        assert!(owner.log2_stride > last.log2_stride);
        DrLayerExecutionContract {
            common_eq_owner_count: 1,
            final_publication: Some(DrFinalPublicationContract {
                owner_log2_stride: owner.log2_stride,
                planned_log2_stride: last.log2_stride,
                planned_per_poly_len: last.per_poly_len,
                selected_log2_stride: last.log2_stride,
            }),
        }
    }

    fn dispatch(
        contract: &DrLayerExecutionContract,
    ) -> (
        Result<(), DrTailScheduleError>,
        Vec<DrLayerExecutionStage>,
        Vec<DrLayerExecutionStage>,
    ) {
        let mut observed = Vec::new();
        let mut launched = Vec::new();
        let mut observer = |stage| observed.push(stage);
        let result = schedule_dr_layer_execution(
            Some(contract),
            DrLayerExecutionSelection::CompleteNewChain {
                continuation_count: 4,
            },
            Some(&mut observer),
            |stage| {
                launched.push(stage);
                Ok(())
            },
        );
        (result, observed, launched)
    }

    #[test]
    fn cpu_complete_chain_observer_is_the_production_enqueue_boundary() {
        let (result, observed, launched) = dispatch(&production_contract());
        assert_eq!(result, Ok(()));
        assert_eq!(
            observed,
            [
                DrLayerExecutionStage::R0,
                DrLayerExecutionStage::Continuation(0),
                DrLayerExecutionStage::Continuation(1),
                DrLayerExecutionStage::Continuation(2),
                DrLayerExecutionStage::Continuation(3),
                DrLayerExecutionStage::Megakernel,
            ]
        );
        assert_eq!(launched, observed);
    }

    #[test]
    fn cpu_wrong_final_stride_dispatch_rejects_without_retry() {
        let mut contract = production_contract();
        let final_publication = contract.final_publication.as_mut().unwrap();
        final_publication.selected_log2_stride = final_publication.owner_log2_stride;
        let expected = DrTailScheduleError::FinalPublicationStrideMismatch {
            owner_log2_stride: final_publication.owner_log2_stride,
            planned_log2_stride: final_publication.planned_log2_stride,
            planned_per_poly_len: final_publication.planned_per_poly_len,
            selected_log2_stride: final_publication.owner_log2_stride,
        };
        let (result, observed, launched) = dispatch(&contract);
        assert_eq!(result, Err(expected));
        assert!(observed.is_empty());
        assert!(launched.is_empty());
    }

    #[test]
    fn cpu_duplicate_eq_dispatch_rejects_without_legacy_fallback() {
        let mut contract = production_contract();
        contract.common_eq_owner_count = 2;
        let (result, observed, launched) = dispatch(&contract);
        assert_eq!(
            result,
            Err(DrTailScheduleError::DuplicateEqOwner { observed: 2 })
        );
        assert!(observed.is_empty());
        assert!(launched.is_empty());
    }
}

fn preflighted_dr_window_result<T>(
    result: Result<T, DrWindowBindError>,
    contract: &'static str,
) -> Result<T, DrTailScheduleError> {
    result.map_err(|error| match dr_window_schedule_error(error) {
        DrTailScheduleError::WindowBinding { detail } => DrTailScheduleError::WindowBinding {
            detail: format!("{contract}: {detail}"),
        },
        error => error,
    })
}

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

    fn launch_continuation_kernels(
        &mut self,
        mut batch: GpuGKRDimensionReducingBatch<E4>,
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
        dr_tail_capacity: Option<&DrTailCapacityDecision>,
        window_tail: WindowTailArm,
        storage: &mut GpuGKRStorage<BF, E4>,
        context: &ProverContext,
    ) -> Result<GpuGKRDimensionReducingScheduledLayerExecution, DrTailScheduleError> {
        let stream = context.get_exec_stream();
        let dr_window_prepared = self.dr_window.is_some();
        if dr_tail_capacity.is_some() {
            assert!(
                dr_window_prepared,
                "DR-tail activation requires the prepared window seam"
            );
        }
        assert_eq!(
            dr_window_prepared,
            self.dr_window_bundle_final_log.is_some(),
            "a prepared DR hook must carry its resolved bundle final-log identity"
        );
        let dr_window_bundle_final_log = self.dr_window_bundle_final_log;
        let exact_memory_layer_idx = self.layer_idx;
        let exact_memory_folding_steps = self.folding_steps;
        let exact_memory_canonical_source_count = self.folding_addresses.len();
        let exact_memory_dr_tail_entry_round =
            dr_tail_capacity.map(DrTailCapacityDecision::entry_round);
        let mut tracing_ranges = Vec::new();
        assert!(self.folding_steps >= 2);
        let last_step = self.folding_steps - 1;
        // The production-shaped measurement interval covers the complete DR
        // layer, including its arm-specific allocations and the final LSB /
        // transcript work.  It is intentionally present for every geometry;
        // the old >=19 guard made small layers invisible to the analyzer.
        let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
        let layer_range = {
            let range = Range::new(layer_name)?;
            range.start(stream)?;
            Some(range)
        };
        let mut first3_recorder = super::round_timing::First3Recorder::begin(
            "dim_reducing",
            if dr_tail_capacity.is_some() {
                "mega_dr"
            } else {
                "per_round"
            },
            self.layer_idx,
            self.folding_steps,
            stream,
        )?;
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
        let challenge_count = self.folding_steps - 1;
        if dr_tail_capacity.is_none() {
            launch_build_eq_high_and_low_groups_from_point(
                device_claim_point_in.as_ptr(),
                1,
                challenge_count,
                get_eq_high_constant_device_ptr() as *mut E4,
                self.round_scratch.eq_low_group.as_mut_ptr(),
                context,
            )?;
            self.eq_sizes = make_eq_sizes(challenge_count);
        }

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
        let mut dr_tail_output: Option<DeviceAllocation<E4>> = None;
        if let Some(capacity) = dr_tail_capacity {
            let prepared = self
                .dr_window
                .take()
                .expect("DR-tail production requires the prepared R0 launch object");
            assert_eq!(
                prepared.continuation_readiness,
                DrWindowContinuationReadiness::ProducerReady,
                "DR-tail production requires accepted continuation readiness",
            );
            let mut hook = preflighted_dr_window_result(
                prepared.activate(storage, device_claim_point_out.as_ptr(), context),
                "preflighted DR window launch binding drifted",
            )?;
            assert_eq!(
                hook.continuation_launches.len(),
                hook.continuation_window_count,
                "every accepted continuation object must be launch-ready",
            );
            assert_eq!(
                hook.megakernel_entry_round,
                capacity.entry_round(),
                "DR window boundary must match the admitted recursive-tail entry",
            );
            assert_eq!(
                hook.continuation_projection.canonical_sources(),
                self.folding_addresses,
                "DR window publication order must match the canonical tail order",
            );
            let canonical_sources = preflighted_dr_window_result(
                hook.megakernel_source_pointers(storage),
                "preflighted DR tail publication binding drifted",
            )?;
            let execution_contract = DrLayerExecutionContract::from_hook(&hook);
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

            // Continuation producers intentionally use one in-place point:
            // untouched suffix coordinates remain tau while completed prefix
            // coordinates become the stream-ordered challenges they consume.
            memory_copy_async(
                device_claim_point_out.slice_mut(0, self.folding_steps),
                device_claim_point_in.slice(0, self.folding_steps),
                stream,
            )?;

            let continuation_count = hook.continuation_launches.len();
            schedule_dr_layer_execution(
                Some(&execution_contract),
                DrLayerExecutionSelection::CompleteNewChain { continuation_count },
                #[cfg(test)]
                None,
                |stage| -> Result<(), DrTailScheduleError> {
                    match stage {
                        DrLayerExecutionStage::R0 => {
                            launch_dr_window_r0(&hook, device_claim_point_out.as_ptr(), context)?;
                            let (active_eq_slot_base, active_eq_size_before_fold) =
                                resolve_active_eq_slot(
                                    &hook.r0_eq.eq_sizes,
                                    hook.r0_eq.eq_low.as_mut_ptr(),
                                );
                            let state = WindowTailState {
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
                            };
                            launch_window_tensor_round_tail(window_tail, &state, context)?;
                            storage.purge_up_to_layer(self.layer_idx);
                            if let Some(recorder) = first3_recorder.as_mut() {
                                recorder.mark("window_r0", stream)?;
                            }
                        }
                        DrLayerExecutionStage::Continuation(pass_index) => {
                            let pass = &hook.continuation_launches[pass_index];
                            assert_eq!(pass.geometry.pass_index, pass_index);
                            let mut one_fold_sizes = pass.eq_entry.sizes;
                            record_active_eq_slot_fold(&mut one_fold_sizes);
                            assert_eq!(one_fold_sizes, pass.one_fold_boundary_sizes);
                            assert_eq!(one_fold_sizes, pass.geometry.one_fold_boundary_sizes);
                            launch_dr_window_continuation(&pass.launch, context)?;
                            let (active_eq_slot_base, active_eq_size_before_fold) =
                                resolve_dr_global_active_eq_slot(&pass.eq_entry);
                            let start_round = pass.geometry.start_round;
                            // SAFETY: every bound pass is a validated width-three
                            // boundary within the layer point and proof slab.
                            let point =
                                unsafe { device_claim_point_out.as_mut_ptr().add(start_round) };
                            let coeffs_out = unsafe { coeffs_buffer_ptr.add(4 * start_round) };
                            let state = WindowTailState {
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
                            };
                            launch_window_tensor_round_tail(window_tail, &state, context)?;
                            if let Some(recorder) = first3_recorder.as_mut() {
                                recorder
                                    .mark(format!("window_continuation_{pass_index}"), stream)?;
                            }
                        }
                        DrLayerExecutionStage::Megakernel => {
                            let mut output =
                                context.alloc(folding_poly_count * 4, AllocationPlacement::Top)?;
                            let desc = DrTailMegakernelDesc {
                                enabled_mask: self.layer_slots.enabled_mask(),
                                folding_steps: self.folding_steps as u32,
                                entry_round: hook.megakernel_entry_round as u32,
                                source_count: folding_poly_count as u32,
                                source_ptrs,
                                final_sources: output.as_mut_ptr(),
                                tau: device_claim_point_in.as_ptr(),
                                seed: device_seed.as_mut_ptr(),
                                claim: device_claim.as_mut_ptr(),
                                eq_prefactor: device_eq_prefactor.as_mut_ptr(),
                                coeffs_out: coeffs_buffer_ptr,
                                challenges_out: device_claim_point_out.as_mut_ptr(),
                                slots,
                            };
                            launch_dr_tail_megakernel_e4(desc, capacity, context)?;
                            dr_tail_output = Some(output);
                            if let Some(recorder) = first3_recorder.as_mut() {
                                recorder.mark("megakernel", stream)?;
                            }
                        }
                        DrLayerExecutionStage::LegacyDiagnostic => unreachable!(
                            "the admitted complete-chain iterator cannot enter the diagnostic arm"
                        ),
                    }
                    Ok(())
                },
            )?;
            assert!(
                dr_tail_output.is_some(),
                "the complete-chain scheduler must consume the recursive-tail stage",
            );
        } else {
            // `dr_tail_capacity == None` is the explicit diagnostic selector.
            // A prepared window hook may exist for host diagnostics, but no
            // production call can arrive here without an admitted plan.
            schedule_dr_layer_execution(
                None,
                DrLayerExecutionSelection::LegacyDiagnostic,
                #[cfg(test)]
                None,
                |stage| -> Result<(), DrTailScheduleError> {
                    assert_eq!(stage, DrLayerExecutionStage::LegacyDiagnostic);
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
                                let batch =
                                    dim_reducing_encoder::build_round1_batch_compact_for_arena(
                                        &self.layer_slots,
                                        storage,
                                        &self.folding_addresses,
                                        destination_binding,
                                    );
                                self.launch_continuation_kernels(batch, step, acc_size, context)?;
                            } else {
                                let current = folding_current
                                    .as_ref()
                                    .expect("continuation round requires current folding arena");
                                let current_binding = FoldingArenaBinding::new(
                                    current.as_ptr() as *const u8,
                                    folding_current_len.trailing_zeros(),
                                );
                                let batch =
                                    dim_reducing_encoder::build_continuation_batch_compact_for_arenas(
                                        &self.layer_slots,
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
                        let coeffs_round_slice = unsafe {
                            DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(step * 4), 4)
                        };
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
                        if let Some(recorder) = first3_recorder.as_mut() {
                            recorder.mark_round_end(step, stream)?;
                        }
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
                            &self.layer_slots,
                            storage,
                            &self.folding_addresses,
                            destination_binding,
                        );
                        self.launch_continuation_kernels(batch, last_step, 1, context)?;
                    } else {
                        let current = folding_current
                            .as_ref()
                            .expect("final continuation round requires current folding arena");
                        let current_binding = FoldingArenaBinding::new(
                            current.as_ptr() as *const u8,
                            folding_current_len.trailing_zeros(),
                        );
                        let batch =
                            dim_reducing_encoder::build_continuation_batch_compact_for_arenas(
                                &self.layer_slots,
                                storage,
                                &self.folding_addresses,
                                current_binding,
                                destination_binding,
                            );
                        self.launch_continuation_kernels(batch, last_step, 1, context)?;
                    }
                    folding_current = Some(destination);
                    folding_current_len = destination_len;

                    let prev_coord_slice = device_claim_point_in.slice(last_step, 1);
                    // SAFETY: `last_step < folding_steps`, and every round owns four slab elements.
                    let coeffs_round_slice = unsafe {
                        DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(last_step * 4), 4)
                    };
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
                    Ok(())
                },
            )?;
        }
        let transcript_input_sources = if let Some(output) = dr_tail_output.as_ref() {
            self.final_evaluation_sources_for_last_step(storage, output, 4)
        } else {
            self.final_evaluation_sources_for_last_step(
                storage,
                folding_current
                    .as_ref()
                    .expect("final folding arena must be present"),
                folding_current_len,
            )
        };
        let num_addresses = transcript_input_sources.len();
        assert!(
            num_addresses > 0,
            "dimension-reducing layer must produce a next-layer claim"
        );
        let last_evals_len = num_addresses * 4;
        let final_step_evals_len = num_addresses * 2;
        let transcript_input_addresses: Vec<GKRAddress> =
            transcript_input_sources.keys().copied().collect();

        // Preserve the raw-address-sorted epilogue even when aliases merge in
        // canonical publication space. The recursive tail owns canonical
        // cells; this gather restores the exact legacy transcript ordering.
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

        let device_next_claim_point = schedule_dim_reducing_next_layer_claim_point(
            &device_claim_point_out,
            self.folding_steps,
            context,
        )?;

        let next_claim_layout = ClaimBufferLayout::from_addresses(transcript_input_addresses);
        if let Some(recorder) = first3_recorder.take() {
            recorder.finish(stream)?;
        }
        if let Some(layer_range) = layer_range {
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
            dr_window_prepared,
            dr_window_bundle_final_log,
            layer_idx: exact_memory_layer_idx,
            folding_steps: exact_memory_folding_steps,
            canonical_source_count: exact_memory_canonical_source_count,
            dr_tail_entry_round: exact_memory_dr_tail_entry_round,
            device_seed: Some(device_seed),
            device_claim_point_for_next_layer: Some(DeviceClaimPointAndBatching::from_allocation(
                device_next_claim_point,
            )),
            device_claims_for_next_layer: Some(device_new_claims),
            claim_layout_for_next_layer: Some(next_claim_layout),
        })
    }
}

/// Test-only continuation executor used by the locked D3 differential. R0 is
/// deliberately absent: callers must have already played its three rounds.
/// Every continuation snapshots one Eq entry and validates exactly one fold;
/// no mutable Eq state crosses the pass boundary.
#[cfg(test)]
pub(crate) struct DrWindowContinuationEqSnapshot {
    pub(crate) entry_sizes: GkrEqSizes,
    pub(crate) entry_active_size: u32,
    pub(crate) entry_active_values: Vec<E4>,
    pub(crate) one_fold_sizes: GkrEqSizes,
    pub(crate) one_fold_active_size: u32,
    pub(crate) one_fold_active_values: Vec<E4>,
}

#[cfg(test)]
fn snapshot_dr_window_active_eq(
    active_eq_slot: *const E4,
    active_eq_size: u32,
    context: &ProverContext,
) -> CudaResult<Vec<E4>> {
    let len = 1usize << active_eq_size;
    let mut host = vec![E4::default(); len];
    // SAFETY: the pass-local view points into a live 256-entry Eq group and
    // `active_eq_size <= 8` by construction.
    let device = unsafe { DeviceSlice::from_raw_parts(active_eq_slot, len) };
    memory_copy_async(&mut host[..], device, context.get_exec_stream())?;
    context.get_exec_stream().synchronize()?;
    Ok(host)
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_dr_window_continuation_chain_for_test(
    hook: &crate::backward::window_dr::DrWindowLayerCompositionHook,
    tail_arm: crate::backward::window::tail::WindowTailArm,
    claim_point: *mut E4,
    coeffs: *mut E4,
    seed: *mut u32,
    claim: *mut E4,
    eq_prefactor: *mut E4,
    context: &ProverContext,
    mut observe_pass: impl FnMut(
        &crate::backward::window_dr::DrWindowContinuationPass,
    ) -> CudaResult<()>,
) -> CudaResult<Vec<DrWindowContinuationEqSnapshot>> {
    use crate::backward::window::tail::{launch_window_tensor_round_tail, WindowTailState};
    use crate::backward::window_dr::{
        launch_dr_window_continuation, resolve_dr_global_active_eq_slot,
    };

    assert_eq!(
        hook.continuation_launches.len(),
        hook.continuation_window_count,
    );
    let mut eq_snapshots = Vec::with_capacity(hook.continuation_launches.len());
    for pass in &hook.continuation_launches {
        launch_dr_window_continuation(&pass.launch, context)?;
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_dr_global_active_eq_slot(&pass.eq_entry);
        let entry_active_values = snapshot_dr_window_active_eq(
            active_eq_slot_base.cast_const(),
            active_eq_size_before_fold,
            context,
        )?;
        let start_round = pass.geometry.start_round;
        // SAFETY: the layer-owned claim-point allocation has `folding_steps`
        // round slots, and every planned boundary is validated before binding.
        let challenge_alias = unsafe { claim_point.add(start_round) };
        // SAFETY: the proof slab reserves four coefficients per round.
        let coeffs_out = unsafe { coeffs.add(4 * start_round) };
        let state = WindowTailState {
            partials: pass.launch.binding.partials,
            row_tiles: pass.launch.row_tiles,
            reduced_tensor: pass.launch.reduced_tensor,
            prev_claim_coords: challenge_alias.cast_const(),
            seed,
            claim,
            eq_prefactor,
            coeffs_out,
            challenges_out: challenge_alias,
            active_eq_slot_base,
            active_eq_size_before_fold,
        };
        launch_window_tensor_round_tail(tail_arm, &state, context)?;

        let mut one_fold_sizes = pass.eq_entry.sizes;
        super::kernels::record_active_eq_slot_fold(&mut one_fold_sizes);
        assert_eq!(one_fold_sizes, pass.one_fold_boundary_sizes);
        assert_eq!(one_fold_sizes, pass.geometry.one_fold_boundary_sizes);
        let one_fold_active_size = active_eq_size_before_fold - 1;
        let one_fold_active_values = snapshot_dr_window_active_eq(
            active_eq_slot_base.cast_const(),
            one_fold_active_size,
            context,
        )?;
        eq_snapshots.push(DrWindowContinuationEqSnapshot {
            entry_sizes: pass.eq_entry.sizes,
            entry_active_size: active_eq_size_before_fold,
            entry_active_values,
            one_fold_sizes,
            one_fold_active_size,
            one_fold_active_values,
        });
        observe_pass(pass)?;
    }
    Ok(eq_snapshots)
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
