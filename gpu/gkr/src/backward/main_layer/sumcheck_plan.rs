use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use crate::GpuGKRStorage;

use super::super::kernels::*;
use super::super::main_tail::{bind_main_tail, launch_main_tail, MainTailRuntimeState};
use super::super::vm::production_bind::MainChainRepointReceipt;
use super::super::window::binding::{launch_window_program, BWD_WINDOW_COORDINATES};
use super::super::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use super::extras::{schedule_main_layer_extras_eval, MainLayerExtrasKeepalive};
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use crate::MainLayerScheduleError;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(test)]
static MAIN_LAYER_EXT_BANK_FILL_COUNT: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
pub(crate) fn reset_main_layer_ext_bank_fill_count_for_test() {
    MAIN_LAYER_EXT_BANK_FILL_COUNT.store(0, Ordering::SeqCst);
}

#[cfg(test)]
pub(crate) fn main_layer_ext_bank_fill_count_for_test() -> usize {
    MAIN_LAYER_EXT_BANK_FILL_COUNT.load(Ordering::SeqCst)
}

#[cfg(test)]
fn record_main_layer_ext_bank_fill_for_test() {
    MAIN_LAYER_EXT_BANK_FILL_COUNT.fetch_add(1, Ordering::SeqCst);
}

fn require_main_tail_publication<T>(
    publication: Option<T>,
    layer: usize,
    tail_start: u8,
) -> Result<T, MainLayerScheduleError> {
    publication.ok_or(MainLayerScheduleError::MissingPublication { layer, tail_start })
}

fn preserve_main_tail_bind_error<T, E: core::fmt::Display>(
    result: Result<T, E>,
    layer: usize,
) -> Result<T, MainLayerScheduleError> {
    result.map_err(|error| MainLayerScheduleError::MainTailBind {
        layer,
        detail: error.to_string(),
    })
}

fn preserve_main_tail_launch_error<T, E: core::fmt::Display>(
    result: Result<T, E>,
    layer: usize,
) -> Result<T, MainLayerScheduleError> {
    result.map_err(|error| MainLayerScheduleError::MainTailLaunch {
        layer,
        detail: error.to_string(),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MainTailPublicationSource {
    R0,
    Continuation,
}

fn main_tail_publication_source(
    main_chain_selected: bool,
    window_count: u8,
) -> Option<MainTailPublicationSource> {
    main_chain_selected.then_some(if window_count == 0 {
        MainTailPublicationSource::R0
    } else {
        MainTailPublicationSource::Continuation
    })
}

/// The production main-chain tail sequence: publication -> tail bind -> tail
/// enqueue -> canonical repoint, fail-closed at every step with no retry.
/// Production routes both chain arms through this exact function; the host
/// orchestration test executes it with injected operations. The production
/// operation types (`ContinuationPublishedLevel`, `MainTailLaunch`,
/// `MainTailLaunched`, `MainChainRepointReceipt`) are constructible only by
/// the real producers, so a production step cannot skip its call and still
/// type-check.
fn run_main_chain_tail<Published, Bound, Launched, FPublish, FBind, FLaunch, FRepoint>(
    publish: FPublish,
    bind: FBind,
    launch: FLaunch,
    repoint: FRepoint,
) -> Result<Launched, MainLayerScheduleError>
where
    FPublish: FnOnce() -> Result<Published, MainLayerScheduleError>,
    FBind: FnOnce(Published) -> Result<Bound, MainLayerScheduleError>,
    FLaunch: FnOnce(Bound) -> Result<Launched, MainLayerScheduleError>,
    FRepoint: FnOnce(&Launched) -> Result<MainChainRepointReceipt, MainLayerScheduleError>,
{
    let published = publish()?;
    let bound = bind(published)?;
    let launched = launch(bound)?;
    let _repointed: MainChainRepointReceipt = repoint(&launched)?;
    Ok(launched)
}

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
        mut recorder: Option<&mut super::super::round_timing::First3Recorder>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let stream = context.get_exec_stream();
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
        if let Some(recorder) = recorder.as_mut() {
            recorder.mark("window_bank_fill", stream)?;
        }
        launch_window_program(&windowed.window, context)?;
        if let Some(recorder) = recorder.as_mut() {
            recorder.mark("window_vm", stream)?;
        }
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
        #[cfg(test)]
        record_main_layer_ext_bank_fill_for_test();
        if let Some(recorder) = recorder.as_mut() {
            recorder.mark("ext_bank_fill", stream)?;
        }
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
        if let Some(recorder) = recorder.as_mut() {
            recorder.mark("window_tail", stream)?;
        }
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
    ) -> Result<GpuGKRMainLayerScheduledLayerExecution, MainLayerScheduleError> {
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
        let (first_ext_round, r0_first_round_in_loop) = match &self.bwd_vm_r0 {
            MainLayerR0Binding::PerRound(_) => (1, 0),
            MainLayerR0Binding::Windowed(_) => (BWD_WINDOW_COORDINATES, BWD_WINDOW_COORDINATES),
        };
        let continuation_tail_start = self.main_continuation.tail_start_round();
        let first_round_in_loop = if self.main_execution_plan.window_count() > 0 {
            usize::from(continuation_tail_start)
        } else {
            r0_first_round_in_loop
        };
        let challenge_count = self.folding_steps - first_ext_round;
        let arm = match &self.bwd_vm_r0 {
            MainLayerR0Binding::PerRound(_) => "per_round",
            MainLayerR0Binding::Windowed(windowed)
                if self.main_execution_plan.window_count() > 0 =>
            {
                match windowed.tail_arm {
                    crate::WindowTailArm::Absorbed => "windowed_cont_absorbed",
                    crate::WindowTailArm::Split => "windowed_cont_split",
                }
            }
            MainLayerR0Binding::Windowed(windowed) => match windowed.tail_arm {
                crate::WindowTailArm::Absorbed => "windowed_absorbed",
                crate::WindowTailArm::Split => "windowed_split",
            },
        };
        let mut recorder = super::super::round_timing::First3Recorder::begin(
            "main",
            arm,
            self.layer_idx,
            self.folding_steps,
            stream,
        )?;
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
        if let Some(recorder) = recorder.as_mut() {
            recorder.mark("prologue", stream)?;
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
        let mut transcript_input_sources: BTreeMap<GKRAddress, *const E4> = self
            .folding_evaluation_sources
            .iter()
            .map(|address| (*address, std::ptr::null()))
            .collect();
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
                recorder.as_mut(),
                context,
            )?;
            if self.main_chain_selected {
                let tail_arm = match &self.bwd_vm_r0 {
                    MainLayerR0Binding::Windowed(windowed) => windowed.tail_arm,
                    MainLayerR0Binding::PerRound(_) => {
                        unreachable!("the production main chain requires windowed R0")
                    }
                };
                let source = main_tail_publication_source(
                    self.main_chain_selected,
                    self.main_execution_plan.window_count(),
                )
                .expect("the selected production chain has one publication source");
                let scratch =
                    super::super::main_continuation::MainContinuationWindowRuntimeScratch {
                        eq_low: self.round_scratch.eq_low_group.as_ptr(),
                        partials: self.round_scratch.partials.as_mut_ptr(),
                        partials_capacity: self.round_scratch.partials.len(),
                    };
                let layer_idx = self.layer_idx;
                let folding_steps = self.folding_steps;
                let eq_low_group_ptr = self.round_scratch.eq_low_group.as_mut_ptr();
                let claim_point_in_ptr = device_claim_point_in.as_ptr();
                let seed_ptr = device_seed.as_mut_ptr();
                let claim_ptr = device_claim.as_mut_ptr();
                let eq_prefactor_ptr = device_eq_prefactor.as_mut_ptr();
                let claim_point_out_ptr = device_claim_point_out.as_mut_ptr();
                let main_continuation = &mut self.main_continuation;
                let eq_sizes = &mut self.eq_sizes;
                let main_tail_program = &self.main_tail_program;
                let bwd_vm_ext = &mut self.bwd_vm_ext;
                let folding_evaluation_sources = &self.folding_evaluation_sources;
                let canonical_final_addresses = &self.canonical_final_addresses;
                let recorder_slot = &mut recorder;
                let transcript_sources = &mut transcript_input_sources;
                let publish_storage = &mut *storage;
                let publish = || {
                    match source {
                        MainTailPublicationSource::R0 => main_continuation
                            .schedule_r0_publication(
                                publish_storage,
                                folding_steps,
                                scratch,
                                *eq_sizes,
                                recorder_slot.as_mut(),
                                context,
                            )?,
                        MainTailPublicationSource::Continuation => main_continuation
                            .schedule_windows(
                                publish_storage,
                                folding_steps,
                                scratch,
                                claim_point_in_ptr,
                                seed_ptr,
                                claim_ptr,
                                eq_prefactor_ptr,
                                coeffs_buffer_ptr,
                                claim_point_out_ptr,
                                tail_arm,
                                recorder_slot.as_mut(),
                                context,
                            )?,
                    }
                    let boundary = main_continuation.final_eq_boundary().ok_or_else(|| {
                        MainLayerScheduleError::MainContinuation {
                            layer: layer_idx,
                            pass_start: usize::from(continuation_tail_start.saturating_sub(3)),
                            detail: "the producer did not publish its Eq boundary".to_owned(),
                        }
                    })?;
                    assert_eq!(
                        boundary.consumer_round, continuation_tail_start,
                        "the final continuation boundary must name the prepared remainder"
                    );
                    let expected_remainder_eq = super::super::vm::production_bind::drained_eq_sizes(
                        make_eq_sizes(folding_steps - usize::from(continuation_tail_start)),
                        1,
                    );
                    assert_eq!(
                        boundary.eq_sizes, expected_remainder_eq,
                        "the final pass-local Eq state must equal the first legacy descriptor"
                    );
                    *eq_sizes = boundary.eq_sizes;
                    let published = require_main_tail_publication(
                        main_continuation.take_published_level(),
                        layer_idx,
                        continuation_tail_start,
                    )?;
                    Ok((published, boundary))
                };
                let bind = |(published, boundary): (
                    super::super::main_continuation::ContinuationPublishedLevel,
                    super::execution_plan::MainEqBoundaryWitness,
                )| {
                    let tail_program = main_tail_program.as_ref().expect(
                        "windowed production path requires a preflighted main-tail program",
                    );
                    preserve_main_tail_bind_error(
                        bind_main_tail(
                            layer_idx,
                            tail_program,
                            published,
                            usize::from(continuation_tail_start),
                            folding_steps,
                            boundary,
                            MainTailRuntimeState {
                                eq_low: eq_low_group_ptr,
                                prev_claim_coordinates: claim_point_in_ptr,
                                seed: seed_ptr,
                                claim: claim_ptr,
                                eq_prefactor: eq_prefactor_ptr,
                                coefficients_out: coeffs_buffer_ptr,
                                challenges_out: claim_point_out_ptr,
                            },
                            context,
                        ),
                        layer_idx,
                    )
                };
                let launch = |bound| {
                    preserve_main_tail_launch_error(launch_main_tail(bound, context), layer_idx)
                };
                let repoint = |launched: &super::super::main_tail::MainTailLaunched| {
                    let expected: std::collections::BTreeSet<_> =
                        folding_evaluation_sources.iter().copied().collect();
                    let actual: std::collections::BTreeSet<_> = canonical_final_addresses
                        .iter()
                        .map(|(_, address)| *address)
                        .collect();
                    if expected != actual {
                        return Err(MainLayerScheduleError::MainTailBind {
                            layer: layer_idx,
                            detail:
                                "canonical final-evaluation source set is incomplete or mismatched"
                                    .to_owned(),
                        });
                    }
                    bwd_vm_ext
                        .set_external_final_evaluation_offsets(
                            canonical_final_addresses.iter().copied(),
                        )
                        .map_err(|detail| MainLayerScheduleError::MainTailBind {
                            layer: layer_idx,
                            detail: detail.to_owned(),
                        })?;
                    Ok(bwd_vm_ext.repoint_final_evaluations_from_external_buffer(
                        launched.final_level().allocation(),
                        transcript_sources,
                    ))
                };
                self.main_tail_launched =
                    Some(run_main_chain_tail(publish, bind, launch, repoint)?);
            }
        }

        if !self.main_chain_selected {
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
                        #[cfg(test)]
                        record_main_layer_ext_bank_fill_for_test();
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
                if let Some(recorder) = recorder.as_mut() {
                    recorder.mark_round_end(step, stream)?;
                }
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
                let coeffs_round_slice = unsafe {
                    DeviceSlice::from_raw_parts_mut(coeffs_buffer_ptr.add(last_step * 4), 4)
                };
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
        }
        if let Some(recorder) = recorder.take() {
            recorder.finish(stream)?;
        }

        // The production chain repointed through its canonical receipt inside
        // `run_main_chain_tail`; only the explicit diagnostic arms repoint from
        // the legacy per-round folding buffers here.
        if self.main_tail_launched.is_none() {
            self.bwd_vm_ext
                .repoint_final_evaluations(&mut transcript_input_sources);
        }
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

        #[cfg(not(test))]
        drop(device_claim);
        #[cfg(not(test))]
        drop(device_eq_prefactor);
        #[cfg(test)]
        let device_final_claim_for_test = Some(device_claim);
        #[cfg(test)]
        let device_final_eq_prefactor_for_test = Some(device_eq_prefactor);
        drop(device_last_evals);
        drop(device_claim_point_in);
        drop(device_claims_in);
        // Release extras scratch immediately after its last queued use.
        drop(extras_keepalive);
        let r0_bank_staging = match &mut self.bwd_vm_r0 {
            MainLayerR0Binding::PerRound(round0) => round0.take_bank_staging(),
            MainLayerR0Binding::Windowed(windowed) => windowed.bank.take_bank_staging(),
        };
        let main_tail_staging = self
            .main_tail_launched
            .as_mut()
            .and_then(super::super::main_tail::MainTailLaunched::take_host_staging);
        let coeff_bank_staging = [
            r0_bank_staging,
            self.bwd_vm_ext.take_bank_staging(),
            main_tail_staging,
        ]
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
            main_continuation_eq_boundary: self.main_continuation.final_eq_boundary(),
            #[cfg(test)]
            device_final_claim_for_test,
            #[cfg(test)]
            device_final_eq_prefactor_for_test,
        })
    }
}

#[cfg(test)]
mod cpu_main_chain_dispatch {
    use super::*;
    use crate::{
        production_main_chain_selected, BackwardExecutionStrategy, GkrBackwardOptions,
        WindowTailArm,
    };

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Event {
        R0,
        R0Publication,
        Continuation,
        TailBind,
        TailLaunch,
        CanonicalRepoint,
        Legacy,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Inject {
        None,
        MissingPublication,
        Bind,
        Launch,
    }

    fn host_schedule(
        options: GkrBackwardOptions,
        strategy: BackwardExecutionStrategy,
        window_count: u8,
        inject: Inject,
    ) -> (Vec<Event>, Result<(), MainLayerScheduleError>) {
        let mut events = Vec::new();
        if strategy == BackwardExecutionStrategy::WindowedR0 {
            events.push(Event::R0);
        }
        let selected = production_main_chain_selected(options, strategy);
        let Some(source) = main_tail_publication_source(selected, window_count) else {
            events.push(Event::Legacy);
            return (events, Ok(()));
        };
        events.push(match source {
            MainTailPublicationSource::R0 => Event::R0Publication,
            MainTailPublicationSource::Continuation => Event::Continuation,
        });
        let publication = (inject != Inject::MissingPublication).then_some(());
        let publication = match require_main_tail_publication(publication, 7, 3) {
            Ok(publication) => publication,
            Err(error) => return (events, Err(error)),
        };
        let _ = publication;
        events.push(Event::TailBind);
        if let Err(error) = preserve_main_tail_bind_error(
            if inject == Inject::Bind {
                Err("injected bind")
            } else {
                Ok(())
            },
            7,
        ) {
            return (events, Err(error));
        }
        events.push(Event::TailLaunch);
        if let Err(error) = preserve_main_tail_launch_error(
            if inject == Inject::Launch {
                Err("injected post-launch failure")
            } else {
                Ok(())
            },
            7,
        ) {
            return (events, Err(error));
        }
        events.push(Event::CanonicalRepoint);
        (events, Ok(()))
    }

    fn production_options() -> GkrBackwardOptions {
        GkrBackwardOptions {
            windowed_r0: true,
            windowed_main_continuations: true,
            window_tail: WindowTailArm::Split,
            ..GkrBackwardOptions::default()
        }
    }

    #[test]
    fn zero_and_continuation_windows_reach_the_tail_through_the_exact_source() {
        let (zero_events, zero_result) = host_schedule(
            production_options(),
            BackwardExecutionStrategy::WindowedR0,
            0,
            Inject::None,
        );
        assert_eq!(zero_result, Ok(()));
        assert_eq!(
            zero_events,
            [
                Event::R0,
                Event::R0Publication,
                Event::TailBind,
                Event::TailLaunch,
                Event::CanonicalRepoint,
            ]
        );

        let (continuation_events, continuation_result) = host_schedule(
            production_options(),
            BackwardExecutionStrategy::WindowedR0,
            2,
            Inject::None,
        );
        assert_eq!(continuation_result, Ok(()));
        assert_eq!(
            continuation_events,
            [
                Event::R0,
                Event::Continuation,
                Event::TailBind,
                Event::TailLaunch,
                Event::CanonicalRepoint,
            ]
        );
        assert_ne!(zero_events, continuation_events);
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Remove {
        Nothing,
        Publication,
        TailBind,
        TailEnqueue,
        CanonicalRepoint,
    }

    /// Execute the exact production sequence function with recording
    /// operations. Every stage records before it (optionally) fails, so a red
    /// mutation is distinguishable from a stage that never ran.
    fn run_recorded_chain(
        source: MainTailPublicationSource,
        remove: Remove,
    ) -> (Vec<Event>, Result<(), MainLayerScheduleError>) {
        use crate::backward::vm::production_bind::MainChainRepointReceipt;
        let events = std::cell::RefCell::new(Vec::new());
        let record = |event: Event| events.borrow_mut().push(event);
        let result = run_main_chain_tail(
            || {
                record(match source {
                    MainTailPublicationSource::R0 => Event::R0Publication,
                    MainTailPublicationSource::Continuation => Event::Continuation,
                });
                if remove == Remove::Publication {
                    return Err(MainLayerScheduleError::MissingPublication {
                        layer: 7,
                        tail_start: 3,
                    });
                }
                Ok(())
            },
            |(): ()| {
                record(Event::TailBind);
                preserve_main_tail_bind_error(
                    if remove == Remove::TailBind {
                        Err("tail bind removed")
                    } else {
                        Ok(())
                    },
                    7,
                )
            },
            |(): ()| {
                record(Event::TailLaunch);
                preserve_main_tail_launch_error(
                    if remove == Remove::TailEnqueue {
                        Err("tail enqueue removed")
                    } else {
                        Ok(())
                    },
                    7,
                )
            },
            |_launched: &()| {
                record(Event::CanonicalRepoint);
                if remove == Remove::CanonicalRepoint {
                    return Err(MainLayerScheduleError::MainTailBind {
                        layer: 7,
                        detail: "canonical repoint removed".to_owned(),
                    });
                }
                Ok(MainChainRepointReceipt::for_test())
            },
        );
        (events.into_inner(), result.map(|()| ()))
    }

    #[test]
    fn cpu_main_chain_tail_orchestration() {
        // The W=0 plans admitted for folding_steps 4..=6 and every W>0 plan
        // route through the same production sequence; only the publication
        // source differs.
        for (folding_steps, window_count) in [(4u8, 0u8), (5, 0), (6, 0), (7, 1)] {
            let source = main_tail_publication_source(true, window_count)
                .expect("the production chain always has a publication source");
            let expected_first = if window_count == 0 {
                assert!((4..=6).contains(&folding_steps));
                Event::R0Publication
            } else {
                Event::Continuation
            };
            let (events, result) = run_recorded_chain(source, Remove::Nothing);
            assert!(result.is_ok());
            assert_eq!(
                events,
                [
                    expected_first,
                    Event::TailBind,
                    Event::TailLaunch,
                    Event::CanonicalRepoint,
                ],
                "folding_steps={folding_steps}"
            );

            for (remove, surviving_events) in [
                (Remove::Publication, 1),
                (Remove::TailBind, 2),
                (Remove::TailEnqueue, 3),
                (Remove::CanonicalRepoint, 4),
            ] {
                let (events, result) = run_recorded_chain(source, remove);
                let error = result.expect_err("a removed production operation must be red");
                match (remove, &error) {
                    (
                        Remove::Publication,
                        MainLayerScheduleError::MissingPublication { layer: 7, .. },
                    )
                    | (Remove::TailBind, MainLayerScheduleError::MainTailBind { layer: 7, .. })
                    | (
                        Remove::TailEnqueue,
                        MainLayerScheduleError::MainTailLaunch { layer: 7, .. },
                    )
                    | (
                        Remove::CanonicalRepoint,
                        MainLayerScheduleError::MainTailBind { layer: 7, .. },
                    ) => {}
                    (remove, error) => panic!("wrong typed error for {remove:?}: {error:?}"),
                }
                // Fail-closed with zero retry: the sequence stops at the
                // removed stage and never re-enters an earlier one.
                assert_eq!(events.len(), surviving_events, "{remove:?}");
                assert!(!events.contains(&Event::Legacy), "{remove:?} fell back");
                let unique: std::collections::BTreeSet<_> =
                    events.iter().map(|event| format!("{event:?}")).collect();
                assert_eq!(unique.len(), events.len(), "{remove:?} retried a stage");
            }
        }
    }

    #[test]
    fn publication_bind_and_launch_failures_remain_typed_without_legacy_retry() {
        for (inject, expected) in [
            (Inject::MissingPublication, "missing"),
            (Inject::Bind, "bind"),
            (Inject::Launch, "launch"),
        ] {
            let (events, result) = host_schedule(
                production_options(),
                BackwardExecutionStrategy::WindowedR0,
                0,
                inject,
            );
            assert!(
                !events.contains(&Event::Legacy),
                "{expected} retried legacy"
            );
            let error = result.expect_err("the injected production failure must propagate");
            match (expected, error) {
                ("missing", MainLayerScheduleError::MissingPublication { layer: 7, .. })
                | ("bind", MainLayerScheduleError::MainTailBind { layer: 7, .. })
                | ("launch", MainLayerScheduleError::MainTailLaunch { layer: 7, .. }) => {}
                (_, error) => panic!("wrong typed error for {expected}: {error:?}"),
            }
        }
    }

    #[test]
    fn only_explicit_diagnostic_configuration_enters_the_legacy_loop() {
        let mut diagnostic = production_options();
        diagnostic.windowed_main_continuations = false;
        let (events, result) = host_schedule(
            diagnostic,
            BackwardExecutionStrategy::WindowedR0,
            0,
            Inject::None,
        );
        assert_eq!(result, Ok(()));
        assert_eq!(events, [Event::R0, Event::Legacy]);

        let mut per_round = production_options();
        per_round.windowed_r0 = false;
        let (events, result) = host_schedule(
            per_round,
            BackwardExecutionStrategy::PerRound,
            0,
            Inject::None,
        );
        assert_eq!(result, Ok(()));
        assert_eq!(events, [Event::Legacy]);

        // Proven-fail mutations: either production selector or either window
        // count must change the observed arm/source.
        assert_ne!(
            main_tail_publication_source(true, 0),
            main_tail_publication_source(false, 0)
        );
        assert_ne!(
            main_tail_publication_source(true, 0),
            main_tail_publication_source(true, 1)
        );
    }
}
