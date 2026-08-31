//! Stream-ordered scheduling for width-three main continuation windows.

use era_cudart::result::CudaResult;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::MainContinuationWindowProgram;
use gpu_prover_context::ProverContext;

use super::binding::{
    bind_first_main_continuation_window, bind_later_main_continuation_window,
    bind_main_r0_publication, launch_main_continuation_window, MainContinuationWindowBindError,
    MainContinuationWindowRuntimeScratch,
};
use super::ContinuationPublishedLevel;
use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
    record_active_eq_slot_fold, resolve_active_eq_slot,
};
use crate::backward::main_layer::execution_plan::{
    main_continuation_post_tail_eq_boundary, MainEqBoundaryWitness, MainLayerExecutionPlan,
};
use crate::backward::window::state::launch_bwd_build_fold_weights;
use crate::backward::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use crate::{GkrPrograms, GpuGKRStorage};

/// Owns the canonical publication that links consecutive continuation passes.
/// The previous level is released only after its reader kernel has been
/// enqueued; the final level remains available for exactly one consumer.
pub(crate) struct MainContinuationWindowSequence {
    execution_plan: MainLayerExecutionPlan,
    layer_idx: usize,
    programs: std::sync::Arc<GkrPrograms>,
    published: Option<ContinuationPublishedLevel>,
    final_eq_boundary: Option<MainEqBoundaryWitness>,
}

impl MainContinuationWindowSequence {
    pub(crate) fn new(
        execution_plan: MainLayerExecutionPlan,
        layer_idx: usize,
        programs: std::sync::Arc<GkrPrograms>,
    ) -> Self {
        Self {
            execution_plan,
            layer_idx,
            programs,
            published: None,
            final_eq_boundary: None,
        }
    }

    pub(crate) fn window_count(&self) -> u8 {
        self.execution_plan.window_count()
    }

    pub(crate) fn tail_start_round(&self) -> u8 {
        self.execution_plan.tail_start_round()
    }

    pub(crate) fn take_published_level(&mut self) -> Option<ContinuationPublishedLevel> {
        self.published.take()
    }

    pub(crate) fn final_eq_boundary(&self) -> Option<MainEqBoundaryWitness> {
        self.final_eq_boundary
    }

    /// Materialize the canonical depth-zero E4 arena consumed by a tail that
    /// starts immediately after R0. This is a device producer launch, not a
    /// fabricated publication and not a host/device copy.
    pub(crate) fn schedule_r0_publication(
        &mut self,
        storage: &mut GpuGKRStorage<BF, E4>,
        folding_steps: usize,
        scratch: MainContinuationWindowRuntimeScratch,
        r0_eq_sizes: crate::backward::GkrEqSizes,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(
            self.window_count(),
            0,
            "the R0 publication-only launch belongs only to a zero-window plan"
        );
        assert!(
            self.published.is_none() && self.final_eq_boundary.is_none(),
            "a continuation sequence may be scheduled only once"
        );
        let program = self.programs.main_continuation_window_layer(self.layer_idx);
        let launch = Self::unwrap_binding(
            bind_main_r0_publication(program, storage, folding_steps, scratch, context),
            self.layer_idx,
            0,
        )?;
        let launched = launch_main_continuation_window(launch, context)?;
        self.published = Some(launched.into_published_level());
        self.final_eq_boundary = Some(main_continuation_post_tail_eq_boundary(
            0,
            folding_steps,
            r0_eq_sizes,
        ));
        storage.purge_up_to_layer(self.layer_idx);
        Ok(())
    }

    fn unwrap_binding<T>(
        result: Result<T, MainContinuationWindowBindError>,
        layer_idx: usize,
        pass_start: usize,
    ) -> CudaResult<T> {
        match result {
            Ok(value) => Ok(value),
            Err(MainContinuationWindowBindError::Cuda(error)) => Err(error),
            Err(error) => panic!(
                "main continuation binding for layer {layer_idx} pass {pass_start}: {error:?}"
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn schedule_windows(
        &mut self,
        storage: &mut GpuGKRStorage<BF, E4>,
        folding_steps: usize,
        scratch: MainContinuationWindowRuntimeScratch,
        claim_point_in: *const E4,
        seed: *mut u32,
        claim: *mut E4,
        eq_prefactor: *mut E4,
        coeffs_out: *mut E4,
        challenges_out: *mut E4,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.published.is_none() && self.final_eq_boundary.is_none(),
            "a continuation sequence may be scheduled only once"
        );
        let program: &MainContinuationWindowProgram =
            self.programs.main_continuation_window_layer(self.layer_idx);
        let window_count = self.window_count();
        for pass_index in 0..window_count {
            let pass_start = 3usize + 3usize * usize::from(pass_index);
            let challenge_offset = pass_start + 3;
            let challenge_count = folding_steps
                .checked_sub(challenge_offset)
                .expect("continuation pass extends beyond the folding width");
            assert!(
                challenge_count > 0,
                "every continuation pass leaves a consumer"
            );

            launch_build_eq_high_and_low_groups_from_point(
                claim_point_in,
                challenge_offset,
                challenge_count,
                get_eq_high_constant_device_ptr(),
                scratch.eq_low.cast_mut(),
                context,
            )?;
            launch_bwd_build_fold_weights(pass_start as u32, context)?;

            let launch = match self.published.as_ref() {
                None => Self::unwrap_binding(
                    bind_first_main_continuation_window(
                        program,
                        storage,
                        folding_steps,
                        pass_start,
                        scratch,
                        context,
                    ),
                    self.layer_idx,
                    pass_start,
                )?,
                Some(prior) => Self::unwrap_binding(
                    bind_later_main_continuation_window(
                        program,
                        prior,
                        folding_steps,
                        pass_start,
                        scratch,
                        context,
                    ),
                    self.layer_idx,
                    pass_start,
                )?,
            };
            let launched = launch_main_continuation_window(launch, context)?;

            // The first continuation pass is the last reader of raw layer
            // storage. Pool reuse is safe immediately after that launch has
            // been enqueued on the execution stream.
            if pass_index == 0 {
                storage.purge_up_to_layer(self.layer_idx);
            }

            let mut actual_eq_sizes = launched.eq_sizes();
            let (active_eq_slot_base, active_eq_size_before_fold) =
                resolve_active_eq_slot(&actual_eq_sizes, scratch.eq_low.cast_mut());
            let tail_state = WindowTailState {
                partials: scratch.partials,
                row_tiles: launched.row_tiles(),
                reduced_tensor: launched.reduced_tensor(),
                // SAFETY: the plan guarantees pass_start + 3 <= folding_steps.
                prev_claim_coords: unsafe { claim_point_in.add(pass_start) },
                seed,
                claim,
                eq_prefactor,
                // SAFETY: the coefficient slab owns four cells per round.
                coeffs_out: unsafe { coeffs_out.add(4 * pass_start) },
                // SAFETY: output claim-point slots cover every folding round.
                challenges_out: unsafe { challenges_out.add(pass_start) },
                active_eq_slot_base,
                active_eq_size_before_fold,
            };
            launch_window_tensor_round_tail(&tail_state, context)?;
            record_active_eq_slot_fold(&mut actual_eq_sizes);
            let boundary = main_continuation_post_tail_eq_boundary(
                pass_start as u8,
                folding_steps,
                actual_eq_sizes,
            );

            let consumed = self.published.take();
            self.published = Some(launched.into_published_level());
            // The later pass's reader kernel was enqueued above. Its input
            // owner may now be released without waiting for completion.
            drop(consumed);
            self.final_eq_boundary = Some(boundary);
        }
        assert_eq!(
            self.published.is_some(),
            window_count > 0,
            "only a non-empty sequence owns a publication"
        );
        Ok(())
    }
}
