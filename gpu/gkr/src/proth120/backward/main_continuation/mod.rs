pub(crate) mod binding;
mod dispatch;
mod publication;

use era_cudart::result::CudaResult;
use gpu_gkr_compiler::MainContinuationWindowProgram;
use gpu_prover_context::ProverContext;

pub(crate) use binding::{
    bind_first_main_continuation_pr, bind_later_main_continuation_pr, publication_shape_pr,
    MainContinuationBindErrorPr, MainContinuationLaunchPr, MainContinuationScratchPr,
};
pub(crate) use dispatch::{
    launch_main_continuation_pr, resolve_pr_main_continuation_kernel, MainContinuationLaunchedPr,
};
pub(crate) use publication::{ContinuationPublishedLevelPr, PR_MAIN_FINAL_EVALUATIONS_PER_ADDRESS};

use super::eq::{launch_eq_high_low_pr, resolve_active_eq_slot_pr};
use super::main_continuation_window_manifest::PrMainContinuationWindowKernelEntry;
use super::window::{launch_build_fold_weights_pr, launch_window_tail_pr, WindowTailStatePr};
use crate::backward::main_layer::execution_plan::{
    derive_main_layer_execution_plan, main_continuation_post_tail_eq_boundary,
    MainEqBoundaryWitness, MainLayerExecutionPlan,
};
use crate::backward::{record_active_eq_slot_fold, GKR_EQ_GROUP_TABLE_LEN};
use crate::upstream::PR;
use crate::GpuGKRStorage;

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainLayerRoundStatePr {
    pub(crate) claim_point_in: *const PR,
    pub(crate) seed: *mut u8,
    pub(crate) claim: *mut PR,
    pub(crate) eq_prefactor: *mut PR,
    pub(crate) coeffs_out: *mut PR,
    pub(crate) challenges_out: *mut PR,
}

pub(crate) struct MainContinuationSequencePr {
    execution_plan: MainLayerExecutionPlan,
    layer_idx: usize,
    folding_steps: usize,
    kernel: &'static PrMainContinuationWindowKernelEntry,
    published: Option<ContinuationPublishedLevelPr>,
    final_eq_boundary: Option<MainEqBoundaryWitness>,
}

impl MainContinuationSequencePr {
    pub(crate) fn new(
        program: &MainContinuationWindowProgram,
        layer_idx: usize,
        folding_steps: usize,
    ) -> Self {
        let kernel = resolve_pr_main_continuation_kernel(program.shape.bits());
        let execution_plan = derive_main_layer_execution_plan(folding_steps);
        assert!(
            execution_plan.window_count() > 0,
            "Proth120 main continuation requires at least one window pass (folding steps {folding_steps})"
        );
        Self {
            execution_plan,
            layer_idx,
            folding_steps,
            kernel,
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

    pub(crate) fn take_published_level(&mut self) -> Option<ContinuationPublishedLevelPr> {
        self.published.take()
    }

    pub(crate) fn final_eq_boundary(&self) -> Option<MainEqBoundaryWitness> {
        self.final_eq_boundary
    }

    fn unwrap_binding<T>(
        result: Result<T, MainContinuationBindErrorPr>,
        layer_idx: usize,
        pass_start: usize,
    ) -> CudaResult<T> {
        match result {
            Ok(value) => Ok(value),
            Err(MainContinuationBindErrorPr::Cuda(error)) => Err(error),
            Err(error) => panic!(
                "Proth120 main continuation binding for layer {layer_idx} pass {pass_start}: {error:?}"
            ),
        }
    }

    pub(crate) fn schedule_windows(
        &mut self,
        program: &MainContinuationWindowProgram,
        storage: &mut GpuGKRStorage<PR, PR>,
        scratch: MainContinuationScratchPr,
        round: MainLayerRoundStatePr,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.published.is_none() && self.final_eq_boundary.is_none(),
            "Proth120 main continuation sequence may be scheduled only once"
        );
        assert_eq!(
            u16::from(self.kernel.mask),
            program.shape.bits(),
            "Proth120 main continuation program differs from the prepared layer"
        );
        let folding_steps = self.folding_steps;
        let eq_high_1 = scratch.eq_high.wrapping_add(GKR_EQ_GROUP_TABLE_LEN);
        for pass_index in 0..self.window_count() {
            let pass_start = 3 + 3 * usize::from(pass_index);
            let challenge_offset = pass_start + 3;
            let challenge_count = folding_steps
                .checked_sub(challenge_offset)
                .filter(|count| *count > 0)
                .expect("Proth120 continuation pass must leave a consumer round");
            launch_eq_high_low_pr(
                round.claim_point_in,
                challenge_offset as u32,
                challenge_count as u32,
                scratch.eq_high,
                eq_high_1,
                scratch.eq_low,
                context,
            )?;
            launch_build_fold_weights_pr(
                scratch.fold_weights,
                round.challenges_out.cast_const(),
                pass_start as u32,
                context,
            )?;
            let launched = match self.published.as_ref() {
                None => {
                    let launch = Self::unwrap_binding(
                        bind_first_main_continuation_pr(
                            program,
                            self.kernel,
                            storage,
                            folding_steps,
                            scratch,
                            context,
                        ),
                        self.layer_idx,
                        pass_start,
                    )?;
                    launch_main_continuation_pr(launch, context)?
                }
                Some(prior) => {
                    let launch = Self::unwrap_binding(
                        bind_later_main_continuation_pr(
                            program,
                            self.kernel,
                            prior,
                            folding_steps,
                            pass_start,
                            scratch,
                            context,
                        ),
                        self.layer_idx,
                        pass_start,
                    )?;
                    launch_main_continuation_pr(launch, context)?
                }
            };
            if pass_index == 0 {
                storage.release_main_layer_inputs(self.layer_idx);
            }

            let mut eq_sizes = launched.eq_sizes();
            let (active_eq_slot_base, active_eq_size_before_fold) =
                resolve_active_eq_slot_pr(&eq_sizes, scratch.eq_low, scratch.eq_high, eq_high_1);
            launch_window_tail_pr(
                &WindowTailStatePr {
                    partials: launched.partials(),
                    row_tiles: launched.row_tiles(),
                    reduced_tensor: launched.reduced_tensor(),
                    prev_claim_coords: round.claim_point_in.wrapping_add(pass_start),
                    seed: round.seed,
                    claim: round.claim,
                    eq_prefactor: round.eq_prefactor,
                    coeffs_out: round.coeffs_out.wrapping_add(4 * pass_start),
                    challenges_out: round.challenges_out.wrapping_add(pass_start),
                    active_eq_slot_base,
                    active_eq_size_before_fold,
                },
                context,
            )?;
            record_active_eq_slot_fold(&mut eq_sizes);
            let boundary =
                main_continuation_post_tail_eq_boundary(pass_start as u8, folding_steps, eq_sizes);
            let consumed = self.published.replace(launched.into_published_level());
            drop(consumed);
            self.final_eq_boundary = Some(boundary);
        }
        assert!(
            self.published.is_some(),
            "Proth120 main continuation sequence did not publish its final level"
        );
        Ok(())
    }
}
