//! Stream-ordered scheduling for width-three main continuation windows.

use era_cudart::result::CudaResult;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::MainContinuationWindowProgram;
use gpu_prover_context::ProverContext;

use super::binding::{
    bind_first_main_continuation_window, bind_later_main_continuation_window,
    launch_main_continuation_window, MainContinuationWindowBindError,
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
use crate::backward::round_timing::First3Recorder;
use crate::backward::vm::seg::launch_bwd_seg_build_fold_weights;
use crate::backward::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use crate::{GkrPrograms, GpuGKRStorage, WindowTailArm};

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

    pub(crate) fn published_level(&self) -> Option<&ContinuationPublishedLevel> {
        self.published.as_ref()
    }

    pub(crate) fn take_published_level(&mut self) -> Option<ContinuationPublishedLevel> {
        self.published.take()
    }

    pub(crate) fn final_eq_boundary(&self) -> Option<MainEqBoundaryWitness> {
        self.final_eq_boundary
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
        tail_arm: WindowTailArm,
        mut recorder: Option<&mut First3Recorder>,
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
            launch_bwd_seg_build_fold_weights(pass_start as u32, context)?;

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
            if let Some(recorder) = recorder.as_deref_mut() {
                recorder.mark(
                    format!("window_cont{pass_index}"),
                    context.get_exec_stream(),
                )?;
            }

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
            launch_window_tensor_round_tail(tail_arm, &tail_state, context)?;
            record_active_eq_slot_fold(&mut actual_eq_sizes);
            let boundary = main_continuation_post_tail_eq_boundary(
                pass_start as u8,
                folding_steps,
                actual_eq_sizes,
            );
            if let Some(recorder) = recorder.as_deref_mut() {
                recorder.mark(
                    format!("window_cont_tail{pass_index}"),
                    context.get_exec_stream(),
                )?;
            }

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

#[cfg(test)]
mod cpu_main_continuation_schedule {
    use crate::backward::main_layer::execution_plan::{
        try_derive_main_layer_execution_plan, MainLayerExecutionPlan, MainTailRoundBudget,
        LEGACY_MAIN_TAIL_MIN_ROUNDS,
    };
    use crate::{BackwardExecutionStrategy, GkrBackwardOptions};

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum ScheduleEvent {
        R0BankFill,
        R0Window,
        ExtBankFill,
        R0Tail,
        FreshEq {
            pass_start: u8,
            challenge_offset: u8,
            challenge_count: u8,
        },
        FoldWeights {
            pass_start: u8,
        },
        Window {
            pass_start: u8,
            prev_claim: [u8; 2],
            challenge_out: [u8; 2],
            input_depth: Option<u8>,
            output_depth: u8,
        },
        Tail {
            pass_start: u8,
        },
        DropAfterRead {
            depth: u8,
            reader_start: u8,
        },
        AdoptLegacy {
            tail_start: u8,
            depth: u8,
        },
        Remainder {
            tail_start: u8,
        },
    }

    fn schedule_trace(folding_steps: usize, plan: MainLayerExecutionPlan) -> Vec<ScheduleEvent> {
        let mut trace = vec![
            ScheduleEvent::R0BankFill,
            ScheduleEvent::R0Window,
            ScheduleEvent::ExtBankFill,
            ScheduleEvent::R0Tail,
        ];
        for pass_index in 0..plan.window_count() {
            let pass_start = 3 + 3 * pass_index;
            trace.push(ScheduleEvent::FreshEq {
                pass_start,
                challenge_offset: pass_start + 3,
                challenge_count: folding_steps as u8 - pass_start - 3,
            });
            trace.push(ScheduleEvent::FoldWeights { pass_start });
            trace.push(ScheduleEvent::Window {
                pass_start,
                prev_claim: [pass_start, pass_start + 3],
                challenge_out: [pass_start, pass_start + 3],
                input_depth: (pass_index > 0).then_some(pass_start - 3),
                output_depth: pass_start,
            });
            trace.push(ScheduleEvent::Tail { pass_start });
            if pass_index > 0 {
                trace.push(ScheduleEvent::DropAfterRead {
                    depth: pass_start - 3,
                    reader_start: pass_start,
                });
            }
        }
        if plan.window_count() > 0 {
            trace.push(ScheduleEvent::AdoptLegacy {
                tail_start: plan.tail_start_round(),
                depth: plan.tail_start_round() - 3,
            });
        }
        trace.push(ScheduleEvent::Remainder {
            tail_start: plan.tail_start_round(),
        });
        trace
    }

    fn validate_trace(
        folding_steps: usize,
        plan: MainLayerExecutionPlan,
        actual: &[ScheduleEvent],
    ) -> Result<(), usize> {
        let expected = schedule_trace(folding_steps, plan);
        if actual == expected {
            Ok(())
        } else {
            Err(actual
                .iter()
                .zip(&expected)
                .position(|(actual, expected)| actual != expected)
                .unwrap_or(actual.len().min(expected.len())))
        }
    }

    fn enabled_options() -> GkrBackwardOptions {
        GkrBackwardOptions {
            windowed_main_continuations: true,
            ..GkrBackwardOptions::default()
        }
    }

    #[test]
    fn cpu_main_continuation_schedule_ruled_widths_and_stale_eq_mutation() {
        for (folding_steps, expected_windows, tail_start) in
            [(20usize, 5u8, 18u8), (22, 6, 21), (23, 6, 21), (24, 6, 21)]
        {
            let plan = try_derive_main_layer_execution_plan(
                enabled_options(),
                BackwardExecutionStrategy::WindowedR0,
                folding_steps,
                MainTailRoundBudget::AtLeast {
                    min_tail_rounds: LEGACY_MAIN_TAIL_MIN_ROUNDS,
                },
            )
            .unwrap();
            assert_eq!(plan.window_count(), expected_windows);
            assert_eq!(plan.tail_start_round(), tail_start);

            let trace = schedule_trace(folding_steps, plan);
            assert_eq!(
                &trace[..4],
                &[
                    ScheduleEvent::R0BankFill,
                    ScheduleEvent::R0Window,
                    ScheduleEvent::ExtBankFill,
                    ScheduleEvent::R0Tail,
                ]
            );
            assert_eq!(
                trace
                    .iter()
                    .filter(|event| matches!(event, ScheduleEvent::ExtBankFill))
                    .count(),
                1
            );
            let eq_builds: Vec<_> = trace
                .iter()
                .filter_map(|event| match event {
                    ScheduleEvent::FreshEq {
                        pass_start,
                        challenge_offset,
                        challenge_count,
                    } => Some((*pass_start, *challenge_offset, *challenge_count)),
                    _ => None,
                })
                .collect();
            let expected_eq_builds: Vec<_> = (0..expected_windows)
                .map(|index| {
                    let pass_start = 3 + 3 * index;
                    (
                        pass_start,
                        pass_start + 3,
                        folding_steps as u8 - pass_start - 3,
                    )
                })
                .collect();
            assert_eq!(eq_builds, expected_eq_builds);

            let windows: Vec<_> = trace
                .iter()
                .filter_map(|event| match event {
                    ScheduleEvent::Window {
                        pass_start,
                        prev_claim,
                        challenge_out,
                        input_depth,
                        output_depth,
                    } => Some((
                        *pass_start,
                        *prev_claim,
                        *challenge_out,
                        *input_depth,
                        *output_depth,
                    )),
                    _ => None,
                })
                .collect();
            assert_eq!(windows.len(), usize::from(expected_windows));
            for (index, window) in windows.iter().enumerate() {
                let pass_start = 3 + 3 * index as u8;
                assert_eq!(
                    *window,
                    (
                        pass_start,
                        [pass_start, pass_start + 3],
                        [pass_start, pass_start + 3],
                        (index > 0).then_some(pass_start - 3),
                        pass_start,
                    )
                );
                let window_position = trace
                    .iter()
                    .position(|event| {
                        matches!(event, ScheduleEvent::Window { pass_start: r, .. } if *r == pass_start)
                    })
                    .unwrap();
                let tail_position = trace
                    .iter()
                    .position(|event| {
                        matches!(event, ScheduleEvent::Tail { pass_start: r } if *r == pass_start)
                    })
                    .unwrap();
                assert_eq!(tail_position, window_position + 1);
                if index > 0 {
                    let drop_position = trace
                        .iter()
                        .position(|event| {
                            matches!(
                                event,
                                ScheduleEvent::DropAfterRead {
                                    depth,
                                    reader_start,
                                } if *depth == pass_start - 3 && *reader_start == pass_start
                            )
                        })
                        .unwrap();
                    assert!(drop_position > window_position);
                }
            }
            assert_eq!(trace.last(), Some(&ScheduleEvent::Remainder { tail_start }));
            assert!(trace.contains(&ScheduleEvent::AdoptLegacy {
                tail_start,
                depth: tail_start - 3,
            }));
            assert_eq!(validate_trace(folding_steps, plan, &trace), Ok(()));

            let mut stale_eq = trace.clone();
            let mut eq_indices = stale_eq.iter().enumerate().filter_map(|(index, event)| {
                matches!(event, ScheduleEvent::FreshEq { .. }).then_some(index)
            });
            let first = eq_indices.next().expect("at least one Eq build");
            let second = eq_indices.next().expect("at least two Eq builds");
            stale_eq[second] = stale_eq[first];
            assert!(
                validate_trace(folding_steps, plan, &stale_eq).is_err(),
                "reusing the prior pass-local Eq plan must fail"
            );
        }
    }
}
