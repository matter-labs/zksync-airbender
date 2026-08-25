use crate::{
    BackwardExecutionStrategy, GkrBackwardOptions, MainLayerExecutionPlanError,
    MainTailRoundBudgetKind,
};

use crate::backward::kernels::{make_eq_sizes, record_active_eq_slot_fold, GkrEqSizes};

pub(crate) const WINDOW_WIDTH: usize = 3;

pub(crate) const LEGACY_MAIN_TAIL_MIN_ROUNDS: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MainTailRoundBudget {
    AtLeast {
        min_tail_rounds: u8,
    },
    #[allow(dead_code)] // Main-tail supplies this policy after its rebase.
    AtMost {
        max_tail_rounds: u8,
    },
}

fn unsatisfied_tail_budget(
    folding_steps: usize,
    tail_round_budget: MainTailRoundBudget,
) -> MainLayerExecutionPlanError {
    let (tail_round_budget, budget_rounds) = match tail_round_budget {
        MainTailRoundBudget::AtLeast { min_tail_rounds } => {
            (MainTailRoundBudgetKind::AtLeast, min_tail_rounds)
        }
        MainTailRoundBudget::AtMost { max_tail_rounds } => {
            (MainTailRoundBudgetKind::AtMost, max_tail_rounds)
        }
    };
    MainLayerExecutionPlanError::TailBudgetCannotBeSatisfied {
        folding_steps,
        tail_round_budget,
        budget_rounds,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MainLayerExecutionPlan {
    pub(crate) window_count: u8,
    pub(crate) tail_start_round: u8,
}

impl MainLayerExecutionPlan {
    pub(crate) fn window_count(self) -> u8 {
        self.window_count
    }

    #[allow(dead_code)] // Task 6 consumes the boundary when scheduling windows.
    pub(crate) fn tail_start_round(self) -> u8 {
        self.tail_start_round
    }
}

/// Checked plan builder used by preflight and by the main-tail consumer after
/// rebase. An enabled `AtLeast` policy may validly return zero continuation
/// windows; an enabled `AtMost` policy requires a positive window count.
pub(crate) fn try_derive_main_layer_execution_plan(
    options: GkrBackwardOptions,
    strategy: BackwardExecutionStrategy,
    folding_steps: usize,
    tail_round_budget: MainTailRoundBudget,
) -> Result<MainLayerExecutionPlan, MainLayerExecutionPlanError> {
    if strategy == BackwardExecutionStrategy::PerRound {
        return Ok(MainLayerExecutionPlan {
            window_count: 0,
            tail_start_round: 1,
        });
    }
    if !options.windowed_main_continuations {
        return Ok(MainLayerExecutionPlan {
            window_count: 0,
            tail_start_round: WINDOW_WIDTH as u8,
        });
    }

    let rounds_after_r0 = folding_steps
        .checked_sub(WINDOW_WIDTH)
        .ok_or(MainLayerExecutionPlanError::FoldingStepsBeforeWindowedR0 { folding_steps })?;
    let window_count = match tail_round_budget {
        MainTailRoundBudget::AtLeast { min_tail_rounds } => {
            if min_tail_rounds == 0 {
                return Err(MainLayerExecutionPlanError::ZeroTailRoundBudget);
            }
            let min_tail_rounds = usize::from(min_tail_rounds);
            let windowable_rounds = rounds_after_r0
                .checked_sub(min_tail_rounds)
                .ok_or_else(|| unsatisfied_tail_budget(folding_steps, tail_round_budget))?;
            windowable_rounds / WINDOW_WIDTH
        }
        MainTailRoundBudget::AtMost { max_tail_rounds } => {
            if max_tail_rounds == 0 {
                return Err(MainLayerExecutionPlanError::ZeroTailRoundBudget);
            }
            let excess_rounds = rounds_after_r0.saturating_sub(usize::from(max_tail_rounds));
            excess_rounds.div_ceil(WINDOW_WIDTH).max(1)
        }
    };

    let tail_start_round = window_count
        .checked_mul(WINDOW_WIDTH)
        .and_then(|rounds| WINDOW_WIDTH.checked_add(rounds))
        .ok_or(MainLayerExecutionPlanError::ArithmeticOverflow)?;
    let tail_rounds = folding_steps
        .checked_sub(tail_start_round)
        .ok_or_else(|| unsatisfied_tail_budget(folding_steps, tail_round_budget))?;
    let budget_is_satisfied = match tail_round_budget {
        MainTailRoundBudget::AtLeast { min_tail_rounds } => {
            tail_rounds >= usize::from(min_tail_rounds)
        }
        MainTailRoundBudget::AtMost { max_tail_rounds } => {
            window_count > 0 && tail_rounds > 0 && tail_rounds <= usize::from(max_tail_rounds)
        }
    };
    if !budget_is_satisfied {
        return Err(unsatisfied_tail_budget(folding_steps, tail_round_budget));
    }

    let window_count = u8::try_from(window_count).map_err(|_| {
        MainLayerExecutionPlanError::PlanDoesNotFitRuntimeFields {
            window_count,
            tail_start_round,
        }
    })?;
    let tail_start_round = u8::try_from(tail_start_round).map_err(|_| {
        MainLayerExecutionPlanError::PlanDoesNotFitRuntimeFields {
            window_count: usize::from(window_count),
            tail_start_round,
        }
    })?;
    Ok(MainLayerExecutionPlan {
        window_count,
        tail_start_round,
    })
}

#[allow(dead_code)] // Task 6 and main-tail consume the validated infallible seam.
pub(crate) fn derive_main_layer_execution_plan(
    options: GkrBackwardOptions,
    strategy: BackwardExecutionStrategy,
    folding_steps: usize,
    tail_round_budget: MainTailRoundBudget,
) -> MainLayerExecutionPlan {
    try_derive_main_layer_execution_plan(options, strategy, folding_steps, tail_round_budget)
        .unwrap_or_else(|error| panic!("invalid main-layer execution policy: {error:?}"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)] // Task 6 and main-tail consume the pass-local boundary witness.
pub(crate) struct MainEqBoundaryWitness {
    pub(crate) consumer_round: u8,
    pub(crate) semantic_suffix_offset: u8,
    pub(crate) eq_sizes: GkrEqSizes,
}

/// Checks the one-fold boundary of a fresh pass-local Eq table. A pass at `r`
/// builds `Eq(tau[r+3..folding_steps])`; its tensor tail folds that table once,
/// leaving the consumer at `r+3` the semantic suffix `tau[r+4..]`.
#[allow(dead_code)] // Task 6 validates each scheduled continuation tail with this seam.
pub(crate) fn main_continuation_post_tail_eq_boundary(
    pass_start_round: u8,
    folding_steps: usize,
    actual_eq_sizes: GkrEqSizes,
) -> MainEqBoundaryWitness {
    let pass_start_round = usize::from(pass_start_round);
    let consumer_round = pass_start_round
        .checked_add(WINDOW_WIDTH)
        .expect("continuation consumer round overflowed usize");
    let semantic_suffix_offset = consumer_round
        .checked_add(1)
        .expect("continuation Eq suffix offset overflowed usize");
    let challenge_count = folding_steps
        .checked_sub(consumer_round)
        .expect("continuation pass extends past the layer folding steps");
    assert!(
        challenge_count > 0,
        "continuation pass must leave at least one consumer round"
    );
    let mut expected_eq_sizes = make_eq_sizes(challenge_count);
    record_active_eq_slot_fold(&mut expected_eq_sizes);
    assert_eq!(
        actual_eq_sizes, expected_eq_sizes,
        "continuation tail must fold its fresh pass-local Eq table exactly once"
    );
    MainEqBoundaryWitness {
        consumer_round: u8::try_from(consumer_round)
            .expect("continuation consumer round does not fit the runtime field"),
        semantic_suffix_offset: u8::try_from(semantic_suffix_offset)
            .expect("continuation Eq suffix offset does not fit the runtime field"),
        eq_sizes: actual_eq_sizes,
    }
}

#[cfg(test)]
mod cpu_main_layer_execution_plan {
    use super::*;

    fn enabled_options() -> GkrBackwardOptions {
        GkrBackwardOptions {
            windowed_main_continuations: true,
            ..GkrBackwardOptions::default()
        }
    }

    #[test]
    fn ruled_legacy_and_main_tail_tables_are_exact() {
        for (folding_steps, expected_windows, expected_start, expected_tail) in [
            (20, 5, 18, 2),
            (22, 6, 21, 1),
            (23, 6, 21, 2),
            (24, 6, 21, 3),
        ] {
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
            assert_eq!(plan.tail_start_round(), expected_start);
            assert_eq!(
                folding_steps - usize::from(plan.tail_start_round()),
                expected_tail
            );
        }

        for (folding_steps, expected_windows, expected_start, expected_tail) in [
            (20, 4, 15, 5),
            (22, 5, 18, 4),
            (23, 5, 18, 5),
            (24, 5, 18, 6),
        ] {
            let plan = try_derive_main_layer_execution_plan(
                enabled_options(),
                BackwardExecutionStrategy::WindowedR0,
                folding_steps,
                MainTailRoundBudget::AtMost { max_tail_rounds: 6 },
            )
            .unwrap();
            assert_eq!(plan.window_count(), expected_windows);
            assert_eq!(plan.tail_start_round(), expected_start);
            assert_eq!(
                folding_steps - usize::from(plan.tail_start_round()),
                expected_tail
            );
        }
    }

    #[test]
    fn diagnostic_per_round_and_enabled_zero_window_plans_keep_exact_boundaries() {
        let diagnostic = GkrBackwardOptions {
            windowed_main_continuations: false,
            ..GkrBackwardOptions::default()
        };
        let disabled = try_derive_main_layer_execution_plan(
            diagnostic,
            BackwardExecutionStrategy::WindowedR0,
            24,
            MainTailRoundBudget::AtLeast { min_tail_rounds: 1 },
        )
        .unwrap();
        assert_eq!(disabled.window_count(), 0);
        assert_eq!(disabled.tail_start_round(), 3);

        let per_round = try_derive_main_layer_execution_plan(
            enabled_options(),
            BackwardExecutionStrategy::PerRound,
            24,
            MainTailRoundBudget::AtMost { max_tail_rounds: 0 },
        )
        .unwrap();
        assert_eq!(per_round.window_count(), 0);
        assert_eq!(per_round.tail_start_round(), 1);

        for folding_steps in 4..=6 {
            let plan = try_derive_main_layer_execution_plan(
                enabled_options(),
                BackwardExecutionStrategy::WindowedR0,
                folding_steps,
                MainTailRoundBudget::AtLeast { min_tail_rounds: 1 },
            )
            .unwrap();
            assert_eq!(plan.window_count(), 0);
            assert_eq!(plan.tail_start_round(), 3);
        }
    }

    #[test]
    fn invalid_budgets_widths_and_runtime_narrowing_are_typed_errors() {
        for budget in [
            MainTailRoundBudget::AtLeast { min_tail_rounds: 0 },
            MainTailRoundBudget::AtMost { max_tail_rounds: 0 },
        ] {
            assert_eq!(
                try_derive_main_layer_execution_plan(
                    enabled_options(),
                    BackwardExecutionStrategy::WindowedR0,
                    24,
                    budget,
                ),
                Err(MainLayerExecutionPlanError::ZeroTailRoundBudget)
            );
        }
        assert!(matches!(
            try_derive_main_layer_execution_plan(
                enabled_options(),
                BackwardExecutionStrategy::WindowedR0,
                6,
                MainTailRoundBudget::AtMost { max_tail_rounds: 6 },
            ),
            Err(MainLayerExecutionPlanError::TailBudgetCannotBeSatisfied { .. })
        ));
        assert!(matches!(
            try_derive_main_layer_execution_plan(
                enabled_options(),
                BackwardExecutionStrategy::WindowedR0,
                2,
                MainTailRoundBudget::AtLeast { min_tail_rounds: 1 },
            ),
            Err(MainLayerExecutionPlanError::FoldingStepsBeforeWindowedR0 { .. })
        ));
        assert!(matches!(
            try_derive_main_layer_execution_plan(
                enabled_options(),
                BackwardExecutionStrategy::WindowedR0,
                1_000,
                MainTailRoundBudget::AtLeast { min_tail_rounds: 1 },
            ),
            Err(MainLayerExecutionPlanError::PlanDoesNotFitRuntimeFields { .. })
        ));
    }

    #[test]
    fn pass_local_eq_boundary_is_one_fresh_fold() {
        for pass_start_round in [3u8, 6, 9, 12, 15] {
            let count = 24 - usize::from(pass_start_round) - WINDOW_WIDTH;
            let fresh = make_eq_sizes(count);
            let mut once_folded = fresh;
            record_active_eq_slot_fold(&mut once_folded);
            let witness =
                main_continuation_post_tail_eq_boundary(pass_start_round, 24, once_folded);
            assert_eq!(witness.consumer_round, pass_start_round + 3);
            assert_eq!(witness.semantic_suffix_offset, pass_start_round + 4);
            assert_eq!(witness.eq_sizes, once_folded);

            assert!(
                std::panic::catch_unwind(|| {
                    main_continuation_post_tail_eq_boundary(pass_start_round, 24, fresh)
                })
                .is_err(),
                "an unfurled pass-local Eq table must be rejected at round {pass_start_round}"
            );
            let mut twice_folded = once_folded;
            record_active_eq_slot_fold(&mut twice_folded);
            assert!(
                std::panic::catch_unwind(|| {
                    main_continuation_post_tail_eq_boundary(pass_start_round, 24, twice_folded)
                })
                .is_err(),
                "a twice-folded pass-local Eq table must be rejected at round {pass_start_round}"
            );
        }
    }
}
