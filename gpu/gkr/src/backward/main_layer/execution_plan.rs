use crate::backward::kernels::{make_eq_sizes, record_active_eq_slot_fold, GkrEqSizes};

pub(crate) const WINDOW_WIDTH: usize = 3;
const MAIN_TAIL_MIN_ROUNDS: usize = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MainLayerExecutionPlan {
    window_count: u8,
    tail_start_round: u8,
}

impl MainLayerExecutionPlan {
    pub(crate) fn window_count(self) -> u8 {
        self.window_count
    }

    pub(crate) fn tail_start_round(self) -> u8 {
        self.tail_start_round
    }
}

pub(crate) fn derive_main_layer_execution_plan(folding_steps: usize) -> MainLayerExecutionPlan {
    let rounds_after_r0 = folding_steps
        .checked_sub(WINDOW_WIDTH)
        .expect("main layer is too narrow for windowed R0");
    let windowable_rounds = rounds_after_r0
        .checked_sub(MAIN_TAIL_MIN_ROUNDS)
        .expect("main layer must retain a tail round");
    let window_count = windowable_rounds / WINDOW_WIDTH;
    let tail_start_round = window_count
        .checked_mul(WINDOW_WIDTH)
        .and_then(|rounds| WINDOW_WIDTH.checked_add(rounds))
        .expect("main layer execution plan overflowed");
    let tail_rounds = folding_steps
        .checked_sub(tail_start_round)
        .expect("main layer tail starts after its final round");
    assert!(tail_rounds >= MAIN_TAIL_MIN_ROUNDS);
    MainLayerExecutionPlan {
        window_count: window_count.try_into().unwrap(),
        tail_start_round: tail_start_round.try_into().unwrap(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MainEqBoundaryWitness {
    pub(crate) consumer_round: u8,
    pub(crate) semantic_suffix_offset: u8,
    pub(crate) eq_sizes: GkrEqSizes,
}

/// Checks the one-fold boundary of a fresh pass-local Eq table. A pass at `r`
/// builds `Eq(tau[r+3..folding_steps])`; its tensor tail folds that table once,
/// leaving the consumer at `r+3` the semantic suffix `tau[r+4..]`.
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
mod tests {
    use super::*;

    #[test]
    fn production_plan_preserves_a_nonempty_tail() {
        for (folding_steps, windows, tail_start) in
            [(20, 5, 18), (22, 6, 21), (23, 6, 21), (24, 6, 21)]
        {
            let plan = derive_main_layer_execution_plan(folding_steps);
            assert_eq!(plan.window_count(), windows);
            assert_eq!(plan.tail_start_round(), tail_start);
            assert!(folding_steps > usize::from(tail_start));
        }
    }
}
