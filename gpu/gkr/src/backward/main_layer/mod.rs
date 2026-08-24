pub(super) mod blueprints;
pub(crate) mod execution_plan {
    // Task 6 consumes this reviewed path when continuation scheduling lands.
    #[allow(unused_imports)]
    pub(crate) use crate::main_layer_execution_plan::{
        derive_main_layer_execution_plan, main_continuation_post_tail_eq_boundary,
        try_derive_main_layer_execution_plan, MainEqBoundaryWitness, MainLayerExecutionPlan,
        MainTailRoundBudget, LEGACY_MAIN_TAIL_MIN_ROUNDS,
    };
}
pub(super) mod extras;
pub(super) mod input_addresses;
pub(super) mod state;
mod sumcheck_plan;
