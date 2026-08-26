mod binding;
mod composition;
mod generated_registry;

pub(crate) use binding::{
    dr_window_partials_len, launch_dr_window_continuation, launch_dr_window_r0,
    prepare_dr_window_r0, resolve_dr_global_active_eq_slot, DrWindowBindError,
};
pub(crate) use composition::{DrWindowLayerPreparationHook, DrWindowPassEqState};

pub(crate) fn validate_dr_window_folding_steps(
    folding_steps: usize,
) -> Result<(), DrWindowBindError> {
    binding::validate_dr_window_folding_steps(folding_steps)
}
