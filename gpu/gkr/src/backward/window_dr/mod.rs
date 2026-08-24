mod binding;
mod composition;
mod generated_registry;

#[cfg(test)]
mod reference;

#[cfg(all(test, not(no_cuda)))]
mod differential_tests;

// Task 5 directly exercises these stable producer names; Task 6 prepares them.
#[allow(unused_imports)]
pub(crate) use binding::{
    bind_dr_window_r0, build_dr_window_continuation_batch, dr_window_partials_len,
    dr_window_row_tiles, launch_dr_window_r0, prepare_dr_window_r0,
    resolve_dr_global_active_eq_slot, DrCompactSourceTableBuilder, DrContinuationFactoredEqScratch,
    DrContinuationFactoredEqView, DrWindowBindError, DrWindowContinuationArena,
    DrWindowContinuationSource, DrWindowLaunch, DrWindowLaunchBinding, DrWindowR0Preparation,
    DrWindowRuntimeScratch,
};
// D1/DR-cont consumes the composition policy and persistent ownership seam.
#[allow(unused_imports)]
pub(crate) use composition::{
    continuation_window_count, megakernel_entry_round, DrWindowLayerCompositionHook,
    DrWindowLayerPreparationHook, DrWindowPassEqState, DrWindowPassEqView,
    DrWindowRawInputKeepalive,
};

pub(crate) fn validate_dr_window_folding_steps(
    folding_steps: usize,
) -> Result<(), DrWindowBindError> {
    binding::validate_dr_window_folding_steps(folding_steps)
}

#[cfg(test)]
mod tests;
