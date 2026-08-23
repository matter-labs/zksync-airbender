mod abi;
#[allow(dead_code)] // Task 6 schedules the launch-ready Task 5 surface.
mod binding;
#[allow(dead_code)] // Task 6 dispatches the generated bank through `binding`.
mod generated_registry;
mod publication;
mod reference;

#[allow(unused_imports)] // Task 6 consumes this staged production seam.
pub(crate) use binding::{
    bind_first_main_continuation_window, bind_later_main_continuation_window,
    launch_main_continuation_window, MainContinuationWindowBindError,
    MainContinuationWindowLaunched, MainContinuationWindowRuntimeScratch,
};

pub(crate) use publication::{
    preserve_owned_on_validation_error, repoint_final_evaluations_from_raw,
    validate_adoption_state, validate_canonical_publication, ContinuationPublicationError,
    ContinuationPublishedLevel, ContinuationPublishedShape,
};
#[doc(hidden)]
pub use reference::{continuation_window_tensor_reference, ContinuationWindowReferenceError};

#[cfg(test)]
mod cpu_tests;
