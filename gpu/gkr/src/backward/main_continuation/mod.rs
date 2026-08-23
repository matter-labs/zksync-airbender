mod publication;
mod reference;

pub(crate) use publication::{
    preserve_owned_on_validation_error, repoint_final_evaluations_from_raw,
    validate_adoption_state, validate_canonical_publication, ContinuationPublicationError,
    ContinuationPublishedLevel, ContinuationPublishedShape,
};
#[doc(hidden)]
pub use reference::{continuation_window_tensor_reference, ContinuationWindowReferenceError};

#[cfg(test)]
mod cpu_tests;
