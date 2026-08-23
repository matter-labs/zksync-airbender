mod reference;

#[doc(hidden)]
pub use reference::{continuation_window_tensor_reference, ContinuationWindowReferenceError};

#[cfg(test)]
mod cpu_tests;
