//! One GPU startup/runtime failure type.
//!
//! `era_cudart_sys::CudaError` does not implement `std::error::Error`, so it
//! cannot itself be the `source` of an `ExecutionProverError`; it is carried
//! as a typed field instead, and the whole error stays downcastable out of the
//! backend-neutral error it is boxed into.

use era_cudart_sys::CudaError;
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct GpuBackendError {
    /// The rendered message, formatted where the failure was detected.
    pub detail: String,
    /// The originating CUDA status, where there was one.
    pub source: Option<CudaError>,
}

impl GpuBackendError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            detail: message.into(),
            source: None,
        }
    }

    /// `context` names what failed; the CUDA status is appended to it and also
    /// kept typed, so a caller can still read it back off the boxed error.
    pub fn cuda(context: impl Into<String>, source: CudaError) -> Self {
        Self {
            detail: format!("{}: {source:?}", context.into()),
            source: Some(source),
        }
    }
}

impl fmt::Display for GpuBackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.detail)
    }
}

impl Error for GpuBackendError {}

/// Fold per-worker startup acknowledgements into one result.
///
/// A worker that dies before it can report leaves silence, and silence must
/// not read as success — hence the count check. A reported failure is
/// preferred over the bare count mismatch because it says more.
pub(crate) fn collect_worker_acknowledgements(
    expected: usize,
    acknowledgements: impl IntoIterator<Item = Result<(), GpuBackendError>>,
) -> Result<(), GpuBackendError> {
    let mut received = 0usize;
    let mut first_error = None;
    for acknowledgement in acknowledgements {
        received += 1;
        if let Err(error) = acknowledgement {
            if first_error.is_none() {
                first_error = Some(error);
            }
        }
    }
    if let Some(error) = first_error {
        return Err(error);
    }
    if received != expected {
        return Err(GpuBackendError::new(format!(
            "only {received} of {expected} GPU workers acknowledged startup"
        )));
    }
    Ok(())
}

/// Await the manager's single aggregate startup result. The manager publishes
/// exactly one value and then drops the sender, so a disconnect without a
/// value means the manager itself died.
pub(crate) fn await_startup_aggregate(
    receiver: &crossbeam_channel::Receiver<Result<(), GpuBackendError>>,
) -> Result<(), GpuBackendError> {
    match receiver.recv() {
        Ok(result) => result,
        Err(_) => Err(GpuBackendError::new(
            "the GPU manager exited before reporting startup",
        )),
    }
}
