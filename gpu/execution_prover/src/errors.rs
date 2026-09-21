//! Typed GPU startup and runtime failures.
//!
//! `era_cudart_sys::CudaError` does not implement `std::error::Error`, so it
//! cannot itself be the `source` of an `ExecutionProverError`; these variants
//! carry it as a typed field so a caller can still match on it after boxing.

use era_cudart_sys::CudaError;
use gpu_circuit_prover::config::UnsupportedGpuSecurityLevel;
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub enum GpuBackendError {
    UnsupportedSecurityLevel(UnsupportedGpuSecurityLevel),
    DeviceCountQuery(CudaError),
    NoDevices,
    /// A device worker failed to set its device, read its properties, or build
    /// its prover context.
    WorkerInitialization {
        device_id: i32,
        source: CudaError,
    },
    /// `device_count * host_allocators_per_device_count` does not fit.
    ExtraTraceBlocksOverflow {
        device_count: usize,
        per_device: usize,
    },
    HostAllocation {
        bytes: usize,
        source: CudaError,
    },
    HostRegistration {
        bytes: usize,
        source: CudaError,
    },
    Precomputation(CudaError),
    /// The manager thread ended before publishing a startup result — it
    /// panicked, or a scoped worker did.
    ManagerExitedBeforeStartup,
    /// Fewer acknowledgements arrived than there are devices, so at least one
    /// worker died before it could report.
    MissingWorkerAcknowledgements {
        expected: usize,
        received: usize,
    },
    /// A worker's results channel disconnected: it left its loop without
    /// reporting an error of its own.
    WorkerExitedWithoutReporting {
        worker_id: usize,
    },
    /// A device worker or the manager failed while serving accepted work.
    Runtime {
        device_id: i32,
        source: CudaError,
    },
}

impl fmt::Display for GpuBackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedSecurityLevel(inner) => write!(f, "{inner}"),
            Self::DeviceCountQuery(source) => {
                write!(f, "CUDA device count query failed: {source:?}")
            }
            Self::NoDevices => write!(f, "no CUDA capable devices found"),
            Self::WorkerInitialization { device_id, source } => {
                write!(f, "GPU worker {device_id} failed to initialize: {source:?}")
            }
            Self::ExtraTraceBlocksOverflow {
                device_count,
                per_device,
            } => write!(
                f,
                "{device_count} devices x {per_device} host buffers per device overflows"
            ),
            Self::HostAllocation { bytes, source } => {
                write!(
                    f,
                    "pinned host allocation of {bytes} bytes failed: {source:?}"
                )
            }
            Self::HostRegistration { bytes, source } => write!(
                f,
                "CUDA registration of {bytes} bytes of guest RAM failed: {source:?}"
            ),
            Self::Precomputation(source) => {
                write!(f, "GPU precomputation failed: {source:?}")
            }
            Self::ManagerExitedBeforeStartup => {
                write!(f, "the GPU manager exited before reporting startup")
            }
            Self::MissingWorkerAcknowledgements { expected, received } => write!(
                f,
                "only {received} of {expected} GPU workers acknowledged startup"
            ),
            Self::WorkerExitedWithoutReporting { worker_id } => write!(
                f,
                "GPU worker {worker_id} exited without reporting a result"
            ),
            Self::Runtime { device_id, source } => {
                write!(
                    f,
                    "GPU worker {device_id} failed during execution: {source:?}"
                )
            }
        }
    }
}

impl Error for GpuBackendError {}

/// Total extra host trace blocks the per-device allowance adds. Checked here
/// because the shared accounting only sees the already-multiplied result.
pub(crate) fn extra_trace_blocks_for(
    device_count: usize,
    per_device: usize,
) -> Result<usize, GpuBackendError> {
    device_count
        .checked_mul(per_device)
        .ok_or(GpuBackendError::ExtraTraceBlocksOverflow {
            device_count,
            per_device,
        })
}

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
        return Err(GpuBackendError::MissingWorkerAcknowledgements { expected, received });
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
        Err(_) => Err(GpuBackendError::ManagerExitedBeforeStartup),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_extra_trace_blocks_multiply_and_reject_overflow() {
        assert_eq!(extra_trace_blocks_for(2, 128).unwrap(), 256);
        assert_eq!(extra_trace_blocks_for(0, 128).unwrap(), 0);

        let error = extra_trace_blocks_for(usize::MAX, 2).unwrap_err();
        assert!(matches!(
            error,
            GpuBackendError::ExtraTraceBlocksOverflow { .. }
        ));
    }

    #[test]
    fn cpu_worker_acknowledgements_report_the_first_failure() {
        collect_worker_acknowledgements(2, [Ok(()), Ok(())]).unwrap();

        let error = collect_worker_acknowledgements(
            3,
            [
                Ok(()),
                Err(GpuBackendError::WorkerInitialization {
                    device_id: 1,
                    source: CudaError::ErrorMemoryAllocation,
                }),
                Err(GpuBackendError::NoDevices),
            ],
        )
        .unwrap_err();

        match error {
            GpuBackendError::WorkerInitialization { device_id, source } => {
                assert_eq!(device_id, 1);
                assert_eq!(source, CudaError::ErrorMemoryAllocation);
            }
            other => panic!("expected the first failure, got {other:?}"),
        }
    }

    /// Silence must not read as success: a worker that dies before
    /// acknowledging would otherwise produce a "started" dead manager.
    #[test]
    fn cpu_missing_acknowledgements_are_a_startup_failure() {
        let error = collect_worker_acknowledgements(2, []).unwrap_err();
        assert!(matches!(
            error,
            GpuBackendError::MissingWorkerAcknowledgements {
                expected: 2,
                received: 0
            }
        ));

        // A partial list of all-Ok acknowledgements is the same failure.
        let error = collect_worker_acknowledgements(2, [Ok(())]).unwrap_err();
        assert!(matches!(
            error,
            GpuBackendError::MissingWorkerAcknowledgements {
                expected: 2,
                received: 1
            }
        ));
    }

    /// A manager that panics drops its sender without publishing; the
    /// handshake must read that as failure, not as an empty success.
    #[test]
    fn cpu_manager_death_before_the_aggregate_is_a_startup_failure() {
        let (sender, receiver) = crossbeam_channel::unbounded::<Result<(), GpuBackendError>>();
        drop(sender);

        assert!(matches!(
            await_startup_aggregate(&receiver).unwrap_err(),
            GpuBackendError::ManagerExitedBeforeStartup
        ));
    }

    /// The point of the typed error: a caller can still recover what went
    /// wrong after it has been boxed into the backend-neutral error.
    #[test]
    fn cpu_startup_errors_survive_as_an_execution_prover_error_source() {
        let startup = GpuBackendError::WorkerInitialization {
            device_id: 3,
            source: CudaError::ErrorInvalidValue,
        };
        let error = execution_prover::ExecutionProverError::backend_initialization("gpu", startup);

        let source = std::error::Error::source(&error).expect("source chain preserved");
        let downcast = source
            .downcast_ref::<GpuBackendError>()
            .expect("the typed GPU error survives boxing");
        assert!(matches!(
            downcast,
            GpuBackendError::WorkerInitialization {
                device_id: 3,
                source: CudaError::ErrorInvalidValue
            }
        ));
        assert!(error.to_string().contains("gpu"));
    }
}
