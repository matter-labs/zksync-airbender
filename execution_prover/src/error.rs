use std::error::Error;
use std::fmt;

/// Backend-neutral construction/validation failure. Backend errors are wrapped
/// rather than flattened, so a caller can still reach the original.
#[derive(Debug)]
pub enum ExecutionProverError {
    InvalidConfiguration {
        field: &'static str,
        reason: String,
    },
    BackendInitialization {
        backend: &'static str,
        source: Box<dyn Error + Send + Sync>,
    },
}

impl ExecutionProverError {
    pub fn invalid_configuration(field: &'static str, reason: impl Into<String>) -> Self {
        Self::InvalidConfiguration {
            field,
            reason: reason.into(),
        }
    }

    pub fn backend_initialization(
        backend: &'static str,
        source: impl Into<Box<dyn Error + Send + Sync>>,
    ) -> Self {
        Self::BackendInitialization {
            backend,
            source: source.into(),
        }
    }
}

impl fmt::Display for ExecutionProverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConfiguration { field, reason } => {
                write!(
                    f,
                    "invalid execution prover configuration: {field}: {reason}"
                )
            }
            Self::BackendInitialization { backend, source } => {
                write!(f, "{backend} backend initialization failed: {source}")
            }
        }
    }
}

impl Error for ExecutionProverError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidConfiguration { .. } => None,
            Self::BackendInitialization { source, .. } => Some(source.as_ref()),
        }
    }
}
