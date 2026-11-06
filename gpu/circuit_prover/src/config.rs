//! GPU prover configuration policy.
//! Circuit configurations come from `CircuitType::prover_config_in_mode`.

use crate::upstream::SecurityLevel;

/// Security levels the GPU prover supports.
pub const GPU_SUPPORTED_SECURITY_LEVELS: [SecurityLevel; 1] = [SecurityLevel::Sec100];
