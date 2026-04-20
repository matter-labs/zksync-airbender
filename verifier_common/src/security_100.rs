use crate::{SecurityConfig, SecurityModel, SizedProofSecurityConfig};

pub const POW_BITS: usize = 28;
pub const SECURITY_BITS: usize = 100;

#[cfg(not(feature = "worst_case_config_generation"))]
pub const MEMORY_DELEGATION_POW_BITS: usize =
    crate::pow_config_worst_constants::MEMORY_DELEGATION_POW_BITS_100;

#[cfg(feature = "worst_case_config_generation")]
pub const MEMORY_DELEGATION_POW_BITS: usize = 0;

pub struct Security100Marker;

impl<const NUM_FOLDINGS: usize> SecurityConfig<NUM_FOLDINGS> for Security100Marker {
    const CONFIG: SizedProofSecurityConfig<NUM_FOLDINGS> =
        SizedProofSecurityConfig::<NUM_FOLDINGS>::worst_case_config(SecurityModel::Security100);
}
