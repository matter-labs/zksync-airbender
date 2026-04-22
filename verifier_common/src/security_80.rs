use crate::{SecurityConfig, SecurityMarker, SecurityModel, SizedProofSecurityConfig};

pub const POW_BITS: usize = 28;
pub const SECURITY_BITS: usize = 80;

#[cfg(not(feature = "worst_case_config_generation"))]
pub const MEMORY_DELEGATION_POW_BITS: usize =
    crate::pow_config_worst_constants::MEMORY_DELEGATION_POW_BITS_80;

#[cfg(feature = "worst_case_config_generation")]
pub const MEMORY_DELEGATION_POW_BITS: usize = 0;

pub struct Security80Marker;

impl SecurityMarker for Security80Marker {
    const MODEL: SecurityModel = SecurityModel::Security80;

    fn proof_security_config<const NUM_FOLDINGS: usize>() -> SizedProofSecurityConfig<NUM_FOLDINGS>
    {
        <Self as SecurityConfig<NUM_FOLDINGS>>::CONFIG
    }
}

impl<const NUM_FOLDINGS: usize> SecurityConfig<NUM_FOLDINGS> for Security80Marker {
    const CONFIG: SizedProofSecurityConfig<NUM_FOLDINGS> =
        SizedProofSecurityConfig::<NUM_FOLDINGS>::worst_case_config(Self::MODEL);
}
