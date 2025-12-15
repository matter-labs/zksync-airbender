pub const MERSENNE31QUARTIC_SIZE_LOG2: usize = 124; // Mersenne31Quartic size in bits

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProofPowConfig {
    pub lookup_pow_bits: u32,
    pub quotient_alpha_pow_bits: u32,
    pub quotient_z_pow_bits: u32,
    pub deep_poly_alpha_pow_bits: u32,
    pub foldings_pow_bits: Vec<u32>,
    pub fri_queries_pow_bits: u32,
}

// The file should be generated with tools/pow_config_generator
#[cfg(not(feature = "worst_case_config_generation"))]
include!("pow_config_worst_constants.rs");

#[cfg(not(feature = "worst_case_config_generation"))]
impl ProofPowConfig {
    pub fn worst_case_config(
        security_bits: usize,
        num_foldings: usize,
    ) -> Self {
        match security_bits {
            80 => ProofPowConfig {
                lookup_pow_bits: LOOKUP_POW_BITS_FOR_80_SECURITY_BITS as u32,
                quotient_alpha_pow_bits: QUOTIENT_ALPHA_POW_BITS_FOR_80_SECURITY_BITS as u32,
                quotient_z_pow_bits: QUOTIENT_Z_POW_BITS_FOR_80_SECURITY_BITS as u32,
                deep_poly_alpha_pow_bits: DEEP_POLY_ALPHA_POW_BITS_FOR_80_SECURITY_BITS as u32,
                foldings_pow_bits: vec![MAX_FOLDINGS_POW_BITS_FOR_80_SECURITY_BITS as u32; num_foldings],
                fri_queries_pow_bits: FRI_QUERIES_POW_BITS_FOR_80_SECURITY_BITS as u32,
            },
            100 => ProofPowConfig {
                lookup_pow_bits: LOOKUP_POW_BITS_FOR_100_SECURITY_BITS as u32,
                quotient_alpha_pow_bits: QUOTIENT_ALPHA_POW_BITS_FOR_100_SECURITY_BITS as u32,
                quotient_z_pow_bits: QUOTIENT_Z_POW_BITS_FOR_100_SECURITY_BITS as u32,
                deep_poly_alpha_pow_bits: DEEP_POLY_ALPHA_POW_BITS_FOR_100_SECURITY_BITS as u32,
                foldings_pow_bits: vec![MAX_FOLDINGS_POW_BITS_FOR_100_SECURITY_BITS as u32; num_foldings],
                fri_queries_pow_bits: FRI_QUERIES_POW_BITS_FOR_100_SECURITY_BITS as u32,
            },
            _ => panic!("Unsupported security bits"),
        }
    }
}

#[cfg(feature = "worst_case_config_generation")]
impl ProofPowConfig {
    pub fn worst_case_config(
        _security_bits: usize,
        _num_queries: usize,
    ) -> Self {
        ProofPowConfig {
            lookup_pow_bits: 0,
            quotient_alpha_pow_bits: 0,
            quotient_z_pow_bits: 0,
            deep_poly_alpha_pow_bits: 0,
            foldings_pow_bits: vec![],
            fri_queries_pow_bits: 0,
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProofPowChallenges {
    pub lookup_pow_challenge: u64,
    pub quotient_alpha_pow_challenge: u64,
    pub quotient_z_pow_challenge: u64,
    pub deep_poly_alpha_pow_challenge: u64,
    pub foldings_pow_challenges: Vec<u64>,
    pub fri_queries_pow_challenge: u64,
}
