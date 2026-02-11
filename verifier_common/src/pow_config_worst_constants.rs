const MAX_TRACE_LEN_LOG2: usize = 24usize;
const MAX_FRI_FACTOR_LOG2: usize = 1usize;
const MAX_CHALLENGE_FIELD_SIZE_LOG2: usize = 124usize;
const MAX_NUMBER_OF_COLUMNS: usize = 1224usize;
const MAX_NUM_QUOTIENT_TERMS: usize = 928usize;
const MAX_NUM_OPENINGS_AT_Z: usize = 1225usize;
const MAX_NUM_OPENINGS_AT_Z_OMEGA: usize = 13usize;
const MAX_FRI_FOLDING_FACTOR_LOG2: usize = 4usize;
const POW_BITS_FOR_MEMORY_AND_DELEGATION_FOR_80_SECURITY_BITS: usize = 0usize;
const POW_BITS_FOR_MEMORY_AND_DELEGATION_FOR_100_SECURITY_BITS: usize = 8usize;
const LOOKUP_POW_BITS_FOR_80_SECURITY_BITS: usize = 0usize;
const LOOKUP_POW_BITS_FOR_100_SECURITY_BITS: usize = 5usize;
const QUOTIENT_ALPHA_POW_BITS_FOR_80_SECURITY_BITS: usize = 0usize;
const QUOTIENT_ALPHA_POW_BITS_FOR_100_SECURITY_BITS: usize = 0usize;
const QUOTIENT_Z_POW_BITS_FOR_80_SECURITY_BITS: usize = 0usize;
const QUOTIENT_Z_POW_BITS_FOR_100_SECURITY_BITS: usize = 6usize;
const DEEP_POLY_ALPHA_POW_BITS_FOR_80_SECURITY_BITS: usize = 0usize;
const DEEP_POLY_ALPHA_POW_BITS_FOR_100_SECURITY_BITS: usize = 11usize;
const MAX_FOLDINGS_POW_BITS_FOR_80_SECURITY_BITS: usize = 0usize;
const MAX_FOLDINGS_POW_BITS_FOR_100_SECURITY_BITS: usize = 4usize;
const FRI_QUERIES_POW_BITS_FOR_80_SECURITY_BITS: usize = 28usize;
const FRI_QUERIES_POW_BITS_FOR_100_SECURITY_BITS: usize = 28usize;
const NUM_QUERIES_FOR_80_SECURITY_BITS: usize = 63usize;
const NUM_QUERIES_FOR_100_SECURITY_BITS: usize = 87usize;
impl<const NUM_FOLDINGS: usize> SizedProofSecurityConfig<NUM_FOLDINGS> {
    pub const fn worst_case_config() -> Self {
        if cfg!(feature = "security_80") {
            SizedProofSecurityConfig {
                lookup_pow_bits: LOOKUP_POW_BITS_FOR_80_SECURITY_BITS as u32,
                quotient_alpha_pow_bits: QUOTIENT_ALPHA_POW_BITS_FOR_80_SECURITY_BITS as u32,
                quotient_z_pow_bits: QUOTIENT_Z_POW_BITS_FOR_80_SECURITY_BITS as u32,
                deep_poly_alpha_pow_bits: DEEP_POLY_ALPHA_POW_BITS_FOR_80_SECURITY_BITS as u32,
                foldings_pow_bits: [MAX_FOLDINGS_POW_BITS_FOR_80_SECURITY_BITS as u32;
                    NUM_FOLDINGS],
                fri_queries_pow_bits: FRI_QUERIES_POW_BITS_FOR_80_SECURITY_BITS as u32,
                num_queries: NUM_QUERIES_FOR_80_SECURITY_BITS,
            }
        } else if cfg!(feature = "security_100") {
            SizedProofSecurityConfig {
                lookup_pow_bits: LOOKUP_POW_BITS_FOR_100_SECURITY_BITS as u32,
                quotient_alpha_pow_bits: QUOTIENT_ALPHA_POW_BITS_FOR_100_SECURITY_BITS as u32,
                quotient_z_pow_bits: QUOTIENT_Z_POW_BITS_FOR_100_SECURITY_BITS as u32,
                deep_poly_alpha_pow_bits: DEEP_POLY_ALPHA_POW_BITS_FOR_100_SECURITY_BITS as u32,
                foldings_pow_bits: [MAX_FOLDINGS_POW_BITS_FOR_100_SECURITY_BITS as u32;
                    NUM_FOLDINGS],
                fri_queries_pow_bits: FRI_QUERIES_POW_BITS_FOR_100_SECURITY_BITS as u32,
                num_queries: NUM_QUERIES_FOR_100_SECURITY_BITS,
            }
        } else {
            panic!("No security level selected");
        }
    }
}
