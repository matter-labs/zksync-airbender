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

impl ProofPowConfig {
    pub fn from_parameters(
        security_bits: usize,
        domain_size_log2: usize,
        lde_domain_size_log2: usize,
        field_size_log2: usize,
        powers_of_quotient_alpha: usize,
        powers_of_deep_poly_alpha: usize,
        folding_sequence: &[usize],
        num_queries: usize,
        lde_factor_log2: usize,
    ) -> Self {
        let foldings_pow_bits = folding_sequence
            .iter()
            .map(|&folding_factor_log2| {
                pow_bits_for_folding_round(
                    security_bits,
                    field_size_log2,
                    domain_size_log2,
                    folding_factor_log2,
                ) as u32
            })
            .collect();
        Self {
            lookup_pow_bits: pow_bits_for_cq_lookup(
                security_bits,
                domain_size_log2,
                field_size_log2,
            ) as u32,
            quotient_alpha_pow_bits: pow_bits_for_quotient(
                security_bits,
                field_size_log2,
                powers_of_quotient_alpha,
                lde_factor_log2,
            ) as u32,
            quotient_z_pow_bits: pow_bits_for_deep_z(
                security_bits,
                field_size_log2,
                lde_domain_size_log2,
            ) as u32,
            deep_poly_alpha_pow_bits: pow_bits_for_deep_poly_alpha(
                security_bits,
                field_size_log2,
                domain_size_log2,
                powers_of_deep_poly_alpha,
            ) as u32,
            foldings_pow_bits,
            fri_queries_pow_bits: pow_bits_for_queries(security_bits, num_queries, lde_factor_log2)
                as u32,
        }
    }

    pub fn from_compiled_circuit(
        security_bits: usize,
        compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        lde_factor: usize,
        num_queries: usize,
    ) -> Self {
        let domain_size_log2 = compiled_circuit.trace_len.trailing_zeros() as usize;
        let lde_factor_log2 = lde_factor.trailing_zeros() as usize;
        let lde_domain_size_log2 = domain_size_log2 + lde_factor_log2;
        let field_size_log2 = MERSENNE31QUARTIC_SIZE_LOG2;
        let powers_of_quotient_alpha = compiled_circuit.compute_num_quotient_terms();
        let powers_of_deep_poly_alpha =
            compiled_circuit.num_openings_at_z() + compiled_circuit.num_openings_at_z_omega();
        let optimal_folding = crate::definitions::OPTIMAL_FOLDING_PROPERTIES[domain_size_log2];
        let folding_sequence = &optimal_folding.folding_sequence;

        Self::from_parameters(
            security_bits,
            domain_size_log2,
            lde_domain_size_log2,
            field_size_log2,
            powers_of_quotient_alpha,
            powers_of_deep_poly_alpha,
            folding_sequence,
            num_queries,
            lde_factor_log2,
        )
    }

    pub fn for_queries_only(pow_bits: u32) -> Self {
        Self {
            lookup_pow_bits: 0,
            quotient_alpha_pow_bits: 0,
            quotient_z_pow_bits: 0,
            deep_poly_alpha_pow_bits: 0,
            foldings_pow_bits: vec![0; 5],
            fri_queries_pow_bits: pow_bits,
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

/// PoW before getting challenges for
/// - memory (linearization + gamma)
/// - delegation (linearization + gamma)
/// - state_permutation (linearization + gamma)
pub const fn pow_bits_for_memory_and_delegation(
    security_bits: usize,
    // These challenges are shared between all circuits in one layer, so we need to use the max number of cycles
    max_cycles_log2: usize,
    field_size_log2: usize,
) -> usize {
    let lookup_pow = pow_bits_for_cq_lookup(security_bits, max_cycles_log2, field_size_log2);
    let memory_pow = pow_bits_for_memory_argument(security_bits, max_cycles_log2, field_size_log2);

    if lookup_pow > memory_pow {
        lookup_pow
    } else {
        memory_pow
    }
}

#[derive(Clone, Copy, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct SizedProofPowConfig<const NUM_FOLDINGS: usize> {
    pub lookup_pow_bits: u32,
    pub quotient_alpha_pow_bits: u32,
    pub quotient_z_pow_bits: u32,
    pub deep_poly_alpha_pow_bits: u32,
    #[serde(bound(deserialize = "[u32; NUM_FOLDINGS]: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "[u32; NUM_FOLDINGS]: serde::Serialize"))]
    pub foldings_pow_bits: [u32; NUM_FOLDINGS],
    pub fri_queries_pow_bits: u32,
}

impl<const NUM_FOLDINGS: usize> From<SizedProofPowConfig<NUM_FOLDINGS>> for ProofPowConfig {
    fn from(value: SizedProofPowConfig<NUM_FOLDINGS>) -> Self {
        ProofPowConfig {
            lookup_pow_bits: value.lookup_pow_bits,
            quotient_alpha_pow_bits: value.quotient_alpha_pow_bits,
            quotient_z_pow_bits: value.quotient_z_pow_bits,
            deep_poly_alpha_pow_bits: value.deep_poly_alpha_pow_bits,
            foldings_pow_bits: value.foldings_pow_bits.to_vec(),
            fri_queries_pow_bits: value.fri_queries_pow_bits,
        }
    }
}

use cs::one_row_compiler::CompiledCircuitArtifact;
use field::Mersenne31Field;
impl<const NUM_FOLDINGS: usize> SizedProofPowConfig<NUM_FOLDINGS> {
    pub const fn from_parameters(
        security_bits: usize,
        domain_size_log2: usize,
        lde_domain_size_log2: usize,
        field_size_log2: usize,
        powers_of_quotient_alpha: usize,
        powers_of_deep_poly_alpha: usize,
        folding_sequence: &[usize],
        num_queries: usize,
        lde_factor_log2: usize,
    ) -> Self {
        assert!(folding_sequence.len() == NUM_FOLDINGS);
        let mut foldings_pow_bits = [0u32; NUM_FOLDINGS];
        let mut i = 0;
        while i < NUM_FOLDINGS {
            foldings_pow_bits[i] = pow_bits_for_folding_round(
                security_bits,
                field_size_log2,
                domain_size_log2,
                folding_sequence[i],
            ) as u32;
            i += 1;
        }
        Self {
            lookup_pow_bits: pow_bits_for_cq_lookup(
                security_bits,
                domain_size_log2,
                field_size_log2,
            ) as u32,
            quotient_alpha_pow_bits: pow_bits_for_quotient(
                security_bits,
                field_size_log2,
                powers_of_quotient_alpha,
                lde_factor_log2,
            ) as u32,
            quotient_z_pow_bits: pow_bits_for_deep_z(
                security_bits,
                field_size_log2,
                lde_domain_size_log2,
            ) as u32,
            deep_poly_alpha_pow_bits: pow_bits_for_deep_poly_alpha(
                security_bits,
                field_size_log2,
                domain_size_log2,
                powers_of_deep_poly_alpha,
            ) as u32,
            foldings_pow_bits,
            fri_queries_pow_bits: pow_bits_for_queries(security_bits, num_queries, lde_factor_log2)
                as u32,
        }
    }

    pub fn from_compiled_circuit(
        security_bits: usize,
        compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        lde_factor: usize,
        num_queries: usize,
    ) -> Self {
        let domain_size_log2 = compiled_circuit.trace_len.trailing_zeros() as usize;
        let lde_factor_log2 = lde_factor.trailing_zeros() as usize;
        let lde_domain_size_log2 = domain_size_log2 + lde_factor_log2;
        let field_size_log2 = MERSENNE31QUARTIC_SIZE_LOG2;
        let powers_of_quotient_alpha = compiled_circuit.compute_num_quotient_terms();
        let powers_of_deep_poly_alpha =
            compiled_circuit.num_openings_at_z() + compiled_circuit.num_openings_at_z_omega();
        let optimal_folding = crate::definitions::OPTIMAL_FOLDING_PROPERTIES[domain_size_log2];
        let folding_sequence = &optimal_folding.folding_sequence;

        Self::from_parameters(
            security_bits,
            domain_size_log2,
            lde_domain_size_log2,
            field_size_log2,
            powers_of_quotient_alpha,
            powers_of_deep_poly_alpha,
            folding_sequence,
            num_queries,
            lde_factor_log2,
        )
    }
}

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
pub const fn transcript_challenge_array_size(num_elements: usize, pow_bits: usize) -> usize {
    if pow_bits > 0 {
        (num_elements + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)
    } else {
        num_elements.next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)
    }
}

#[derive(Clone, Copy, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct SizedProofPowChallenges<const NUM_FOLDINGS: usize> {
    pub lookup_pow_challenge: u64,
    pub quotient_alpha_pow_challenge: u64,
    pub quotient_z_pow_challenge: u64,
    pub deep_poly_alpha_pow_challenge: u64,
    #[serde(bound(deserialize = "[u64; NUM_FOLDINGS]: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "[u64; NUM_FOLDINGS]: serde::Serialize"))]
    pub foldings_pow_challenges: [u64; NUM_FOLDINGS],
    pub fri_queries_pow_challenge: u64,
}

/// PoW before getting challenges for
/// - FRI queries
pub const fn num_queries_for_security_params(
    security_bits: usize,
    pow_bits: usize,
    lde_factor_log2: usize,
) -> usize {
    let bits = security_bits - pow_bits;
    let init_res = bits.div_ceil(lde_factor_log2);

    // We should add extra 20% of queries
    init_res + init_res.div_ceil(5)
}

const fn pow_bits_for_cq_lookup(
    security_bits: usize,
    domain_size_log2: usize,
    field_size_log2: usize,
) -> usize {
    let no_pow_security_bits = field_size_log2 - domain_size_log2 - 5;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

const fn pow_bits_for_memory_argument(
    security_bits: usize,
    domain_size_log2: usize,
    field_size_log2: usize,
) -> usize {
    let no_pow_security_bits = field_size_log2 - domain_size_log2 - 2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://eprint.iacr.org/2022/1216.pdf
// We can bound L^+ as 4
const fn pow_bits_for_quotient(
    security_bits: usize,
    challenge_field_size_log2: usize,
    powers_of_alpha: usize,
    lde_factor_log2: usize,
) -> usize {
    let powers_of_alpha_log2 = powers_of_alpha.next_power_of_two().trailing_zeros() as usize;
    let no_pow_security_bits =
        challenge_field_size_log2 - powers_of_alpha_log2 - 2 - lde_factor_log2.div_ceil(2);
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://eprint.iacr.org/2022/1216.pdf
// We can bound L^+ as 4
const fn pow_bits_for_deep_z(
    security_bits: usize,
    challenge_field_size_log2: usize,
    lde_domain_size_log2: usize,
) -> usize {
    let no_pow_security_bits = challenge_field_size_log2 - lde_domain_size_log2 - 5;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://hackmd.io/@pgaf/HkKs_1ytT
const fn pow_bits_for_deep_poly_alpha(
    security_bits: usize,
    challenge_field_size_log2: usize,
    domain_size_log2: usize,
    powers_of_alpha: usize,
) -> usize {
    let powers_of_alpha_log2 = powers_of_alpha.next_power_of_two().trailing_zeros() as usize;
    let no_pow_security_bits = challenge_field_size_log2 - powers_of_alpha_log2 - domain_size_log2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://hackmd.io/@pgaf/HkKs_1ytT
const fn pow_bits_for_folding_round(
    security_bits: usize,
    challenge_field_size_log2: usize,
    domain_size_log2: usize,
    folding_factor_log2: usize,
) -> usize {
    let no_pow_security_bits = challenge_field_size_log2 - folding_factor_log2 - domain_size_log2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

pub const fn pow_bits_for_queries(
    security_bits: usize,
    num_queries: usize,
    lde_factor_log2: usize,
) -> usize {
    // We should add extra 20% of queries
    let queries_contribution = 5 * num_queries / 6;
    let no_pow_security_bits = queries_contribution * lde_factor_log2;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

pub use worst_case_constants::{worst_pow_config, worst_sized_pow_config};
mod worst_case_constants {
    use super::*;
    // Worst-case constants for PoW bits calculations
    const TRACE_LEN_LOG2: usize = 24; // add_sub_lui_auipc_mop_verifier
    const FRI_FACTOR_LOG2: usize = 1; // always
    const CHALLENGE_FIELD_SIZE_LOG2: usize = MERSENNE31QUARTIC_SIZE_LOG2; // always
    const NUM_QUOTIENT_TERMS: usize = 928; // blake2_with_compression_verifier
    const NUM_OPENINGS_AT_Z: usize = 1225; // blake2_with_compression_verifier
    const NUM_OPENINGS_AT_Z_OMEGA: usize = 13; // inits_and_teardowns_verifier
    const FRI_FOLDING_FACTOR_LOG2: usize = 4; // from OPTIMAL_FOLDING_PROPERTIES
    const POW_BITS_FOR_QUERIES: usize = 28; // always

    #[test]
    fn worst_case_constants() {
        dbg!(worst_pow_config(80, 5));
        dbg!(worst_pow_config(100, 5));
    }

    pub const fn worst_sized_pow_config<const NUM_FRI_STEPS: usize>(
        security_bits: usize,
    ) -> SizedProofPowConfig<NUM_FRI_STEPS> {
        let num_queries =
            num_queries_for_security_params(security_bits, POW_BITS_FOR_QUERIES, FRI_FACTOR_LOG2);

        SizedProofPowConfig::from_parameters(
            security_bits,
            TRACE_LEN_LOG2,
            TRACE_LEN_LOG2 + FRI_FACTOR_LOG2,
            CHALLENGE_FIELD_SIZE_LOG2,
            NUM_QUOTIENT_TERMS,
            NUM_OPENINGS_AT_Z + NUM_OPENINGS_AT_Z_OMEGA,
            &[FRI_FOLDING_FACTOR_LOG2; NUM_FRI_STEPS],
            num_queries,
            FRI_FACTOR_LOG2,
        )
    }

    pub fn worst_pow_config(security_bits: usize, num_fri_steps: usize) -> ProofPowConfig {
        let num_queries =
            num_queries_for_security_params(security_bits, POW_BITS_FOR_QUERIES, FRI_FACTOR_LOG2);

        ProofPowConfig::from_parameters(
            security_bits,
            TRACE_LEN_LOG2,
            TRACE_LEN_LOG2 + FRI_FACTOR_LOG2,
            CHALLENGE_FIELD_SIZE_LOG2,
            NUM_QUOTIENT_TERMS,
            NUM_OPENINGS_AT_Z + NUM_OPENINGS_AT_Z_OMEGA,
            &vec![FRI_FOLDING_FACTOR_LOG2; num_fri_steps],
            num_queries,
            FRI_FACTOR_LOG2,
        )
    }
}
