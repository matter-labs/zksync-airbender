/// PoW before getting challenges for
/// - memory (linearization + gamma)
/// - delegation (linearization + gamma)
/// - state_permutation (linearization + gamma)
pub fn pow_bits_for_memory_and_delegation(
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

/// PoW before getting challenges for
/// - FRI queries
pub fn num_queries_for_security_params(
    security_bits: usize,
    pow_bits: usize,
    lde_factor_log2: usize,
) -> usize {
    let bits = security_bits - pow_bits;
    let init_res = bits.div_ceil(lde_factor_log2);

    // We should add extra 20% of queries
    init_res + init_res.div_ceil(5)
}

pub fn pow_bits_for_cq_lookup(
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

pub fn pow_bits_for_memory_argument(
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
pub fn pow_bits_for_quotient(
    security_bits: usize,
    challenge_field_size_log2: usize,
    powers_of_alpha: usize,
    lde_factor_log2: usize,
) -> usize {
    let powers_of_alpha_log2 = powers_of_alpha.next_power_of_two().trailing_zeros() as usize;
    let no_pow_security_bits =
        challenge_field_size_log2 - powers_of_alpha_log2 - 4 - lde_factor_log2.div_ceil(2);
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

// https://eprint.iacr.org/2022/1216.pdf
// We can bound L^+ as 4
pub fn pow_bits_for_deep_z(
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
pub fn pow_bits_for_deep_poly_alpha(
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
pub fn pow_bits_for_folding_round(
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

pub fn pow_bits_for_queries(
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
