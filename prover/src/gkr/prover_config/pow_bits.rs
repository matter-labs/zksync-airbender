

/// log2 of the challenge-field size (BabyBear quartic).
/// BabyBear order `p = 2^31 - 2^27 + 1 = 2013265921`, so `log2(p) ≈ 30.907` and
/// the degree-4 extension has `≈ 4·30.907 = 123.63` bits. We take the
/// conservative floor `123`: a smaller field size in the formulas can only
/// *increase* the required PoW, never decrease it, so rounding down is the
/// soundness-safe choice.
pub const CHALLENGE_FIELD_SIZE_LOG2: usize = 123;

/// PoW bits required before the lookup challenges (`lookup_alpha`,
/// `lookup_additive`), so that the `cq`-style lookup argument reaches
/// `security_bits` of security over a domain of `domain_size_log2` rows.
pub const fn pow_bits_for_cq_lookup(
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

pub const fn lookup_challenges_pow_bits(security_bits: usize, trace_len_log_2: usize) -> u32 {
    pow_bits_for_cq_lookup(security_bits, trace_len_log_2, CHALLENGE_FIELD_SIZE_LOG2) as u32
}

/// PoW bits required before the WHIR batching (proximity) challenge `γ`.
pub const fn pow_bits_for_batched_proximity(
    security_bits: usize,
    domain_size_log2: usize,
    lde_factor_log2: usize,
    field_size_log2: usize,
) -> usize {
    let lde_domain_log2 = domain_size_log2 + lde_factor_log2;
    let no_pow_security_bits = field_size_log2 - lde_domain_log2 - 5;
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

/// PoW bits for the WHIR batching challenge at the given security level, trace
/// length and base LDE rate (`lde_factor_log2 = log2(base_lde_factor)`).
pub const fn batched_proximity_check_pow_bits(
    security_bits: usize,
    trace_len_log_2: usize,
    lde_factor_log2: usize,
) -> u32 {
    pow_bits_for_batched_proximity(
        security_bits,
        trace_len_log_2,
        lde_factor_log2,
        CHALLENGE_FIELD_SIZE_LOG2,
    ) as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_pow_is_zero_at_80_bits() {
        // no_pow_security = 123 - trace - 5 = 118 - trace; for traces 20..=24 this
        // is 98..94, all > 80, so no PoW is required at the 80-bit level.
        for trace in [20usize, 22, 24] {
            assert_eq!(
                lookup_challenges_pow_bits(80, trace),
                0
            );
        }
    }

    #[test]
    fn lookup_pow_at_100_bits_matches_hand_computation() {
        // no_pow_security = 118 - trace; pow = max(0, 100 - (118 - trace)) = max(0, trace - 18).
        assert_eq!(lookup_challenges_pow_bits(100, 20), 2);
        assert_eq!(lookup_challenges_pow_bits(100, 22), 4);
        assert_eq!(lookup_challenges_pow_bits(100, 24), 6);
    }

    #[test]
    fn batched_proximity_pow_is_zero_at_80_bits() {
        // no_pow_security = 123 - (trace + 1) - 5 = 117 - trace; for traces 20..=24 this
        // is 97..93, all > 80.
        for trace in [20usize, 22, 24] {
            assert_eq!(batched_proximity_check_pow_bits(80, trace, 1), 0);
        }
    }

    #[test]
    fn batched_proximity_pow_at_100_bits_matches_hand_computation() {
        // base LDE factor 2 => lde_factor_log2 = 1; no_pow = 117 - trace;
        // pow = max(0, 100 - (117 - trace)) = max(0, trace - 17).
        assert_eq!(batched_proximity_check_pow_bits(100, 20, 1), 3);
        assert_eq!(batched_proximity_check_pow_bits(100, 22, 1), 5);
        assert_eq!(batched_proximity_check_pow_bits(100, 24, 1), 7);
    }
}
