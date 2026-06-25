use cs::gkr_compiler::GKRCircuitArtifact;
use field::PrimeField;

/// log2 of the challenge-field size (BabyBear quartic).
///
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

pub fn total_base_oracle_columns<F: PrimeField>(compiled_circuit: &GKRCircuitArtifact<F>) -> usize {
    compiled_circuit.memory_layout.total_width
        + compiled_circuit.witness_layout.total_width
        + compiled_circuit.generic_lookup_tables_width
}

/// PoW bits required before the WHIR batching (proximity) challenge `γ`.
pub const fn pow_bits_for_batched_proximity(
    security_bits: usize,
    domain_size_log2: usize,
    lde_factor_log2: usize,
    num_batched_oracles: usize,
    field_size_log2: usize,
) -> usize {
    let batch_bits = num_batched_oracles.next_power_of_two().trailing_zeros() as usize;
    let lde_domain_log2 = domain_size_log2 + lde_factor_log2;
    let no_pow_security_bits = field_size_log2
        .saturating_sub(lde_domain_log2)
        .saturating_sub(batch_bits);
    if security_bits > no_pow_security_bits {
        security_bits - no_pow_security_bits
    } else {
        0
    }
}

/// PoW bits for the WHIR batching challenge at the given security level, trace
/// length, base LDE rate (`lde_factor_log2 = log2(base_lde_factor)`) and number
/// of batched base-oracle columns
pub const fn batched_proximity_check_pow_bits(
    security_bits: usize,
    trace_len_log_2: usize,
    lde_factor_log2: usize,
    num_batched_oracles: usize,
) -> u32 {
    pow_bits_for_batched_proximity(
        security_bits,
        trace_len_log_2,
        lde_factor_log2,
        num_batched_oracles,
        CHALLENGE_FIELD_SIZE_LOG2,
    ) as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_pow_is_zero_at_80_bits() {
        // no_pow = 123 - trace - 5 = 118 - trace; for traces 20..=24 this is 98..94, all > 80.
        for trace in [20usize, 22, 24] {
            assert_eq!(lookup_challenges_pow_bits(80, trace), 0);
        }
    }

    #[test]
    fn lookup_pow_at_100_bits_matches_hand_computation() {
        // no_pow = 118 - trace; pow = max(0, 100 - (118 - trace)) = max(0, trace - 18).
        assert_eq!(lookup_challenges_pow_bits(100, 20), 2);
        assert_eq!(lookup_challenges_pow_bits(100, 22), 4);
        assert_eq!(lookup_challenges_pow_bits(100, 24), 6);
    }

    #[test]
    fn batched_proximity_pow_is_zero_at_80_bits() {
        // batch_bits = ceil_log2(ℓ) ≤ 10 for ℓ ≤ 1024; no_pow = 123 - (trace+1) - batch_bits ≥ 87 > 80.
        for &(trace, ell) in &[(20usize, 49usize), (24, 875)] {
            assert_eq!(batched_proximity_check_pow_bits(80, trace, 1, ell), 0);
        }
    }

    #[test]
    fn batched_proximity_pow_at_100_scales_with_oracle_count() {
        // no_pow = 123 - (trace + lde) - ceil_log2(ℓ); pow = max(0, 100 - no_pow).
        // trace 24, lde 1: ℓ=49 → ceil_log2=6 → no_pow=92 → pow=8; ℓ=875 → 10 → no_pow=88 → pow=12.
        assert_eq!(batched_proximity_check_pow_bits(100, 24, 1, 49), 8);
        assert_eq!(batched_proximity_check_pow_bits(100, 24, 1, 875), 12);
        // smaller trace ⇒ fewer bits: trace 20, ℓ=875 → no_pow=92 → pow=8.
        assert_eq!(batched_proximity_check_pow_bits(100, 20, 1, 875), 8);
    }
}
