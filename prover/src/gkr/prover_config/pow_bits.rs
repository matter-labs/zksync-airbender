use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
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

/// Total degree (in the lookup challenges α = `lookup_alpha`, γ = `lookup_additive`)
/// of the cleared logUp identity, which bounds the lookup-argument soundness error
/// by Schwartz–Zippel: `ε ≤ degree / |F|`.
///
/// The verifier draws α, γ and checks
///     `Σ_lookups 1/(RLC_α(tuple) + γ) = Σ_table mult · 1/(RLC_α(entry) + γ)`,
/// where `RLC_α` folds a width-`w` tuple into one field element (degree `w-1` in α)
/// and γ is the logarithmic-derivative denominator shift. Cleared to a polynomial
/// `P(α, γ)`, its total degree is `≤ T·w`, where `T` is the total number of
/// fractions (every lookup access + every table entry) and `w` the max tuple
/// width. We charge every fraction the max α-degree, which over-counts the
/// width-1 range-check fractions — conservative, i.e. it can only ask for *more*
/// PoW, never less. `T = (lookups per row)·N + table entries`.
pub fn lookup_identity_degree<F: PrimeField>(compiled_circuit: &GKRCircuitArtifact<F>) -> usize {
    // Max tuple width folded by `lookup_alpha`; `max(_, 1)` so range-check-only
    // circuits (width 1, no α) still bound the γ-degree (= T).
    let tuple_width = compiled_circuit.generic_lookup_tables_width.max(1);
    // One logUp fraction per (lookup relation × row), across all lookup kinds.
    let fractions_per_row = compiled_circuit.num_generic_lookups
        + compiled_circuit.range_check_16_lookup_expressions.len()
        + compiled_circuit
            .timestamp_range_check_lookup_expressions
            .len();
    let virtual_table_fractions = if compiled_circuit
        .range_check_16_lookup_expressions
        .is_empty()
    {
        0
    } else {
        1usize << 16
    } + if compiled_circuit
        .timestamp_range_check_lookup_expressions
        .is_empty()
    {
        0
    } else {
        1usize << TIMESTAMP_COLUMNS_NUM_BITS
    };
    let total_fractions = fractions_per_row
        .saturating_mul(compiled_circuit.trace_len)
        .saturating_add(compiled_circuit.total_tables_size)
        .saturating_add(virtual_table_fractions);
    total_fractions.saturating_mul(tuple_width)
}

/// PoW bits required before the lookup challenges `lookup_alpha` (α) and
/// `lookup_additive` (γ), so the cq/logUp lookup argument reaches `security_bits`.
///
/// By [`lookup_identity_degree`] the soundness error is `ε ≤ D / |F|`, so the
/// no-PoW security is `log2|F| − ceil(log2 D)` and the PoW closes the gap to
/// `security_bits`.
pub const fn pow_bits_for_cq_lookup(
    security_bits: usize,
    identity_degree: usize,
    field_size_log2: usize,
) -> usize {
    let degree_log2 = identity_degree.next_power_of_two().trailing_zeros() as usize;
    let no_pow_security_bits = field_size_log2.saturating_sub(degree_log2);
    security_bits.saturating_sub(no_pow_security_bits)
}

/// PoW bits for the lookup challenges at the given security level, for a logUp
/// identity of total degree `identity_degree` (see [`lookup_identity_degree`]).
pub const fn lookup_challenges_pow_bits(security_bits: usize, identity_degree: usize) -> u32 {
    pow_bits_for_cq_lookup(security_bits, identity_degree, CHALLENGE_FIELD_SIZE_LOG2) as u32
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
    num_batched_columns: usize,
    field_size_log2: usize,
) -> usize {
    let batch_bits = num_batched_columns.next_power_of_two().trailing_zeros() as usize;
    let lde_domain_log2 = domain_size_log2 + lde_factor_log2;
    let no_pow_security_bits = field_size_log2
        .saturating_sub(lde_domain_log2)
        .saturating_sub(batch_bits);
    security_bits.saturating_sub(no_pow_security_bits)
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
        // no_pow = 123 - ceil(log2 D); for any realistic degree (D <= 2^43 ⇒
        // no_pow >= 80) the lookup PoW is 0 at 80-bit security.
        for degree_log2 in [20u32, 30, 40] {
            assert_eq!(lookup_challenges_pow_bits(80, 1usize << degree_log2), 0);
        }
    }

    #[test]
    fn lookup_pow_at_100_scales_with_identity_degree() {
        // no_pow = 123 - ceil(log2 D); pow = max(0, 100 - no_pow) = max(0, ceil(log2 D) - 23).
        assert_eq!(lookup_challenges_pow_bits(100, 1usize << 24), 1); // 24 - 23
        assert_eq!(lookup_challenges_pow_bits(100, 1usize << 30), 7); // 30 - 23
        assert_eq!(lookup_challenges_pow_bits(100, 1usize << 33), 10); // 33 - 23
                                                                       // ceil(log2) rounds a non-power-of-two up: D = 2^30 + 1 ⇒ 31 ⇒ pow 8.
        assert_eq!(lookup_challenges_pow_bits(100, (1usize << 30) + 1), 8);
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
