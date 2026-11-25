use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::{FieldExtension, PrimeField};
use transcript::ChallengePointMass;

use super::{BaseSoundness, ProximityRegime};

/// `floor(log2 |E|)` for the challenge field `E` of degree `E::DEGREE` over `F`.
///
/// BabyBear quartic: `p = 2^31 - 2^27 + 1`, `4·log2(p) ≈ 123.63` → `123`.
/// Proth120: `p = 7·2^120 + 1`, `log2(p) ≈ 122.81` → `122`. Rounding down is
/// the soundness-safe choice: a smaller field size in the formulas can only
/// *increase* the required PoW, never decrease it.
pub const fn challenge_field_size_log2<F: PrimeField, E: FieldExtension<F>>() -> usize {
    let mut size = 1u128;
    let mut i = 0;
    while i < E::DEGREE {
        size = match size.checked_mul(F::CHARACTERISTICS_U128) {
            Some(size) => size,
            None => panic!("challenge field order exceeds u128"),
        };
        i += 1;
    }
    size.ilog2() as usize
}

/// Total degree (in the lookup challenges α = `lookup_alpha`, γ = `lookup_additive`)
/// of the cleared logUp identity, which bounds the lookup-argument soundness error
/// by Schwartz–Zippel: `ε ≤ degree · max_point_mass` per candidate base witness.
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
    let fractions_per_row = compiled_circuit
        .num_generic_lookups
        .checked_add(compiled_circuit.range_check_16_lookup_expressions.len())
        .and_then(|count| {
            count.checked_add(
                compiled_circuit
                    .timestamp_range_check_lookup_expressions
                    .len(),
            )
        })
        .expect("lookup fraction count per row exceeds usize");
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
    fractions_per_row
        .checked_mul(compiled_circuit.trace_len)
        .and_then(|count| count.checked_add(compiled_circuit.total_tables_size))
        .and_then(|count| count.checked_add(virtual_table_fractions))
        .and_then(|count| count.checked_mul(tuple_width))
        .expect("lookup identity degree exceeds usize")
}

pub(super) const fn ceil_log2(value: u128) -> u32 {
    assert!(value > 0, "ceil_log2 requires a positive integer");
    u128::BITS - (value - 1).leading_zeros()
}

/// PoW bits for LogUp at the requested security level, charging the rounded
/// identity degree and the rounded product of the point mass and base list size.
pub(super) fn lookup_challenges_pow_bits(
    security_bits: u32,
    identity_degree: usize,
    base: BaseSoundness,
    base_lde_log2: usize,
    sampler: ChallengePointMass,
) -> u32 {
    if identity_degree == 0 {
        return 0;
    }
    let preimages = u128::from(sampler.max_preimages);
    let mut loss = ceil_log2(preimages);
    if let BaseSoundness::Ethproofs(ProximityRegime::JohnsonBound { m }) = base {
        assert!(m >= 3, "Johnson base multiplicity must be at least 3");
        assert!(
            (1..usize::BITS as usize).contains(&base_lde_log2),
            "Johnson base LDE log2 must be positive and fit the base domain",
        );
        // (K·L)^2 = (K·(2m+1))^2 · 2^r / 4.
        let scaled = preimages * (2 * u128::from(m) + 1);
        let squared = scaled
            .checked_mul(scaled)
            .expect("lookup list charge exceeds u128");
        loss = (ceil_log2(squared) + base_lde_log2 as u32).div_ceil(2) - 1;
    }
    let no_pow_bits = sampler
        .random_bits
        .saturating_sub(loss + ceil_log2(identity_degree as u128));
    let pow_bits = security_bits.saturating_sub(no_pow_bits);
    assert!(
        pow_bits <= sampler.max_pow_bits,
        "lookup PoW {pow_bits} exceeds the transcript limit of {} bits",
        sampler.max_pow_bits,
    );
    pow_bits
}

/// Number of base-layer columns (memory + witness + committed setup): the
/// number of COMMITTED base-oracle columns when the base commitment is not
/// packed. See [`committed_base_oracle_columns`] for the packed count.
pub fn total_base_oracle_columns<F: PrimeField>(compiled_circuit: &GKRCircuitArtifact<F>) -> usize {
    compiled_circuit.memory_layout.total_width
        + compiled_circuit.witness_layout.total_width
        + compiled_circuit.generic_lookup_tables_width
}

/// Number of PHYSICALLY committed polynomials for three committed column sets
/// of `num_memory_columns`, `num_witness_columns` and `num_setup_columns`
/// base columns, each packed by `2^pack_log2` consecutive columns (a short
/// tail group is zero-padded): `ceil(n / 2^pack_log2)` per set. A merged
/// memory+witness commitment is ONE set — pass its total as the memory count
/// and `0` witness columns. The count the WHIR batching challenge is raised
/// to powers over, and thus the `num_batched_oracles` of
/// [`batched_proximity_check_pow_bits`].
pub const fn physically_committed_polys(
    num_memory_columns: usize,
    num_witness_columns: usize,
    num_setup_columns: usize,
    pack_log2: usize,
) -> usize {
    let pack = 1usize << pack_log2;
    num_memory_columns.div_ceil(pack)
        + num_witness_columns.div_ceil(pack)
        + num_setup_columns.div_ceil(pack)
}

/// [`physically_committed_polys`] of a compiled circuit's base layer: its
/// memory, witness and (committed, non-virtual) setup columns, with memory and
/// witness as ONE set when `merged_memory_and_witness`. Equals
/// [`total_base_oracle_columns`] when `pack_log2 == 0`.
pub fn committed_base_oracle_columns<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    pack_log2: usize,
    merged_memory_and_witness: bool,
) -> usize {
    let memory = compiled_circuit.memory_layout.total_width;
    let witness = compiled_circuit.witness_layout.total_width;
    let setup = compiled_circuit.generic_lookup_tables_width;
    if merged_memory_and_witness {
        physically_committed_polys(memory + witness, 0, setup, pack_log2)
    } else {
        physically_committed_polys(memory, witness, setup, pack_log2)
    }
}

/// PoW bits required before the WHIR batching (proximity) challenge `γ`.
///
/// The challenge combines the `ℓ = num_batched_columns` committed base
/// codewords `f_i : L → F` (each claimed in `RS[L, 2^domain_size_log2]`,
/// `|L| = 2^(domain_size_log2 + lde_factor_log2)`) into `g = Σ γ^i f_i`. The
/// term bounded here is the correlated-agreement error of that combination —
/// `g` being `δ`-close to the code while some `f_i` is not (or the closest
/// codewords not combining to the one `g` is close to) — which under the
/// linear proximity-gap conjecture is `≈ ℓ · |L| / |F|`: `ceil_log2(ℓ)` bits
/// for the powers-of-`γ` curve plus the evaluation-domain size.
///
/// The base round's `fold_log2` does NOT enter. With `fold_log2 > 0` the
/// verifier then folds `g` by a separate challenge and shift-queries the
/// fold; with `fold_log2 == 0` (virtual packing) it shift-queries `g`
/// itself against the re-encoded intermediate oracle 0 — in the WHIR view a
/// `2^ceil_log2(ℓ)`-ary fold of the virtual interleaving of the columns,
/// whose sub-functions are exactly the `f_i` on `L`, so the fold error is the
/// same `ℓ`, `|L|` and rate as the batching reading. Both modes query the
/// same code (`RS[·, ·]` at the base rate) with the same bits per query; the
/// only term the folding mode adds is its own `fold_log2`-step
/// folding-challenge error (gated by `folding_pow_bits`, not by this PoW).
/// Physical packing enters through the inputs: the packed message size and
/// the physically committed (packed) column count.
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

/// PoW bits for the WHIR batching challenge at the given security level, size
/// of the batched polynomials (`message_size_log2`: the trace length, or the
/// trace length plus `pack_log2` in the packed commitment mode), base LDE rate
/// (`lde_factor_log2 = log2(base_lde_factor)`) and number of batched
/// base-oracle columns
pub const fn batched_proximity_check_pow_bits<F: PrimeField, E: FieldExtension<F>>(
    security_bits: usize,
    message_size_log2: usize,
    lde_factor_log2: usize,
    num_batched_oracles: usize,
) -> u32 {
    pow_bits_for_batched_proximity(
        security_bits,
        message_size_log2,
        lde_factor_log2,
        num_batched_oracles,
        challenge_field_size_log2::<F, E>(),
    ) as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::Proth120;
    use transcript::{Blake2sTranscript, Keccak256Transcript, Transcript};

    const BABY_BEAR: ChallengePointMass =
        <Blake2sTranscript as Transcript<BabyBearField, BabyBearExt4>>::CHALLENGE_POINT_MASS;
    const PROTH120: ChallengePointMass = Keccak256Transcript::CHALLENGE_POINT_MASS;

    fn batched_bits(security_bits: usize, message_log2: usize, lde: usize, ell: usize) -> u32 {
        batched_proximity_check_pow_bits::<BabyBearField, BabyBearExt4>(
            security_bits,
            message_log2,
            lde,
            ell,
        )
    }

    #[test]
    fn physically_committed_polys_counts_packed_sets() {
        // unpacked: one committed poly per column
        assert_eq!(physically_committed_polys(225, 538, 6, 0), 769);
        // the Blake pack4 fixture: 15 + 34 + 1 (tail groups zero-padded)
        assert_eq!(physically_committed_polys(225, 538, 6, 4), 50);
        // merged memory+witness: one set of 763 -> 48, plus the setup
        assert_eq!(physically_committed_polys(225 + 538, 0, 6, 4), 49);
        // empty sets commit nothing
        assert_eq!(physically_committed_polys(0, 7, 0, 2), 2);
    }

    #[test]
    fn challenge_field_sizes() {
        assert_eq!(
            challenge_field_size_log2::<BabyBearField, BabyBearExt4>(),
            123
        );
        assert_eq!(
            challenge_field_size_log2::<BabyBearField, BabyBearField>(),
            30
        );
        assert_eq!(challenge_field_size_log2::<Proth120, Proth120>(), 122);
    }

    #[test]
    fn lookup_challenge_point_masses() {
        assert_eq!((BABY_BEAR.random_bits, BABY_BEAR.max_preimages), (128, 81));
        assert_eq!((PROTH120.random_bits, PROTH120.max_preimages), (128, 37));
    }

    #[test]
    fn lookup_degree_is_rounded_up() {
        let pow = |target, degree| {
            lookup_challenges_pow_bits(
                target,
                degree,
                BaseSoundness::PessimisticConjecture,
                1,
                BABY_BEAR,
            )
        };
        assert_eq!(pow(100, 1 << 30), 9);
        assert_eq!(pow(100, (1 << 30) + 1), 10);
        assert_eq!(pow(80, 1 << 30), 0);
        assert_eq!(pow(150, 0), 0);
    }

    #[test]
    fn lookup_pow_charges_the_johnson_base_list() {
        let unique = BaseSoundness::Ethproofs(ProximityRegime::UniqueDecoding);
        let johnson = BaseSoundness::Ethproofs(ProximityRegime::JohnsonBound { m: 3 });
        let degree = 2_302_283_530;
        assert_eq!(
            lookup_challenges_pow_bits(100, degree, unique, 3, BABY_BEAR),
            11
        );
        assert_eq!(
            lookup_challenges_pow_bits(100, degree, johnson, 3, BABY_BEAR),
            14
        );
        assert_eq!(
            lookup_challenges_pow_bits(100, degree, johnson, 4, BABY_BEAR),
            15
        );
        assert_eq!(
            lookup_challenges_pow_bits(100, 1_235_357_450, johnson, 7, PROTH120),
            14
        );
    }

    #[test]
    #[should_panic(expected = "exceeds the transcript limit")]
    fn lookup_pow_rejects_difficulty_above_transcript_limit() {
        lookup_challenges_pow_bits(154, 1, BaseSoundness::PessimisticConjecture, 1, BABY_BEAR);
    }

    #[test]
    fn batched_proximity_pow_is_zero_at_80_bits() {
        // batch_bits = ceil_log2(ℓ) ≤ 10 for ℓ ≤ 1024; no_pow = 123 - (trace+1) - batch_bits ≥ 87 > 80.
        for &(trace, ell) in &[(20usize, 49usize), (24, 875)] {
            assert_eq!(batched_bits(80, trace, 1, ell), 0);
        }
    }

    #[test]
    fn batched_proximity_pow_at_100_scales_with_oracle_count() {
        // no_pow = 123 - (trace + lde) - ceil_log2(ℓ); pow = max(0, 100 - no_pow).
        // trace 24, lde 1: ℓ=49 → ceil_log2=6 → no_pow=92 → pow=8; ℓ=875 → 10 → no_pow=88 → pow=12.
        assert_eq!(batched_bits(100, 24, 1, 49), 8);
        assert_eq!(batched_bits(100, 24, 1, 875), 12);
        // smaller trace ⇒ fewer bits: trace 20, ℓ=875 → no_pow=92 → pow=8.
        assert_eq!(batched_bits(100, 20, 1, 875), 8);
    }

    #[test]
    fn batched_proximity_pow_for_packed_proth120() {
        // 2^22 trace packed by 2^4 → 2^26 message at LDE 32, ℓ=114:
        // no_pow = 122 - (26 + 5) - 7 = 84 → pow = 16.
        assert_eq!(
            batched_proximity_check_pow_bits::<Proth120, Proth120>(100, 26, 5, 114),
            16
        );
    }
}
