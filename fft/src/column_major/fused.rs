//! Fused front-end for the LDE coset pipeline: one out-of-place pass that
//! combines the input copy, the coset-offset scaling (`x[i]·offset^i`) and the
//! bit-reversal permutation, feeding the classic DIT
//! (`serial_ct_ntt_bitreversed_to_natural`) directly.
//!
//! Compared to the historical `to_vec + distribute_powers_serial + bitreverse`
//! prefix this removes two full passes over the array and, more importantly,
//! replaces `distribute_powers`' serial multiplication chain (latency-bound: each
//! element's factor depends on the previous one) with a two-table split
//! `offset^i = lo[i & (2^h-1)] · hi[i >> h]` of two ~√n tables — a
//! throughput-bound lookup+multiply per element.
//!
//! The output VALUES are identical to the historical pipeline (exact field
//! arithmetic), so commitments/proofs are unchanged.

use crate::column_major::naive::serial_ct_ntt_bitreversed_to_natural;
use crate::utils::{
    bitreverse_index, MEDIUM_BITREVERSE_LOOKUP_TABLE, TINY_BITREVERSE_LOOKUP_TABLE,
    TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE,
};
use ::field::*;

/// `offset^i` factored as `lo[i & (2^h - 1)] · hi[i >> h]` with `h = ⌈log n / 2⌉`:
/// two ~√n tables instead of an n-long serial power chain.
pub struct SplitPowers<F: Field> {
    lo: Vec<F>,
    hi: Vec<F>,
    h: u32,
}

impl<F: Field> SplitPowers<F> {
    pub fn new(offset: F, n: usize) -> Self {
        debug_assert!(n.is_power_of_two());
        let log_n = n.trailing_zeros();
        let h = log_n.div_ceil(2);
        let lo_len = 1usize << h;
        let hi_len = n >> h;

        let mut lo = Vec::with_capacity(lo_len);
        let mut cur = F::ONE;
        for _ in 0..lo_len {
            lo.push(cur);
            cur.mul_assign(&offset);
        }
        // `cur` is now offset^{2^h}, the stride of the hi table.
        let stride = cur;
        let mut hi = Vec::with_capacity(hi_len);
        let mut cur = F::ONE;
        for _ in 0..hi_len {
            hi.push(cur);
            cur.mul_assign(&stride);
        }
        Self { lo, hi, h }
    }

    #[inline(always)]
    pub fn get(&self, i: usize) -> F {
        let mut f = unsafe { *self.lo.get_unchecked(i & ((1usize << self.h) - 1)) };
        f.mul_assign(unsafe { self.hi.get_unchecked(i >> self.h) });
        f
    }
}

/// `dst[j] = src[bitrev(j)] · offset^{bitrev(j)}` for every `j` — the fused
/// copy + scale + bit-reversal. Pass `None` for `powers` when `offset == 1`.
///
/// Loop structure mirrors the optimized in-place bit-reversal: `j` is split into
/// a low `TINY`-sized part and a high part so that for each fixed high part a
/// batch of `2^TINY` destinations is written; the batched sources share their
/// high bits, keeping reads within `2^TINY` cache lines per batch.
pub fn scaled_bitreverse_gather<F: Field, E: Field + FieldExtension<F>>(
    src: &[E],
    powers: Option<&SplitPowers<F>>,
    dst: &mut [E],
) {
    let n = src.len();
    assert_eq!(dst.len(), n);
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();

    // Small inputs: direct loop.
    if n <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
        for j in 0..n {
            let src_idx = bitreverse_index(j, log_n);
            let mut v = src[src_idx];
            if let Some(p) = powers {
                v.mul_assign_by_base(&p.get(src_idx));
            }
            dst[j] = v;
        }
        return;
    }

    let tiny_log = TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32;
    let common_part_log_n = log_n - tiny_log;
    let work_size = 1u32 << common_part_log_n;

    let mut i = 0u32;
    while i < work_size {
        // bitreverse the common (high destination) part byte by byte
        let mut bytes = i.swap_bytes().to_le_bytes();
        bytes[0] = 0;
        bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
        bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
        bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];
        let reversed_i = u32::from_le_bytes(bytes) >> (32 - common_part_log_n);

        debug_assert!(reversed_i == i.reverse_bits() >> (32 - common_part_log_n));

        let mut j = 0usize;
        while j < TINY_BITREVERSE_LOOKUP_TABLE.len() {
            let reversed_j = TINY_BITREVERSE_LOOKUP_TABLE[j] as usize;
            let dst_idx = (i as usize) | (j << common_part_log_n);
            let src_idx = reversed_j | ((reversed_i as usize) << tiny_log);
            unsafe {
                let mut v = *src.get_unchecked(src_idx);
                if let Some(p) = powers {
                    v.mul_assign_by_base(&p.get(src_idx));
                }
                *dst.get_unchecked_mut(dst_idx) = v;
            }
            j += 1;
        }

        i += 1;
    }
}

/// `dst[i] = src[i] · offset^i` in one sequential pass, with the offset powers
/// from the two-table split (no serial multiplication chain). Fuses the
/// historical `to_vec + distribute_powers_serial` prefix.
pub fn scaled_copy_sequential<F: Field, E: Field + FieldExtension<F>>(
    src: &[E],
    powers: Option<&SplitPowers<F>>,
    dst: &mut [E],
) {
    debug_assert_eq!(src.len(), dst.len());
    match powers {
        None => dst.copy_from_slice(src),
        Some(p) => {
            let mask = (1usize << p.h) - 1;
            // walk hi/lo sequentially: lo cycles, hi advances every 2^h elements
            let mut i = 0;
            let n = src.len();
            while i < n {
                let hi = unsafe { *p.hi.get_unchecked(i >> p.h) };
                let block_end = core::cmp::min(n, i + mask + 1);
                for j in i..block_end {
                    unsafe {
                        let mut f = *p.lo.get_unchecked(j & mask);
                        f.mul_assign(&hi);
                        let mut v = *src.get_unchecked(j);
                        v.mul_assign_by_base(&f);
                        *dst.get_unchecked_mut(j) = v;
                    }
                }
                i = block_end;
            }
        }
    }
}

/// One serial LDE coset (natural order in/out) with the sequential fused
/// prefix: scaled copy (split-table powers) → in-place bit-reversal → DIT.
/// Every pass keeps its best memory-access pattern; the `distribute_powers`
/// latency chain is gone.
pub fn lde_coset_natural_seq_fused<F: Field, E: Field + FieldExtension<F>>(
    monomials_natural_order: &[E],
    offset: F,
    omegas_bit_reversed: &[F],
) -> Vec<E> {
    let n = monomials_natural_order.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();

    let mut out: Vec<E> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        out.set_len(n)
    };

    let powers = (offset != F::ONE).then(|| SplitPowers::new(offset, n));
    scaled_copy_sequential(monomials_natural_order, powers.as_ref(), &mut out[..]);
    crate::utils::bitreverse_enumeration_inplace(&mut out[..]);
    serial_ct_ntt_bitreversed_to_natural(&mut out, log_n, &omegas_bit_reversed[..(n / 2).max(1)]);
    out
}

/// One serial LDE coset from monomial coefficients (natural order in, natural
/// order out): the fused equivalent of
/// `to_vec + distribute_powers_serial + bitreverse + serial DIT`. `scratch` is
/// resized to `n` and holds the result (returned); reuse it across calls to
/// avoid re-allocation.
pub fn lde_coset_natural_fused<F: Field, E: Field + FieldExtension<F>>(
    monomials_natural_order: &[E],
    offset: F,
    omegas_bit_reversed: &[F],
) -> Vec<E> {
    let n = monomials_natural_order.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();

    let mut out: Vec<E> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        out.set_len(n)
    };

    let powers = (offset != F::ONE).then(|| SplitPowers::new(offset, n));
    scaled_bitreverse_gather(monomials_natural_order, powers.as_ref(), &mut out[..]);
    serial_ct_ntt_bitreversed_to_natural(&mut out, log_n, &omegas_bit_reversed[..(n / 2).max(1)]);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field_utils::{distribute_powers_serial, domain_generator_for_size};
    use crate::twiddles::precompute_all_twiddles_for_fft_serial;
    use crate::utils::bitreverse_enumeration_inplace;
    use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use ::field::Proth120;
    use std::alloc::Global;

    fn check<F: PrimeField + TwoAdicField + Rand, E: Field + FieldExtension<F> + Rand>(
        log_n: u32,
        with_offset: bool,
    ) {
        let n = 1usize << log_n;
        let mut rng = rand::rng();
        let x: Vec<E> = (0..n).map(|_| E::random_element(&mut rng)).collect();
        let tw: Vec<F, Global> = precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);
        let offset = if with_offset {
            domain_generator_for_size::<F>((n * 8) as u64)
        } else {
            F::ONE
        };

        // reference pipeline
        let mut expected = x.clone();
        if offset != F::ONE {
            distribute_powers_serial(&mut expected, F::ONE, offset);
        }
        bitreverse_enumeration_inplace(&mut expected);
        serial_ct_ntt_bitreversed_to_natural(&mut expected, log_n, &tw[..n / 2]);

        let got = lde_coset_natural_fused(&x, offset, &tw);
        assert_eq!(got, expected, "fused pipeline diverged at log_n={log_n}");

        let got = lde_coset_natural_seq_fused(&x, offset, &tw);
        assert_eq!(
            got, expected,
            "seq-fused pipeline diverged at log_n={log_n}"
        );
    }

    #[test]
    fn fused_matches_reference() {
        for log_n in [1u32, 3, 6, 8, 9, 12, 14, 16] {
            check::<BabyBearField, BabyBearField>(log_n, false);
            check::<BabyBearField, BabyBearField>(log_n, true);
            check::<BabyBearField, BabyBearExt4>(log_n, true);
            check::<Proth120, Proth120>(log_n, true);
        }
    }
}
