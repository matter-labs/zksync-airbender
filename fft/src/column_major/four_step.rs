//! Four-step (Bailey) NTT: a natural-order → natural-order transform that never
//! performs a full-size bit-reversal permutation and keeps every FFT butterfly
//! pass inside the cache.
//!
//! For `N = N1·N2` (both ≈ √N), writing an input index `i = i1 + N1·i2` and an
//! output index `k = k2 + N2·k1`:
//!
//! ```text
//! Y[k2 + N2·k1] = Σ_{i1} ω^{i1·k2} · ω_{N1}^{i1·k1} · ( Σ_{i2} x[i1 + N1·i2] · ω_{N2}^{i2·k2} )
//! ```
//!
//! which factors into: (1) a transposed gather of `x` into `N1` contiguous rows
//! of length `N2` (the coset-offset scaling `x[i]·offset^i` is fused into this
//! copy as `offset^{i1} · (offset^{N1})^{i2}`), (2) an `N2`-point FFT of every
//! row plus the `ω^{i1·k2}` twiddle correction while the row is cache-hot,
//! (3) a tiled transpose, (4) an `N1`-point FFT of every (now contiguous)
//! column, (5) a final tiled transpose into natural output order.
//!
//! Every pass streams memory sequentially (tiled for the transposes); the row
//! FFTs run on √N-sized slices that fit in L1/L2, where the small bit-reversal
//! and the classic DIT butterflies are cheap. The row FFTs reuse the standard
//! bit-reversed twiddle table: the table for a size-`M` domain is a prefix of
//! the table for any larger domain.
//!
//! The output VALUES are identical to the classic
//! `distribute_powers + bitreverse + serial_ct_ntt_bitreversed_to_natural`
//! pipeline (exact field arithmetic, same mathematical DFT), so commitments and
//! proofs do not depend on which implementation is used.

use crate::column_major::naive::serial_ct_ntt_bitreversed_to_natural;
use crate::utils::bitreverse_enumeration_inplace;
use ::field::*;

/// Transpose tile side. 16 elements = 64 B..256 B per tile row for the field
/// sizes in use (4 B base fields to 16 B extensions) — 1..4 cache lines.
const TILE: usize = 16;

/// Below this size the four-step bookkeeping is not worth it; the caller should
/// use the classic pipeline. `lde_coset_natural_four_step` applies the fallback
/// automatically.
pub const FOUR_STEP_MIN_LOG2: u32 = 14;

/// `dst[c·rows + r] = src[r·cols + c]` (viewing `src` as `rows`×`cols`
/// row-major), tiled for cache locality.
fn transpose_into<E: Copy>(src: &[E], rows: usize, cols: usize, dst: &mut [E]) {
    debug_assert_eq!(src.len(), rows * cols);
    debug_assert_eq!(dst.len(), rows * cols);
    let mut rt = 0;
    while rt < rows {
        let r_end = core::cmp::min(rt + TILE, rows);
        let mut ct = 0;
        while ct < cols {
            let c_end = core::cmp::min(ct + TILE, cols);
            for r in rt..r_end {
                for c in ct..c_end {
                    unsafe {
                        *dst.get_unchecked_mut(c * rows + r) = *src.get_unchecked(r * cols + c);
                    }
                }
            }
            ct += TILE;
        }
        rt += TILE;
    }
}

/// Step 1: gather `x` (viewed as `N2`×`N1` row-major) transposed into
/// `dst` = `N1`×`N2`, scaling element `i = i1 + N1·i2` by
/// `pa[i1]·pb[i2] = offset^{i1} · (offset^{N1})^{i2}` on the way. `pa`/`pb`
/// empty means no scaling (offset == 1).
fn gather_transpose_scaled<F: Field, E: Field + FieldExtension<F>>(
    x: &[E],
    n1: usize,
    n2: usize,
    pa: &[F],
    pb: &[F],
    dst: &mut [E],
) {
    debug_assert_eq!(x.len(), n1 * n2);
    let scale = !pa.is_empty();
    let mut i2t = 0;
    while i2t < n2 {
        let i2_end = core::cmp::min(i2t + TILE, n2);
        let mut i1t = 0;
        while i1t < n1 {
            let i1_end = core::cmp::min(i1t + TILE, n1);
            for i2 in i2t..i2_end {
                for i1 in i1t..i1_end {
                    unsafe {
                        let mut v = *x.get_unchecked(i2 * n1 + i1);
                        if scale {
                            let mut f = *pa.get_unchecked(i1);
                            f.mul_assign(pb.get_unchecked(i2));
                            v.mul_assign_by_base(&f);
                        }
                        *dst.get_unchecked_mut(i1 * n2 + i2) = v;
                    }
                }
            }
            i1t += TILE;
        }
        i2t += TILE;
    }
}

/// Powers `base^0 .. base^{count-1}`.
fn powers<F: Field>(base: F, count: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(count);
    let mut cur = F::ONE;
    for _ in 0..count {
        out.push(cur);
        cur.mul_assign(&base);
    }
    out
}

/// Serial four-step forward NTT of `x` (multilinear/monomial coefficients in
/// natural order) evaluated on the coset `offset·<ω>`: returns
/// `y[k] = Σ_i x[i]·offset^i·ω^{ik}` in natural order.
///
/// * `omega` — the domain generator for `N = x.len()` (`ω`).
/// * `omegas_bit_reversed` — the standard bit-reversed forward twiddle table for
///   a domain of size ≥ `N` (only the `N1/2`-prefix is read).
/// * `scratch` — resized to `N` and used as the intermediate buffer; reuse it
///   across calls to avoid re-allocation.
///
/// Values are exactly equal to the classic
/// `copy + distribute_powers + bitreverse + DIT` pipeline.
pub fn fft_natural_to_natural_four_step<F: Field, E: Field + FieldExtension<F>>(
    x: &[E],
    offset: F,
    omega: F,
    omegas_bit_reversed: &[F],
    scratch: &mut Vec<E>,
) -> Vec<E> {
    fft_natural_to_natural_four_step_with_kernel(
        x,
        offset,
        omega,
        omegas_bit_reversed,
        scratch,
        serial_ct_ntt_bitreversed_to_natural::<F, E>,
    )
}

/// [`fft_natural_to_natural_four_step`] with radix-4 row FFTs (see
/// `higher_radix`): same values, 2 butterfly levels fused per row pass.
pub fn fft_natural_to_natural_four_step_r4<F: Field, E: Field + FieldExtension<F>>(
    x: &[E],
    offset: F,
    omega: F,
    omegas_bit_reversed: &[F],
    scratch: &mut Vec<E>,
) -> Vec<E> {
    fft_natural_to_natural_four_step_with_kernel(
        x,
        offset,
        omega,
        omegas_bit_reversed,
        scratch,
        crate::column_major::higher_radix::serial_ct_ntt_bitreversed_to_natural_radix4::<F, E>,
    )
}

/// [`fft_natural_to_natural_four_step`] with radix-8 row FFTs.
pub fn fft_natural_to_natural_four_step_r8<F: Field, E: Field + FieldExtension<F>>(
    x: &[E],
    offset: F,
    omega: F,
    omegas_bit_reversed: &[F],
    scratch: &mut Vec<E>,
) -> Vec<E> {
    fft_natural_to_natural_four_step_with_kernel(
        x,
        offset,
        omega,
        omegas_bit_reversed,
        scratch,
        crate::column_major::higher_radix::serial_ct_ntt_bitreversed_to_natural_radix8::<F, E>,
    )
}

/// Shared four-step body; `row_ntt` is the bit-reversed→natural row transform
/// (radix-2 reference or a fused higher-radix variant — identical values).
fn fft_natural_to_natural_four_step_with_kernel<F: Field, E: Field + FieldExtension<F>>(
    x: &[E],
    offset: F,
    omega: F,
    omegas_bit_reversed: &[F],
    scratch: &mut Vec<E>,
    row_ntt: fn(&mut [E], u32, &[F]),
) -> Vec<E> {
    let n = x.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();
    assert!(log_n >= 2, "four-step needs at least 4 points");

    // N1 rows of length N2; N1 >= N2.
    let log_n2 = log_n / 2;
    let log_n1 = log_n - log_n2;
    let n1 = 1usize << log_n1;
    let n2 = 1usize << log_n2;

    // Offset-scaling factor tables (empty = no scaling).
    let (pa, pb) = if offset != F::ONE {
        let pa = powers(offset, n1);
        let step = offset.pow(n1 as u32);
        let pb = powers(step, n2);
        (pa, pb)
    } else {
        (Vec::new(), Vec::new())
    };

    // Buffers: `a` is the primary (returned) buffer, `scratch` the secondary.
    let mut a: Vec<E> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        a.set_len(n)
    };
    scratch.clear();
    scratch.reserve(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        scratch.set_len(n)
    };

    // Step 1: transposed gather (+ fused offset scaling): a = N1×N2.
    gather_transpose_scaled(x, n1, n2, &pa, &pb, &mut a[..]);

    // Step 2: per-row N2-point FFT + ω^{i1·k2} twiddle correction while hot.
    let row_twiddles_n2 = &omegas_bit_reversed[..(n2 / 2).max(1)];
    let mut w_row = F::ONE; // ω^{i1}
    for i1 in 0..n1 {
        let row = &mut a[i1 * n2..(i1 + 1) * n2];
        bitreverse_enumeration_inplace(row);
        row_ntt(row, log_n2, row_twiddles_n2);
        if i1 != 0 {
            // row[k2] *= ω^{i1·k2}, running product (k2 = 0 factor is one).
            let mut acc = w_row;
            for el in row[1..].iter_mut() {
                el.mul_assign_by_base(&acc);
                acc.mul_assign(&w_row);
            }
        }
        w_row.mul_assign(&omega);
    }

    // Step 3: transpose a (N1×N2) -> scratch (N2×N1).
    transpose_into(&a[..], n1, n2, &mut scratch[..]);

    // Step 4: per-row N1-point FFT over the former columns.
    let row_twiddles_n1 = &omegas_bit_reversed[..(n1 / 2).max(1)];
    for k2 in 0..n2 {
        let row = &mut scratch[k2 * n1..(k2 + 1) * n1];
        bitreverse_enumeration_inplace(row);
        row_ntt(row, log_n1, row_twiddles_n1);
    }

    // Step 5: transpose scratch (N2×N1) -> a; a[k1·N2 + k2] = Y[N2·k1 + k2] is
    // exactly the natural output order.
    transpose_into(&scratch[..], n2, n1, &mut a[..]);

    a
}

/// One serial LDE coset from monomial coefficients, natural order out — the
/// drop-in faster equivalent of the classic
/// `to_vec + distribute_powers_serial + bitreverse + serial DIT` pipeline.
/// Falls back to that classic pipeline below [`FOUR_STEP_MIN_LOG2`].
pub fn lde_coset_natural_four_step<F: Field, E: Field + FieldExtension<F>>(
    monomials_natural_order: &[E],
    offset: F,
    omega: F,
    omegas_bit_reversed: &[F],
    scratch: &mut Vec<E>,
) -> Vec<E> {
    let n = monomials_natural_order.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();
    if log_n < FOUR_STEP_MIN_LOG2 {
        let mut evals = monomials_natural_order.to_vec();
        if offset != F::ONE {
            crate::field_utils::distribute_powers_serial(&mut evals, F::ONE, offset);
        }
        bitreverse_enumeration_inplace(&mut evals);
        serial_ct_ntt_bitreversed_to_natural(
            &mut evals,
            log_n,
            &omegas_bit_reversed[..(n / 2).max(1)],
        );
        return evals;
    }
    fft_natural_to_natural_four_step(
        monomials_natural_order,
        offset,
        omega,
        omegas_bit_reversed,
        scratch,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field_utils::distribute_powers_serial;
    use crate::field_utils::domain_generator_for_size;
    use crate::twiddles::precompute_all_twiddles_for_fft_serial;
    use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use ::field::Proth120;
    use std::alloc::Global;

    fn reference<F: Field, E: Field + FieldExtension<F>>(
        x: &[E],
        offset: F,
        omegas_bit_reversed: &[F],
    ) -> Vec<E> {
        let mut v = x.to_vec();
        if offset != F::ONE {
            distribute_powers_serial(&mut v, F::ONE, offset);
        }
        bitreverse_enumeration_inplace(&mut v);
        serial_ct_ntt_bitreversed_to_natural(
            &mut v,
            x.len().trailing_zeros(),
            &omegas_bit_reversed[..x.len() / 2],
        );
        v
    }

    fn check<F: PrimeField + TwoAdicField + Rand, E: Field + FieldExtension<F> + Rand>(
        log_n: u32,
        with_offset: bool,
    ) {
        let n = 1usize << log_n;
        let mut rng = rand::rng();
        let x: Vec<E> = (0..n).map(|_| E::random_element(&mut rng)).collect();
        let tw: Vec<F, Global> = precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);
        let omega = domain_generator_for_size::<F>(n as u64);
        let offset = if with_offset {
            domain_generator_for_size::<F>((n * 8) as u64)
        } else {
            F::ONE
        };

        let expected = reference(&x, offset, &tw);
        let mut scratch = Vec::new();
        let got = fft_natural_to_natural_four_step(&x, offset, omega, &tw, &mut scratch);
        assert_eq!(got, expected, "four-step diverged at log_n={log_n}");
        let got = fft_natural_to_natural_four_step_r4(&x, offset, omega, &tw, &mut scratch);
        assert_eq!(got, expected, "four-step r4 diverged at log_n={log_n}");
        let got = fft_natural_to_natural_four_step_r8(&x, offset, omega, &tw, &mut scratch);
        assert_eq!(got, expected, "four-step r8 diverged at log_n={log_n}");
    }

    #[test]
    fn four_step_matches_reference_babybear() {
        for log_n in [2u32, 3, 4, 5, 8, 11, 14, 16] {
            check::<BabyBearField, BabyBearField>(log_n, false);
            check::<BabyBearField, BabyBearField>(log_n, true);
            check::<BabyBearField, BabyBearExt4>(log_n, true);
        }
    }

    #[test]
    fn four_step_matches_reference_proth120() {
        for log_n in [2u32, 5, 9, 12, 15] {
            check::<Proth120, Proth120>(log_n, false);
            check::<Proth120, Proth120>(log_n, true);
        }
    }
}
