use super::*;
use worker::Worker;

pub fn multivariate_coeffs_into_hypercube_evals<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1 << size_log2);

    // e.g. we have a poly over X1 and X2 of c0 + c1 X1 + c2 X2 + c3 X1X2
    // and want to compute evaluations at (0, 0), (1, 0), (0, 1), and (1, 1) (and output in this order, so X1 is most-signinicant digit in enumeration)
    // Coefficient at index [i] is one for the term where coefficient in front of X1 is get_bit(i, 0), coefficient for X2 is get_bit(i, 1) and so on.
    // This naturally corresponds to the mapping into univariate poly if X1 = X, X2 = X^2 and so on - then index [i] is just a coefficient for X^i

    // Evaluation procedure is very much like FFT - it's recursive, but out evaluation basis is not polynomial, even though highly structured.
    // E.g. let's look at evaluations for some fixed X2, and for X1 = 0 and 1
    // f(0, X2) = c0 + c1 * 0 + c2 * X2 + c3 * 0 * X2
    // f(1, X2) = c0 + c1 * 1 + c2 * X2 + c3 * 1 * X2
    // That differ only in the value that have bit(i, 0) == 1. So, what we do, is we "fix" some bit, and for all remaining pairs
    // compute either their value, or value + value of opposite bit

    // Self-check
    // f(0, 0) = c0
    // f(0, 1) = c0 + c2
    // f(1, 0) = c0 + c1
    // f(1, 1) = c0 + c1 + c2 + c3

    // we start with the vector of c0, c1, c2, c3
    // "fix" the bit 0 - so our pairs are (c0, c1) and (c2, c3)
    // new evaluations are (c0, c0 + c1), (c2, c2 + c3)
    // then we "fix" bit 1 - new pairs are (c0, c2) and (c0 + c1, c2 + c3) (but we do not rearrange the array and just use stride)
    // and so we get c0, c0 + c1, c0 + c2, c0 + c1 + c2 + c3  - exactly the values, where x1-corresponding "bit" is the lowest one in the index

    // Inverse transformation requires to compute pairs as a' = a, b' = b - a instead, but starting from the MSB (largest stride)

    // first round for simplicity
    for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
        b.add_assign(&a);
    }

    let mut stride = 2;
    let mut iterations = 2;
    let len = 1 << size_log2;
    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].add_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride *= 2;
        iterations *= 2;
    }
}

/// One fused radix-4 sweep over the stride pair `(stride, stride/2)` of the
/// evals→coeffs (Mobius) transform: same subtraction sequence as two
/// single-stride sweeps => identical values, half the loads/stores.
#[inline(always)]
fn evals_into_coeffs_radix4_sweep<F: Field>(input: &mut [F], stride: usize) {
    let len = input.len();
    let s2 = stride / 2;
    let mut base = 0usize;
    while base < len {
        for j in base..base + s2 {
            unsafe {
                let x0 = *input.get_unchecked(j);
                let x1 = *input.get_unchecked(j + s2);
                let x2 = *input.get_unchecked(j + stride);
                let x3 = *input.get_unchecked(j + stride + s2);
                // stage `stride`: x2 -= x0; x3 -= x1. stage `s2`: x1 -= x0; x3 -= x2'
                let mut n2 = x2;
                n2.sub_assign(&x0);
                let mut n3 = x3;
                n3.sub_assign(&x1);
                n3.sub_assign(&n2);
                let mut n1 = x1;
                n1.sub_assign(&x0);
                *input.get_unchecked_mut(j + s2) = n1;
                *input.get_unchecked_mut(j + stride) = n2;
                *input.get_unchecked_mut(j + stride + s2) = n3;
            }
        }
        base += 2 * stride;
    }
}

/// Radix-4 variant of [`multivariate_hypercube_evals_into_coeffs`]: two
/// variables fused per sweep, so the array is traversed `~size_log2/2` times
/// instead of `size_log2`. Identical values (same subtraction sequence);
/// measured ~1.7x (BabyBear) / ~1.2x (Proth120) serial on M3. Supports every
/// power-of-two size (odd variable counts finish with one single-stride pass).
pub fn multivariate_hypercube_evals_into_coeffs_radix4<F: Field>(input: &mut [F], size_log2: u32) {
    let len = 1usize << size_log2;
    assert_eq!(input.len(), len);
    let mut stride = len / 2;
    let mut remaining = size_log2;
    while remaining >= 2 {
        evals_into_coeffs_radix4_sweep(input, stride);
        stride /= 4;
        remaining -= 2;
    }
    if remaining == 1 {
        for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
            b.sub_assign(&a);
        }
    }
}

/// NEON (aarch64) BabyBear variant of
/// [`multivariate_hypercube_evals_into_coeffs`]: radix-8 sweeps with 4-lane
/// vector subtractions for strides >= 4 and in-register `uzp`/`zip` passes for
/// the contiguous small-stride tails. Works on the raw canonical Montgomery
/// values (`repr(transparent)`), byte-identical to the reference; sizes below
/// 16 degrade to the scalar radix-4 path.
#[cfg(target_arch = "aarch64")]
pub fn multivariate_hypercube_evals_into_coeffs_neon_bb(
    input: &mut [::field::baby_bear::base::BabyBearField],
    size_log2: u32,
) {
    use ::field::baby_bear::base::BabyBearField;
    use core::arch::aarch64::*;

    const P: u32 = BabyBearField::ORDER;
    let len = 1usize << size_log2;
    assert_eq!(input.len(), len);
    if len < 16 {
        return multivariate_hypercube_evals_into_coeffs_radix4(input, size_log2);
    }

    #[inline(always)]
    unsafe fn subv(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let d = vsubq_u32(a, b);
        vminq_u32(d, vaddq_u32(d, vdupq_n_u32(P)))
    }

    let p = input.as_mut_ptr() as *mut u32;
    let mut stride = len / 2;
    let mut remaining = size_log2;

    unsafe {
        // fused radix-8 sweeps while the smallest stride in the triple >= 4
        while remaining >= 3 && stride / 4 >= 4 {
            let s2 = stride / 2;
            let s4 = stride / 4;
            let mut base = 0usize;
            while base < len {
                let mut j = base;
                while j < base + s4 {
                    let offs = [
                        j,
                        j + s4,
                        j + s2,
                        j + s2 + s4,
                        j + stride,
                        j + stride + s4,
                        j + stride + s2,
                        j + stride + s2 + s4,
                    ];
                    let mut v = [
                        vld1q_u32(p.add(offs[0])),
                        vld1q_u32(p.add(offs[1])),
                        vld1q_u32(p.add(offs[2])),
                        vld1q_u32(p.add(offs[3])),
                        vld1q_u32(p.add(offs[4])),
                        vld1q_u32(p.add(offs[5])),
                        vld1q_u32(p.add(offs[6])),
                        vld1q_u32(p.add(offs[7])),
                    ];
                    for k in 0..4 {
                        v[k + 4] = subv(v[k + 4], v[k]);
                    }
                    for (hi, lo) in [(2usize, 0usize), (3, 1), (6, 4), (7, 5)] {
                        v[hi] = subv(v[hi], v[lo]);
                    }
                    for (hi, lo) in [(1usize, 0usize), (3, 2), (5, 4), (7, 6)] {
                        v[hi] = subv(v[hi], v[lo]);
                    }
                    for k in 1..8 {
                        vst1q_u32(p.add(offs[k]), v[k]);
                    }
                    j += 4;
                }
                base += 2 * stride;
            }
            stride /= 8;
            remaining -= 3;
        }

        // leftover big strides (>= 4) as single vector sweeps until only a
        // contiguous small-stride tail remains
        while remaining > 3 && stride >= 4 {
            let mut base = 0usize;
            while base < len {
                let mut j = base;
                while j < base + stride {
                    let lo = vld1q_u32(p.add(j));
                    let hi = vld1q_u32(p.add(j + stride));
                    vst1q_u32(p.add(j + stride), subv(hi, lo));
                    j += 4;
                }
                base += 2 * stride;
            }
            stride /= 2;
            remaining -= 1;
        }

        if remaining == 3 {
            // contiguous (4, 2, 1) tail, 8 elements per block in-register.
            // Modular sub against a ZERO lane is the identity, so untouched
            // lanes simply subtract zero.
            debug_assert_eq!(stride, 4);
            let z = vdupq_n_u32(0);
            let mut j = 0usize;
            while j < len {
                let v0 = vld1q_u32(p.add(j));
                let v1 = vld1q_u32(p.add(j + 4));
                let v1 = subv(v1, v0);
                let sh0 = vreinterpretq_u32_u64(vtrn1q_u64(
                    vreinterpretq_u64_u32(z),
                    vreinterpretq_u64_u32(v0),
                ));
                let sh1 = vreinterpretq_u32_u64(vtrn1q_u64(
                    vreinterpretq_u64_u32(z),
                    vreinterpretq_u64_u32(v1),
                ));
                let v0 = subv(v0, sh0);
                let v1 = subv(v1, sh1);
                let e = vuzp1q_u32(v0, v1);
                let o = vuzp2q_u32(v0, v1);
                let no = subv(o, e);
                vst1q_u32(p.add(j), vzip1q_u32(e, no));
                vst1q_u32(p.add(j + 4), vzip2q_u32(e, no));
                j += 8;
            }
            remaining = 0;
        }
        if remaining == 2 {
            // contiguous (2, 1) tail
            debug_assert_eq!(stride, 2);
            let z = vdupq_n_u32(0);
            let mut j = 0usize;
            while j < len {
                let v0 = vld1q_u32(p.add(j));
                let v1 = vld1q_u32(p.add(j + 4));
                let sh0 = vreinterpretq_u32_u64(vtrn1q_u64(
                    vreinterpretq_u64_u32(z),
                    vreinterpretq_u64_u32(v0),
                ));
                let sh1 = vreinterpretq_u32_u64(vtrn1q_u64(
                    vreinterpretq_u64_u32(z),
                    vreinterpretq_u64_u32(v1),
                ));
                let v0 = subv(v0, sh0);
                let v1 = subv(v1, sh1);
                let e = vuzp1q_u32(v0, v1);
                let o = vuzp2q_u32(v0, v1);
                let no = subv(o, e);
                vst1q_u32(p.add(j), vzip1q_u32(e, no));
                vst1q_u32(p.add(j + 4), vzip2q_u32(e, no));
                j += 8;
            }
            remaining = 0;
        }
        if remaining == 1 {
            let mut j = 0usize;
            while j < len {
                let v0 = vld1q_u32(p.add(j));
                let v1 = vld1q_u32(p.add(j + 4));
                let e = vuzp1q_u32(v0, v1);
                let o = vuzp2q_u32(v0, v1);
                let no = subv(o, e);
                vst1q_u32(p.add(j), vzip1q_u32(e, no));
                vst1q_u32(p.add(j + 4), vzip2q_u32(e, no));
                j += 8;
            }
            remaining = 0;
        }
        debug_assert_eq!(remaining, 0, "unhandled tail");
    }
}

pub fn multivariate_hypercube_evals_into_coeffs<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1 << size_log2);
    let len = 1 << size_log2;

    let mut stride = len / 2;
    let mut iterations = len / 2;

    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].sub_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride /= 2;
        iterations /= 2;
    }

    for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
        b.sub_assign(&a);
    }
}

/// Multicore version of [`multivariate_hypercube_evals_into_coeffs`], structured
/// like the parallel NTT in the `fft` crate: the transform is a butterfly network
/// of `size_log2` stages (one per variable, stride `n/2` down to `1`), and every
/// stage is a `worker.scope` over the `n/2` independent butterflies.
///
/// In a stage of stride `S` each butterfly does `input[j + S] -= input[j]` for the
/// `j` whose bit `log2(S)` is zero. Reads come only from the bit-0 positions and
/// writes go only to the disjoint bit-1 positions, so all `n/2` butterflies of a
/// stage touch disjoint pairs — threads can share the buffer (the same
/// `base_addr as usize` trick the parallel NTT uses).
pub fn parallel_multivariate_hypercube_evals_into_coeffs<F: Field>(
    input: &mut [F],
    size_log2: u32,
    worker: &Worker,
) {
    assert_eq!(input.len(), 1 << size_log2);
    let n = input.len();
    if n <= 1 {
        return;
    }

    // Small transforms: per-stage scope overhead dominates, so stay serial.
    const PAR_THRESHOLD: usize = 1 << 12;
    let elem_ratio = (core::mem::size_of::<F>() / core::mem::size_of::<u32>()).max(1);
    let eff_threshold = PAR_THRESHOLD / elem_ratio;
    if n < eff_threshold {
        multivariate_hypercube_evals_into_coeffs(input, size_log2);
        return;
    }

    // Each butterfly writes a disjoint element, so threads can share the buffer.
    // Pass the base address as a `usize` (Send) and reconstruct the pointer per
    // thread — the same pattern as `parallel_ct_ntt_bitreversed_to_natural`.
    let base_addr = input.as_mut_ptr() as usize;
    let half = n / 2;

    // stride goes n/2, n/4, ..., 1 (most-significant variable first, matching the
    // serial routine; the per-variable stages commute so the order is not required
    // for correctness, only for parity with the serial version).
    for round in 0..size_log2 {
        let s = half >> round;
        let s_log = s.trailing_zeros();
        worker.scope(half, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut F;
                    for b in start..(start + size) {
                        // flat butterfly index -> (group k, in-group offset jj) -> j
                        let k = b >> s_log;
                        let jj = b & (s - 1);
                        let j = k * (s << 1) + jj;
                        unsafe {
                            let lhs = *base.add(j);
                            (*base.add(j + s)).sub_assign(&lhs);
                        }
                    }
                });
            }
        });
    }
}

/// Multicore version of [`multivariate_coeffs_into_hypercube_evals`] (the forward
/// transform), structured exactly like [`parallel_multivariate_hypercube_evals_into_coeffs`]
/// but with `+=` instead of `-=`: a butterfly network of `size_log2` stages (one per
/// variable), each a `worker.scope` over the `n/2` independent butterflies.
///
/// In a stage of stride `S` each butterfly does `input[j + S] += input[j]` for the `j`
/// whose bit `log2(S)` is zero. The per-variable stages commute, so the stride order is
/// irrelevant for correctness; we run `S = 1, 2, ..., n/2` to mirror the serial routine.
pub fn parallel_multivariate_coeffs_into_hypercube_evals<F: Field>(
    input: &mut [F],
    size_log2: u32,
    worker: &Worker,
) {
    assert_eq!(input.len(), 1 << size_log2);
    let n = input.len();
    if n <= 1 {
        return;
    }

    // Small transforms: per-stage scope overhead dominates, so stay serial.
    const PAR_THRESHOLD: usize = 1 << 12;
    let elem_ratio = (core::mem::size_of::<F>() / core::mem::size_of::<u32>()).max(1);
    let eff_threshold = PAR_THRESHOLD / elem_ratio;
    if n < eff_threshold {
        multivariate_coeffs_into_hypercube_evals(input, size_log2);
        return;
    }

    // Each butterfly writes a disjoint element, so threads can share the buffer via the
    // base-address-as-`usize` trick (same as the parallel NTT / inverse transform).
    let base_addr = input.as_mut_ptr() as usize;
    let half = n / 2;

    for round in 0..size_log2 {
        let s = 1usize << round;
        let s_log = round;
        worker.scope(half, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut F;
                    for b in start..(start + size) {
                        // flat butterfly index -> (group k, in-group offset jj) -> j
                        let k = b >> s_log;
                        let jj = b & (s - 1);
                        let j = k * (s << 1) + jj;
                        unsafe {
                            let lhs = *base.add(j);
                            (*base.add(j + s)).add_assign(&lhs);
                        }
                    }
                });
            }
        });
    }
}

#[cfg(test)]
mod test {
    use field::baby_bear::base::BabyBearField;

    use super::*;

    type F = BabyBearField;

    /// Radix-4 (any field) and the NEON BabyBear variant must equal the
    /// reference transform exactly, across variable-count parities and the
    /// small-size degradation paths.
    #[test]
    fn radix_variants_match_reference() {
        use field::Rand;
        let mut rng = rand::rng();
        for log_n in 1u32..=13 {
            let n = 1usize << log_n;

            let input: Vec<F> = (0..n).map(|_| F::random_element(&mut rng)).collect();
            let mut expected = input.clone();
            multivariate_hypercube_evals_into_coeffs(&mut expected, log_n);

            let mut got = input.clone();
            multivariate_hypercube_evals_into_coeffs_radix4(&mut got, log_n);
            assert_eq!(got, expected, "radix-4 diverged at log_n={log_n}");

            #[cfg(target_arch = "aarch64")]
            {
                let mut got = input.clone();
                multivariate_hypercube_evals_into_coeffs_neon_bb(&mut got, log_n);
                assert_eq!(got, expected, "NEON diverged at log_n={log_n}");
            }

            let input_p: Vec<field::Proth120> = (0..n)
                .map(|_| field::Proth120::random_element(&mut rng))
                .collect();
            let mut expected_p = input_p.clone();
            multivariate_hypercube_evals_into_coeffs(&mut expected_p, log_n);
            let mut got_p = input_p.clone();
            multivariate_hypercube_evals_into_coeffs_radix4(&mut got_p, log_n);
            assert_eq!(
                got_p, expected_p,
                "radix-4 Proth120 diverged at log_n={log_n}"
            );
        }
    }

    #[test]
    fn test_forward() {
        let size: usize = 4;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        assert_eq!(coeffs[0], F::ZERO); // x1 = 0, x2 = 0, c0
        assert_eq!(coeffs[1], F::ONE); // x1 = 1, x2 = 0, c0 + c1
        assert_eq!(coeffs[2], F::from_u32_unchecked(2)); // x1 = 0, x2 = 1, c0 + c2
        assert_eq!(coeffs[3], F::from_u32_unchecked(1 + 2 + 3)); // x1 = 1, x2 = 1, c0 + c1 + c2 + c3
    }

    #[test]
    fn test_forward_8() {
        let size: usize = 8;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        // as x3 is 0, we should have the same values as in the test above
        assert_eq!(coeffs[0], F::ZERO); // x1 = 0, x2 = 0, x3 = 0, c0
        assert_eq!(coeffs[1], F::ONE); // x1 = 1, x2 = 0, x3 = 0, c0 + c1
        assert_eq!(coeffs[2], F::from_u32_unchecked(2)); // x1 = 0, x2 = 1, x3 = 0, c0 + c2
        assert_eq!(coeffs[3], F::from_u32_unchecked(1 + 2 + 3)); // x1 = 1, x2 = 1, x3 = 0, c0 + c1 + c2 + c3
                                                                 // and only here we start to get contributions due to x3
        assert_eq!(coeffs[4], F::from_u32_unchecked(4)); // x1 = 0, x2 = 0, x3 = 1, c0 + c4
        assert_eq!(coeffs[5], F::from_u32_unchecked(1 + 4 + 5)); // x1 = 1, x2 = 0, x3 = 1, c0 + c1 + c4 + c5
        assert_eq!(coeffs[6], F::from_u32_unchecked(2 + 4 + 6)); // x1 = 0, x2 = 1, x3 = 1, c0 + c2 + c4 + c6
        assert_eq!(coeffs[7], F::from_u32_unchecked(1 + 2 + 3 + 4 + 5 + 6 + 7));
        // x1 = 1, x2 = 1, x3 = 1, all
    }

    #[test]
    fn test_roundtrip() {
        let size: usize = 8;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        let reference = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        multivariate_hypercube_evals_into_coeffs(&mut coeffs, size.trailing_zeros());
        assert_eq!(coeffs, reference);
    }

    #[test]
    fn test_roundtrip_large() {
        let size: usize = 1 << 20;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        let reference = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        multivariate_hypercube_evals_into_coeffs(&mut coeffs, size.trailing_zeros());
        assert_eq!(coeffs, reference);
    }

    #[test]
    fn test_parallel_matches_serial() {
        let worker = Worker::new_with_num_threads(4);
        for size_log2 in [1u32, 4, 10, 16, 18] {
            let size = 1usize << size_log2;
            let evals: Vec<F> = (0..size)
                .map(|el| F::from_u32_with_reduction((el as u32).wrapping_mul(2654435761)))
                .collect();

            let mut serial = evals.clone();
            multivariate_hypercube_evals_into_coeffs(&mut serial, size_log2);

            let mut parallel = evals.clone();
            parallel_multivariate_hypercube_evals_into_coeffs(&mut parallel, size_log2, &worker);

            assert_eq!(serial, parallel, "mismatch at size_log2 = {size_log2}");
        }
    }

    #[test]
    fn test_parallel_forward_matches_serial() {
        let worker = Worker::new_with_num_threads(4);
        for size_log2 in [1u32, 4, 10, 16, 18] {
            let size = 1usize << size_log2;
            let coeffs: Vec<F> = (0..size)
                .map(|el| F::from_u32_with_reduction((el as u32).wrapping_mul(2654435761)))
                .collect();

            let mut serial = coeffs.clone();
            multivariate_coeffs_into_hypercube_evals(&mut serial, size_log2);

            let mut parallel = coeffs.clone();
            parallel_multivariate_coeffs_into_hypercube_evals(&mut parallel, size_log2, &worker);

            assert_eq!(serial, parallel, "mismatch at size_log2 = {size_log2}");
        }
    }
}
