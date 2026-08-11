//! Lazy-reduction Proth120 LDE-coset pipeline on the STANDARD u128 Montgomery
//! representation (R = 2^128) — the non-vectorized fast path for the prover's
//! in-memory backend.
//!
//! Values live in [0, 2p). The Montgomery multiplication drops its final
//! conditional subtraction outright: with inputs < 2p the CIOS output is
//! < 4p²/2^128 + p·(1 + ε) < 2p (4p²/2^128 ≈ 2^119.6 ≪ p ≈ 2^122.8), so the
//! invariant sustains itself. Butterfly adds/subs reduce against 2p with one
//! compare; a single conditional subtract of p canonicalizes at the end.
//!
//! Validated element-exact against `fft::lde_coset_natural_seq_fused`.

use field::{Field, PrimeField, Proth120};
use worker::Worker;

pub const ORDER: u128 = (7u128 << 120) + 1;
pub const TWO_P: u128 = ORDER << 1;

#[inline(always)]
const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + (b as u128) * (c as u128) + carry as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

/// CIOS Montgomery mul WITHOUT the final conditional subtraction: inputs < 2p,
/// output < 2p (fits u128; the third accumulator limb is provably zero).
#[inline(always)]
pub const fn mont_mul_lazy(a: u128, b: u128) -> u128 {
    const P_LO: u64 = 1;
    const P_HI: u64 = 7u64 << 56;
    const NP: u64 = u64::MAX;

    let a = [a as u64, (a >> 64) as u64];
    let b = [b as u64, (b >> 64) as u64];
    let n = [P_LO, P_HI];

    let mut t = [0u64; 4];
    let mut i = 0;
    while i < 2 {
        let mut c;
        let (s, cc) = mac(t[0], a[0], b[i], 0);
        t[0] = s;
        c = cc;
        let (s, cc) = mac(t[1], a[1], b[i], c);
        t[1] = s;
        c = cc;
        let (s, cc) = adc(t[2], c, 0);
        t[2] = s;
        t[3] = cc;

        let m = t[0].wrapping_mul(NP);
        let (_zero, cc) = mac(t[0], m, n[0], 0);
        c = cc;
        let (s, cc) = mac(t[1], m, n[1], c);
        t[0] = s;
        c = cc;
        let (s, cc) = adc(t[2], c, 0);
        t[1] = s;
        t[2] = t[3].wrapping_add(cc);

        i += 1;
    }
    debug_assert!(t[2] == 0, "lazy mont mul exceeded 2p");
    (t[0] as u128) | ((t[1] as u128) << 64)
}

#[inline(always)]
pub const fn add_2p(a: u128, b: u128) -> u128 {
    // a, b < 2p < 2^124 => sum < 2^125 fits
    let t = a + b;
    if t >= TWO_P {
        t - TWO_P
    } else {
        t
    }
}

#[inline(always)]
pub const fn sub_2p(a: u128, b: u128) -> u128 {
    // a + (2p - b), b < 2p
    add_2p(a, TWO_P - b)
}

#[inline(always)]
pub const fn canonicalize(a: u128) -> u128 {
    if a >= ORDER {
        a - ORDER
    } else {
        a
    }
}

/// GS NTT (bit-reversed input -> natural output) over raw u128 values with
/// lazy reduction; same structure and twiddle table as
/// `fft::naive::serial_ct_ntt_bitreversed_to_natural`. Output values < 2p.
pub fn ntt_lazy_bitreversed_to_natural(a: &mut [u128], log_n: u32, twiddles: &[Proth120]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);

    let mut ppg = 1usize;
    let mut num_groups = n / 2;
    while num_groups > 1 {
        for k in 0..num_groups {
            let s = twiddles[k].raw_u128_value();
            let base = k * ppg * 2;
            for j in base..base + ppg {
                let u = a[j];
                let v = a[j + ppg];
                a[j] = add_2p(u, v);
                a[j + ppg] = mont_mul_lazy(sub_2p(u, v), s);
            }
        }
        ppg *= 2;
        num_groups /= 2;
    }
    let half = n / 2;
    for j in 0..half {
        let u = a[j];
        let v = a[j + half];
        a[j] = add_2p(u, v);
        a[j + half] = sub_2p(u, v);
    }
}

/// Fused lazy tail: `num_groups == 2` → last multiplying level + final
/// twiddle-free level in one pass; `num_groups == 1` → final level only.
#[inline(always)]
fn lazy_radix2_tail(a: &mut [u128], num_groups: usize, twiddles: &[Proth120]) {
    let n = a.len();
    match num_groups {
        2 => {
            let q = n / 4;
            let s_a = twiddles[0].raw_u128_value();
            let s_b = twiddles[1].raw_u128_value();
            for j in 0..q {
                unsafe {
                    let x0 = *a.get_unchecked(j);
                    let x1 = *a.get_unchecked(j + q);
                    let x2 = *a.get_unchecked(j + 2 * q);
                    let x3 = *a.get_unchecked(j + 3 * q);
                    let y0 = add_2p(x0, x1);
                    let y1 = mont_mul_lazy(sub_2p(x0, x1), s_a);
                    let y2 = add_2p(x2, x3);
                    let y3 = mont_mul_lazy(sub_2p(x2, x3), s_b);
                    *a.get_unchecked_mut(j) = add_2p(y0, y2);
                    *a.get_unchecked_mut(j + 2 * q) = sub_2p(y0, y2);
                    *a.get_unchecked_mut(j + q) = add_2p(y1, y3);
                    *a.get_unchecked_mut(j + 3 * q) = sub_2p(y1, y3);
                }
            }
        }
        1 => {
            let half = n / 2;
            for j in 0..half {
                unsafe {
                    let u = *a.get_unchecked(j);
                    let v = *a.get_unchecked(j + half);
                    *a.get_unchecked_mut(j) = add_2p(u, v);
                    *a.get_unchecked_mut(j + half) = sub_2p(u, v);
                }
            }
        }
        _ => unreachable!("lazy tail called with num_groups > 2"),
    }
}

/// Radix-4 lazy level pairs while `num_groups >= 4`; returns updated
/// `(ppg, num_groups)`.
#[inline(always)]
fn lazy_radix4_levels(
    a: &mut [u128],
    mut ppg: usize,
    mut num_groups: usize,
    twiddles: &[Proth120],
) -> (usize, usize) {
    while num_groups >= 4 {
        let ng_outer = num_groups / 2;
        for k2 in 0..ng_outer {
            let s_a = twiddles[2 * k2].raw_u128_value();
            let s_b = twiddles[2 * k2 + 1].raw_u128_value();
            let s_o = twiddles[k2].raw_u128_value();
            let base = k2 * ppg * 4;
            for j in base..base + ppg {
                unsafe {
                    let x0 = *a.get_unchecked(j);
                    let x1 = *a.get_unchecked(j + ppg);
                    let x2 = *a.get_unchecked(j + 2 * ppg);
                    let x3 = *a.get_unchecked(j + 3 * ppg);
                    let y0 = add_2p(x0, x1);
                    let y1 = mont_mul_lazy(sub_2p(x0, x1), s_a);
                    let y2 = add_2p(x2, x3);
                    let y3 = mont_mul_lazy(sub_2p(x2, x3), s_b);
                    *a.get_unchecked_mut(j) = add_2p(y0, y2);
                    *a.get_unchecked_mut(j + 2 * ppg) = mont_mul_lazy(sub_2p(y0, y2), s_o);
                    *a.get_unchecked_mut(j + ppg) = add_2p(y1, y3);
                    *a.get_unchecked_mut(j + 3 * ppg) = mont_mul_lazy(sub_2p(y1, y3), s_o);
                }
            }
        }
        ppg *= 4;
        num_groups /= 4;
    }
    (ppg, num_groups)
}

/// Radix-4 variant of [`ntt_lazy_bitreversed_to_natural`]: two butterfly levels
/// fused per pass (half the load/store traffic; 4 values live in registers),
/// same multiplication count, identical outputs.
pub fn ntt_lazy_bitreversed_to_natural_r4(a: &mut [u128], log_n: u32, twiddles: &[Proth120]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);
    let (_, num_groups) = lazy_radix4_levels(a, 1, n / 2, twiddles);
    lazy_radix2_tail(a, num_groups, twiddles);
}

/// Radix-8 variant: three levels fused per pass, remainder via one radix-4
/// pass and/or the fused tail.
pub fn ntt_lazy_bitreversed_to_natural_r8(a: &mut [u128], log_n: u32, twiddles: &[Proth120]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);
    let mut ppg = 1usize;
    let mut num_groups = n / 2;
    while num_groups >= 8 {
        let ng_outer = num_groups / 4;
        for k3 in 0..ng_outer {
            let t_a = twiddles[4 * k3].raw_u128_value();
            let t_b = twiddles[4 * k3 + 1].raw_u128_value();
            let t_c = twiddles[4 * k3 + 2].raw_u128_value();
            let t_d = twiddles[4 * k3 + 3].raw_u128_value();
            let t_e = twiddles[2 * k3].raw_u128_value();
            let t_f = twiddles[2 * k3 + 1].raw_u128_value();
            let t_o = twiddles[k3].raw_u128_value();
            let base = k3 * ppg * 8;
            for j in base..base + ppg {
                unsafe {
                    let x0 = *a.get_unchecked(j);
                    let x1 = *a.get_unchecked(j + ppg);
                    let x2 = *a.get_unchecked(j + 2 * ppg);
                    let x3 = *a.get_unchecked(j + 3 * ppg);
                    let x4 = *a.get_unchecked(j + 4 * ppg);
                    let x5 = *a.get_unchecked(j + 5 * ppg);
                    let x6 = *a.get_unchecked(j + 6 * ppg);
                    let x7 = *a.get_unchecked(j + 7 * ppg);
                    let y0 = add_2p(x0, x1);
                    let y1 = mont_mul_lazy(sub_2p(x0, x1), t_a);
                    let y2 = add_2p(x2, x3);
                    let y3 = mont_mul_lazy(sub_2p(x2, x3), t_b);
                    let y4 = add_2p(x4, x5);
                    let y5 = mont_mul_lazy(sub_2p(x4, x5), t_c);
                    let y6 = add_2p(x6, x7);
                    let y7 = mont_mul_lazy(sub_2p(x6, x7), t_d);
                    let z0 = add_2p(y0, y2);
                    let z2 = mont_mul_lazy(sub_2p(y0, y2), t_e);
                    let z1 = add_2p(y1, y3);
                    let z3 = mont_mul_lazy(sub_2p(y1, y3), t_e);
                    let z4 = add_2p(y4, y6);
                    let z6 = mont_mul_lazy(sub_2p(y4, y6), t_f);
                    let z5 = add_2p(y5, y7);
                    let z7 = mont_mul_lazy(sub_2p(y5, y7), t_f);
                    *a.get_unchecked_mut(j) = add_2p(z0, z4);
                    *a.get_unchecked_mut(j + 4 * ppg) = mont_mul_lazy(sub_2p(z0, z4), t_o);
                    *a.get_unchecked_mut(j + ppg) = add_2p(z1, z5);
                    *a.get_unchecked_mut(j + 5 * ppg) = mont_mul_lazy(sub_2p(z1, z5), t_o);
                    *a.get_unchecked_mut(j + 2 * ppg) = add_2p(z2, z6);
                    *a.get_unchecked_mut(j + 6 * ppg) = mont_mul_lazy(sub_2p(z2, z6), t_o);
                    *a.get_unchecked_mut(j + 3 * ppg) = add_2p(z3, z7);
                    *a.get_unchecked_mut(j + 7 * ppg) = mont_mul_lazy(sub_2p(z3, z7), t_o);
                }
            }
        }
        ppg *= 8;
        num_groups /= 8;
    }
    let (_, num_groups) = lazy_radix4_levels(a, ppg, num_groups, twiddles);
    lazy_radix2_tail(a, num_groups, twiddles);
}

/// Full serial LDE coset with lazy reduction: scaled copy (split-table offset
/// powers, lazy muls) -> bit-reversal -> lazy GS NTT -> one canonicalization
/// pass. Drop-in equivalent of `fft::lde_coset_natural_seq_fused`.
pub fn lde_coset_lazy(
    input: &[Proth120],
    offset: Proth120,
    twiddles: &[Proth120],
) -> Vec<Proth120> {
    lde_coset_lazy_with_kernel(input, offset, twiddles, ntt_lazy_bitreversed_to_natural)
}

/// [`lde_coset_lazy`] with the radix-4 lazy NTT.
pub fn lde_coset_lazy_r4(
    input: &[Proth120],
    offset: Proth120,
    twiddles: &[Proth120],
) -> Vec<Proth120> {
    lde_coset_lazy_with_kernel(input, offset, twiddles, ntt_lazy_bitreversed_to_natural_r4)
}

/// [`lde_coset_lazy`] with the radix-8 lazy NTT.
pub fn lde_coset_lazy_r8(
    input: &[Proth120],
    offset: Proth120,
    twiddles: &[Proth120],
) -> Vec<Proth120> {
    lde_coset_lazy_with_kernel(input, offset, twiddles, ntt_lazy_bitreversed_to_natural_r8)
}

/// Worker-PARALLEL counterpart of [`ntt_lazy_bitreversed_to_natural_r8`]:
/// radix-8 fused passes (radix-4 / fused radix-2 tail for leftover levels),
/// each pass distributed over the worker with a barrier between passes — so a
/// parallel transform makes `~log_n/3` synchronized sweeps instead of `log_n`.
/// Butterfly items within a pass touch pairwise-disjoint index sets.
pub fn parallel_ntt_lazy_bitreversed_to_natural_r8(
    a: &mut [u128],
    log_n: u32,
    twiddles: &[Proth120],
    worker: &Worker,
) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);
    // Small transforms: per-pass scope overhead dominates — stay serial.
    const PAR_THRESHOLD: usize = 1 << 13;
    if n < PAR_THRESHOLD {
        return ntt_lazy_bitreversed_to_natural_r8(a, log_n, twiddles);
    }

    let base_addr = a.as_mut_ptr() as usize;
    let mut ppg = 1usize;
    let mut num_groups = n / 2;

    // Fused radix-8 passes: n/8 disjoint 8-element work items each.
    while num_groups >= 8 {
        let ppg_log = ppg.trailing_zeros();
        let cur_ppg = ppg;
        worker.scope(n / 8, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut u128;
                    for b in start..(start + size) {
                        let k3 = b >> ppg_log;
                        let jj = b & (cur_ppg - 1);
                        let j = k3 * (cur_ppg << 3) + jj;
                        let t_a = twiddles[4 * k3].raw_u128_value();
                        let t_b = twiddles[4 * k3 + 1].raw_u128_value();
                        let t_c = twiddles[4 * k3 + 2].raw_u128_value();
                        let t_d = twiddles[4 * k3 + 3].raw_u128_value();
                        let t_e = twiddles[2 * k3].raw_u128_value();
                        let t_f = twiddles[2 * k3 + 1].raw_u128_value();
                        let t_o = twiddles[k3].raw_u128_value();
                        unsafe {
                            let x0 = *base.add(j);
                            let x1 = *base.add(j + cur_ppg);
                            let x2 = *base.add(j + 2 * cur_ppg);
                            let x3 = *base.add(j + 3 * cur_ppg);
                            let x4 = *base.add(j + 4 * cur_ppg);
                            let x5 = *base.add(j + 5 * cur_ppg);
                            let x6 = *base.add(j + 6 * cur_ppg);
                            let x7 = *base.add(j + 7 * cur_ppg);
                            let y0 = add_2p(x0, x1);
                            let y1 = mont_mul_lazy(sub_2p(x0, x1), t_a);
                            let y2 = add_2p(x2, x3);
                            let y3 = mont_mul_lazy(sub_2p(x2, x3), t_b);
                            let y4 = add_2p(x4, x5);
                            let y5 = mont_mul_lazy(sub_2p(x4, x5), t_c);
                            let y6 = add_2p(x6, x7);
                            let y7 = mont_mul_lazy(sub_2p(x6, x7), t_d);
                            let z0 = add_2p(y0, y2);
                            let z2 = mont_mul_lazy(sub_2p(y0, y2), t_e);
                            let z1 = add_2p(y1, y3);
                            let z3 = mont_mul_lazy(sub_2p(y1, y3), t_e);
                            let z4 = add_2p(y4, y6);
                            let z6 = mont_mul_lazy(sub_2p(y4, y6), t_f);
                            let z5 = add_2p(y5, y7);
                            let z7 = mont_mul_lazy(sub_2p(y5, y7), t_f);
                            *base.add(j) = add_2p(z0, z4);
                            *base.add(j + 4 * cur_ppg) = mont_mul_lazy(sub_2p(z0, z4), t_o);
                            *base.add(j + cur_ppg) = add_2p(z1, z5);
                            *base.add(j + 5 * cur_ppg) = mont_mul_lazy(sub_2p(z1, z5), t_o);
                            *base.add(j + 2 * cur_ppg) = add_2p(z2, z6);
                            *base.add(j + 6 * cur_ppg) = mont_mul_lazy(sub_2p(z2, z6), t_o);
                            *base.add(j + 3 * cur_ppg) = add_2p(z3, z7);
                            *base.add(j + 7 * cur_ppg) = mont_mul_lazy(sub_2p(z3, z7), t_o);
                        }
                    }
                });
            }
        });
        ppg <<= 3;
        num_groups >>= 3;
    }

    // At most one radix-4 pass for leftover levels: n/4 disjoint items.
    if num_groups >= 4 {
        let ppg_log = ppg.trailing_zeros();
        let cur_ppg = ppg;
        worker.scope(n / 4, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut u128;
                    for b in start..(start + size) {
                        let k2 = b >> ppg_log;
                        let jj = b & (cur_ppg - 1);
                        let j = k2 * (cur_ppg << 2) + jj;
                        let s_a = twiddles[2 * k2].raw_u128_value();
                        let s_b = twiddles[2 * k2 + 1].raw_u128_value();
                        let s_o = twiddles[k2].raw_u128_value();
                        unsafe {
                            let x0 = *base.add(j);
                            let x1 = *base.add(j + cur_ppg);
                            let x2 = *base.add(j + 2 * cur_ppg);
                            let x3 = *base.add(j + 3 * cur_ppg);
                            let y0 = add_2p(x0, x1);
                            let y1 = mont_mul_lazy(sub_2p(x0, x1), s_a);
                            let y2 = add_2p(x2, x3);
                            let y3 = mont_mul_lazy(sub_2p(x2, x3), s_b);
                            *base.add(j) = add_2p(y0, y2);
                            *base.add(j + 2 * cur_ppg) = mont_mul_lazy(sub_2p(y0, y2), s_o);
                            *base.add(j + cur_ppg) = add_2p(y1, y3);
                            *base.add(j + 3 * cur_ppg) = mont_mul_lazy(sub_2p(y1, y3), s_o);
                        }
                    }
                });
            }
        });
        ppg <<= 2;
        num_groups >>= 2;
    }

    // Tail: fused (last multiplying + final) pass, or the final pass alone.
    if num_groups == 2 {
        let q = n / 4;
        let s_a = twiddles[0].raw_u128_value();
        let s_b = twiddles[1].raw_u128_value();
        worker.scope(q, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut u128;
                    for j in start..(start + size) {
                        unsafe {
                            let x0 = *base.add(j);
                            let x1 = *base.add(j + q);
                            let x2 = *base.add(j + 2 * q);
                            let x3 = *base.add(j + 3 * q);
                            let y0 = add_2p(x0, x1);
                            let y1 = mont_mul_lazy(sub_2p(x0, x1), s_a);
                            let y2 = add_2p(x2, x3);
                            let y3 = mont_mul_lazy(sub_2p(x2, x3), s_b);
                            *base.add(j) = add_2p(y0, y2);
                            *base.add(j + 2 * q) = sub_2p(y0, y2);
                            *base.add(j + q) = add_2p(y1, y3);
                            *base.add(j + 3 * q) = sub_2p(y1, y3);
                        }
                    }
                });
            }
        });
    } else {
        debug_assert_eq!(num_groups, 1);
        let half = n / 2;
        worker.scope(half, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let base = base_addr as *mut u128;
                    for j in start..(start + size) {
                        unsafe {
                            let u = *base.add(j);
                            let v = *base.add(j + half);
                            *base.add(j) = add_2p(u, v);
                            *base.add(j + half) = sub_2p(u, v);
                        }
                    }
                });
            }
        });
    }
}

/// Worker-PARALLEL lazy LDE coset with radix-8 fused sweeps: the counterpart of
/// [`lde_coset_lazy_r8`] for the few-tasks/many-threads plan (e.g. the SMALLER
/// intermediate-WHIR-oracle FFTs, where `lde_factor` cosets < worker threads).
/// Every pass (scaled copy, bit-reversal, each fused NTT sweep, the final
/// canonicalization) runs worker-wide; nested inside a rayon task it composes
/// through the shared pool. Identical values to the serial pipelines.
pub fn lde_coset_lazy_parallel_r8(
    input: &[Proth120],
    offset: Proth120,
    twiddles: &[Proth120],
    worker: &Worker,
) -> Vec<Proth120> {
    let n = input.len();
    const PAR_THRESHOLD: usize = 1 << 13;
    if n < PAR_THRESHOLD {
        return lde_coset_lazy_r8(input, offset, twiddles);
    }
    let log_n = n.trailing_zeros();

    // offset power split tables (canonical raw values), as in the serial path
    let h = log_n.div_ceil(2);
    let lo_len = 1usize << h;
    let hi_len = n >> h;
    let mut lo = Vec::with_capacity(lo_len);
    let mut cur = Proth120::ONE;
    for _ in 0..lo_len {
        lo.push(cur.raw_u128_value());
        cur.mul_assign(&offset);
    }
    let stride = cur;
    let mut hi = Vec::with_capacity(hi_len);
    let mut cur = Proth120::ONE;
    for _ in 0..hi_len {
        hi.push(cur.raw_u128_value());
        cur.mul_assign(&stride);
    }

    let mut v: Vec<u128> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        v.set_len(n)
    };
    let mask = lo_len - 1;
    let scale = offset != Proth120::ONE;
    let src_addr = input.as_ptr() as usize;
    let dst_addr = v.as_mut_ptr() as usize;
    let lo_ref = &lo[..];
    let hi_ref = &hi[..];
    worker.scope(n, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(thread_idx);
            let size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let src = src_addr as *const Proth120;
                let dst = dst_addr as *mut u128;
                for i in start..(start + size) {
                    unsafe {
                        let raw = (*src.add(i)).raw_u128_value();
                        *dst.add(i) = if scale {
                            let f = mont_mul_lazy(lo_ref[i & mask], hi_ref[i >> h]);
                            mont_mul_lazy(raw, f)
                        } else {
                            raw
                        };
                    }
                }
            });
        }
    });

    crate::utils::parallel_bitreverse_enumeration_inplace(&mut v, worker);

    parallel_ntt_lazy_bitreversed_to_natural_r8(&mut v, log_n, &twiddles[..n / 2], worker);

    // parallel canonicalization in place, then reinterpret (repr(transparent))
    let dst_addr = v.as_mut_ptr() as usize;
    worker.scope(n, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(thread_idx);
            let size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let dst = dst_addr as *mut u128;
                for i in start..(start + size) {
                    unsafe {
                        *dst.add(i) = canonicalize(*dst.add(i));
                    }
                }
            });
        }
    });
    // SAFETY: Proth120 is repr(transparent) over u128 and every value is
    // canonical after the pass above.
    unsafe { core::mem::transmute::<Vec<u128>, Vec<Proth120>>(v) }
}

fn lde_coset_lazy_with_kernel(
    input: &[Proth120],
    offset: Proth120,
    twiddles: &[Proth120],
    ntt: fn(&mut [u128], u32, &[Proth120]),
) -> Vec<Proth120> {
    let n = input.len();
    let log_n = n.trailing_zeros();

    // offset power split tables (canonical raw values)
    let h = log_n.div_ceil(2);
    let lo_len = 1usize << h;
    let hi_len = n >> h;
    let mut lo = Vec::with_capacity(lo_len);
    let mut cur = Proth120::ONE;
    for _ in 0..lo_len {
        lo.push(cur.raw_u128_value());
        cur.mul_assign(&offset);
    }
    let stride = cur; // offset^{2^h} in field form
    let mut hi = Vec::with_capacity(hi_len);
    let mut cur = Proth120::ONE;
    for _ in 0..hi_len {
        hi.push(cur.raw_u128_value());
        cur.mul_assign(&stride);
    }

    let mut v: Vec<u128> = Vec::with_capacity(n);
    let mask = lo_len - 1;
    let scale = offset != Proth120::ONE;
    for (i, x) in input.iter().enumerate() {
        let raw = x.raw_u128_value();
        v.push(if scale {
            let f = mont_mul_lazy(lo[i & mask], hi[i >> h]);
            mont_mul_lazy(raw, f)
        } else {
            raw
        });
    }

    crate::utils::bitreverse_enumeration_inplace(&mut v);

    ntt(&mut v, log_n, &twiddles[..n / 2]);

    v.into_iter()
        .map(|x| Proth120::from_raw_u128(canonicalize(x)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::twiddles::precompute_all_twiddles_for_fft_serial;
    use field::{Rand, TwoAdicField};
    use std::alloc::Global;

    /// The lazy pipeline must equal `lde_coset_natural_seq_fused` exactly.
    #[test]
    fn lazy_lde_matches_reference() {
        for log_n in [8u32, 11, 14] {
            let n = 1usize << log_n;
            let mut rng = rand::rng();
            let input: Vec<Proth120> = (0..n).map(|_| Proth120::random_element(&mut rng)).collect();
            let tw: Vec<Proth120, Global> =
                precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);
            let offset = crate::field_utils::domain_generator_for_size::<Proth120>((n * 8) as u64);

            let expected = crate::lde_coset_natural_seq_fused(&input, offset, &tw);
            let got = lde_coset_lazy(&input, offset, &tw);
            assert_eq!(got, expected, "lazy pipeline diverged at log_n={log_n}");
            let got = lde_coset_lazy_r4(&input, offset, &tw);
            assert_eq!(got, expected, "lazy r4 pipeline diverged at log_n={log_n}");
            let got = lde_coset_lazy_r8(&input, offset, &tw);
            assert_eq!(got, expected, "lazy r8 pipeline diverged at log_n={log_n}");

            // offset == 1 branch
            let expected = crate::lde_coset_natural_seq_fused(&input, Proth120::ONE, &tw);
            let got = lde_coset_lazy(&input, Proth120::ONE, &tw);
            assert_eq!(got, expected, "lazy pipeline (offset 1) diverged");
        }
    }

    /// The worker-parallel radix-8 pipeline must equal the reference exactly,
    /// both below the serial-fallback threshold and above it, for every fused
    /// level-count residue (log_n mod 3).
    #[test]
    fn lazy_parallel_r8_matches_reference() {
        let worker = Worker::new_with_num_threads(4);
        for log_n in [8u32, 13, 14, 15, 16] {
            let n = 1usize << log_n;
            let mut rng = rand::rng();
            let input: Vec<Proth120> = (0..n).map(|_| Proth120::random_element(&mut rng)).collect();
            let tw: Vec<Proth120, Global> =
                precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);
            let offset = crate::field_utils::domain_generator_for_size::<Proth120>((n * 8) as u64);

            let expected = crate::lde_coset_natural_seq_fused(&input, offset, &tw);
            let got = lde_coset_lazy_parallel_r8(&input, offset, &tw, &worker);
            assert_eq!(got, expected, "parallel lazy r8 diverged at log_n={log_n}");

            let expected = crate::lde_coset_natural_seq_fused(&input, Proth120::ONE, &tw);
            let got = lde_coset_lazy_parallel_r8(&input, Proth120::ONE, &tw, &worker);
            assert_eq!(got, expected, "parallel lazy r8 (offset 1) diverged");
        }
    }
}
