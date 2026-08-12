//! DRAFT: NEON-vectorized BabyBear LDE-coset kernels (aarch64 / Apple M-class).
//!
//! BabyBear is `p = 2^31 - 2^27 + 1` in standard 32-bit Montgomery form
//! (`R = 2^32`, `-p^{-1} mod 2^32 = 0x77ffffff`), canonical at rest — four
//! elements fit one NEON vector and the Montgomery product vectorizes with two
//! `umull` pairs + `uzp2` for the high words; every op returns canonical
//! values, so all kernels here are BYTE-IDENTICAL to the scalar reference
//! (asserted by [`self_check`]).
//!
//! Variants (all `natural monomials -> natural coset evals`, the base-commit
//! task shape):
//!  - [`lde_flat_neon_r4`]: the FLAT pipeline (scaled copy, bit-reversal, GS
//!    DIT NTT) with every butterfly stage vectorized — stages `ppg = 1, 2` via
//!    in-register `uzp`/`zip` shuffles, stages `ppg >= 4` as radix-4 fused
//!    NEON passes (two butterfly levels per sweep), and the last multiplying
//!    level fused with the final twiddle-free level.
//!  - [`lde_six_step_neon`]: six-step `N = N1 x N2` with NEON 4x4 in-register
//!    tile transposes for all three data-movement passes (gather+scale,
//!    middle transpose, scatter), L1-resident NEON row FFTs, and a vectorized
//!    outer twiddle correction. ~5 DRAM sweeps instead of ~25.
//!
//! The scalar references live in the `fft` crate; on non-aarch64 hosts this
//! module only exposes the self-checks (delegating to the scalar path).

#![allow(dead_code)]

use field::baby_bear::base::BabyBearField;
use field::{Field, PrimeField, Rand, TwoAdicField};
use std::alloc::Global;

pub const P: u32 = 0x78000001;
pub const K: u32 = 0x77ffffff;

/// Scalar Montgomery mul on raw values — mirror of the field crate's
/// `ops::mul_mod` (kept here for power tables on raw values).
#[inline(always)]
pub fn mont_mul_scalar(a: u32, b: u32) -> u32 {
    let mut product = (a as u64).wrapping_mul(b as u64);
    let m = (product as u32).wrapping_mul(K);
    product = product.wrapping_add((m as u64).wrapping_mul(P as u64));
    let mut result = (product >> 32) as u32;
    if result >= P {
        result -= P;
    }
    result
}

#[inline(always)]
fn add_scalar(a: u32, b: u32) -> u32 {
    let mut s = a.wrapping_add(b);
    if s >= P {
        s -= P;
    }
    s
}

#[inline(always)]
fn sub_scalar(a: u32, b: u32) -> u32 {
    let (mut d, uf) = a.overflowing_sub(b);
    if uf {
        d = d.wrapping_add(P);
    }
    d
}

/// Split-table offset powers on RAW values: `f_i = lo[i & mask] * hi[i >> h]`,
/// exactly as `fft::lde_coset_natural_seq_fused` computes them (same op
/// order => identical canonical values).
struct SplitPowersRaw {
    lo: Vec<u32>,
    hi: Vec<u32>,
    h: u32,
    mask: usize,
}

impl SplitPowersRaw {
    fn new(offset: BabyBearField, log_n: u32) -> Self {
        let h = log_n.div_ceil(2);
        let lo_len = 1usize << h;
        let hi_len = 1usize << (log_n - h);
        let mut lo = Vec::with_capacity(lo_len);
        let mut cur = BabyBearField::ONE;
        for _ in 0..lo_len {
            lo.push(cur.raw_u32_value());
            cur.mul_assign(&offset);
        }
        let stride = cur;
        let mut hi = Vec::with_capacity(hi_len);
        let mut cur = BabyBearField::ONE;
        for _ in 0..hi_len {
            hi.push(cur.raw_u32_value());
            cur.mul_assign(&stride);
        }
        Self {
            lo,
            hi,
            h,
            mask: lo_len - 1,
        }
    }

    #[inline(always)]
    fn factor(&self, i: usize) -> u32 {
        mont_mul_scalar(self.lo[i & self.mask], self.hi[i >> self.h])
    }
}

// ---------------------------------------------------------------------------
// NEON kernels
// ---------------------------------------------------------------------------

#[cfg(target_arch = "aarch64")]
pub mod neon {
    use super::{K, P};
    use core::arch::aarch64::*;

    #[inline(always)]
    unsafe fn pv() -> uint32x4_t {
        vdupq_n_u32(P)
    }

    /// 4-lane Montgomery multiplication, canonical in/out.
    #[inline(always)]
    pub unsafe fn mont_mul(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let lo = vmulq_u32(a, b);
        let prod_l = vmull_u32(vget_low_u32(a), vget_low_u32(b));
        let prod_h = vmull_high_u32(a, b);
        let m = vmulq_u32(lo, vdupq_n_u32(K));
        let mp_l = vmull_u32(vget_low_u32(m), vget_low_u32(pv()));
        let mp_h = vmull_high_u32(m, pv());
        let t_l = vaddq_u64(prod_l, mp_l);
        let t_h = vaddq_u64(prod_h, mp_h);
        // per-lane (t >> 32): the odd 32-bit words of the 64-bit sums
        let r = vuzp2q_u32(vreinterpretq_u32_u64(t_l), vreinterpretq_u32_u64(t_h));
        let rs = vsubq_u32(r, pv());
        vminq_u32(r, rs)
    }

    /// 4-lane modular add of canonical values.
    #[inline(always)]
    pub unsafe fn add(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let s = vaddq_u32(a, b);
        vminq_u32(s, vsubq_u32(s, pv()))
    }

    /// 4-lane modular sub of canonical values.
    #[inline(always)]
    pub unsafe fn sub(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let d = vsubq_u32(a, b);
        vminq_u32(d, vaddq_u32(d, pv()))
    }

    /// GS butterfly on vectors: `(u, v) -> (u + v, (u - v) * s)`.
    #[inline(always)]
    unsafe fn butterfly(u: uint32x4_t, v: uint32x4_t, s: uint32x4_t) -> (uint32x4_t, uint32x4_t) {
        (add(u, v), mont_mul(sub(u, v), s))
    }

    /// Stage `ppg == 1`: pairs `(2k, 2k+1)`, twiddle `tw[k]` — 8 contiguous
    /// elements are 4 pairs with 4 contiguous twiddles; split even/odd lanes
    /// with `uzp`, butterfly, re-`zip`.
    #[inline(always)]
    unsafe fn pass_ppg1(a: *mut u32, n: usize, tw: *const u32) {
        let mut j = 0usize;
        while j < n {
            let v0 = vld1q_u32(a.add(j));
            let v1 = vld1q_u32(a.add(j + 4));
            let u = vuzp1q_u32(v0, v1);
            let v = vuzp2q_u32(v0, v1);
            let s = vld1q_u32(tw.add(j >> 1));
            let (na, nb) = butterfly(u, v, s);
            vst1q_u32(a.add(j), vzip1q_u32(na, nb));
            vst1q_u32(a.add(j + 4), vzip2q_u32(na, nb));
            j += 8;
        }
    }

    /// Stage `ppg == 2`: pairs `(j, j+2)` in 4-element groups — split/merge on
    /// 64-bit lanes, twiddle lanes `[tw[k], tw[k], tw[k+1], tw[k+1]]`.
    #[inline(always)]
    unsafe fn pass_ppg2(a: *mut u32, n: usize, tw: *const u32) {
        let mut j = 0usize;
        while j < n {
            let v0 = vreinterpretq_u64_u32(vld1q_u32(a.add(j)));
            let v1 = vreinterpretq_u64_u32(vld1q_u32(a.add(j + 4)));
            let u = vreinterpretq_u32_u64(vuzp1q_u64(v0, v1));
            let v = vreinterpretq_u32_u64(vuzp2q_u64(v0, v1));
            let d = vld1_u32(tw.add(j >> 2)); // [tw[k], tw[k+1]]
            let t = vcombine_u32(d, d);
            let s = vzip1q_u32(t, t); // [twk, twk, twk1, twk1]
            let (na, nb) = butterfly(u, v, s);
            let na64 = vreinterpretq_u64_u32(na);
            let nb64 = vreinterpretq_u64_u32(nb);
            vst1q_u32(a.add(j), vreinterpretq_u32_u64(vzip1q_u64(na64, nb64)));
            vst1q_u32(a.add(j + 4), vreinterpretq_u32_u64(vzip2q_u64(na64, nb64)));
            j += 8;
        }
    }

    /// Radix-4 fused NEON pass over two multiplying levels (`ppg >= 4`,
    /// `num_groups >= 4`), broadcast twiddles: same math and twiddle indexing
    /// as the scalar `higher_radix` kernels.
    #[inline(always)]
    unsafe fn radix4_pass(a: *mut u32, ppg: usize, num_groups: usize, tw: *const u32) {
        let ng_outer = num_groups / 2;
        for k2 in 0..ng_outer {
            let s_a = vdupq_n_u32(*tw.add(2 * k2));
            let s_b = vdupq_n_u32(*tw.add(2 * k2 + 1));
            let s_o = vdupq_n_u32(*tw.add(k2));
            let base = k2 * ppg * 4;
            let mut j = base;
            while j < base + ppg {
                let x0 = vld1q_u32(a.add(j));
                let x1 = vld1q_u32(a.add(j + ppg));
                let x2 = vld1q_u32(a.add(j + 2 * ppg));
                let x3 = vld1q_u32(a.add(j + 3 * ppg));
                let (y0, y1) = butterfly(x0, x1, s_a);
                let (y2, y3) = butterfly(x2, x3, s_b);
                let (z0, z2) = butterfly(y0, y2, s_o);
                let (z1, z3) = butterfly(y1, y3, s_o);
                vst1q_u32(a.add(j), z0);
                vst1q_u32(a.add(j + ppg), z1);
                vst1q_u32(a.add(j + 2 * ppg), z2);
                vst1q_u32(a.add(j + 3 * ppg), z3);
                j += 4;
            }
        }
    }

    /// Single radix-2 NEON pass (`ppg >= 4`): parity filler when the level
    /// count doesn't pair up.
    #[inline(always)]
    unsafe fn radix2_pass(a: *mut u32, ppg: usize, num_groups: usize, tw: *const u32) {
        for k in 0..num_groups {
            let s = vdupq_n_u32(*tw.add(k));
            let base = k * ppg * 2;
            let mut j = base;
            while j < base + ppg {
                let u = vld1q_u32(a.add(j));
                let v = vld1q_u32(a.add(j + ppg));
                let (na, nb) = butterfly(u, v, s);
                vst1q_u32(a.add(j), na);
                vst1q_u32(a.add(j + ppg), nb);
                j += 4;
            }
        }
    }

    /// Fused tail: last multiplying level (groups 0/1, `tw[0]`/`tw[1]`) + the
    /// final twiddle-free level in one sweep (`q = n/4 >= 4`).
    #[inline(always)]
    unsafe fn tail_two_groups(a: *mut u32, n: usize, tw: *const u32) {
        let q = n / 4;
        let s_a = vdupq_n_u32(*tw);
        let s_b = vdupq_n_u32(*tw.add(1));
        let mut j = 0usize;
        while j < q {
            let x0 = vld1q_u32(a.add(j));
            let x1 = vld1q_u32(a.add(j + q));
            let x2 = vld1q_u32(a.add(j + 2 * q));
            let x3 = vld1q_u32(a.add(j + 3 * q));
            let (y0, y1) = butterfly(x0, x1, s_a);
            let (y2, y3) = butterfly(x2, x3, s_b);
            vst1q_u32(a.add(j), add(y0, y2));
            vst1q_u32(a.add(j + 2 * q), sub(y0, y2));
            vst1q_u32(a.add(j + q), add(y1, y3));
            vst1q_u32(a.add(j + 3 * q), sub(y1, y3));
            j += 4;
        }
    }

    /// Final twiddle-free level alone.
    #[inline(always)]
    unsafe fn tail_final(a: *mut u32, n: usize) {
        let half = n / 2;
        let mut j = 0usize;
        while j < half {
            let u = vld1q_u32(a.add(j));
            let v = vld1q_u32(a.add(j + half));
            vst1q_u32(a.add(j), add(u, v));
            vst1q_u32(a.add(j + half), sub(u, v));
            j += 4;
        }
    }

    /// Fully-NEON GS DIT NTT, bit-reversed input -> natural output, on raw
    /// canonical values. `n >= 16`. Identical values to
    /// `fft::naive::serial_ct_ntt_bitreversed_to_natural`.
    pub unsafe fn ntt_bitrev_to_natural(a: &mut [u32], log_n: u32, tw: &[u32]) {
        let n = a.len();
        debug_assert_eq!(n, 1usize << log_n);
        debug_assert!(n >= 16);
        let p = a.as_mut_ptr();
        let t = tw.as_ptr();

        pass_ppg1(p, n, t);
        pass_ppg2(p, n, t);
        let mut ppg = 4usize;
        let mut num_groups = n / 8;
        while num_groups >= 4 {
            radix4_pass(p, ppg, num_groups, t);
            ppg *= 4;
            num_groups /= 4;
        }
        match num_groups {
            2 => tail_two_groups(p, n, t),
            1 => tail_final(p, n),
            _ => unreachable!(),
        }
    }

    /// TIMING PROBE ONLY — Montgomery mul with the final conditional
    /// subtraction removed. NOT value-correct in a butterfly chain (BabyBear
    /// has no lazy headroom in 32-bit lanes: 2p ~ 2^31.9, so lazy adds
    /// overflow and lazy x lazy muls exceed 2p) — used solely to measure the
    /// op-count ceiling that any partial-reduction scheme could reach.
    #[inline(always)]
    pub unsafe fn mont_mul_nomin(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let lo = vmulq_u32(a, b);
        let prod_l = vmull_u32(vget_low_u32(a), vget_low_u32(b));
        let prod_h = vmull_high_u32(a, b);
        let m = vmulq_u32(lo, vdupq_n_u32(K));
        let mp_l = vmull_u32(vget_low_u32(m), vget_low_u32(pv()));
        let mp_h = vmull_high_u32(m, pv());
        let t_l = vaddq_u64(prod_l, mp_l);
        let t_h = vaddq_u64(prod_h, mp_h);
        vuzp2q_u32(vreinterpretq_u32_u64(t_l), vreinterpretq_u32_u64(t_h))
    }

    /// TIMING PROBE ONLY — radix-4 pass with all conditional subtractions
    /// stripped from muls AND adds/subs (adds/subs wrap): the pure-ALU floor.
    #[inline(always)]
    unsafe fn radix4_pass_nomin(a: *mut u32, ppg: usize, num_groups: usize, tw: *const u32) {
        let ng_outer = num_groups / 2;
        for k2 in 0..ng_outer {
            let s_a = vdupq_n_u32(*tw.add(2 * k2));
            let s_b = vdupq_n_u32(*tw.add(2 * k2 + 1));
            let s_o = vdupq_n_u32(*tw.add(k2));
            let base = k2 * ppg * 4;
            let mut j = base;
            while j < base + ppg {
                let x0 = vld1q_u32(a.add(j));
                let x1 = vld1q_u32(a.add(j + ppg));
                let x2 = vld1q_u32(a.add(j + 2 * ppg));
                let x3 = vld1q_u32(a.add(j + 3 * ppg));
                let y0 = vaddq_u32(x0, x1);
                let y1 = mont_mul_nomin(vsubq_u32(x0, x1), s_a);
                let y2 = vaddq_u32(x2, x3);
                let y3 = mont_mul_nomin(vsubq_u32(x2, x3), s_b);
                let z0 = vaddq_u32(y0, y2);
                let z2 = mont_mul_nomin(vsubq_u32(y0, y2), s_o);
                let z1 = vaddq_u32(y1, y3);
                let z3 = mont_mul_nomin(vsubq_u32(y1, y3), s_o);
                vst1q_u32(a.add(j), z0);
                vst1q_u32(a.add(j + ppg), z1);
                vst1q_u32(a.add(j + 2 * ppg), z2);
                vst1q_u32(a.add(j + 3 * ppg), z3);
                j += 4;
            }
        }
    }

    /// TIMING PROBE ONLY — the whole NTT with reduction-free passes for the
    /// `ppg >= 4` bulk (ppg 1/2 + tail stay exact; they are a small fraction).
    /// Output values are GARBAGE; wall time is the interesting part.
    pub unsafe fn ntt_bitrev_to_natural_nomin_probe(a: &mut [u32], log_n: u32, tw: &[u32]) {
        let n = a.len();
        debug_assert_eq!(n, 1usize << log_n);
        let p = a.as_mut_ptr();
        let t = tw.as_ptr();
        pass_ppg1(p, n, t);
        pass_ppg2(p, n, t);
        let mut ppg = 4usize;
        let mut num_groups = n / 8;
        while num_groups >= 4 {
            radix4_pass_nomin(p, ppg, num_groups, t);
            ppg *= 4;
            num_groups /= 4;
        }
        match num_groups {
            2 => tail_two_groups(p, n, t),
            1 => tail_final(p, n),
            _ => unreachable!(),
        }
    }

    /// Montgomery REDC of 64-bit lane accumulators (`t < R*p`), canonical
    /// output. Input as two u64x2 vectors (lanes 0,1 / 2,3).
    #[inline(always)]
    unsafe fn redc64(t_l: uint64x2_t, t_h: uint64x2_t) -> uint32x4_t {
        let lo32 = vuzp1q_u32(vreinterpretq_u32_u64(t_l), vreinterpretq_u32_u64(t_h));
        let m = vmulq_u32(lo32, vdupq_n_u32(K));
        let mp_l = vmull_u32(vget_low_u32(m), vget_low_u32(pv()));
        let mp_h = vmull_high_u32(m, pv());
        let s_l = vaddq_u64(t_l, mp_l);
        let s_h = vaddq_u64(t_h, mp_h);
        let r = vuzp2q_u32(vreinterpretq_u32_u64(s_l), vreinterpretq_u32_u64(s_h));
        let rs = vsubq_u32(r, pv());
        vminq_u32(r, rs)
    }

    /// Full 64-bit product of 4 u32 lanes as two u64x2 vectors.
    #[inline(always)]
    unsafe fn widening_mul(a: uint32x4_t, b: uint32x4_t) -> (uint64x2_t, uint64x2_t) {
        (
            vmull_u32(vget_low_u32(a), vget_low_u32(b)),
            vmull_high_u32(a, b),
        )
    }

    /// Radix-4 pass with U64 ACCUMULATION: the two odd outputs are computed as
    /// single REDCs of 64-bit product sums —
    ///   `X1 = REDC(D01*s_a + D23*s_b)`            (2 REDCs fused into 1)
    ///   `X3 = REDC(D01*s_ao - D23*s_bo + p*s_bo)` (COMBINED twiddles
    ///          `s_ao = mont(s_a, s_o)`, `s_bo = mont(s_b, s_o)` — kills the
    ///          chained mul-after-sub-after-mul)
    /// Bounds: every accumulator < 2p^2 < R*p, so REDC stays exact; outputs
    /// canonical => byte-identical to the plain pass.
    #[inline(always)]
    unsafe fn radix4_pass_acc(
        a: *mut u32,
        ppg: usize,
        num_groups: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) {
        let ng_outer = num_groups / 2;
        for k2 in 0..ng_outer {
            let s_a = vdupq_n_u32(*tw.add(2 * k2));
            let s_b = vdupq_n_u32(*tw.add(2 * k2 + 1));
            let s_o = vdupq_n_u32(*tw.add(k2));
            let s_ao = vdupq_n_u32(*tw_ao.add(k2));
            let s_bo = vdupq_n_u32(*tw_bo.add(k2));
            // p * s_bo as a broadcast 64-bit bias (makes the X3 accumulator
            // non-negative)
            let bias = vdupq_n_u64((P as u64) * (*tw_bo.add(k2) as u64));
            let base = k2 * ppg * 4;
            let mut j = base;
            while j < base + ppg {
                let x0 = vld1q_u32(a.add(j));
                let x1 = vld1q_u32(a.add(j + ppg));
                let x2 = vld1q_u32(a.add(j + 2 * ppg));
                let x3 = vld1q_u32(a.add(j + 3 * ppg));

                // even outputs (unchanged structure)
                let y0 = add(x0, x1);
                let y2 = add(x2, x3);
                let z0 = add(y0, y2);
                let z2 = mont_mul(sub(y0, y2), s_o);

                // odd outputs via u64 accumulation
                let d01 = sub(x0, x1);
                let d23 = sub(x2, x3);
                let (p1l, p1h) = widening_mul(d01, s_a);
                let (p2l, p2h) = widening_mul(d23, s_b);
                let z1 = redc64(vaddq_u64(p1l, p2l), vaddq_u64(p1h, p2h));
                let (p3l, p3h) = widening_mul(d01, s_ao);
                let (p4l, p4h) = widening_mul(d23, s_bo);
                let z3 = redc64(
                    vsubq_u64(vaddq_u64(p3l, bias), p4l),
                    vsubq_u64(vaddq_u64(p3h, bias), p4h),
                );

                vst1q_u32(a.add(j), z0);
                vst1q_u32(a.add(j + ppg), z1);
                vst1q_u32(a.add(j + 2 * ppg), z2);
                vst1q_u32(a.add(j + 3 * ppg), z3);
                j += 4;
            }
        }
    }

    /// NTT with the u64-accumulation radix-4 passes. `tw_ao`/`tw_bo` are the
    /// combined-twiddle tables `mont(tw[2k], tw[k])` / `mont(tw[2k+1], tw[k])`
    /// (indexed by outer group k — pass-independent, precomputable once per
    /// twiddle table).
    pub unsafe fn ntt_bitrev_to_natural_acc(
        a: &mut [u32],
        log_n: u32,
        tw: &[u32],
        tw_ao: &[u32],
        tw_bo: &[u32],
    ) {
        let n = a.len();
        debug_assert_eq!(n, 1usize << log_n);
        debug_assert!(n >= 16);
        let p = a.as_mut_ptr();
        let t = tw.as_ptr();
        pass_ppg1(p, n, t);
        pass_ppg2(p, n, t);
        let mut ppg = 4usize;
        let mut num_groups = n / 8;
        while num_groups >= 4 {
            radix4_pass_acc(p, ppg, num_groups, t, tw_ao.as_ptr(), tw_bo.as_ptr());
            ppg *= 4;
            num_groups /= 4;
        }
        match num_groups {
            2 => tail_two_groups(p, n, t),
            1 => tail_final(p, n),
            _ => unreachable!(),
        }
    }

    /// 4x4 u32 in-register transpose: `c_j` holds column `j` of rows
    /// `r0..r3`.
    #[inline(always)]
    pub unsafe fn transpose4x4(
        r0: uint32x4_t,
        r1: uint32x4_t,
        r2: uint32x4_t,
        r3: uint32x4_t,
    ) -> (uint32x4_t, uint32x4_t, uint32x4_t, uint32x4_t) {
        let t0 = vtrn1q_u32(r0, r1);
        let t1 = vtrn2q_u32(r0, r1);
        let t2 = vtrn1q_u32(r2, r3);
        let t3 = vtrn2q_u32(r2, r3);
        let t0 = vreinterpretq_u64_u32(t0);
        let t1 = vreinterpretq_u64_u32(t1);
        let t2 = vreinterpretq_u64_u32(t2);
        let t3 = vreinterpretq_u64_u32(t3);
        (
            vreinterpretq_u32_u64(vtrn1q_u64(t0, t2)),
            vreinterpretq_u32_u64(vtrn1q_u64(t1, t3)),
            vreinterpretq_u32_u64(vtrn2q_u64(t0, t2)),
            vreinterpretq_u32_u64(vtrn2q_u64(t1, t3)),
        )
    }
}

/// Combined-twiddle tables for the u64-accumulation radix-4 passes:
/// `tw_ao[k] = mont(tw[2k], tw[k])`, `tw_bo[k] = mont(tw[2k+1], tw[k])` for
/// `k < n/16` (the largest outer-group range). Pass-independent — computed
/// once per twiddle table.
pub fn build_combined_twiddles(tw_raw: &[u32], n: usize) -> (Vec<u32>, Vec<u32>) {
    let len = n / 16;
    let mut ao = Vec::with_capacity(len);
    let mut bo = Vec::with_capacity(len);
    for k in 0..len {
        ao.push(mont_mul_scalar(tw_raw[2 * k], tw_raw[k]));
        bo.push(mont_mul_scalar(tw_raw[2 * k + 1], tw_raw[k]));
    }
    (ao, bo)
}

// ---------------------------------------------------------------------------
// Flat NEON pipeline
// ---------------------------------------------------------------------------

/// FLAT LDE coset, fully NEON: scaled copy (vector muls, same split-power
/// factors as the fused scalar kernel), scalar bit-reversal, NEON radix-4 NTT.
/// Byte-identical to `fft::lde_coset_natural_seq_fused`.
#[cfg(target_arch = "aarch64")]
pub fn lde_flat_neon_r4(
    input: &[BabyBearField],
    offset: BabyBearField,
    twiddles_raw: &[u32],
) -> Vec<BabyBearField> {
    let n = input.len();
    let log_n = n.trailing_zeros();
    assert!(n >= 16);

    let input_raw: &[u32] = unsafe { core::slice::from_raw_parts(input.as_ptr() as *const u32, n) };

    let mut v: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        v.set_len(n)
    };

    if offset != BabyBearField::ONE {
        let sp = SplitPowersRaw::new(offset, log_n);
        unsafe {
            use core::arch::aarch64::*;
            let lo_len = sp.mask + 1;
            let src = input_raw.as_ptr();
            let dst = v.as_mut_ptr();
            let mut i = 0usize;
            // hi factor constant within each lo-table period
            while i < n {
                let hi = vdupq_n_u32(sp.hi[i >> sp.h]);
                let block_end = i + lo_len;
                let mut j = i;
                while j < block_end {
                    let lo = vld1q_u32(sp.lo.as_ptr().add(j - i));
                    let f = neon::mont_mul(lo, hi);
                    let x = vld1q_u32(src.add(j));
                    vst1q_u32(dst.add(j), neon::mont_mul(x, f));
                    j += 4;
                }
                i = block_end;
            }
        }
    } else {
        v.copy_from_slice(input_raw);
    }

    fft::bitreverse_enumeration_inplace(&mut v);

    unsafe {
        neon::ntt_bitrev_to_natural(&mut v, log_n, &twiddles_raw[..n / 2]);
    }

    // raw -> field (canonical, repr(transparent))
    unsafe { core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(v) }
}

// ---------------------------------------------------------------------------
// Six-step NEON pipeline
// ---------------------------------------------------------------------------

/// Per-stage wall times of one six-step LDE task, seconds.
#[derive(Default, Clone, Copy, Debug)]
pub struct BbStageTimes {
    pub gather_scale: f64,
    pub rows_a: f64,
    pub transpose: f64,
    pub rows_b: f64,
    pub scatter: f64,
}

/// Six-step LDE coset with NEON row FFTs and NEON 4x4 tile transposes.
/// `N = N1 x N2` (`N1 >= N2`), natural monomials in -> natural coset evals
/// out; identical values to `fft::fft_natural_to_natural_four_step` (and so
/// to the classic pipeline).
#[cfg(target_arch = "aarch64")]
pub fn lde_six_step_neon(
    input: &[BabyBearField],
    offset: BabyBearField,
    omega: BabyBearField,
    twiddles_raw: &[u32],
    mut stages: Option<&mut BbStageTimes>,
) -> Vec<BabyBearField> {
    use core::arch::aarch64::*;
    use std::time::Instant;

    let n = input.len();
    let log_n = n.trailing_zeros();
    let log_n2 = log_n / 2;
    let log_n1 = log_n - log_n2;
    let n1 = 1usize << log_n1;
    let n2 = 1usize << log_n2;
    assert!(n2 >= 16, "six-step draft needs N2 >= 16");

    let input_raw: &[u32] = unsafe { core::slice::from_raw_parts(input.as_ptr() as *const u32, n) };

    // offset scaling tables: pa[i1] = offset^{i1}, pb[i2] = (offset^{N1})^{i2}
    // (same factor construction as the reference four-step).
    let scale = offset != BabyBearField::ONE;
    let (pa, pb): (Vec<u32>, Vec<u32>) = if scale {
        let mut pa = Vec::with_capacity(n1);
        let mut cur = BabyBearField::ONE;
        for _ in 0..n1 {
            pa.push(cur.raw_u32_value());
            cur.mul_assign(&offset);
        }
        let step = offset.pow(n1 as u32);
        let mut pb = Vec::with_capacity(n2);
        let mut cur = BabyBearField::ONE;
        for _ in 0..n2 {
            pb.push(cur.raw_u32_value());
            cur.mul_assign(&step);
        }
        (pa, pb)
    } else {
        (Vec::new(), Vec::new())
    };

    let mut a: Vec<u32> = Vec::with_capacity(n);
    let mut b: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        a.set_len(n);
        b.set_len(n);
    }

    // Pass 1: gather-transpose x (N2 x N1 row-major) -> a (N1 x N2) via 4x4
    // NEON tiles, with the scale factor pa[i1]*pb[i2] applied in-register.
    let t0 = Instant::now();
    unsafe {
        let src = input_raw.as_ptr();
        let dst = a.as_mut_ptr();
        let mut i2t = 0usize;
        while i2t < n2 {
            let mut i1t = 0usize;
            while i1t < n1 {
                // load 4 source rows (fixed i2, consecutive i1)
                let r0 = vld1q_u32(src.add(i2t * n1 + i1t));
                let r1 = vld1q_u32(src.add((i2t + 1) * n1 + i1t));
                let r2 = vld1q_u32(src.add((i2t + 2) * n1 + i1t));
                let r3 = vld1q_u32(src.add((i2t + 3) * n1 + i1t));
                let (c0, c1, c2, c3) = neon::transpose4x4(r0, r1, r2, r3);
                // c_j = row (i1t + j) of a, elements i2t..i2t+4
                if scale {
                    let pbv = vld1q_u32(pb.as_ptr().add(i2t));
                    let f0 = neon::mont_mul(vdupq_n_u32(pa[i1t]), pbv);
                    let f1 = neon::mont_mul(vdupq_n_u32(pa[i1t + 1]), pbv);
                    let f2 = neon::mont_mul(vdupq_n_u32(pa[i1t + 2]), pbv);
                    let f3 = neon::mont_mul(vdupq_n_u32(pa[i1t + 3]), pbv);
                    vst1q_u32(dst.add(i1t * n2 + i2t), neon::mont_mul(c0, f0));
                    vst1q_u32(dst.add((i1t + 1) * n2 + i2t), neon::mont_mul(c1, f1));
                    vst1q_u32(dst.add((i1t + 2) * n2 + i2t), neon::mont_mul(c2, f2));
                    vst1q_u32(dst.add((i1t + 3) * n2 + i2t), neon::mont_mul(c3, f3));
                } else {
                    vst1q_u32(dst.add(i1t * n2 + i2t), c0);
                    vst1q_u32(dst.add((i1t + 1) * n2 + i2t), c1);
                    vst1q_u32(dst.add((i1t + 2) * n2 + i2t), c2);
                    vst1q_u32(dst.add((i1t + 3) * n2 + i2t), c3);
                }
                i1t += 4;
            }
            i2t += 4;
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.gather_scale = t0.elapsed().as_secs_f64();
    }

    // Pass 2: per-row bitrev + NEON NTT(N2) + outer twiddle correction
    // row[k2] *= omega^{i1*k2} (vectorized power ladder: cur *= w^4).
    let t0 = Instant::now();
    let row_tw2 = &twiddles_raw[..(n2 / 2).max(1)];
    let mut w_row = BabyBearField::ONE;
    unsafe {
        for i1 in 0..n1 {
            let row = core::slice::from_raw_parts_mut(a.as_mut_ptr().add(i1 * n2), n2);
            fft::bitreverse_enumeration_inplace(row);
            neon::ntt_bitrev_to_natural(row, log_n2, row_tw2);
            if i1 != 0 {
                // lanes [w^0, w^1, w^2, w^3] * w_row applied as running vector
                let w = w_row;
                let mut w2 = w;
                w2.mul_assign(&w);
                let mut w3 = w2;
                w3.mul_assign(&w);
                let mut w4 = w3;
                w4.mul_assign(&w);
                let lanes = [
                    BabyBearField::ONE.raw_u32_value(),
                    w.raw_u32_value(),
                    w2.raw_u32_value(),
                    w3.raw_u32_value(),
                ];
                let mut cur = vld1q_u32(lanes.as_ptr());
                let step = vdupq_n_u32(w4.raw_u32_value());
                // row[0] *= w^0 stays; process from 0 in vectors anyway
                let p = row.as_mut_ptr();
                let mut k2 = 0usize;
                while k2 < n2 {
                    let d = vld1q_u32(p.add(k2));
                    vst1q_u32(p.add(k2), neon::mont_mul(d, cur));
                    cur = neon::mont_mul(cur, step);
                    k2 += 4;
                }
            }
            w_row.mul_assign(&omega);
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.rows_a = t0.elapsed().as_secs_f64();
    }

    // Pass 3: transpose a (N1 x N2) -> b (N2 x N1), 4x4 NEON tiles.
    let t0 = Instant::now();
    unsafe {
        let src = a.as_ptr();
        let dst = b.as_mut_ptr();
        let mut i1t = 0usize;
        while i1t < n1 {
            let mut i2t = 0usize;
            while i2t < n2 {
                let r0 = vld1q_u32(src.add(i1t * n2 + i2t));
                let r1 = vld1q_u32(src.add((i1t + 1) * n2 + i2t));
                let r2 = vld1q_u32(src.add((i1t + 2) * n2 + i2t));
                let r3 = vld1q_u32(src.add((i1t + 3) * n2 + i2t));
                let (c0, c1, c2, c3) = neon::transpose4x4(r0, r1, r2, r3);
                vst1q_u32(dst.add(i2t * n1 + i1t), c0);
                vst1q_u32(dst.add((i2t + 1) * n1 + i1t), c1);
                vst1q_u32(dst.add((i2t + 2) * n1 + i1t), c2);
                vst1q_u32(dst.add((i2t + 3) * n1 + i1t), c3);
                i2t += 4;
            }
            i1t += 4;
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.transpose = t0.elapsed().as_secs_f64();
    }

    // Pass 4: per-row bitrev + NEON NTT(N1), no twiddle correction.
    let t0 = Instant::now();
    let row_tw1 = &twiddles_raw[..(n1 / 2).max(1)];
    unsafe {
        for k2 in 0..n2 {
            let row = core::slice::from_raw_parts_mut(b.as_mut_ptr().add(k2 * n1), n1);
            fft::bitreverse_enumeration_inplace(row);
            neon::ntt_bitrev_to_natural(row, log_n1, row_tw1);
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.rows_b = t0.elapsed().as_secs_f64();
    }

    // Pass 5: transpose b (N2 x N1) -> a; a[k1*N2 + k2] is the natural output.
    let t0 = Instant::now();
    unsafe {
        let src = b.as_ptr();
        let dst = a.as_mut_ptr();
        let mut i2t = 0usize;
        while i2t < n2 {
            let mut i1t = 0usize;
            while i1t < n1 {
                let r0 = vld1q_u32(src.add(i2t * n1 + i1t));
                let r1 = vld1q_u32(src.add((i2t + 1) * n1 + i1t));
                let r2 = vld1q_u32(src.add((i2t + 2) * n1 + i1t));
                let r3 = vld1q_u32(src.add((i2t + 3) * n1 + i1t));
                let (c0, c1, c2, c3) = neon::transpose4x4(r0, r1, r2, r3);
                vst1q_u32(dst.add(i1t * n2 + i2t), c0);
                vst1q_u32(dst.add((i1t + 1) * n2 + i2t), c1);
                vst1q_u32(dst.add((i1t + 2) * n2 + i2t), c2);
                vst1q_u32(dst.add((i1t + 3) * n2 + i2t), c3);
                i1t += 4;
            }
            i2t += 4;
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.scatter = t0.elapsed().as_secs_f64();
    }

    drop(b);
    unsafe { core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(a) }
}

// ---------------------------------------------------------------------------
// Hypercube -> monomial (Mobius) transform: radix-N drafts
// ---------------------------------------------------------------------------

/// Reference (mirror of the prover's `multivariate_hypercube_evals_into_coeffs`):
/// one stride-halving subtraction sweep per variable.
pub fn hc_to_monomial_ref<F: Field>(input: &mut [F], size_log2: u32) {
    let len = 1usize << size_log2;
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

/// One fused radix-4 sweep over the stride pair `(stride, stride/2)`; same
/// subtraction sequence as two reference sweeps => identical values.
#[inline(always)]
fn hc_radix4_sweep<F: Field>(input: &mut [F], len: usize, stride: usize) {
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

/// Radix-4 hypercube->monomial: two variables per sweep (half the loads and
/// stores of the reference), identical values.
pub fn hc_to_monomial_radix4<F: Field>(input: &mut [F], size_log2: u32) {
    let len = 1usize << size_log2;
    debug_assert_eq!(input.len(), len);
    let mut stride = len / 2;
    let mut remaining = size_log2;
    while remaining >= 2 {
        hc_radix4_sweep(input, len, stride);
        stride /= 4;
        remaining -= 2;
    }
    if remaining == 1 {
        for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
            b.sub_assign(&a);
        }
    }
}

/// Radix-8 hypercube->monomial: three variables per sweep (a third of the
/// loads/stores), radix-4/final tail for leftover variables. Identical values.
pub fn hc_to_monomial_radix8<F: Field>(input: &mut [F], size_log2: u32) {
    let len = 1usize << size_log2;
    debug_assert_eq!(input.len(), len);
    let mut stride = len / 2;
    let mut remaining = size_log2;
    while remaining >= 3 {
        let s2 = stride / 2;
        let s4 = stride / 4;
        let mut base = 0usize;
        while base < len {
            for j in base..base + s4 {
                unsafe {
                    // v_{b2 b1 b0} at j + b2*stride + b1*s2 + b0*s4
                    let mut v = [
                        *input.get_unchecked(j),
                        *input.get_unchecked(j + s4),
                        *input.get_unchecked(j + s2),
                        *input.get_unchecked(j + s2 + s4),
                        *input.get_unchecked(j + stride),
                        *input.get_unchecked(j + stride + s4),
                        *input.get_unchecked(j + stride + s2),
                        *input.get_unchecked(j + stride + s2 + s4),
                    ];
                    // stage `stride` (bit 2), then `s2` (bit 1), then `s4` (bit 0)
                    for k in 0..4 {
                        let lhs = v[k];
                        v[k + 4].sub_assign(&lhs);
                    }
                    for (hi, lo) in [(2, 0), (3, 1), (6, 4), (7, 5)] {
                        let lhs = v[lo];
                        v[hi].sub_assign(&lhs);
                    }
                    for (hi, lo) in [(1, 0), (3, 2), (5, 4), (7, 6)] {
                        let lhs = v[lo];
                        v[hi].sub_assign(&lhs);
                    }
                    *input.get_unchecked_mut(j + s4) = v[1];
                    *input.get_unchecked_mut(j + s2) = v[2];
                    *input.get_unchecked_mut(j + s2 + s4) = v[3];
                    *input.get_unchecked_mut(j + stride) = v[4];
                    *input.get_unchecked_mut(j + stride + s4) = v[5];
                    *input.get_unchecked_mut(j + stride + s2) = v[6];
                    *input.get_unchecked_mut(j + stride + s2 + s4) = v[7];
                }
            }
            base += 2 * stride;
        }
        stride /= 8;
        remaining -= 3;
    }
    if remaining == 2 {
        hc_radix4_sweep(input, len, stride);
        remaining = 0;
    }
    if remaining == 1 {
        for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
            b.sub_assign(&a);
        }
    }
}

/// NEON hypercube->monomial for BabyBear raw values: radix-8 sweeps with
/// vector subs for strides >= 4; the final `(4, 2, 1)` stride triple is one
/// in-register pass (contiguous 8 elements: whole-vector sub for stride 4,
/// u64-lane shuffle for stride 2, `uzp`/`zip` for stride 1).
#[cfg(target_arch = "aarch64")]
pub fn hc_to_monomial_neon_bb(input: &mut [u32], size_log2: u32) {
    use core::arch::aarch64::*;
    let len = 1usize << size_log2;
    debug_assert_eq!(input.len(), len);
    if len < 16 {
        // degrade to scalar via field view
        let view = unsafe {
            core::slice::from_raw_parts_mut(input.as_mut_ptr() as *mut BabyBearField, len)
        };
        hc_to_monomial_radix8(view, size_log2);
        return;
    }

    #[inline(always)]
    unsafe fn subv(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let d = vsubq_u32(a, b);
        vminq_u32(d, vaddq_u32(d, vdupq_n_u32(P)))
    }

    let p = input.as_mut_ptr();
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

        // leftover big strides (>= 4) as radix-4 / radix-2 vector sweeps until
        // only the (4, 2, 1) tail remains
        while remaining > 3 && stride >= 4 {
            // single-stride vector sweep
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
            // the contiguous (4, 2, 1) tail: 8 elements per block, in-register.
            // Modular sub against a ZERO lane is the identity (min(x, x+P) = x),
            // so lanes that must stay untouched simply subtract zero.
            debug_assert_eq!(stride, 4);
            let z = vdupq_n_u32(0);
            let mut j = 0usize;
            while j < len {
                let v0 = vld1q_u32(p.add(j)); // x0..x3
                let v1 = vld1q_u32(p.add(j + 4)); // x4..x7
                                                  // stride 4: x4..x7 -= x0..x3
                let v1 = subv(v1, v0);
                // stride 2: [x2,x3] -= [x0,x1] per vector — subtract the low
                // u64 lane shifted into the high position, zeros below
                let sh0 = vreinterpretq_u32_u64(vtrn1q_u64(
                    vreinterpretq_u64_u32(z),
                    vreinterpretq_u64_u32(v0),
                )); // [0, 0, x0, x1]
                let sh1 = vreinterpretq_u32_u64(vtrn1q_u64(
                    vreinterpretq_u64_u32(z),
                    vreinterpretq_u64_u32(v1),
                ));
                let v0 = subv(v0, sh0);
                let v1 = subv(v1, sh1);
                // stride 1: odd lanes -= even lanes (uzp / zip across both)
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
            // strides (2, 1) tail
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
            // stride-1 tail alone
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

/// Radix-N and NEON hypercube->monomial variants must match the reference
/// exactly (same subtraction sequence => canonical equality).
pub fn hc_self_check(log_n: u32) {
    let n = 1usize << log_n;
    let mut rng = rand::rng();
    let input: Vec<BabyBearField> = (0..n)
        .map(|_| BabyBearField::random_element(&mut rng))
        .collect();

    let mut expected = input.clone();
    hc_to_monomial_ref(&mut expected, log_n);

    let mut got = input.clone();
    hc_to_monomial_radix4(&mut got, log_n);
    assert_eq!(got, expected, "hc radix-4 diverged at log_n={log_n}");

    let mut got = input.clone();
    hc_to_monomial_radix8(&mut got, log_n);
    assert_eq!(got, expected, "hc radix-8 diverged at log_n={log_n}");

    #[cfg(target_arch = "aarch64")]
    {
        let mut got: Vec<u32> = input.iter().map(|x| x.raw_u32_value()).collect();
        hc_to_monomial_neon_bb(&mut got, log_n);
        let expected_raw: Vec<u32> = expected.iter().map(|x| x.raw_u32_value()).collect();
        assert_eq!(got, expected_raw, "hc NEON diverged at log_n={log_n}");
    }

    // large-field path: Proth120 through the same generic radix kernels
    let inp_p: Vec<field::Proth120> = (0..n)
        .map(|_| field::Proth120::random_element(&mut rng))
        .collect();
    let mut expected_p = inp_p.clone();
    hc_to_monomial_ref(&mut expected_p, log_n);
    let mut got_p = inp_p.clone();
    hc_to_monomial_radix8(&mut got_p, log_n);
    assert_eq!(
        got_p, expected_p,
        "hc radix-8 Proth120 diverged at log_n={log_n}"
    );
}

// ---------------------------------------------------------------------------
// Self-checks
// ---------------------------------------------------------------------------

/// Every NEON variant must be BYTE-IDENTICAL to
/// `fft::lde_coset_natural_seq_fused` (which the prover uses today).
pub fn self_check(log_n: u32) {
    let n = 1usize << log_n;
    let mut rng = rand::rng();
    let input: Vec<BabyBearField> = (0..n)
        .map(|_| BabyBearField::random_element(&mut rng))
        .collect();
    let tw: Vec<BabyBearField, Global> =
        fft::precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, false>(n);
    let offset = fft::domain_generator_for_size::<BabyBearField>((n * 2) as u64);

    for off in [offset, BabyBearField::ONE] {
        let expected = fft::lde_coset_natural_seq_fused(&input, off, &tw);
        #[cfg(target_arch = "aarch64")]
        {
            let tw_raw: Vec<u32> = tw.iter().map(|t| t.raw_u32_value()).collect();
            let got = lde_flat_neon_r4(&input, off, &tw_raw);
            assert_eq!(got, expected, "flat NEON diverged at log_n={log_n}");

            // u64-accumulation variant: identical NTT values
            let (tw_ao, tw_bo) = build_combined_twiddles(&tw_raw, n);
            let mut acc: Vec<u32> = expected.iter().map(|_| 0).collect();
            let mut plain: Vec<u32> = input.iter().map(|x| x.raw_u32_value()).collect();
            fft::bitreverse_enumeration_inplace(&mut plain);
            acc.copy_from_slice(&plain);
            unsafe {
                neon::ntt_bitrev_to_natural(&mut plain, log_n, &tw_raw[..n / 2]);
                neon::ntt_bitrev_to_natural_acc(&mut acc, log_n, &tw_raw[..n / 2], &tw_ao, &tw_bo);
            }
            assert_eq!(acc, plain, "u64-acc NTT diverged at log_n={log_n}");

            let omega = fft::domain_generator_for_size::<BabyBearField>(n as u64);
            let got = lde_six_step_neon(&input, off, omega, &tw_raw, None);
            assert_eq!(got, expected, "six-step NEON diverged at log_n={log_n}");
        }
        #[cfg(not(target_arch = "aarch64"))]
        {
            std::hint::black_box(&expected);
        }
    }
}
