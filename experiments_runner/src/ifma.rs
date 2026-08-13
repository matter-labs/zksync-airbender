//! DRAFT: AVX-512 IFMA (vpmadd52) vectorized Proth120 NTT.
//!
//! Representation: radix-2^52, three limbs per element (`p < 2^123`), in a
//! dedicated Montgomery domain `R = 2^156`. The special modulus form carries
//! over: in base-2^52 limbs `p = [1, 0, 7·2^16]` and `-p^{-1} mod 2^52 = -1`,
//! so each Montgomery reduction step is `m = -t0 mod 2^52` (no multiply) plus
//! one small-constant `madd52` pair for `m·(7·2^16)`.
//!
//! Data layout is SoA "limb planes": three `u64` arrays. A butterfly processes
//! 8 elements per instruction; the DIT stage structure is copied from
//! `fft::naive::serial_ct_ntt_bitreversed_to_natural` (same twiddle table,
//! bit-reversed, converted into the 2^52 domain), so outputs agree exactly with
//! the scalar reference after conversion — verified by [`self_check`].
//!
//! Stages with fewer than 8 butterflies per group (the first three) run with
//! the scalar 52-bit kernel; everything else is vectorized.
//!
//! Compile-time gated: the remote build uses `-Ctarget-cpu=sapphirerapids`.

#![allow(dead_code)]

use field::{Field, Proth120, Rand};

pub const MASK52: u64 = (1u64 << 52) - 1;
/// `p` in base-2^52 limbs: `7·2^120 + 1 = [1, 0, 7·2^16]`.
pub const P0: u64 = 1;
pub const P1: u64 = 0;
pub const P2: u64 = 7u64 << 16;

/// `2^k mod p` (for domain constants).
fn pow2_mod(k: usize) -> u128 {
    const ORDER: u128 = (7u128 << 120) + 1;
    let mut x = 1u128;
    for _ in 0..k {
        x <<= 1;
        if x >= ORDER {
            x -= ORDER;
        }
    }
    x
}

pub type Fp52 = [u64; 3];

pub fn limbs_of(x: u128) -> Fp52 {
    [
        (x as u64) & MASK52,
        ((x >> 52) as u64) & MASK52,
        (x >> 104) as u64,
    ]
}

pub fn value_of(l: Fp52) -> u128 {
    (l[0] as u128) | ((l[1] as u128) << 52) | ((l[2] as u128) << 104)
}

/// Natural value -> the 2^156 Montgomery domain (via the existing Proth120
/// arithmetic: `x · 2^156 mod p`).
pub fn to_mont52(x_natural: u128) -> Fp52 {
    let mut t = Proth120::new(x_natural);
    t.mul_assign(&Proth120::new(pow2_mod(156)));
    limbs_of(t.to_u128())
}

/// 2^156-domain value -> natural.
pub fn from_mont52(l: Fp52) -> u128 {
    let inv = Proth120::new(pow2_mod(156)).inverse().unwrap();
    let mut t = Proth120::new(value_of(l));
    t.mul_assign(&inv);
    t.to_u128()
}

/// Scalar base-2^52 Montgomery multiplication (used by the < 8-butterfly stages
/// and as the reference for the SIMD kernel).
#[inline(always)]
pub fn mont52_mul(a: &Fp52, b: &Fp52) -> Fp52 {
    const M: u128 = MASK52 as u128;
    let c = P2 as u128;

    let (mut t0, mut t1, mut t2, mut t3) = (0u128, 0u128, 0u128, 0u128);
    let mut i = 0;
    while i < 3 {
        let bi = b[i] as u128;
        let p = (a[0] as u128) * bi;
        t0 += p & M;
        t1 += p >> 52;
        let p = (a[1] as u128) * bi;
        t1 += p & M;
        t2 += p >> 52;
        let p = (a[2] as u128) * bi;
        t2 += p & M;
        t3 += p >> 52;

        // reduction: m = -t0 mod 2^52; t = (t + m + (7·2^16 · m)·2^104) >> 52
        let m = ((1u128 << 52) - (t0 & M)) & M;
        let carry = (t0 + m) >> 52;
        let pm = m * c;
        t2 += pm & M;
        t3 += pm >> 52;
        t0 = t1 + carry;
        t1 = t2;
        t2 = t3;
        t3 = 0;
        i += 1;
    }
    // normalize
    t1 += t0 >> 52;
    t0 &= M;
    t2 += t1 >> 52;
    t1 &= M;
    debug_assert!(t2 < (1u128 << 54));

    // conditional subtract p (result < 2p)
    let (mut r0, mut r1, mut r2) = (t0 as u64, t1 as u64, t2 as u64);
    let value_ge_p = r2 > P2 || (r2 == P2 && (r1 > 0 || r0 >= 1));
    if value_ge_p {
        let b0 = (r0 < P0) as u64;
        r0 = (r0.wrapping_sub(P0)) & MASK52;
        let b1 = (r1 < b0) as u64;
        r1 = (r1.wrapping_sub(b0)) & MASK52;
        r2 = r2 - P2 - b1;
    }
    [r0, r1, r2]
}

#[inline(always)]
fn add52(a: &Fp52, b: &Fp52) -> Fp52 {
    let mut t0 = a[0] + b[0];
    let mut t1 = a[1] + b[1] + (t0 >> 52);
    t0 &= MASK52;
    let mut t2 = a[2] + b[2] + (t1 >> 52);
    t1 &= MASK52;
    let ge = t2 > P2 || (t2 == P2 && (t1 > 0 || t0 >= 1));
    if ge {
        let b0 = (t0 < P0) as u64;
        t0 = (t0.wrapping_sub(P0)) & MASK52;
        let b1 = (t1 < b0) as u64;
        t1 = (t1.wrapping_sub(b0)) & MASK52;
        t2 = t2 - P2 - b1;
    }
    [t0, t1, t2]
}

#[inline(always)]
fn sub52(a: &Fp52, b: &Fp52) -> Fp52 {
    // a + (p - b), b canonical
    let b0 = (P0 < b[0]) as u64;
    let d0 = (P0.wrapping_sub(b[0])) & MASK52;
    let bb = b[1] + b0;
    let b1 = (P1 < bb) as u64;
    let d1 = (P1.wrapping_sub(bb)) & MASK52;
    let d2 = P2 - b[2] - b1;
    add52(a, &[d0, d1, d2])
}

// ---------------------------------------------------------------------------
// SIMD kernels (x86_64 with avx512ifma compiled in)
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
pub mod simd {
    use super::*;
    use core::arch::x86_64::*;

    #[inline(always)]
    unsafe fn mask52() -> __m512i {
        _mm512_set1_epi64(MASK52 as i64)
    }

    /// 8-lane batched `v · s` in the 2^52 Montgomery domain, `s` broadcast.
    /// Returns canonical (< p) limbs.
    #[inline(always)]
    pub unsafe fn mul_by_scalar8(v: [__m512i; 3], s: &Fp52) -> [__m512i; 3] {
        let zero = _mm512_setzero_si512();
        let m52 = mask52();
        let cvec = _mm512_set1_epi64(P2 as i64);

        let mut t0 = zero;
        let mut t1 = zero;
        let mut t2 = zero;
        let mut t3 = zero;

        let mut i = 0;
        while i < 3 {
            let bi = _mm512_set1_epi64(s[i] as i64);
            t0 = _mm512_madd52lo_epu64(t0, v[0], bi);
            t1 = _mm512_madd52hi_epu64(t1, v[0], bi);
            t1 = _mm512_madd52lo_epu64(t1, v[1], bi);
            t2 = _mm512_madd52hi_epu64(t2, v[1], bi);
            t2 = _mm512_madd52lo_epu64(t2, v[2], bi);
            t3 = _mm512_madd52hi_epu64(t3, v[2], bi);

            // m = (-t0) mod 2^52
            let m = _mm512_and_si512(_mm512_sub_epi64(zero, t0), m52);
            let carry = _mm512_srli_epi64::<52>(_mm512_add_epi64(t0, m));
            t2 = _mm512_madd52lo_epu64(t2, m, cvec);
            t3 = _mm512_madd52hi_epu64(t3, m, cvec);
            t0 = _mm512_add_epi64(t1, carry);
            t1 = t2;
            t2 = t3;
            t3 = zero;
            i += 1;
        }

        // normalize lazy limbs
        t1 = _mm512_add_epi64(t1, _mm512_srli_epi64::<52>(t0));
        t0 = _mm512_and_si512(t0, m52);
        t2 = _mm512_add_epi64(t2, _mm512_srli_epi64::<52>(t1));
        t1 = _mm512_and_si512(t1, m52);

        cond_sub_p([t0, t1, t2])
    }

    /// 8-lane batched full multiplication `a · b` (per-lane multiplicands) in
    /// the 2^52 Montgomery domain. Same algorithm as [`mul_by_scalar8`] with
    /// vector `b` limbs.
    #[inline(always)]
    pub unsafe fn mul8(a: [__m512i; 3], b: [__m512i; 3]) -> [__m512i; 3] {
        let zero = _mm512_setzero_si512();
        let m52 = mask52();
        let cvec = _mm512_set1_epi64(P2 as i64);

        let mut t0 = zero;
        let mut t1 = zero;
        let mut t2 = zero;
        let mut t3 = zero;

        let mut i = 0;
        while i < 3 {
            let bi = b[i];
            t0 = _mm512_madd52lo_epu64(t0, a[0], bi);
            t1 = _mm512_madd52hi_epu64(t1, a[0], bi);
            t1 = _mm512_madd52lo_epu64(t1, a[1], bi);
            t2 = _mm512_madd52hi_epu64(t2, a[1], bi);
            t2 = _mm512_madd52lo_epu64(t2, a[2], bi);
            t3 = _mm512_madd52hi_epu64(t3, a[2], bi);

            let m = _mm512_and_si512(_mm512_sub_epi64(zero, t0), m52);
            let carry = _mm512_srli_epi64::<52>(_mm512_add_epi64(t0, m));
            t2 = _mm512_madd52lo_epu64(t2, m, cvec);
            t3 = _mm512_madd52hi_epu64(t3, m, cvec);
            t0 = _mm512_add_epi64(t1, carry);
            t1 = t2;
            t2 = t3;
            t3 = zero;
            i += 1;
        }

        t1 = _mm512_add_epi64(t1, _mm512_srli_epi64::<52>(t0));
        t0 = _mm512_and_si512(t0, m52);
        t2 = _mm512_add_epi64(t2, _mm512_srli_epi64::<52>(t1));
        t1 = _mm512_and_si512(t1, m52);

        cond_sub_p([t0, t1, t2])
    }

    /// WARNING (vector b caveat): `madd52` uses only the LOW 52 bits of each
    /// multiplicand lane — all inputs here are canonical 52-bit limbs, so this
    /// is exact.
    /// Subtract `p` from lanes where the 3-limb value is >= p.
    #[inline(always)]
    unsafe fn cond_sub_p(t: [__m512i; 3]) -> [__m512i; 3] {
        let m52 = mask52();
        let one = _mm512_set1_epi64(1);
        let cvec = _mm512_set1_epi64(P2 as i64);

        // borrow chain of t - p; final borrow set => t < p (keep t)
        let b0 = _mm512_cmplt_epu64_mask(t[0], one);
        let s0 = _mm512_and_si512(_mm512_sub_epi64(t[0], one), m52);
        let b0v = _mm512_maskz_set1_epi64(b0, 1);
        let b1 = _mm512_cmplt_epu64_mask(t[1], b0v);
        let s1 = _mm512_and_si512(_mm512_sub_epi64(t[1], b0v), m52);
        let b1v = _mm512_maskz_set1_epi64(b1, 1);
        let sub2 = _mm512_add_epi64(cvec, b1v);
        let keep = _mm512_cmplt_epu64_mask(t[2], sub2); // t < p
        let s2 = _mm512_sub_epi64(t[2], sub2);

        [
            _mm512_mask_blend_epi64(keep, s0, t[0]),
            _mm512_mask_blend_epi64(keep, s1, t[1]),
            _mm512_mask_blend_epi64(keep, s2, t[2]),
        ]
    }

    /// 8-lane modular addition of canonical values.
    #[inline(always)]
    pub unsafe fn add8(a: [__m512i; 3], b: [__m512i; 3]) -> [__m512i; 3] {
        let m52 = mask52();
        let mut t0 = _mm512_add_epi64(a[0], b[0]);
        let mut t1 = _mm512_add_epi64(a[1], b[1]);
        let mut t2 = _mm512_add_epi64(a[2], b[2]);
        t1 = _mm512_add_epi64(t1, _mm512_srli_epi64::<52>(t0));
        t0 = _mm512_and_si512(t0, m52);
        t2 = _mm512_add_epi64(t2, _mm512_srli_epi64::<52>(t1));
        t1 = _mm512_and_si512(t1, m52);
        cond_sub_p([t0, t1, t2])
    }

    /// 8-lane modular subtraction `a - b` of canonical values (`a + (p - b)`).
    #[inline(always)]
    pub unsafe fn sub8(a: [__m512i; 3], b: [__m512i; 3]) -> [__m512i; 3] {
        let m52 = mask52();
        let one = _mm512_set1_epi64(P0 as i64);
        let cvec = _mm512_set1_epi64(P2 as i64);
        let zero = _mm512_setzero_si512();

        // p - b with borrow chain (b canonical => no final borrow)
        let bb0 = _mm512_cmplt_epu64_mask(one, b[0]);
        let d0 = _mm512_and_si512(_mm512_sub_epi64(one, b[0]), m52);
        let b0v = _mm512_maskz_set1_epi64(bb0, 1);
        let bplus = _mm512_add_epi64(b[1], b0v);
        let bb1 = _mm512_cmplt_epu64_mask(zero, bplus);
        let d1 = _mm512_and_si512(_mm512_sub_epi64(zero, bplus), m52);
        let b1v = _mm512_maskz_set1_epi64(bb1, 1);
        let d2 = _mm512_sub_epi64(cvec, _mm512_add_epi64(b[2], b1v));

        add8(a, [d0, d1, d2])
    }

    #[inline(always)]
    pub unsafe fn load3(l0: *const u64, l1: *const u64, l2: *const u64) -> [__m512i; 3] {
        [
            _mm512_loadu_epi64(l0 as *const i64),
            _mm512_loadu_epi64(l1 as *const i64),
            _mm512_loadu_epi64(l2 as *const i64),
        ]
    }

    /// IN-REGISTER REPACK, load side: 8 contiguous stored `u128` values
    /// (little-endian qword pairs `[lo, hi]`) -> three 52-bit limb vectors.
    /// Two 64-B loads, two `vpermt2q` to split lo/hi qwords, then shifts/masks:
    /// `l0 = lo & m52`, `l1 = (lo>>52 | hi<<12) & m52`, `l2 = hi >> 40`.
    #[inline(always)]
    pub unsafe fn load8_u128_split(ptr: *const u128) -> [__m512i; 3] {
        let z0 = _mm512_loadu_epi64(ptr as *const i64);
        let z1 = _mm512_loadu_epi64(ptr.add(4) as *const i64);
        let idx_lo = _mm512_setr_epi64(0, 2, 4, 6, 8, 10, 12, 14);
        let idx_hi = _mm512_setr_epi64(1, 3, 5, 7, 9, 11, 13, 15);
        let lo = _mm512_permutex2var_epi64(z0, idx_lo, z1);
        let hi = _mm512_permutex2var_epi64(z0, idx_hi, z1);
        let m52 = mask52();
        [
            _mm512_and_si512(lo, m52),
            _mm512_and_si512(
                _mm512_or_si512(_mm512_srli_epi64::<52>(lo), _mm512_slli_epi64::<12>(hi)),
                m52,
            ),
            _mm512_srli_epi64::<40>(hi),
        ]
    }

    /// IN-REGISTER REPACK, store side: three canonical limb vectors -> 8
    /// contiguous `u128` stores. `lo = l0 | l1<<52`, `hi = l1>>12 | l2<<40`,
    /// two `vpermt2q` to interleave back into qword pairs, two 64-B stores.
    #[inline(always)]
    pub unsafe fn store8_u128_combine(v: [__m512i; 3], ptr: *mut u128) {
        let lo = _mm512_or_si512(v[0], _mm512_slli_epi64::<52>(v[1]));
        let hi = _mm512_or_si512(_mm512_srli_epi64::<12>(v[1]), _mm512_slli_epi64::<40>(v[2]));
        let idx_a = _mm512_setr_epi64(0, 8, 1, 9, 2, 10, 3, 11);
        let idx_b = _mm512_setr_epi64(4, 12, 5, 13, 6, 14, 7, 15);
        let z0 = _mm512_permutex2var_epi64(lo, idx_a, hi);
        let z1 = _mm512_permutex2var_epi64(lo, idx_b, hi);
        _mm512_storeu_epi64(ptr as *mut i64, z0);
        _mm512_storeu_epi64(ptr.add(4) as *mut i64, z1);
    }

    #[inline(always)]
    pub unsafe fn store3(v: [__m512i; 3], l0: *mut u64, l1: *mut u64, l2: *mut u64) {
        _mm512_storeu_epi64(l0 as *mut i64, v[0]);
        _mm512_storeu_epi64(l1 as *mut i64, v[1]);
        _mm512_storeu_epi64(l2 as *mut i64, v[2]);
    }
}

// ---------------------------------------------------------------------------
// SoA planes + NTT driver
// ---------------------------------------------------------------------------

/// SoA limb planes for a vector of field elements.
#[derive(Clone)]
pub struct Planes {
    pub l0: Vec<u64>,
    pub l1: Vec<u64>,
    pub l2: Vec<u64>,
}

impl Planes {
    pub fn from_proth(vals: &[Proth120]) -> Self {
        let n = vals.len();
        let mut l0 = Vec::with_capacity(n);
        let mut l1 = Vec::with_capacity(n);
        let mut l2 = Vec::with_capacity(n);
        for v in vals.iter() {
            let l = to_mont52(v.to_u128());
            l0.push(l[0]);
            l1.push(l[1]);
            l2.push(l[2]);
        }
        Self { l0, l1, l2 }
    }

    pub fn to_naturals(&self) -> Vec<u128> {
        (0..self.l0.len())
            .map(|i| from_mont52([self.l0[i], self.l1[i], self.l2[i]]))
            .collect()
    }

    #[inline(always)]
    pub fn get(&self, i: usize) -> Fp52 {
        [self.l0[i], self.l1[i], self.l2[i]]
    }

    #[inline(always)]
    pub fn set(&mut self, i: usize, v: Fp52) {
        self.l0[i] = v[0];
        self.l1[i] = v[1];
        self.l2[i] = v[2];
    }
}

/// Convert the (bit-reversed) Proth120 twiddle table into the 2^52 domain.
pub fn convert_twiddles(tw: &[Proth120]) -> Vec<Fp52> {
    tw.iter().map(|t| to_mont52(t.to_u128())).collect()
}

/// DIT NTT, bit-reversed input -> natural output, on limb planes. Same stage
/// structure and twiddle table (converted) as
/// `fft::naive::serial_ct_ntt_bitreversed_to_natural`, so the output NATURAL
/// values are identical to the scalar reference.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
pub fn ifma_ntt_bitreversed_to_natural(p: &mut Planes, log_n: u32, tw52: &[Fp52]) {
    let n = p.l0.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);

    let mut pairs_per_group = 1usize;
    let mut num_groups = n / 2;

    while num_groups > 1 {
        let ppg = pairs_per_group;
        if ppg >= 8 {
            for k in 0..num_groups {
                let s = &tw52[k];
                let base = k * ppg * 2;
                let mut j = 0;
                while j < ppg {
                    unsafe {
                        let idx = base + j;
                        let u = simd::load3(
                            p.l0.as_ptr().add(idx),
                            p.l1.as_ptr().add(idx),
                            p.l2.as_ptr().add(idx),
                        );
                        let v = simd::load3(
                            p.l0.as_ptr().add(idx + ppg),
                            p.l1.as_ptr().add(idx + ppg),
                            p.l2.as_ptr().add(idx + ppg),
                        );
                        // reference butterfly: new_u = u + v; new_v = (u - v)*s
                        let a = simd::add8(u, v);
                        let b = simd::mul_by_scalar8(simd::sub8(u, v), s);
                        simd::store3(
                            a,
                            p.l0.as_mut_ptr().add(idx),
                            p.l1.as_mut_ptr().add(idx),
                            p.l2.as_mut_ptr().add(idx),
                        );
                        simd::store3(
                            b,
                            p.l0.as_mut_ptr().add(idx + ppg),
                            p.l1.as_mut_ptr().add(idx + ppg),
                            p.l2.as_mut_ptr().add(idx + ppg),
                        );
                    }
                    j += 8;
                }
            }
        } else {
            // few butterflies per group: scalar kernel
            for k in 0..num_groups {
                let s = tw52[k];
                let base = k * ppg * 2;
                for j in base..base + ppg {
                    let u = p.get(j);
                    let v = p.get(j + ppg);
                    let d = sub52(&u, &v);
                    p.set(j, add52(&u, &v));
                    p.set(j + ppg, mont52_mul(&d, &s));
                }
            }
        }
        pairs_per_group *= 2;
        num_groups /= 2;
    }

    // final stage: omega = 1, butterflies without multiplication
    let half = n / 2;
    debug_assert_eq!(pairs_per_group, half);
    let mut j = 0;
    while j < half {
        unsafe {
            let u = simd::load3(
                p.l0.as_ptr().add(j),
                p.l1.as_ptr().add(j),
                p.l2.as_ptr().add(j),
            );
            let v = simd::load3(
                p.l0.as_ptr().add(j + half),
                p.l1.as_ptr().add(j + half),
                p.l2.as_ptr().add(j + half),
            );
            let a = simd::add8(u, v);
            let b = simd::sub8(u, v);
            simd::store3(
                a,
                p.l0.as_mut_ptr().add(j),
                p.l1.as_mut_ptr().add(j),
                p.l2.as_mut_ptr().add(j),
            );
            simd::store3(
                b,
                p.l0.as_mut_ptr().add(j + half),
                p.l1.as_mut_ptr().add(j + half),
                p.l2.as_mut_ptr().add(j + half),
            );
        }
        j += 8;
    }
}

/// Scalar-kernel fallback with identical structure (for cross-checks off-IFMA
/// hosts; unused when the SIMD path exists).
pub fn scalar52_ntt_bitreversed_to_natural(p: &mut Planes, log_n: u32, tw52: &[Fp52]) {
    let n = p.l0.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);
    let mut ppg = 1usize;
    let mut num_groups = n / 2;
    while num_groups > 1 {
        #[expect(
            clippy::needless_range_loop,
            reason = "index arithmetic / parallel multi-array indexing in a hot kernel; iterator form obscures the chunk offsets"
        )]
        for k in 0..num_groups {
            let s = tw52[k];
            let base = k * ppg * 2;
            for j in base..base + ppg {
                let u = p.get(j);
                let v = p.get(j + ppg);
                let d = sub52(&u, &v);
                p.set(j, add52(&u, &v));
                p.set(j + ppg, mont52_mul(&d, &s));
            }
        }
        ppg *= 2;
        num_groups /= 2;
    }
    let half = n / 2;
    for j in 0..half {
        let u = p.get(j);
        let v = p.get(j + half);
        p.set(j, add52(&u, &v));
        p.set(j + half, sub52(&u, &v));
    }
}

/// End-to-end check: the 52-bit-domain NTT (SIMD when available, scalar kernel
/// otherwise) must produce the same NATURAL values as the reference Proth120
/// NTT for the same bit-reversed input and twiddles.
pub fn self_check(log_n: u32) {
    use std::alloc::Global;

    let n = 1usize << log_n;
    let mut rng = rand::rng();
    let input: Vec<Proth120> = (0..n).map(|_| Proth120::random_element(&mut rng)).collect();
    let tw: Vec<Proth120, Global> =
        fft::precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);

    let mut reference = input.clone();
    fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut reference, log_n, &tw[..n / 2]);
    let expected: Vec<u128> = reference.iter().map(|x| x.to_u128()).collect();

    let tw52 = convert_twiddles(&tw[..n / 2]);
    let mut planes = Planes::from_proth(&input);
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
    ifma_ntt_bitreversed_to_natural(&mut planes, log_n, &tw52);
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512ifma")))]
    scalar52_ntt_bitreversed_to_natural(&mut planes, log_n, &tw52);

    let got = planes.to_naturals();
    assert_eq!(got, expected, "52-bit-domain NTT diverged at log_n={log_n}");
}

// ---------------------------------------------------------------------------
// Six-step NTT with 8-rows-in-lockstep blocks
// ---------------------------------------------------------------------------
//
// N = N1·N2 (N1 rows of length N2 in phase A). Rows are grouped in blocks of
// 8 and stored INTERLEAVED: element j of the 8 rows of a block occupies one
// contiguous 64-byte group per limb plane. Consequently a butterfly (j, j+d)
// is a single 8-lane vector op with a BROADCAST twiddle for every stage —
// including d = 1, 2, 4, which the flat SoA layout had to scalarize — and the
// per-row bit-reversal becomes a permutation of 64-byte groups. Each row
// transform touches N2·3·8 B (row block ≈ 96 KiB per 8 rows at N2 = 2^12) —
// L2-resident on SPR — while DRAM sees only the three block-granular
// relayout passes instead of log N butterfly sweeps.

/// Lane kernel abstraction: 8 field elements as three 8-lane limb vectors.
/// `ScalarK` is the portable reference (validates layout/twiddle logic on any
/// host); `IfmaK` is the AVX-512 IFMA implementation.
pub trait Kernel8 {
    type V: Copy;
    /// Load 8 lanes from the three limb planes at `off` (must be 8-aligned
    /// block starts in the interleaved layout).
    unsafe fn load(l0: *const u64, l1: *const u64, l2: *const u64) -> Self::V;
    unsafe fn store(v: Self::V, l0: *mut u64, l1: *mut u64, l2: *mut u64);
    unsafe fn add(a: Self::V, b: Self::V) -> Self::V;
    unsafe fn sub(a: Self::V, b: Self::V) -> Self::V;
    unsafe fn mul_broadcast(a: Self::V, s: &Fp52) -> Self::V;
    unsafe fn mul_lanes(a: Self::V, b: Self::V) -> Self::V;
    unsafe fn splat(s: &Fp52) -> Self::V;

    /// Boundary repack, load side: 8 CONTIGUOUS stored `u128` values split into
    /// limb lanes. Default goes through a stack buffer (portable); the IFMA
    /// kernels override with an in-register permute/shift sequence.
    unsafe fn load8_split(ptr: *const u128) -> Self::V {
        let mut xb = [[0u64; 8]; 3];
        #[expect(
            clippy::needless_range_loop,
            reason = "index arithmetic / parallel multi-array indexing in a hot kernel; iterator form obscures the chunk offsets"
        )]
        for l in 0..8 {
            let raw = ptr.add(l).read_unaligned();
            xb[0][l] = (raw as u64) & MASK52;
            xb[1][l] = ((raw >> 52) as u64) & MASK52;
            xb[2][l] = (raw >> 104) as u64;
        }
        Self::load(xb[0].as_ptr(), xb[1].as_ptr(), xb[2].as_ptr())
    }

    /// Boundary repack, store side: limb lanes recombined into 8 CONTIGUOUS
    /// `u128` stores. Same override story as [`Self::load8_split`].
    unsafe fn store8_combine(v: Self::V, ptr: *mut u128) {
        let mut yb = [[0u64; 8]; 3];
        Self::store(
            v,
            yb[0].as_mut_ptr(),
            yb[1].as_mut_ptr(),
            yb[2].as_mut_ptr(),
        );
        #[expect(
            clippy::needless_range_loop,
            reason = "index arithmetic / parallel multi-array indexing in a hot kernel; iterator form obscures the chunk offsets"
        )]
        for l in 0..8 {
            let val = (yb[0][l] as u128) | ((yb[1][l] as u128) << 52) | ((yb[2][l] as u128) << 104);
            ptr.add(l).write_unaligned(val);
        }
    }
}

/// 8x8 u64 tile transpose between two CONTIGUOUS 64-element tiles
/// (`dst[c*8 + r] = src[r*8 + c]`) — the whole relayout pass reduces to these.
/// AVX-512: 8 loads, 24 shuffles, 8 stores; scalar otherwise.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
#[inline(always)]
unsafe fn transpose8x8_u64(src: *const u64, dst: *mut u64) {
    use core::arch::x86_64::*;
    let r0 = _mm512_loadu_epi64(src.add(0) as *const i64);
    let r1 = _mm512_loadu_epi64(src.add(8) as *const i64);
    let r2 = _mm512_loadu_epi64(src.add(16) as *const i64);
    let r3 = _mm512_loadu_epi64(src.add(24) as *const i64);
    let r4 = _mm512_loadu_epi64(src.add(32) as *const i64);
    let r5 = _mm512_loadu_epi64(src.add(40) as *const i64);
    let r6 = _mm512_loadu_epi64(src.add(48) as *const i64);
    let r7 = _mm512_loadu_epi64(src.add(56) as *const i64);

    let t0 = _mm512_unpacklo_epi64(r0, r1);
    let t1 = _mm512_unpackhi_epi64(r0, r1);
    let t2 = _mm512_unpacklo_epi64(r2, r3);
    let t3 = _mm512_unpackhi_epi64(r2, r3);
    let t4 = _mm512_unpacklo_epi64(r4, r5);
    let t5 = _mm512_unpackhi_epi64(r4, r5);
    let t6 = _mm512_unpacklo_epi64(r6, r7);
    let t7 = _mm512_unpackhi_epi64(r6, r7);

    let s0 = _mm512_shuffle_i64x2::<0x88>(t0, t2);
    let s1 = _mm512_shuffle_i64x2::<0xDD>(t0, t2);
    let s2 = _mm512_shuffle_i64x2::<0x88>(t1, t3);
    let s3 = _mm512_shuffle_i64x2::<0xDD>(t1, t3);
    let s4 = _mm512_shuffle_i64x2::<0x88>(t4, t6);
    let s5 = _mm512_shuffle_i64x2::<0xDD>(t4, t6);
    let s6 = _mm512_shuffle_i64x2::<0x88>(t5, t7);
    let s7 = _mm512_shuffle_i64x2::<0xDD>(t5, t7);

    let c0 = _mm512_shuffle_i64x2::<0x88>(s0, s4);
    let c4 = _mm512_shuffle_i64x2::<0xDD>(s0, s4);
    let c1 = _mm512_shuffle_i64x2::<0x88>(s2, s6);
    let c5 = _mm512_shuffle_i64x2::<0xDD>(s2, s6);
    let c2 = _mm512_shuffle_i64x2::<0x88>(s1, s5);
    let c6 = _mm512_shuffle_i64x2::<0xDD>(s1, s5);
    let c3 = _mm512_shuffle_i64x2::<0x88>(s3, s7);
    let c7 = _mm512_shuffle_i64x2::<0xDD>(s3, s7);

    _mm512_storeu_epi64(dst.add(0) as *mut i64, c0);
    _mm512_storeu_epi64(dst.add(8) as *mut i64, c1);
    _mm512_storeu_epi64(dst.add(16) as *mut i64, c2);
    _mm512_storeu_epi64(dst.add(24) as *mut i64, c3);
    _mm512_storeu_epi64(dst.add(32) as *mut i64, c4);
    _mm512_storeu_epi64(dst.add(40) as *mut i64, c5);
    _mm512_storeu_epi64(dst.add(48) as *mut i64, c6);
    _mm512_storeu_epi64(dst.add(56) as *mut i64, c7);
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
#[inline(always)]
unsafe fn transpose8x8_u64(src: *const u64, dst: *mut u64) {
    for r in 0..8 {
        for c in 0..8 {
            *dst.add(c * 8 + r) = *src.add(r * 8 + c);
        }
    }
}

/// Relayout A-interleaved (N1 x N2) -> B-interleaved (N2 x N1): both the source
/// and destination 8x8 tiles are contiguous 64-u64 spans, so the pass is pure
/// tile transposes per limb plane.
fn relayout_interleaved(a: &Planes, b: &mut Planes, n1: usize, n2: usize) {
    for i1b in (0..n1).step_by(8) {
        for i2b in (0..n2).step_by(8) {
            let src = ib_off(i1b, i2b, n2);
            let dst = ib_off(i2b, i1b, n1);
            unsafe {
                transpose8x8_u64(a.l0.as_ptr().add(src), b.l0.as_mut_ptr().add(dst));
                transpose8x8_u64(a.l1.as_ptr().add(src), b.l1.as_mut_ptr().add(dst));
                transpose8x8_u64(a.l2.as_ptr().add(src), b.l2.as_mut_ptr().add(dst));
            }
        }
    }
}

/// Portable scalar kernel (one `Fp52` per lane).
pub struct ScalarK;
impl Kernel8 for ScalarK {
    type V = [Fp52; 8];
    unsafe fn load(l0: *const u64, l1: *const u64, l2: *const u64) -> Self::V {
        core::array::from_fn(|l| [*l0.add(l), *l1.add(l), *l2.add(l)])
    }
    unsafe fn store(v: Self::V, l0: *mut u64, l1: *mut u64, l2: *mut u64) {
        #[expect(
            clippy::needless_range_loop,
            reason = "index arithmetic / parallel multi-array indexing in a hot kernel; iterator form obscures the chunk offsets"
        )]
        for l in 0..8 {
            *l0.add(l) = v[l][0];
            *l1.add(l) = v[l][1];
            *l2.add(l) = v[l][2];
        }
    }
    unsafe fn add(a: Self::V, b: Self::V) -> Self::V {
        core::array::from_fn(|l| add52(&a[l], &b[l]))
    }
    unsafe fn sub(a: Self::V, b: Self::V) -> Self::V {
        core::array::from_fn(|l| sub52(&a[l], &b[l]))
    }
    unsafe fn mul_broadcast(a: Self::V, s: &Fp52) -> Self::V {
        core::array::from_fn(|l| mont52_mul(&a[l], s))
    }
    unsafe fn mul_lanes(a: Self::V, b: Self::V) -> Self::V {
        core::array::from_fn(|l| mont52_mul(&a[l], &b[l]))
    }
    unsafe fn splat(s: &Fp52) -> Self::V {
        [*s; 8]
    }
}

/// AVX-512 IFMA kernel.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
pub struct IfmaK;
#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
impl Kernel8 for IfmaK {
    type V = [core::arch::x86_64::__m512i; 3];
    unsafe fn load(l0: *const u64, l1: *const u64, l2: *const u64) -> Self::V {
        simd::load3(l0, l1, l2)
    }
    unsafe fn store(v: Self::V, l0: *mut u64, l1: *mut u64, l2: *mut u64) {
        simd::store3(v, l0, l1, l2)
    }
    unsafe fn add(a: Self::V, b: Self::V) -> Self::V {
        simd::add8(a, b)
    }
    unsafe fn sub(a: Self::V, b: Self::V) -> Self::V {
        simd::sub8(a, b)
    }
    unsafe fn mul_broadcast(a: Self::V, s: &Fp52) -> Self::V {
        simd::mul_by_scalar8(a, s)
    }
    unsafe fn mul_lanes(a: Self::V, b: Self::V) -> Self::V {
        simd::mul8(a, b)
    }
    unsafe fn splat(s: &Fp52) -> Self::V {
        use core::arch::x86_64::*;
        [
            _mm512_set1_epi64(s[0] as i64),
            _mm512_set1_epi64(s[1] as i64),
            _mm512_set1_epi64(s[2] as i64),
        ]
    }
    unsafe fn load8_split(ptr: *const u128) -> Self::V {
        simd::load8_u128_split(ptr)
    }
    unsafe fn store8_combine(v: Self::V, ptr: *mut u128) {
        simd::store8_u128_combine(v, ptr)
    }
}

/// Precomputed outer-twiddle table for the six-step transform: `wrow[i1] =
/// ω_N^{i1}` in the 2^52 Montgomery domain, stored as limb planes so a block's
/// 8 per-row multipliers are one vector load.
pub struct SixStepTables {
    pub wrow_l0: Vec<u64>,
    pub wrow_l1: Vec<u64>,
    pub wrow_l2: Vec<u64>,
    pub n1: usize,
    pub n2: usize,
}

pub fn build_six_step_tables(log_n: u32) -> SixStepTables {
    let log_n2 = log_n / 2;
    let log_n1 = log_n - log_n2;
    let n1 = 1usize << log_n1;
    let n2 = 1usize << log_n2;
    let omega = fft::domain_generator_for_size::<Proth120>(1u64 << log_n);
    let mut cur = Proth120::ONE;
    let mut l0 = Vec::with_capacity(n1);
    let mut l1 = Vec::with_capacity(n1);
    let mut l2 = Vec::with_capacity(n1);
    for _ in 0..n1 {
        let l = to_mont52(cur.to_u128());
        l0.push(l[0]);
        l1.push(l[1]);
        l2.push(l[2]);
        cur.mul_assign(&omega);
    }
    SixStepTables {
        wrow_l0: l0,
        wrow_l1: l1,
        wrow_l2: l2,
        n1,
        n2,
    }
}

/// Interleaved-block offset: element `col` of `row` in an `R x C` matrix whose
/// rows are grouped in 8s.
#[inline(always)]
fn ib_off(row: usize, col: usize, cols: usize) -> usize {
    (row / 8) * (cols * 8) + col * 8 + (row % 8)
}

/// In-place NTT of ONE interleaved 8-row block (`len` blocks of 8 lanes per
/// plane slice), all stages vectorized, GS butterflies matching the scalar
/// reference. `tw52` is the (bit-reversed, nested-prefix) twiddle table.
unsafe fn ntt_block8<K: Kernel8>(
    l0: *mut u64,
    l1: *mut u64,
    l2: *mut u64,
    log_len: u32,
    tw52: &[Fp52],
) {
    let len = 1usize << log_len;
    let mut ppg = 1usize;
    let mut num_groups = len / 2;
    while num_groups > 1 {
        #[expect(
            clippy::needless_range_loop,
            reason = "index arithmetic / parallel multi-array indexing in a hot kernel; iterator form obscures the chunk offsets"
        )]
        for k in 0..num_groups {
            let s = &tw52[k];
            let base = k * ppg * 2;
            for j in base..base + ppg {
                let o_u = j * 8;
                let o_v = (j + ppg) * 8;
                let u = K::load(l0.add(o_u), l1.add(o_u), l2.add(o_u));
                let v = K::load(l0.add(o_v), l1.add(o_v), l2.add(o_v));
                let a = K::add(u, v);
                let b = K::mul_broadcast(K::sub(u, v), s);
                K::store(a, l0.add(o_u), l1.add(o_u), l2.add(o_u));
                K::store(b, l0.add(o_v), l1.add(o_v), l2.add(o_v));
            }
        }
        ppg *= 2;
        num_groups /= 2;
    }
    let half = len / 2;
    for j in 0..half {
        let o_u = j * 8;
        let o_v = (j + half) * 8;
        let u = K::load(l0.add(o_u), l1.add(o_u), l2.add(o_u));
        let v = K::load(l0.add(o_v), l1.add(o_v), l2.add(o_v));
        let a = K::add(u, v);
        let b = K::sub(u, v);
        K::store(a, l0.add(o_u), l1.add(o_u), l2.add(o_u));
        K::store(b, l0.add(o_v), l1.add(o_v), l2.add(o_v));
    }
}

/// Bit-reverse the block order of an interleaved 8-row slice (each element is
/// a 64-byte lane group, so this swaps whole groups).
fn bitrev_blocks(plane: &mut [u64], log_len: u32) {
    let chunks: &mut [[u64; 8]] = plane.as_chunks_mut::<8>().0;
    debug_assert_eq!(chunks.len(), 1usize << log_len);
    fft::bitreverse_enumeration_inplace(chunks);
}

/// Six-step natural→natural NTT over limb planes with 8-rows-in-lockstep
/// blocks. `x` is read-only (natural planar order); returns natural planar
/// output. Generic over the lane kernel.
pub fn six_step_ntt<K: Kernel8>(
    x: &Planes,
    log_n: u32,
    tw52: &[Fp52],
    tables: &SixStepTables,
) -> Planes {
    let n = x.l0.len();
    assert_eq!(n, 1usize << log_n);
    let n1 = tables.n1;
    let n2 = tables.n2;
    assert_eq!(n1 * n2, n);
    let log_n1 = n1.trailing_zeros();
    let log_n2 = n2.trailing_zeros();

    let mut a = Planes {
        l0: vec![0; n],
        l1: vec![0; n],
        l2: vec![0; n],
    };
    let mut b = Planes {
        l0: vec![0; n],
        l1: vec![0; n],
        l2: vec![0; n],
    };

    // Pass 1: gather x (viewed as N2 x N1: x[i2*N1 + i1]) into A-interleaved
    // N1 x N2. For a fixed i1 block, the 8 source lanes of one (i2) group are
    // contiguous in x.
    const TILE: usize = 32;
    for i1b in (0..n1).step_by(8) {
        for i2t in (0..n2).step_by(TILE) {
            let i2_end = core::cmp::min(i2t + TILE, n2);
            for i2 in i2t..i2_end {
                let src = i2 * n1 + i1b;
                let dst = ib_off(i1b, i2, n2);
                a.l0[dst..dst + 8].copy_from_slice(&x.l0[src..src + 8]);
                a.l1[dst..dst + 8].copy_from_slice(&x.l1[src..src + 8]);
                a.l2[dst..dst + 8].copy_from_slice(&x.l2[src..src + 8]);
            }
        }
    }

    // Phase A: per 8-row block — bitrev blocks, NTT(N2), outer twiddle
    // correction row[k2] *= ω^{i1·k2} (per-lane multiplier ω^{i1}).
    for i1b in (0..n1).step_by(8) {
        let base = ib_off(i1b, 0, n2);
        let sl0 = &mut a.l0[base..base + n2 * 8];
        let sl1 = &mut a.l1[base..base + n2 * 8];
        let sl2 = &mut a.l2[base..base + n2 * 8];
        bitrev_blocks(sl0, log_n2);
        bitrev_blocks(sl1, log_n2);
        bitrev_blocks(sl2, log_n2);
        unsafe {
            ntt_block8::<K>(
                sl0.as_mut_ptr(),
                sl1.as_mut_ptr(),
                sl2.as_mut_ptr(),
                log_n2,
                &tw52[..(n2 / 2).max(1)],
            );
            // per-lane row multipliers
            let w = K::load(
                tables.wrow_l0.as_ptr().add(i1b),
                tables.wrow_l1.as_ptr().add(i1b),
                tables.wrow_l2.as_ptr().add(i1b),
            );
            let mut cur = w;
            for k2 in 1..n2 {
                let o = k2 * 8;
                let d = K::load(
                    sl0.as_ptr().add(o),
                    sl1.as_ptr().add(o),
                    sl2.as_ptr().add(o),
                );
                let d = K::mul_lanes(d, cur);
                K::store(
                    d,
                    sl0.as_mut_ptr().add(o),
                    sl1.as_mut_ptr().add(o),
                    sl2.as_mut_ptr().add(o),
                );
                cur = K::mul_lanes(cur, w);
            }
        }
    }

    // Pass 2: relayout A-interleaved (N1 x N2) -> B-interleaved (N2 x N1) via
    // 8x8 tile transposes (in-register on AVX-512).
    relayout_interleaved(&a, &mut b, n1, n2);

    // Phase B: per 8-row block over k2 — bitrev + NTT(N1), no twiddles.
    for k2b in (0..n2).step_by(8) {
        let base = ib_off(k2b, 0, n1);
        let sl0 = &mut b.l0[base..base + n1 * 8];
        let sl1 = &mut b.l1[base..base + n1 * 8];
        let sl2 = &mut b.l2[base..base + n1 * 8];
        bitrev_blocks(sl0, log_n1);
        bitrev_blocks(sl1, log_n1);
        bitrev_blocks(sl2, log_n1);
        unsafe {
            ntt_block8::<K>(
                sl0.as_mut_ptr(),
                sl1.as_mut_ptr(),
                sl2.as_mut_ptr(),
                log_n1,
                &tw52[..(n1 / 2).max(1)],
            );
        }
    }

    // Pass 3: scatter B-interleaved (rows k2, cols k1) into natural planar
    // y[k1*N2 + k2]: one 8-lane group (fixed k1, k2 block) lands contiguously.
    let mut out = a; // reuse buffer
    for k2b in (0..n2).step_by(8) {
        for k1t in (0..n1).step_by(TILE) {
            let k1_end = core::cmp::min(k1t + TILE, n1);
            for k1 in k1t..k1_end {
                let src = ib_off(k2b, k1, n1);
                let dst = k1 * n2 + k2b;
                out.l0[dst..dst + 8].copy_from_slice(&b.l0[src..src + 8]);
                out.l1[dst..dst + 8].copy_from_slice(&b.l1[src..src + 8]);
                out.l2[dst..dst + 8].copy_from_slice(&b.l2[src..src + 8]);
            }
        }
    }
    out
}

/// Validate the six-step transform (chosen kernel) against the scalar
/// reference NTT: natural input, natural output.
pub fn self_check_six_step<K: Kernel8>(log_n: u32) {
    use std::alloc::Global;
    let n = 1usize << log_n;
    let mut rng = rand::rng();
    let input: Vec<Proth120> = (0..n).map(|_| Proth120::random_element(&mut rng)).collect();
    let tw: Vec<Proth120, Global> =
        fft::precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);

    // reference: natural -> natural = bitrev + GS NTT
    let mut reference = input.clone();
    fft::bitreverse_enumeration_inplace(&mut reference);
    fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut reference, log_n, &tw[..n / 2]);
    let expected: Vec<u128> = reference.iter().map(|x| x.to_u128()).collect();

    let tw52 = convert_twiddles(&tw[..n / 2]);
    let tables = build_six_step_tables(log_n);
    let planes = Planes::from_proth(&input);
    let got = six_step_ntt::<K>(&planes, log_n, &tw52, &tables).to_naturals();
    assert_eq!(got, expected, "six-step NTT diverged at log_n={log_n}");
}

// ---------------------------------------------------------------------------
// Lazy-reduction kernels: values kept in [0, 2p), Montgomery multiplication
// SKIPS the final conditional subtraction entirely.
//
// Bound analysis (R = 2^156, p < 2^123): with inputs < 2p the CIOS output is
// < 4p^2/R + p = 2^91.6 + p < 2p — the invariant is self-sustaining with NO
// correction in the multiply. Butterfly adds produce < 4p and are brought back
// under 2p with a single conditional subtract of 2p; subtraction uses
// a + (2p - b). Limbs stay canonical 52-bit (a must: vpmadd52 reads only the
// low 52 bits), only the VALUE is lazy. `canonicalize` (one cond-sub of p)
// runs once at the very end.
// ---------------------------------------------------------------------------

/// `2p` in base-2^52 limbs.
pub const TP0: u64 = 2;
pub const TP1: u64 = 0;
pub const TP2: u64 = 14u64 << 16;

/// Lazy scalar Montgomery mul: inputs < 2p, output < 2p, no final cond-sub.
#[inline(always)]
pub fn mont52_mul_lazy(a: &Fp52, b: &Fp52) -> Fp52 {
    const M: u128 = MASK52 as u128;
    let c = P2 as u128;

    let (mut t0, mut t1, mut t2, mut t3) = (0u128, 0u128, 0u128, 0u128);
    let mut i = 0;
    while i < 3 {
        let bi = b[i] as u128;
        let p = (a[0] as u128) * bi;
        t0 += p & M;
        t1 += p >> 52;
        let p = (a[1] as u128) * bi;
        t1 += p & M;
        t2 += p >> 52;
        let p = (a[2] as u128) * bi;
        t2 += p & M;
        t3 += p >> 52;

        let m = ((1u128 << 52) - (t0 & M)) & M;
        let carry = (t0 + m) >> 52;
        let pm = m * c;
        t2 += pm & M;
        t3 += pm >> 52;
        t0 = t1 + carry;
        t1 = t2;
        t2 = t3;
        t3 = 0;
        i += 1;
    }
    t1 += t0 >> 52;
    t0 &= M;
    t2 += t1 >> 52;
    t1 &= M;
    [t0 as u64, t1 as u64, t2 as u64]
}

#[inline(always)]
fn cond_sub_2p_52(t: Fp52) -> Fp52 {
    let ge = t[2] > TP2 || (t[2] == TP2 && (t[1] > 0 || t[0] >= TP0));
    if ge {
        let b0 = (t[0] < TP0) as u64;
        let r0 = (t[0].wrapping_sub(TP0)) & MASK52;
        let b1 = (t[1] < b0) as u64;
        let r1 = (t[1].wrapping_sub(b0)) & MASK52;
        [r0, r1, t[2] - TP2 - b1]
    } else {
        t
    }
}

#[inline(always)]
fn add52_lazy(a: &Fp52, b: &Fp52) -> Fp52 {
    let mut t0 = a[0] + b[0];
    let mut t1 = a[1] + b[1] + (t0 >> 52);
    t0 &= MASK52;
    let t2 = a[2] + b[2] + (t1 >> 52);
    t1 &= MASK52;
    cond_sub_2p_52([t0, t1, t2])
}

#[inline(always)]
fn sub52_lazy(a: &Fp52, b: &Fp52) -> Fp52 {
    // a + (2p - b), b < 2p
    let b0 = (TP0 < b[0]) as u64;
    let d0 = (TP0.wrapping_sub(b[0])) & MASK52;
    let bb = b[1] + b0;
    let b1 = (TP1 < bb) as u64;
    let d1 = (TP1.wrapping_sub(bb)) & MASK52;
    let d2 = TP2 - b[2] - b1;
    add52_lazy(a, &[d0, d1, d2])
}

/// One conditional subtract of p brings a lazy (< 2p) value to canonical.
#[inline(always)]
pub fn canonicalize52(t: Fp52) -> Fp52 {
    let ge = t[2] > P2 || (t[2] == P2 && (t[1] > 0 || t[0] >= P0));
    if ge {
        let b0 = (t[0] < P0) as u64;
        let r0 = (t[0].wrapping_sub(P0)) & MASK52;
        let b1 = (t[1] < b0) as u64;
        let r1 = (t[1].wrapping_sub(b0)) & MASK52;
        [r0, r1, t[2] - P2 - b1]
    } else {
        t
    }
}

/// Portable lazy kernel.
pub struct ScalarLazyK;
impl Kernel8 for ScalarLazyK {
    type V = [Fp52; 8];
    unsafe fn load(l0: *const u64, l1: *const u64, l2: *const u64) -> Self::V {
        core::array::from_fn(|l| [*l0.add(l), *l1.add(l), *l2.add(l)])
    }
    unsafe fn store(v: Self::V, l0: *mut u64, l1: *mut u64, l2: *mut u64) {
        #[expect(
            clippy::needless_range_loop,
            reason = "index arithmetic / parallel multi-array indexing in a hot kernel; iterator form obscures the chunk offsets"
        )]
        for l in 0..8 {
            *l0.add(l) = v[l][0];
            *l1.add(l) = v[l][1];
            *l2.add(l) = v[l][2];
        }
    }
    unsafe fn add(a: Self::V, b: Self::V) -> Self::V {
        core::array::from_fn(|l| add52_lazy(&a[l], &b[l]))
    }
    unsafe fn sub(a: Self::V, b: Self::V) -> Self::V {
        core::array::from_fn(|l| sub52_lazy(&a[l], &b[l]))
    }
    unsafe fn mul_broadcast(a: Self::V, s: &Fp52) -> Self::V {
        core::array::from_fn(|l| mont52_mul_lazy(&a[l], s))
    }
    unsafe fn mul_lanes(a: Self::V, b: Self::V) -> Self::V {
        core::array::from_fn(|l| mont52_mul_lazy(&a[l], &b[l]))
    }
    unsafe fn splat(s: &Fp52) -> Self::V {
        [*s; 8]
    }
}

/// Canonicalization hook (identity for strict kernels).
pub trait Canonicalize: Kernel8 {
    unsafe fn canonicalize(v: Self::V) -> Self::V;
}
impl Canonicalize for ScalarK {
    unsafe fn canonicalize(v: Self::V) -> Self::V {
        v
    }
}
impl Canonicalize for ScalarLazyK {
    unsafe fn canonicalize(v: Self::V) -> Self::V {
        core::array::from_fn(|l| canonicalize52(v[l]))
    }
}

/// AVX-512 IFMA lazy kernel: mul with NO conditional subtraction; add/sub
/// reduce against 2p with one masked pass.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
pub struct IfmaLazyK;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
pub mod simd_lazy {
    use super::*;
    use core::arch::x86_64::*;

    #[inline(always)]
    unsafe fn mask52() -> __m512i {
        _mm512_set1_epi64(MASK52 as i64)
    }

    /// Core CIOS in the 2^52 domain WITHOUT the final conditional subtract:
    /// inputs < 2p (canonical 52-bit limbs), output < 2p.
    #[inline(always)]
    pub unsafe fn mul8_core(a: [__m512i; 3], b: impl Fn(usize) -> __m512i) -> [__m512i; 3] {
        let zero = _mm512_setzero_si512();
        let m52 = mask52();
        let cvec = _mm512_set1_epi64(P2 as i64);

        let mut t0 = zero;
        let mut t1 = zero;
        let mut t2 = zero;
        let mut t3 = zero;

        let mut i = 0;
        while i < 3 {
            let bi = b(i);
            t0 = _mm512_madd52lo_epu64(t0, a[0], bi);
            t1 = _mm512_madd52hi_epu64(t1, a[0], bi);
            t1 = _mm512_madd52lo_epu64(t1, a[1], bi);
            t2 = _mm512_madd52hi_epu64(t2, a[1], bi);
            t2 = _mm512_madd52lo_epu64(t2, a[2], bi);
            t3 = _mm512_madd52hi_epu64(t3, a[2], bi);

            let m = _mm512_and_si512(_mm512_sub_epi64(zero, t0), m52);
            let carry = _mm512_srli_epi64::<52>(_mm512_add_epi64(t0, m));
            t2 = _mm512_madd52lo_epu64(t2, m, cvec);
            t3 = _mm512_madd52hi_epu64(t3, m, cvec);
            t0 = _mm512_add_epi64(t1, carry);
            t1 = t2;
            t2 = t3;
            t3 = zero;
            i += 1;
        }
        t1 = _mm512_add_epi64(t1, _mm512_srli_epi64::<52>(t0));
        t0 = _mm512_and_si512(t0, m52);
        t2 = _mm512_add_epi64(t2, _mm512_srli_epi64::<52>(t1));
        t1 = _mm512_and_si512(t1, m52);
        [t0, t1, t2]
    }

    /// Subtract `q` (given as limbs) from lanes where value >= q.
    #[inline(always)]
    pub unsafe fn cond_sub_q(t: [__m512i; 3], q: &Fp52) -> [__m512i; 3] {
        let m52 = mask52();
        let q0 = _mm512_set1_epi64(q[0] as i64);
        let q2 = _mm512_set1_epi64(q[2] as i64);

        let b0 = _mm512_cmplt_epu64_mask(t[0], q0);
        let s0 = _mm512_and_si512(_mm512_sub_epi64(t[0], q0), m52);
        let b0v = _mm512_maskz_set1_epi64(b0, 1);
        // q1 == 0 for both p and 2p
        let b1 = _mm512_cmplt_epu64_mask(t[1], b0v);
        let s1 = _mm512_and_si512(_mm512_sub_epi64(t[1], b0v), m52);
        let b1v = _mm512_maskz_set1_epi64(b1, 1);
        let sub2 = _mm512_add_epi64(q2, b1v);
        let keep = _mm512_cmplt_epu64_mask(t[2], sub2);
        let s2 = _mm512_sub_epi64(t[2], sub2);
        [
            _mm512_mask_blend_epi64(keep, s0, t[0]),
            _mm512_mask_blend_epi64(keep, s1, t[1]),
            _mm512_mask_blend_epi64(keep, s2, t[2]),
        ]
    }

    #[inline(always)]
    pub unsafe fn add8_lazy(a: [__m512i; 3], b: [__m512i; 3]) -> [__m512i; 3] {
        let m52 = mask52();
        let mut t0 = _mm512_add_epi64(a[0], b[0]);
        let mut t1 = _mm512_add_epi64(a[1], b[1]);
        let mut t2 = _mm512_add_epi64(a[2], b[2]);
        t1 = _mm512_add_epi64(t1, _mm512_srli_epi64::<52>(t0));
        t0 = _mm512_and_si512(t0, m52);
        t2 = _mm512_add_epi64(t2, _mm512_srli_epi64::<52>(t1));
        t1 = _mm512_and_si512(t1, m52);
        cond_sub_q([t0, t1, t2], &[TP0, TP1, TP2])
    }

    #[inline(always)]
    pub unsafe fn sub8_lazy(a: [__m512i; 3], b: [__m512i; 3]) -> [__m512i; 3] {
        // a + (2p - b), b < 2p
        let m52 = mask52();
        let two = _mm512_set1_epi64(TP0 as i64);
        let c2 = _mm512_set1_epi64(TP2 as i64);
        let zero = _mm512_setzero_si512();

        let bb0 = _mm512_cmplt_epu64_mask(two, b[0]);
        let d0 = _mm512_and_si512(_mm512_sub_epi64(two, b[0]), m52);
        let b0v = _mm512_maskz_set1_epi64(bb0, 1);
        let bplus = _mm512_add_epi64(b[1], b0v);
        let bb1 = _mm512_cmplt_epu64_mask(zero, bplus);
        let d1 = _mm512_and_si512(_mm512_sub_epi64(zero, bplus), m52);
        let b1v = _mm512_maskz_set1_epi64(bb1, 1);
        let d2 = _mm512_sub_epi64(c2, _mm512_add_epi64(b[2], b1v));

        add8_lazy(a, [d0, d1, d2])
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
impl Kernel8 for IfmaLazyK {
    type V = [core::arch::x86_64::__m512i; 3];
    unsafe fn load(l0: *const u64, l1: *const u64, l2: *const u64) -> Self::V {
        simd::load3(l0, l1, l2)
    }
    unsafe fn store(v: Self::V, l0: *mut u64, l1: *mut u64, l2: *mut u64) {
        simd::store3(v, l0, l1, l2)
    }
    unsafe fn add(a: Self::V, b: Self::V) -> Self::V {
        simd_lazy::add8_lazy(a, b)
    }
    unsafe fn sub(a: Self::V, b: Self::V) -> Self::V {
        simd_lazy::sub8_lazy(a, b)
    }
    unsafe fn mul_broadcast(a: Self::V, s: &Fp52) -> Self::V {
        use core::arch::x86_64::*;
        let s0 = _mm512_set1_epi64(s[0] as i64);
        let s1 = _mm512_set1_epi64(s[1] as i64);
        let s2 = _mm512_set1_epi64(s[2] as i64);
        simd_lazy::mul8_core(a, move |i| [s0, s1, s2][i])
    }
    unsafe fn mul_lanes(a: Self::V, b: Self::V) -> Self::V {
        simd_lazy::mul8_core(a, move |i| b[i])
    }
    unsafe fn splat(s: &Fp52) -> Self::V {
        use core::arch::x86_64::*;
        [
            _mm512_set1_epi64(s[0] as i64),
            _mm512_set1_epi64(s[1] as i64),
            _mm512_set1_epi64(s[2] as i64),
        ]
    }
    unsafe fn load8_split(ptr: *const u128) -> Self::V {
        simd::load8_u128_split(ptr)
    }
    unsafe fn store8_combine(v: Self::V, ptr: *mut u128) {
        simd::store8_u128_combine(v, ptr)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
impl Canonicalize for IfmaK {
    unsafe fn canonicalize(v: Self::V) -> Self::V {
        v
    }
}
#[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
impl Canonicalize for IfmaLazyK {
    unsafe fn canonicalize(v: Self::V) -> Self::V {
        simd_lazy::cond_sub_q(v, &[P0, P1, P2])
    }
}

// ---------------------------------------------------------------------------
// Full LDE-coset task via six-step: standard-representation (u128 Montgomery
// R=2^128) monomials in -> standard-representation coset evaluations out, with
// the coset-offset scaling AND both domain conversions fused into the two
// boundary relayout passes.
//
//   in:  x_stored = value·2^128.  Gather multiplier c_in = offset^i · 2^184,
//        because mont52_mul(x_stored, c_in) = value·offset^i·2^156 — exactly
//        the scaled coefficient in the 2^52 Montgomery domain.
//        (offset^i = offset^{i1} · (offset^{N1})^{i2} — per-lane base vector
//        times a broadcast running factor.)
//   out: multiplier c_out = 2^128 mod p turns y52 = value·2^156 back into
//        value·2^128 (one vector mul), then limbs recombine into u128.
// ---------------------------------------------------------------------------

/// Per-stage wall times of one six-step LDE task, seconds.
#[derive(Default, Clone, Copy, Debug)]
pub struct StageTimes {
    pub gather_scale_in: f64,
    pub phase_a_ntt: f64,
    pub twiddle_correction: f64,
    pub relayout: f64,
    pub phase_b_ntt: f64,
    pub scatter_out: f64,
}

pub fn lde_coset_six_step<K: Canonicalize>(
    input: &[Proth120],
    offset: Proth120,
    log_n: u32,
    tw52: &[Fp52],
    tables: &SixStepTables,
    mut stages: Option<&mut StageTimes>,
) -> Vec<Proth120> {
    use std::time::Instant;
    let n = input.len();
    assert_eq!(n, 1usize << log_n);
    let n1 = tables.n1;
    let n2 = tables.n2;
    let log_n1 = n1.trailing_zeros();
    let log_n2 = n2.trailing_zeros();

    // gather multipliers: c_base[i1] = offset^{i1} · 2^184 (canonical), planes.
    let p2_184 = Proth120::new(pow2_mod(184));
    let mut c0 = Vec::with_capacity(n1);
    let mut c1 = Vec::with_capacity(n1);
    let mut c2 = Vec::with_capacity(n1);
    let mut cur = p2_184;
    for _ in 0..n1 {
        let l = limbs_of(cur.to_u128());
        c0.push(l[0]);
        c1.push(l[1]);
        c2.push(l[2]);
        cur.mul_assign(&offset);
    }
    // broadcast running step: mont52(offset^{N1})
    let mut off_n1 = offset;
    for _ in 0..log_n1 {
        let t = off_n1;
        off_n1.mul_assign(&t);
    }
    let step52 = to_mont52(off_n1.to_u128());

    let mut a = Planes {
        l0: vec![0; n],
        l1: vec![0; n],
        l2: vec![0; n],
    };

    // Pass 1: gather + domain conversion + coset scaling. The u128 -> limb
    // split happens IN REGISTERS (`load8_split`); `Proth120` is
    // `repr(transparent)` over `u128`, so the input reads as raw values.
    const _: () = assert!(core::mem::size_of::<Proth120>() == 16);
    let input_raw = input.as_ptr() as *const u128;
    let t0 = Instant::now();
    for i1b in (0..n1).step_by(8) {
        unsafe {
            let mut cvec = K::load(
                c0.as_ptr().add(i1b),
                c1.as_ptr().add(i1b),
                c2.as_ptr().add(i1b),
            );
            for i2 in 0..n2 {
                let src = i2 * n1 + i1b;
                let x = K::load8_split(input_raw.add(src));
                let d = K::mul_lanes(x, cvec);
                let dst = ib_off(i1b, i2, n2);
                K::store(
                    d,
                    a.l0.as_mut_ptr().add(dst),
                    a.l1.as_mut_ptr().add(dst),
                    a.l2.as_mut_ptr().add(dst),
                );
                cvec = K::mul_broadcast(cvec, &step52);
            }
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.gather_scale_in = t0.elapsed().as_secs_f64();
    }

    // Phase A rows + outer twiddle correction.
    let mut t_ntt = 0.0f64;
    let mut t_tw = 0.0f64;
    for i1b in (0..n1).step_by(8) {
        let base = ib_off(i1b, 0, n2);
        let sl0 = &mut a.l0[base..base + n2 * 8];
        let sl1 = &mut a.l1[base..base + n2 * 8];
        let sl2 = &mut a.l2[base..base + n2 * 8];
        let t1 = Instant::now();
        bitrev_blocks(sl0, log_n2);
        bitrev_blocks(sl1, log_n2);
        bitrev_blocks(sl2, log_n2);
        unsafe {
            ntt_block8::<K>(
                sl0.as_mut_ptr(),
                sl1.as_mut_ptr(),
                sl2.as_mut_ptr(),
                log_n2,
                &tw52[..(n2 / 2).max(1)],
            );
        }
        let t2 = Instant::now();
        t_ntt += (t2 - t1).as_secs_f64();
        unsafe {
            let w = K::load(
                tables.wrow_l0.as_ptr().add(i1b),
                tables.wrow_l1.as_ptr().add(i1b),
                tables.wrow_l2.as_ptr().add(i1b),
            );
            let mut curw = w;
            for k2 in 1..n2 {
                let o = k2 * 8;
                let d = K::load(
                    sl0.as_ptr().add(o),
                    sl1.as_ptr().add(o),
                    sl2.as_ptr().add(o),
                );
                let d = K::mul_lanes(d, curw);
                K::store(
                    d,
                    sl0.as_mut_ptr().add(o),
                    sl1.as_mut_ptr().add(o),
                    sl2.as_mut_ptr().add(o),
                );
                curw = K::mul_lanes(curw, w);
            }
        }
        t_tw += t2.elapsed().as_secs_f64();
    }
    if let Some(s) = stages.as_deref_mut() {
        s.phase_a_ntt = t_ntt;
        s.twiddle_correction = t_tw;
    }

    // Pass 2: relayout A (N1 x N2) -> B (N2 x N1) via in-register 8x8 tile
    // transposes. `b` is allocated only now and `a` is freed right after,
    // keeping the task's peak at ~2 buffers.
    let t0 = Instant::now();
    let mut b = Planes {
        l0: vec![0; n],
        l1: vec![0; n],
        l2: vec![0; n],
    };
    relayout_interleaved(&a, &mut b, n1, n2);
    drop(a);
    if let Some(s) = stages.as_deref_mut() {
        s.relayout = t0.elapsed().as_secs_f64();
    }

    // Phase B rows.
    let t0 = Instant::now();
    for k2b in (0..n2).step_by(8) {
        let base = ib_off(k2b, 0, n1);
        let sl0 = &mut b.l0[base..base + n1 * 8];
        let sl1 = &mut b.l1[base..base + n1 * 8];
        let sl2 = &mut b.l2[base..base + n1 * 8];
        bitrev_blocks(sl0, log_n1);
        bitrev_blocks(sl1, log_n1);
        bitrev_blocks(sl2, log_n1);
        unsafe {
            ntt_block8::<K>(
                sl0.as_mut_ptr(),
                sl1.as_mut_ptr(),
                sl2.as_mut_ptr(),
                log_n1,
                &tw52[..(n1 / 2).max(1)],
            );
        }
    }
    if let Some(s) = stages.as_deref_mut() {
        s.phase_b_ntt = t0.elapsed().as_secs_f64();
    }

    // Pass 3: scatter to natural order + convert back to the standard
    // representation (× 2^128 mod p) + canonicalize.
    let t0 = Instant::now();
    let c_out = limbs_of(pow2_mod(128));
    let mut out: Vec<Proth120> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        out.set_len(n)
    };
    let out_raw = out.as_mut_ptr() as *mut u128;
    for k2b in (0..n2).step_by(8) {
        for k1 in 0..n1 {
            unsafe {
                let src = ib_off(k2b, k1, n1);
                let y = K::load(
                    b.l0.as_ptr().add(src),
                    b.l1.as_ptr().add(src),
                    b.l2.as_ptr().add(src),
                );
                let y = K::mul_broadcast(y, &c_out);
                let y = K::canonicalize(y);
                // limbs -> u128 recombination happens in registers.
                K::store8_combine(y, out_raw.add(k1 * n2 + k2b));
            }
        }
    }
    if let Some(s) = stages {
        s.scatter_out = t0.elapsed().as_secs_f64();
    }

    out
}

/// The six-step LDE task must reproduce the prover's coset pipeline exactly.
pub fn self_check_lde<K: Canonicalize>(log_n: u32) {
    use std::alloc::Global;
    let n = 1usize << log_n;
    let mut rng = rand::rng();
    let input: Vec<Proth120> = (0..n).map(|_| Proth120::random_element(&mut rng)).collect();
    let tw: Vec<Proth120, Global> =
        fft::precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);
    let offset = fft::domain_generator_for_size::<Proth120>((n * 8) as u64);

    let expected = fft::lde_coset_natural_seq_fused(&input, offset, &tw);

    let tw52 = convert_twiddles(&tw[..n / 2]);
    let tables = build_six_step_tables(log_n);
    let got = lde_coset_six_step::<K>(&input, offset, log_n, &tw52, &tables, None);
    assert_eq!(got, expected, "six-step LDE task diverged at log_n={log_n}");
}
