// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.

use super::*;
use crate::field::BaseField;
use crate::field::Field;
use crate::field::PrimeField;
use crate::field_like::FieldLikeVectorized;
use crate::Mersenne31Field;
use core::arch::x86_64::{self, __m512i, __mmask16};
use core::mem::transmute;
use core::ops::{Add, Mul, Sub};

pub const WIDTH: usize = 16;
const P: __m512i = unsafe { transmute::<[u32; WIDTH], _>([0x7fffffff; WIDTH]) };
const EVENS: __mmask16 = 0b0101010101010101;
const ODDS: __mmask16 = 0b1010101010101010;
const EVENS4: __mmask16 = 0x0f0f;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(C, align(64))]
pub struct Mersenne31FieldVectorized(pub [Mersenne31Field; WIDTH]);

impl core::fmt::Display for Mersenne31FieldVectorized {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

// use core::Rand;
use rand::Rng;
impl Rand for Mersenne31FieldVectorized {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Mersenne31FieldVectorized {
        let t = [(); WIDTH].map(|_| {
            Mersenne31Field::from_u64_unchecked(rng.gen_range(0..Mersenne31Field::CHARACTERISTICS))
        });
        Mersenne31FieldVectorized(t)
    }
}

impl Mersenne31FieldVectorized {
    #[inline]
    #[must_use]
    pub fn to_vector(self) -> __m512i {
        unsafe { transmute(self) }
    }

    #[inline]
    #[must_use]
    pub unsafe fn from_vector(vector: __m512i) -> Self {
        transmute(vector)
    }

    #[inline]
    #[must_use]
    pub const fn broadcast(value: Mersenne31Field) -> Self {
        Self([value; WIDTH])
    }

    #[inline(always)]
    pub fn permute(&mut self, ix: &[u32; 16]) -> &mut Self {
        let ix = *ix;
        let ix: __m512i = unsafe { transmute(ix) };
        let r = unsafe { x86_64::_mm512_permutexvar_epi32(ix, self.to_vector()) };

        unsafe {
            *self = Self::from_vector(r);
        }
        self
    }

    #[inline]
    pub fn interleave(&self, other: Self, block_len: usize) -> (Self, Self) {
        let (v0, v1) = (self.to_vector(), other.to_vector());
        let (res0, res1) = match block_len {
            1 => interleave1(v0, v1),
            // 2 => interleave2(v0, v1),
            4 => interleave4(v0, v1),
            // 8 => interleave8(v0, v1),
            16 => (v0, v1),
            _ => panic!("unsupported block_len"),
        };
        unsafe { (Self::from_vector(res0), Self::from_vector(res1)) }
    }

    #[inline]
    pub fn interleave_radix4(
        &self,
        b: Self,
        c: Self,
        d: Self,
        block_len: usize,
    ) -> (Self, Self, Self, Self) {
        let (v0, v1, v2, v3) = (
            self.to_vector(),
            b.to_vector(),
            c.to_vector(),
            d.to_vector(),
        );
        let (res0, res1, res2, res3) = match block_len {
            1 => interleave1_radix4(v0, v1, v2, v3),
            4 => interleave4_radix4(v0, v1, v2, v3),
            16 => (v0, v1, v2, v3),
            _ => panic!("unsupported block_len"),
        };
        unsafe {
            (
                Self::from_vector(res0),
                Self::from_vector(res1),
                Self::from_vector(res2),
                Self::from_vector(res3),
            )
        }
    }

    pub fn rotate<const N: i32>(&mut self) -> &mut Self {
        let r = unsafe { x86_64::_mm512_alignr_epi32(self.to_vector(), self.to_vector(), N) };
        unsafe {
            *self = Self::from_vector(r);
        }
        self
    }
}

#[inline]
#[must_use]
fn add(lhs: __m512i, rhs: __m512i) -> __m512i {
    unsafe {
        let t = x86_64::_mm512_add_epi32(lhs, rhs);
        let u = x86_64::_mm512_sub_epi32(t, P);
        x86_64::_mm512_min_epu32(t, u)
    }
}

#[inline]
#[must_use]
fn sub(lhs: __m512i, rhs: __m512i) -> __m512i {
    unsafe {
        let t = x86_64::_mm512_sub_epi32(lhs, rhs);
        let u = x86_64::_mm512_add_epi32(t, P);
        x86_64::_mm512_min_epu32(t, u)
    }
}

#[inline]
#[must_use]
fn movehdup_epi32(a: __m512i) -> __m512i {
    unsafe {
        x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(a)))
    }
}

#[inline]
#[must_use]
fn mask_movehdup_epi32(src: __m512i, k: __mmask16, a: __m512i) -> __m512i {
    unsafe {
        let src = x86_64::_mm512_castsi512_ps(src);
        let a = x86_64::_mm512_castsi512_ps(a);
        x86_64::_mm512_castps_si512(x86_64::_mm512_mask_movehdup_ps(src, k, a))
    }
}

#[inline]
#[must_use]
fn mask_moveldup_epi32(src: __m512i, k: __mmask16, a: __m512i) -> __m512i {
    unsafe {
        let src = x86_64::_mm512_castsi512_ps(src);
        let a = x86_64::_mm512_castsi512_ps(a);
        x86_64::_mm512_castps_si512(x86_64::_mm512_mask_moveldup_ps(src, k, a))
    }
}

#[inline]
#[must_use]
fn mul(lhs: __m512i, rhs: __m512i) -> __m512i {
    unsafe {
        let rhs_even = rhs;
        let lhs_even_dbl = x86_64::_mm512_add_epi32(lhs, lhs);
        let rhs_odd = movehdup_epi32(rhs);
        let lhs_odd_dbl = x86_64::_mm512_srli_epi64::<31>(lhs);
        let mul_odd_dbl = x86_64::_mm512_mul_epu32(lhs_odd_dbl, rhs_odd);
        let mul_even_dbl = x86_64::_mm512_mul_epu32(lhs_even_dbl, rhs_even);
        let mul_lo_dbl = mask_moveldup_epi32(mul_even_dbl, ODDS, mul_odd_dbl);
        let mul_hi = mask_movehdup_epi32(mul_odd_dbl, EVENS, mul_even_dbl);
        let mul_lo = x86_64::_mm512_srli_epi32::<1>(mul_lo_dbl);
        add(mul_lo, mul_hi)
    }
}

#[inline]
#[must_use]
pub fn mul_m31c_interleaved(a: __m512i, b: __m512i, x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    let ax_c0 = mask_moveldup_epi32(a, ODDS, x);
    let ax_c1 = mask_movehdup_epi32(x, EVENS, a);
    let by_c0 = mask_moveldup_epi32(b, ODDS, y);
    let by_c1 = mask_movehdup_epi32(y, EVENS, b);
    let v0 = mul(ax_c0, by_c0);
    let v1 = mul(ax_c1, by_c1);
    let ax_c0c1 = add(ax_c0, ax_c1);
    let by_c0c1 = add(by_c0, by_c1);
    let c1t0 = mul(ax_c0c1, by_c0c1);
    let c1v0 = sub(c1t0, v0);
    let c1v1 = sub(c1v0, v1);
    let v0v1 = sub(v0, v1);
    let ab = mask_moveldup_epi32(v0v1, ODDS, c1v1);
    let xy = mask_movehdup_epi32(c1v1, EVENS, v0v1);
    (ab, xy)
}

#[inline]
#[must_use]
pub fn mul_by_twiddle_m31c_interleaved(
    a: __m512i,
    b: __m512i,
    x: __m512i,
    y: __m512i,
) -> (__m512i, __m512i) {
    unsafe {
        let ax_c0 = mask_moveldup_epi32(a, ODDS, x);
        let ax_c1 = mask_movehdup_epi32(x, EVENS, a);
        let by_c0 = b;
        let by_c1 = y;
        // let v0 = mul(ax_c0, by_c0);
        // let v1 = mul(ax_c1, by_c1);
        let ax_c0c1 = add(ax_c0, ax_c1);
        let by_c0c1 = add(by_c0, by_c1);

        let (v0_lhs_odd_dbl, v0_rhs_odd, v0_lhs_even_dbl, v0_rhs_even) = {
            let rhs_even = by_c0;
            let lhs_even_dbl = x86_64::_mm512_add_epi32(ax_c0, ax_c0);
            let rhs_odd = movehdup_epi32(by_c0);
            let lhs_odd_dbl = x86_64::_mm512_srli_epi64::<31>(ax_c0);
            (lhs_odd_dbl, rhs_odd, lhs_even_dbl, rhs_even)
        };
        let (v1_lhs_odd_dbl, v1_rhs_odd, v1_lhs_even_dbl, v1_rhs_even) = {
            let rhs_even = by_c1;
            let lhs_even_dbl = x86_64::_mm512_add_epi32(ax_c1, ax_c1);
            let rhs_odd = movehdup_epi32(by_c1);
            let lhs_odd_dbl = x86_64::_mm512_srli_epi64::<31>(ax_c1);
            (lhs_odd_dbl, rhs_odd, lhs_even_dbl, rhs_even)
        };
        let (c1t0_lhs_odd_dbl, c1t0_rhs_odd, c1t0_lhs_even_dbl, c1t0_rhs_even) = {
            let rhs_even = by_c0c1;
            let lhs_even_dbl = x86_64::_mm512_add_epi32(ax_c0c1, ax_c0c1);
            let rhs_odd = movehdup_epi32(by_c0c1);
            let lhs_odd_dbl = x86_64::_mm512_srli_epi64::<31>(ax_c0c1);
            (lhs_odd_dbl, rhs_odd, lhs_even_dbl, rhs_even)
        };
        let v0_mul_odd_dbl = x86_64::_mm512_mul_epu32(v0_lhs_odd_dbl, v0_rhs_odd);
        let v0_mul_even_dbl = x86_64::_mm512_mul_epu32(v0_lhs_even_dbl, v0_rhs_even);
        let v1_mul_odd_dbl = x86_64::_mm512_mul_epu32(v1_lhs_odd_dbl, v1_rhs_odd);
        let v1_mul_even_dbl = x86_64::_mm512_mul_epu32(v1_lhs_even_dbl, v1_rhs_even);
        let c1t0_mul_odd_dbl = x86_64::_mm512_mul_epu32(c1t0_lhs_odd_dbl, c1t0_rhs_odd);
        let c1t0_mul_even_dbl = x86_64::_mm512_mul_epu32(c1t0_lhs_even_dbl, c1t0_rhs_even);
        let v0 = {
            let mul_lo_dbl = mask_moveldup_epi32(v0_mul_even_dbl, ODDS, v0_mul_odd_dbl);
            let mul_hi = mask_movehdup_epi32(v0_mul_odd_dbl, EVENS, v0_mul_even_dbl);
            let mul_lo = x86_64::_mm512_srli_epi32::<1>(mul_lo_dbl);
            add(mul_lo, mul_hi)
        };
        let v1 = {
            let mul_lo_dbl = mask_moveldup_epi32(v1_mul_even_dbl, ODDS, v1_mul_odd_dbl);
            let mul_hi = mask_movehdup_epi32(v1_mul_odd_dbl, EVENS, v1_mul_even_dbl);
            let mul_lo = x86_64::_mm512_srli_epi32::<1>(mul_lo_dbl);
            add(mul_lo, mul_hi)
        };
        let c1t0 = {
            let mul_lo_dbl = mask_moveldup_epi32(c1t0_mul_even_dbl, ODDS, c1t0_mul_odd_dbl);
            let mul_hi = mask_movehdup_epi32(c1t0_mul_odd_dbl, EVENS, c1t0_mul_even_dbl);
            let mul_lo = x86_64::_mm512_srli_epi32::<1>(mul_lo_dbl);
            add(mul_lo, mul_hi)
        };

        let c1v0 = sub(c1t0, v0);
        let c1v1 = sub(c1v0, v1);
        let v0v1 = sub(v0, v1);
        let ab = mask_moveldup_epi32(v0v1, ODDS, c1v1);
        let xy = mask_movehdup_epi32(c1v1, EVENS, v0v1);
        (ab, xy)
    }
}

#[inline]
#[must_use]
pub fn rotate_90_m31c_interleaved_forward(a: __m512i, x: __m512i) -> (__m512i, __m512i) {
    unsafe {
        let ax_c0 = mask_moveldup_epi32(a, ODDS, x);
        let ax_c1 = mask_movehdup_epi32(x, EVENS, a);
        let zero = x86_64::_mm512_setzero_si512();
        let ax_c0_negated = sub(zero, ax_c0);
        let chunk_0 = mask_moveldup_epi32(ax_c1, ODDS, ax_c0_negated);
        let chunk_1 = mask_movehdup_epi32(ax_c0_negated, EVENS, ax_c1);
        (chunk_0, chunk_1)
    }
}

#[inline]
#[must_use]
pub fn rotate_90_m31c_interleaved_inversed(a: __m512i, x: __m512i) -> (__m512i, __m512i) {
    unsafe {
        let ax_c0 = mask_moveldup_epi32(a, ODDS, x);
        let ax_c1 = mask_movehdup_epi32(x, EVENS, a);
        let zero = x86_64::_mm512_setzero_si512();
        let ax_c1_negated = sub(zero, ax_c1);
        let chunk_0 = mask_moveldup_epi32(ax_c1_negated, ODDS, ax_c0);
        let chunk_1 = mask_movehdup_epi32(ax_c0, EVENS, ax_c1_negated);
        (chunk_0, chunk_1)
    }
}

impl Add for Mersenne31FieldVectorized {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = add(lhs, rhs);
        unsafe { Self::from_vector(res) }
    }
}

impl Mul for Mersenne31FieldVectorized {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mul(lhs, rhs);
        unsafe { Self::from_vector(res) }
    }
}

impl Sub for Mersenne31FieldVectorized {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = sub(lhs, rhs);
        unsafe { Self::from_vector(res) }
    }
}

impl From<Mersenne31Field> for Mersenne31FieldVectorized {
    #[inline]
    fn from(value: Mersenne31Field) -> Self {
        Self::broadcast(value)
    }
}

impl Default for Mersenne31FieldVectorized {
    #[inline]
    fn default() -> Self {
        Mersenne31Field::default().into()
    }
}

#[inline]
#[must_use]
fn interleave1_radix4(
    a: __m512i,
    b: __m512i,
    c: __m512i,
    d: __m512i,
) -> (__m512i, __m512i, __m512i, __m512i) {
    unsafe {
        // res0 = [ a0 b0 c0 d0 a4 b4 c4 d4 a8 b8 c8 d8 ac bc cc dc ]
        // res1 = [ a1 b1 c1 d1 a5 b5 c5 d5 a9 b9 c9 d9 ad bd cd dd ]
        // res2 = [ a2 b2 c2 d2 a6 b6 c6 d6 aa ba ca da ae be ce de ]
        // res3 = [ a3 b3 c3 d3 a7 b7 c7 d7 ab bb cb db af bf cf df ]

        let mut res0 = x86_64::_mm512_permutex2var_epi32(
            a,
            transmute::<[u32; WIDTH], _>([0, 16, 0, 0, 4, 20, 0, 0, 8, 24, 0, 0, 12, 28, 0, 0]),
            b,
        );
        res0 = x86_64::_mm512_permutex2var_epi32(
            res0,
            transmute::<[u32; WIDTH], _>([0, 1, 16, 0, 4, 5, 20, 0, 8, 9, 24, 0, 12, 13, 28, 0]),
            c,
        );
        res0 = x86_64::_mm512_permutex2var_epi32(
            res0,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 16, 4, 5, 6, 20, 8, 9, 10, 24, 12, 13, 14, 28]),
            d,
        );
        let mut res1 = x86_64::_mm512_permutex2var_epi32(
            a,
            transmute::<[u32; WIDTH], _>([1, 17, 0, 0, 5, 21, 0, 0, 9, 25, 0, 0, 13, 29, 0, 0]),
            b,
        );
        res1 = x86_64::_mm512_permutex2var_epi32(
            res1,
            transmute::<[u32; WIDTH], _>([0, 1, 17, 0, 4, 5, 21, 0, 8, 9, 25, 0, 12, 13, 29, 0]),
            c,
        );
        res1 = x86_64::_mm512_permutex2var_epi32(
            res1,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 17, 4, 5, 6, 21, 8, 9, 10, 25, 12, 13, 14, 29]),
            d,
        );
        let mut res2 = x86_64::_mm512_permutex2var_epi32(
            a,
            transmute::<[u32; WIDTH], _>([2, 18, 0, 0, 6, 22, 0, 0, 10, 26, 0, 0, 14, 30, 0, 0]),
            b,
        );
        res2 = x86_64::_mm512_permutex2var_epi32(
            res2,
            transmute::<[u32; WIDTH], _>([0, 1, 18, 0, 4, 5, 22, 0, 8, 9, 26, 0, 12, 13, 30, 0]),
            c,
        );
        res2 = x86_64::_mm512_permutex2var_epi32(
            res2,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 18, 4, 5, 6, 22, 8, 9, 10, 26, 12, 13, 14, 30]),
            d,
        );
        let mut res3 = x86_64::_mm512_permutex2var_epi32(
            a,
            transmute::<[u32; WIDTH], _>([3, 19, 0, 0, 7, 23, 0, 0, 11, 27, 0, 0, 15, 31, 0, 0]),
            b,
        );
        res3 = x86_64::_mm512_permutex2var_epi32(
            res3,
            transmute::<[u32; WIDTH], _>([0, 1, 19, 0, 4, 5, 23, 0, 8, 9, 27, 0, 12, 13, 31, 0]),
            c,
        );
        res3 = x86_64::_mm512_permutex2var_epi32(
            res3,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 19, 4, 5, 6, 23, 8, 9, 10, 27, 12, 13, 14, 31]),
            d,
        );

        (res0, res1, res2, res3)
    }
}

#[inline]
#[must_use]
fn interleave4_radix4(
    a: __m512i,
    b: __m512i,
    c: __m512i,
    d: __m512i,
) -> (__m512i, __m512i, __m512i, __m512i) {
    unsafe {
        // res0 = [ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 ]
        // res1 = [ a4 a5 a6 a7 b4 b5 b6 b7 c4 c5 c6 c7 d4 d5 d6 d7 ]
        // res2 = [ a8 a9 aa ab b8 b9 ba bb c8 c9 ca cb d8 d9 da db ]
        // res3 = [ ac ad ae af bc bd be bf cc cd ce cf dc dd de df ]

        let mut res0 = x86_64::_mm512_permutex2var_epi64(
            a,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 8, 9, 0, 0, 0, 0]),
            b,
        );
        res0 = x86_64::_mm512_permutex2var_epi64(
            res0,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 8, 9, 0, 0]),
            c,
        );
        res0 = x86_64::_mm512_permutex2var_epi64(
            res0,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 4, 5, 8, 9]),
            d,
        );
        let mut res1 = x86_64::_mm512_permutex2var_epi64(
            a,
            transmute::<[u64; WIDTH / 2], _>([2, 3, 10, 11, 0, 0, 0, 0]),
            b,
        );
        res1 = x86_64::_mm512_permutex2var_epi64(
            res1,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 10, 11, 0, 0]),
            c,
        );
        res1 = x86_64::_mm512_permutex2var_epi64(
            res1,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 4, 5, 10, 11]),
            d,
        );
        let mut res2 = x86_64::_mm512_permutex2var_epi64(
            a,
            transmute::<[u64; WIDTH / 2], _>([4, 5, 12, 13, 0, 0, 0, 0]),
            b,
        );
        res2 = x86_64::_mm512_permutex2var_epi64(
            res2,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 12, 13, 0, 0]),
            c,
        );
        res2 = x86_64::_mm512_permutex2var_epi64(
            res2,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 4, 5, 12, 13]),
            d,
        );
        let mut res3 = x86_64::_mm512_permutex2var_epi64(
            a,
            transmute::<[u64; WIDTH / 2], _>([6, 7, 14, 15, 0, 0, 0, 0]),
            b,
        );
        res3 = x86_64::_mm512_permutex2var_epi64(
            res3,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 14, 15, 0, 0]),
            c,
        );
        res3 = x86_64::_mm512_permutex2var_epi64(
            res3,
            transmute::<[u64; WIDTH / 2], _>([0, 1, 2, 3, 4, 5, 14, 15]),
            d,
        );

        (res0, res1, res2, res3)
    }
}

#[inline]
#[must_use]
fn interleave1_antidiagonal(x: __m512i, y: __m512i) -> __m512i {
    const INTERLEAVE1_INDICES: __m512i = unsafe {
        transmute::<[u32; WIDTH], _>([
            0x01, 0x10, 0x03, 0x12, 0x05, 0x14, 0x07, 0x16, 0x09, 0x18, 0x0b, 0x1a, 0x0d, 0x1c,
            0x0f, 0x1e,
        ])
    };
    unsafe { x86_64::_mm512_permutex2var_epi32(x, INTERLEAVE1_INDICES, y) }
}

#[inline]
#[must_use]
fn interleave1(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    let t = interleave1_antidiagonal(x, y);
    unsafe {
        //   res0 = [ x0  y0  x2  y2  x4  y4  x6  y6  x8  y8  xa  ya  xc  yc  xe  ye ],
        //   res1 = [ x1  y1  x3  y3  x5  y5  x7  y7  x9  y9  xb  yb  xd  yd  xf  yf ].
        (
            x86_64::_mm512_mask_blend_epi32(EVENS, t, x),
            x86_64::_mm512_mask_blend_epi32(EVENS, y, t),
        )
    }
}

#[inline]
#[must_use]
fn interleave4(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    const INTERLEAVE4_INDICES: __m512i = unsafe {
        transmute::<[u64; WIDTH / 2], _>([0o02, 0o03, 0o10, 0o11, 0o06, 0o07, 0o14, 0o15])
    };
    unsafe {
        let t = x86_64::_mm512_permutex2var_epi64(x, INTERLEAVE4_INDICES, y);

        //   res0 = [ x0  x1  x2  x3  y0  y1  y2  y3  x8  x9  xa  xb  y8  y9  ya  yb ],
        //   res1 = [ x4  x5  x6  x7  y4  y5  y6  y7  xc  xd  xe  xf  yc  yd  ye  yf ].
        (
            x86_64::_mm512_mask_blend_epi32(EVENS4, t, x),
            x86_64::_mm512_mask_blend_epi32(EVENS4, y, t),
        )
    }
}

impl Mersenne31FieldVectorized {
    #[inline(always)]
    pub fn slice_into_base_slice_mut(
        input: &mut [Mersenne31FieldVectorized],
    ) -> &mut [Mersenne31Field] {
        let result_len = input.len() * WIDTH;
        unsafe {
            core::slice::from_raw_parts_mut(input.as_ptr() as *mut Mersenne31Field, result_len)
        }
    }
}

impl BaseField for Mersenne31FieldVectorized {
    const QUADRATIC_NON_RESIDUE: Mersenne31FieldVectorized =
        Mersenne31FieldVectorized([Mersenne31Field::MINUS_ONE; WIDTH]);

    fn mul_by_non_residue(elem: &mut Self) {
        elem.negate();
    }
}

impl Field for Mersenne31FieldVectorized {
    const ZERO: Self = Self([Mersenne31Field::ZERO; WIDTH]);
    const ONE: Self = Self([Mersenne31Field::ONE; WIDTH]);

    #[inline(always)]
    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }

    fn is_one(&self) -> bool {
        *self == Self::ONE
    }

    #[inline(always)]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        *self = *self + *other;
        self
    }

    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        *self = *self - *other;
        self
    }

    #[inline(always)]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        *self = *self * *other;
        self
    }

    #[inline(always)]
    fn square(&'_ mut self) -> &'_ mut Self {
        let other = *self;
        self.mul_assign(&other)
    }

    #[inline(always)]
    fn negate(&'_ mut self) -> &'_ mut Self {
        let mut order = Self([Mersenne31Field(Mersenne31Field::ORDER); WIDTH]);
        let neg = order.sub_assign(&self);
        *self = *neg;
        self
    }

    #[inline(always)]
    fn double(&'_ mut self) -> &'_ mut Self {
        let other = *self;
        self.add_assign(&other)
    }

    #[inline(always)]
    fn inverse(&self) -> Option<Self> {
        let mut error = false;
        let mut res = *self;
        for i in 0..WIDTH {
            let inv = Field::inverse(&self.0[i]);
            error = error || inv.is_none();
            res.0[i] = inv.expect("inverse must exist");
        }
        if error {
            None
        } else {
            Some(res)
        }
    }
}

impl FieldLikeVectorized for Mersenne31FieldVectorized {
    type Base = Mersenne31Field;
    const SIZE_FACTOR: usize = 16;

    #[inline(always)]
    fn constant(value: Self::Base) -> Self {
        Self([value; WIDTH])
    }

    fn get_base_element(&self, idx: usize) -> Self::Base {
        self.0[idx]
    }

    fn from_base_elements(input: &[Self::Base]) -> Self {
        let mut res = Self::default();
        res.0.copy_from_slice(input);
        res
    }

    fn from_base_array(input: &[Self::Base; Self::SIZE_FACTOR]) -> Self {
        let mut res = Self::default();
        res.0.copy_from_slice(input);
        res
    }
}
