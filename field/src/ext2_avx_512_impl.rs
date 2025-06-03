// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.
use super::Field;
use super::Mersenne31Quartic;
use super::*;
use crate::avx_512_impl::Mersenne31FieldVectorized;
use crate::avx_512_impl::WIDTH;
use crate::ext_avx_512_impl::Mersenne31ComplexVectorized;
use crate::field::BaseField;
use crate::FieldExtension;
use crate::FieldLikeVectorized;
use crate::Mersenne31Complex;
use core::arch::x86_64::{self, __m512i};
use core::mem::transmute;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(C, align(64))]
pub struct Mersenne31FieldAVX512Quartic {
    pub c0: Mersenne31ComplexVectorized,
    pub c1: Mersenne31ComplexVectorized,
}

impl Mersenne31FieldAVX512Quartic {
    pub fn rotate<const N: i32>(&self) -> Self {
        let mut input = *self;
        input.c0.c0.rotate::<N>();
        input.c0.c1.rotate::<N>();
        input.c1.c0.rotate::<N>();
        input.c1.c1.rotate::<N>();
        input
    }
}

impl From<Mersenne31Quartic> for Mersenne31FieldAVX512Quartic {
    #[inline]
    fn from(value: Mersenne31Quartic) -> Self {
        Self {
            c0: Mersenne31ComplexVectorized::from(
                <Mersenne31Quartic as FieldExtension<Mersenne31Complex>>::into_coeffs_in_base(
                    value,
                )[0],
            ),
            c1: Mersenne31ComplexVectorized::from(
                <Mersenne31Quartic as FieldExtension<Mersenne31Complex>>::into_coeffs_in_base(
                    value,
                )[1],
            ),
        }
    }
}

impl Default for Mersenne31FieldAVX512Quartic {
    #[inline]
    fn default() -> Self {
        Self {
            c0: Mersenne31ComplexVectorized::default(),
            c1: Mersenne31ComplexVectorized::default(),
        }
    }
}

impl core::fmt::Display for Mersenne31FieldAVX512Quartic {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?} {:?}", self.c0, self.c1)
    }
}

use rand::Rng;
impl Rand for Mersenne31FieldAVX512Quartic {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Mersenne31FieldAVX512Quartic {
        let c0 = Mersenne31ComplexVectorized::random_element(rng);
        let c1 = Mersenne31ComplexVectorized::random_element(rng);
        Mersenne31FieldAVX512Quartic { c0, c1 }
    }
}

impl Field for Mersenne31FieldAVX512Quartic {
    const ZERO: Self = Self {
        c0: Mersenne31ComplexVectorized::ZERO,
        c1: Mersenne31ComplexVectorized::ZERO,
    };
    const ONE: Self = Self {
        c0: Mersenne31ComplexVectorized::ONE,
        c1: Mersenne31ComplexVectorized::ZERO,
    };

    #[inline(always)]
    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }

    #[inline(always)]
    fn is_one(&self) -> bool {
        *self == Self::ONE
    }

    #[inline(always)]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
        self
    }

    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
        self
    }

    #[inline(always)]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        let mut v0 = self.c0;
        v0.mul_assign(&other.c0);
        let mut v1 = self.c1;
        v1.mul_assign(&other.c1);

        let t = self.c0;
        self.c1.add_assign(&t);

        let mut t0 = other.c0;
        t0.add_assign(&other.c1);
        self.c1.mul_assign(&t0);
        self.c1.sub_assign(&v0);
        self.c1.sub_assign(&v1);
        self.c0 = v0;
        Mersenne31ComplexVectorized::mul_by_non_residue(&mut v1);
        self.c0.add_assign(&v1);

        self
    }

    #[inline(always)]
    fn square(&'_ mut self) -> &'_ mut Self {
        let mut v0 = self.c0;
        v0.sub_assign(&self.c1);
        let mut v3 = self.c0;
        let mut t0 = self.c1;
        Mersenne31ComplexVectorized::mul_by_non_residue(&mut t0);
        v3.sub_assign(&t0);
        let mut v2 = self.c0;
        v2.mul_assign(&self.c1);
        v0.mul_assign(&v3);
        v0.add_assign(&v2);

        self.c1 = v2;
        self.c1.double();
        self.c0 = v0;
        Mersenne31ComplexVectorized::mul_by_non_residue(&mut v2);
        self.c0.add_assign(&v2);

        self
    }

    #[inline(always)]
    fn negate(&'_ mut self) -> &'_ mut Self {
        self.c0.negate();
        self.c1.negate();
        self
    }

    #[inline(always)]
    fn double(&mut self) -> &mut Self {
        self.c0.double();
        self.c1.double();
        self
    }

    #[inline(always)]
    fn inverse(&self) -> Option<Self> {
        let mut v0 = self.c0;
        v0.square();
        let mut v1 = self.c1;
        v1.square();
        // v0 = v0 - beta * v1
        let mut v1_by_nonresidue = v1;
        Mersenne31ComplexVectorized::mul_by_non_residue(&mut v1_by_nonresidue);
        v0.sub_assign(&v1_by_nonresidue);
        match v0.inverse() {
            Some(inversed) => {
                let mut c0 = self.c0;
                c0.mul_assign(&inversed);
                let mut c1 = self.c1;
                c1.mul_assign(&inversed);
                c1.negate();

                let new = Self { c0: c0, c1: c1 };
                Some(new)
            }
            None => None,
        }
    }
}

impl FieldExtension<Mersenne31ComplexVectorized> for Mersenne31FieldAVX512Quartic {
    const DEGREE: usize = 2;
    #[inline(always)]
    fn mul_assign_by_base(&mut self, base: &Mersenne31ComplexVectorized) -> &mut Self {
        self.c0.mul_assign(base);
        self.c1.mul_assign(base);
        self
    }

    #[inline(always)]
    fn add_assign_base(&mut self, elem: &Mersenne31ComplexVectorized) -> &mut Self {
        self.c0.add_assign(elem);
        self
    }

    #[inline(always)]
    fn sub_assign_base(&mut self, elem: &Mersenne31ComplexVectorized) -> &mut Self {
        self.c0.sub_assign(elem);
        self
    }

    #[inline(always)]
    fn into_coeffs_in_base(self) -> [Mersenne31ComplexVectorized; 2] {
        [self.c0, self.c1]
    }

    #[inline(always)]
    fn coeffs_in_base(&self) -> &[Mersenne31ComplexVectorized] {
        unsafe {
            core::slice::from_raw_parts(
                self.c0.c0.0.as_ptr() as *const Mersenne31ComplexVectorized,
                2,
            )
        }
    }

    #[inline(always)]
    fn from_coeffs_in_base(coeffs: &[Mersenne31ComplexVectorized]) -> Self {
        Self {
            c0: coeffs[0],
            c1: coeffs[1],
        }
    }

    fn from_coeffs_in_base_ref(coeffs: &[&Mersenne31ComplexVectorized]) -> Self {
        Self {
            c0: *coeffs[0],
            c1: *coeffs[1],
        }
    }

    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31ComplexVectorized>>(
        mut coeffs_iter: I,
    ) -> Self {
        Self {
            c0: coeffs_iter.next().unwrap(),
            c1: coeffs_iter.next().unwrap(),
        }
    }

    #[inline(always)]
    fn from_base(elem: Mersenne31ComplexVectorized) -> Self {
        Self {
            c0: elem,
            c1: Mersenne31ComplexVectorized::ZERO,
        }
    }

    #[inline(always)]
    fn get_coef_mut(&mut self, idx: usize) -> &mut Mersenne31ComplexVectorized {
        if idx == 0 {
            return &mut self.c0;
        } else if idx == 1 {
            return &mut self.c1;
        } else {
            panic!("Invalid index");
        }
    }

    fn from_base_coeffs_array(coefs: &[Mersenne31ComplexVectorized; 2]) -> Self {
        Self {
            c0: coefs[0],
            c1: coefs[1],
        }
    }
}

impl FieldExtension<Mersenne31FieldVectorized> for Mersenne31FieldAVX512Quartic {
    const DEGREE: usize = 4;

    fn mul_assign_by_base(&mut self, elem: &Mersenne31FieldVectorized) -> &mut Self {
        self.c0.c0.mul_assign_by_base(elem);
        self.c0.c1.mul_assign_by_base(elem);
        self.c1.c0.mul_assign_by_base(elem);
        self.c1.c1.mul_assign_by_base(elem);
        self
    }

    fn into_coeffs_in_base(self) -> [Mersenne31FieldVectorized; 4] {
        let Mersenne31FieldAVX512Quartic { c0: a, c1: b } = self;
        let [c0, c1] = a.into_coeffs_in_base();
        let [c2, c3] = b.into_coeffs_in_base();
        [c0, c1, c2, c3]
    }

    fn from_coeffs_in_base(coeffs: &[Mersenne31FieldVectorized]) -> Self {
        let c0 = Mersenne31ComplexVectorized::from_coeffs_in_base(&coeffs[0..2]);
        let c1 = Mersenne31ComplexVectorized::from_coeffs_in_base(&coeffs[2..4]);
        Self { c0: c0, c1: c1 }
    }

    fn from_coeffs_in_base_ref(coeffs: &[&Mersenne31FieldVectorized]) -> Self {
        let c0 = Mersenne31ComplexVectorized::from_coeffs_in_base_ref(&coeffs[0..2]);
        let c1 = Mersenne31ComplexVectorized::from_coeffs_in_base_ref(&coeffs[2..4]);
        Self { c0: c0, c1: c1 }
    }

    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31FieldVectorized>>(
        mut coeffs_iter: I,
    ) -> Self {
        let c0 = Mersenne31ComplexVectorized::from_coeffs_in_base(&[
            coeffs_iter.next().unwrap(),
            coeffs_iter.next().unwrap(),
        ]);
        let c1 = Mersenne31ComplexVectorized::from_coeffs_in_base(&[
            coeffs_iter.next().unwrap(),
            coeffs_iter.next().unwrap(),
        ]);
        Self { c0: c0, c1: c1 }
    }

    fn coeffs_in_base(&self) -> &[Mersenne31FieldVectorized] {
        unsafe {
            core::slice::from_raw_parts(
                self.c0.c0.0.as_ptr() as *const Mersenne31FieldVectorized,
                4,
            )
        }
    }

    fn add_assign_base(&mut self, elem: &Mersenne31FieldVectorized) -> &mut Self {
        self.c0.add_assign_base(elem);
        self
    }

    fn sub_assign_base(&mut self, elem: &Mersenne31FieldVectorized) -> &mut Self {
        self.c0.sub_assign_base(elem);
        self
    }

    fn from_base(elem: Mersenne31FieldVectorized) -> Self {
        let c0 = Mersenne31ComplexVectorized::from_base(elem);
        Self {
            c0: c0,
            c1: Mersenne31ComplexVectorized::ZERO,
        }
    }

    fn get_coef_mut(&mut self, idx: usize) -> &mut Mersenne31FieldVectorized {
        if idx < 2 {
            return self.c0.get_coef_mut(idx % 2);
        } else {
            return self.c1.get_coef_mut(idx % 2);
        }
    }

    fn from_base_coeffs_array(coefs: &[Mersenne31FieldVectorized; 4]) -> Self {
        let c0 = Mersenne31ComplexVectorized::from_coeffs_in_base(&coefs[0..2]);
        let c1 = Mersenne31ComplexVectorized::from_coeffs_in_base(&coefs[2..4]);
        Self { c0: c0, c1: c1 }
    }
}

#[inline]
#[must_use]
fn interleave_f4_into_base(a: &mut [__m512i]) {
    unsafe {
        // in0 = [ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 aa ab ac ad ae af ]
        // in1 = [ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf ]
        // in2 = [ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ca cb cc cd ce cf ]
        // in3 = [ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 da db dc dd de df ]

        // res0 = [ a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 ]
        // res1 = [ a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 d7 ]
        // res2 = [ a8 b8 c8 d8 a9 b9 c9 d9 aa ba ca da ab bb cb db ]
        // res3 = [ ac bc cc dc ad bd cd dd ae be ce de af bf cf df ]

        let mut res0 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([0, 16, 0, 0, 1, 17, 0, 0, 2, 18, 0, 0, 3, 19, 0, 0]),
            a[1],
        );
        res0 = x86_64::_mm512_permutex2var_epi32(
            res0,
            transmute::<[u32; WIDTH], _>([0, 1, 16, 0, 4, 5, 17, 0, 8, 9, 18, 0, 12, 13, 19, 0]),
            a[2],
        );
        res0 = x86_64::_mm512_permutex2var_epi32(
            res0,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 16, 4, 5, 6, 17, 8, 9, 10, 18, 12, 13, 14, 19]),
            a[3],
        );
        let mut res1 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([4, 20, 0, 0, 5, 21, 0, 0, 6, 22, 0, 0, 7, 23, 0, 0]),
            a[1],
        );
        res1 = x86_64::_mm512_permutex2var_epi32(
            res1,
            transmute::<[u32; WIDTH], _>([0, 1, 20, 0, 4, 5, 21, 0, 8, 9, 22, 0, 12, 13, 23, 0]),
            a[2],
        );
        res1 = x86_64::_mm512_permutex2var_epi32(
            res1,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 20, 4, 5, 6, 21, 8, 9, 10, 22, 12, 13, 14, 23]),
            a[3],
        );
        let mut res2 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([8, 24, 0, 0, 9, 25, 0, 0, 10, 26, 0, 0, 11, 27, 0, 0]),
            a[1],
        );
        res2 = x86_64::_mm512_permutex2var_epi32(
            res2,
            transmute::<[u32; WIDTH], _>([0, 1, 24, 0, 4, 5, 25, 0, 8, 9, 26, 0, 12, 13, 27, 0]),
            a[2],
        );
        res2 = x86_64::_mm512_permutex2var_epi32(
            res2,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 24, 4, 5, 6, 25, 8, 9, 10, 26, 12, 13, 14, 27]),
            a[3],
        );
        let mut res3 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([12, 28, 0, 0, 13, 29, 0, 0, 14, 30, 0, 0, 15, 31, 0, 0]),
            a[1],
        );
        res3 = x86_64::_mm512_permutex2var_epi32(
            res3,
            transmute::<[u32; WIDTH], _>([0, 1, 28, 0, 4, 5, 29, 0, 8, 9, 30, 0, 12, 13, 31, 0]),
            a[2],
        );
        res3 = x86_64::_mm512_permutex2var_epi32(
            res3,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 28, 4, 5, 6, 29, 8, 9, 10, 30, 12, 13, 14, 31]),
            a[3],
        );

        a[0] = res0;
        a[1] = res1;
        a[2] = res2;
        a[3] = res3;
    }
}

#[inline]
#[must_use]
fn interleave_f4_from_base(a: &mut [__m512i]) {
    unsafe {
        // in0 = [ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 aa ab ac ad ae af ]
        // in1 = [ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf ]
        // in2 = [ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ca cb cc cd ce cf ]
        // in3 = [ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 da db dc dd de df ]

        // res0 = [ a0 a4 a8 ac b0 b4 b8 bc c0 c4 c8 cc d0 d4 d8 dc ]
        // res1 = [ a1 a5 a9 ad b1 b5 b9 bd c1 c5 c9 cd d1 d5 d9 dd ]
        // res2 = [ a2 a6 aa ae b2 b6 ba be c2 c6 ca ce d2 d6 da de ]
        // res3 = [ a3 a7 ab af b3 b7 bb bf c3 c7 cb cf d3 d7 db df ]

        let mut res0 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([0, 4, 8, 12, 16, 20, 24, 28, 0, 0, 0, 0, 0, 0, 0, 0]),
            a[1],
        );
        res0 = x86_64::_mm512_permutex2var_epi32(
            res0,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 16, 20, 24, 28, 0, 0, 0, 0]),
            a[2],
        );
        res0 = x86_64::_mm512_permutex2var_epi32(
            res0,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 20, 24, 28]),
            a[3],
        );
        let mut res1 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([1, 5, 9, 13, 17, 21, 25, 29, 0, 0, 0, 0, 0, 0, 0, 0]),
            a[1],
        );
        res1 = x86_64::_mm512_permutex2var_epi32(
            res1,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 17, 21, 25, 29, 0, 0, 0, 0]),
            a[2],
        );
        res1 = x86_64::_mm512_permutex2var_epi32(
            res1,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 21, 25, 29]),
            a[3],
        );
        let mut res2 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([2, 6, 10, 14, 18, 22, 26, 30, 0, 0, 0, 0, 0, 0, 0, 0]),
            a[1],
        );
        res2 = x86_64::_mm512_permutex2var_epi32(
            res2,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 18, 22, 26, 30, 0, 0, 0, 0]),
            a[2],
        );
        res2 = x86_64::_mm512_permutex2var_epi32(
            res2,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 18, 22, 26, 30]),
            a[3],
        );
        let mut res3 = x86_64::_mm512_permutex2var_epi32(
            a[0],
            transmute::<[u32; WIDTH], _>([3, 7, 11, 15, 19, 23, 27, 31, 0, 0, 0, 0, 0, 0, 0, 0]),
            a[1],
        );
        res3 = x86_64::_mm512_permutex2var_epi32(
            res3,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 19, 23, 27, 31, 0, 0, 0, 0]),
            a[2],
        );
        res3 = x86_64::_mm512_permutex2var_epi32(
            res3,
            transmute::<[u32; WIDTH], _>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19, 23, 27, 31]),
            a[3],
        );

        a[0] = res0;
        a[1] = res1;
        a[2] = res2;
        a[3] = res3;
    }
}

fn permute_into_base_elements(input: Mersenne31FieldAVX512Quartic) -> Mersenne31FieldAVX512Quartic {
    unsafe {
        let mut raw_vecs: [__m512i; 4] = transmute(input);
        let _ = interleave_f4_into_base(&mut raw_vecs);
        transmute(raw_vecs)
    }
}

fn permute_from_base_elements(input: Mersenne31FieldAVX512Quartic) -> Mersenne31FieldAVX512Quartic {
    unsafe {
        let mut raw_vecs: [__m512i; 4] = transmute(input);
        let _ = interleave_f4_from_base(&mut raw_vecs);
        transmute(raw_vecs)
    }
}

impl FieldLikeVectorized for Mersenne31FieldAVX512Quartic {
    type Base = Mersenne31Quartic;
    const SIZE_FACTOR: usize = WIDTH;

    #[inline(always)]
    fn constant(value: Self::Base) -> Self {
        Self {
            c0: Mersenne31ComplexVectorized::constant(value.c0),
            c1: Mersenne31ComplexVectorized::constant(value.c1),
        }
    }

    fn get_base_element(&self, idx: usize) -> Self::Base {
        Self::Base::from_coeffs_in_base(&[
            self.c0.get_base_element(idx),
            self.c1.get_base_element(idx),
        ])
    }

    fn from_base_elements(input: &[Self::Base]) -> Self {
        Self::from_base_array(input.try_into().unwrap())
    }

    fn from_base_array(input: &[Self::Base; Self::SIZE_FACTOR]) -> Self {
        let input =
            unsafe { transmute::<[Mersenne31Quartic; 16], [Mersenne31Complex; 32]>(*input) };
        let vector = Self {
            c0: Mersenne31ComplexVectorized::from_base_elements(&input[..Self::SIZE_FACTOR / 2]),
            c1: Mersenne31ComplexVectorized::from_base_elements(&input[Self::SIZE_FACTOR / 2..]),
        };
        permute_from_base_elements(vector)
    }

    fn as_base_array(&self) -> [Self::Base; Self::SIZE_FACTOR] {
        let permuted = permute_into_base_elements(*self);
        let res: [Self::Base; Self::SIZE_FACTOR] = unsafe { transmute(permuted) };
        res
    }
}
