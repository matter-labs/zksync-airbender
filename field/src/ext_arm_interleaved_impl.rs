// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.

use super::Field;
use super::*;
use crate::FieldExtension;
use crate::FieldLikeVectorized;
use crate::Mersenne31Complex;
use crate::Mersenne31Field;
use crate::Mersenne31FieldVectorized;
use crate::WIDTH;
use core::mem::transmute;
use core::ops::{Add, Mul, Sub};
use seq_macro::seq;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(C, align(64))]
pub struct Mersenne31ComplexVectorizedInterleaved {
    pub chunk_0: Mersenne31FieldVectorized,
    pub chunk_1: Mersenne31FieldVectorized,
}

impl From<Mersenne31Complex> for Mersenne31ComplexVectorizedInterleaved {
    #[inline]
    fn from(value: Mersenne31Complex) -> Self {
        unsafe {
            transmute::<[Mersenne31Complex; WIDTH], Mersenne31ComplexVectorizedInterleaved>(
                [value; WIDTH],
            )
        }
    }
}

impl Default for Mersenne31ComplexVectorizedInterleaved {
    #[inline]
    fn default() -> Self {
        Self {
            chunk_0: Mersenne31FieldVectorized::default(),
            chunk_1: Mersenne31FieldVectorized::default(),
        }
    }
}

impl core::fmt::Display for Mersenne31ComplexVectorizedInterleaved {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?} {:?}", self.chunk_0, self.chunk_1)
    }
}

use rand::Rng;
impl Rand for Mersenne31ComplexVectorizedInterleaved {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Mersenne31ComplexVectorizedInterleaved {
        let chunk_0 = [(); WIDTH / 2].map(|_| Mersenne31Complex::random_element(rng));
        let chunk_1 = [(); WIDTH / 2].map(|_| Mersenne31Complex::random_element(rng));
        Mersenne31ComplexVectorizedInterleaved {
            chunk_0: unsafe {
                transmute::<[Mersenne31Complex; WIDTH / 2], Mersenne31FieldVectorized>(chunk_0)
            },
            chunk_1: unsafe {
                transmute::<[Mersenne31Complex; WIDTH / 2], Mersenne31FieldVectorized>(chunk_1)
            },
        }
    }
}

impl Field for Mersenne31ComplexVectorizedInterleaved {
    const ZERO: Self = {
        let v = unsafe {
            transmute::<[Mersenne31Complex; WIDTH / 2], Mersenne31FieldVectorized>(
                [Mersenne31Complex::ZERO; WIDTH / 2],
            )
        };
        Self {
            chunk_0: v,
            chunk_1: v,
        }
    };
    const ONE: Self = {
        let v = unsafe {
            transmute::<[Mersenne31Complex; WIDTH / 2], Mersenne31FieldVectorized>(
                [Mersenne31Complex::ONE; WIDTH / 2],
            )
        };
        Self {
            chunk_0: v,
            chunk_1: v,
        }
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
        todo!()
    }

    #[inline(always)]
    fn negate(&'_ mut self) -> &'_ mut Self {
        self.chunk_0.negate();
        self.chunk_1.negate();
        self
    }

    #[inline(always)]
    fn double(&mut self) -> &mut Self {
        self.chunk_0.double();
        self.chunk_1.double();
        self
    }

    #[inline(always)]
    fn inverse(&self) -> Option<Self> {
        todo!()
    }
}

impl Add for Mersenne31ComplexVectorizedInterleaved {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            chunk_0: self.chunk_0 + rhs.chunk_0,
            chunk_1: self.chunk_1 + rhs.chunk_1,
        }
    }
}

impl Sub for Mersenne31ComplexVectorizedInterleaved {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            chunk_0: self.chunk_0 - rhs.chunk_0,
            chunk_1: self.chunk_1 - rhs.chunk_1,
        }
    }
}

impl Mul for Mersenne31ComplexVectorizedInterleaved {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let mut value0 = unsafe {
            transmute::<Mersenne31ComplexVectorizedInterleaved, [Mersenne31Complex; WIDTH]>(self)
        };
        let value1 = unsafe {
            transmute::<Mersenne31ComplexVectorizedInterleaved, [Mersenne31Complex; WIDTH]>(rhs)
        };
        seq!(N in 0..16 {
            value0[N].mul_assign(&value1[N]);
        });
        unsafe {
            transmute::<[Mersenne31Complex; WIDTH], Mersenne31ComplexVectorizedInterleaved>(value0)
        }
    }
}

impl Mul<Mersenne31FieldVectorized> for Mersenne31ComplexVectorizedInterleaved {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Mersenne31FieldVectorized) -> Self {
        let mut res = self;
        res.chunk_0.mul_assign(&rhs);
        res.chunk_1.mul_assign(&rhs);
        res
    }
}

impl Mul<Mersenne31ComplexVectorized> for Mersenne31ComplexVectorizedInterleaved {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Mersenne31ComplexVectorized) -> Self {
        let mut value0 = unsafe {
            transmute::<Mersenne31ComplexVectorizedInterleaved, [Mersenne31Complex; WIDTH]>(self)
        };
        seq!(N in 0..16 {
            let value1 = Mersenne31Complex::from_coeffs_in_base(&[rhs.c0.0[N], rhs.c1.0[N]]);
            value0[N].mul_assign(&value1);
        });
        unsafe {
            transmute::<[Mersenne31Complex; WIDTH], Mersenne31ComplexVectorizedInterleaved>(value0)
        }
    }
}

#[inline]
pub fn rotate_90_forward(
    value: Mersenne31ComplexVectorizedInterleaved,
) -> Mersenne31ComplexVectorizedInterleaved {
    let mut value0 = unsafe {
        transmute::<Mersenne31ComplexVectorizedInterleaved, [Mersenne31Complex; WIDTH]>(value)
    };
    seq!(N in 0..16 {
        let mut c0 = value0[N].c0;
        value0[N].c0 = value0[N].c1;
        value0[N].c1 = *c0.negate();
    });
    unsafe {
        transmute::<[Mersenne31Complex; WIDTH], Mersenne31ComplexVectorizedInterleaved>(value0)
    }
}

#[inline]
pub fn rotate_90_inversed(
    value: Mersenne31ComplexVectorizedInterleaved,
) -> Mersenne31ComplexVectorizedInterleaved {
    let mut value0 = unsafe {
        transmute::<Mersenne31ComplexVectorizedInterleaved, [Mersenne31Complex; WIDTH]>(value)
    };
    seq!(N in 0..16 {
        let mut c1 = value0[N].c1;
        value0[N].c1 = value0[N].c0;
        value0[N].c0 = *c1.negate();
    });
    unsafe {
        transmute::<[Mersenne31Complex; WIDTH], Mersenne31ComplexVectorizedInterleaved>(value0)
    }
}

impl FieldExtension<Mersenne31FieldVectorized> for Mersenne31ComplexVectorizedInterleaved {
    const DEGREE: usize = 2;

    // THIS WORKS FOR BROADCASTED BASE VALUE ONLY
    #[inline(always)]
    fn mul_assign_by_base(&mut self, base: &Mersenne31FieldVectorized) -> &mut Self {
        self.chunk_0.mul_assign(base);
        self.chunk_1.mul_assign(base);
        self
    }

    #[inline(always)]
    fn add_assign_base(&mut self, _elem: &Mersenne31FieldVectorized) -> &mut Self {
        todo!()
    }

    #[inline(always)]
    fn sub_assign_base(&mut self, _elem: &Mersenne31FieldVectorized) -> &mut Self {
        todo!()
    }

    #[inline(always)]
    fn into_coeffs_in_base(self) -> [Mersenne31FieldVectorized; 2] {
        [self.chunk_0, self.chunk_1]
    }

    #[inline(always)]
    fn coeffs_in_base(&self) -> &[Mersenne31FieldVectorized] {
        // &[self.c0, self.c1]
        unsafe {
            core::slice::from_raw_parts(
                self.chunk_0.0.as_ptr() as *const Mersenne31FieldVectorized,
                2,
            )
        }
    }

    #[inline(always)]
    fn from_coeffs_in_base(coeffs: &[Mersenne31FieldVectorized]) -> Self {
        Self {
            chunk_0: coeffs[0],
            chunk_1: coeffs[1],
        }
    }

    fn from_coeffs_in_base_ref(coeffs: &[&Mersenne31FieldVectorized]) -> Self {
        Self {
            chunk_0: *coeffs[0],
            chunk_1: *coeffs[1],
        }
    }

    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31FieldVectorized>>(
        mut coeffs_iter: I,
    ) -> Self {
        Self {
            chunk_0: coeffs_iter.next().unwrap(),
            chunk_1: coeffs_iter.next().unwrap(),
        }
    }

    #[inline(always)]
    fn from_base(elem: Mersenne31FieldVectorized) -> Self {
        Self {
            chunk_0: elem,
            chunk_1: Mersenne31FieldVectorized::ZERO,
        }
    }

    #[inline(always)]
    fn get_coef_mut(&mut self, idx: usize) -> &mut Mersenne31FieldVectorized {
        if idx == 0 {
            &mut self.chunk_0
        } else if idx == 1 {
            &mut self.chunk_1
        } else {
            panic!("Invalid index");
        }
    }

    fn from_base_coeffs_array(coefs: &[Mersenne31FieldVectorized; 2]) -> Self {
        Self {
            chunk_0: coefs[0],
            chunk_1: coefs[1],
        }
    }
}

impl FieldLikeVectorized for Mersenne31ComplexVectorizedInterleaved {
    type Base = Mersenne31Complex;
    const SIZE_FACTOR: usize = WIDTH;

    #[inline(always)]
    fn constant(value: Self::Base) -> Self {
        Self::from(value)
    }

    fn get_base_element(&self, idx: usize) -> Self::Base {
        let as_slice = core::slice::from_ref(self);
        unsafe { as_slice.as_ptr().cast::<Self::Base>().add(idx).read() }
    }

    fn from_base_elements(input: &[Self::Base]) -> Self {
        Self::from_base_array(input.try_into().unwrap())
    }

    fn from_base_array(input: &[Self::Base; Self::SIZE_FACTOR]) -> Self {
        let input = unsafe { transmute::<[Mersenne31Complex; 16], [Mersenne31Field; 32]>(*input) };
        let mut res = Self::default();
        res.chunk_0.0.copy_from_slice(&input[..Self::SIZE_FACTOR]);
        res.chunk_1.0.copy_from_slice(&input[Self::SIZE_FACTOR..]);
        res
    }

    fn as_base_array(&self) -> [Self::Base; Self::SIZE_FACTOR] {
        let res: [Self::Base; Self::SIZE_FACTOR] = unsafe { transmute(*self) };
        res
    }
}
