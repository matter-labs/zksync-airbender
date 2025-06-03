// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.

use super::*;
use crate::field::BaseField;
use crate::field::Field;
use crate::field::PrimeField;
use crate::Mersenne31Field;
use core::ops::{Add, Mul, Sub};
// use crate::field_like::FieldLikeVectorized;
use seq_macro::seq;
// use crate::prover::prover::Timer;

pub const WIDTH: usize = 16;

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
            Mersenne31Field::from_u64_unchecked(
                rng.random_range(0..Mersenne31Field::CHARACTERISTICS),
            )
        });
        Mersenne31FieldVectorized(t)
    }
}

impl Mersenne31FieldVectorized {
    #[inline]
    #[must_use]
    pub const fn broadcast(value: Mersenne31Field) -> Self {
        Self([value; WIDTH])
    }
}

impl Add for Mersenne31FieldVectorized {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let mut res = Self::default();
        seq!(N in 0..16 {
            res.0[N] = self.0[N] + rhs.0[N];
        });
        res
    }
}

impl Mul for Mersenne31FieldVectorized {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let mut res = Self::default();
        seq!(N in 0..16 {
            res.0[N] = self.0[N];
            res.0[N].mul_assign(&rhs.0[N]);
        });
        res
    }
}

impl Sub for Mersenne31FieldVectorized {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let mut res = Self::default();
        seq!(N in 0..16 {
            res.0[N] = self.0[N] - rhs.0[N];
        });
        res
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
