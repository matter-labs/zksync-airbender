// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.

use super::Field;
use super::*;
use crate::field::BaseField;
use crate::field::PrimeField;
use crate::FieldExtension;
use crate::Mersenne31Complex;
use crate::Mersenne31Field;
use crate::Mersenne31FieldVectorized;
use crate::WIDTH;
use core::ops::{Add, Mul, Sub};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(C, align(64))]
pub struct Mersenne31ComplexVectorized {
    pub c0: Mersenne31FieldVectorized,
    pub c1: Mersenne31FieldVectorized,
}

impl From<Mersenne31Complex> for Mersenne31ComplexVectorized {
    #[inline]
    fn from(value: Mersenne31Complex) -> Self {
        Self {
            c0: Mersenne31FieldVectorized::from(value.real_part()),
            c1: Mersenne31FieldVectorized::from(value.imag_part()),
        }
    }
}

impl Default for Mersenne31ComplexVectorized {
    #[inline]
    fn default() -> Self {
        Self {
            c0: Mersenne31FieldVectorized::default(),
            c1: Mersenne31FieldVectorized::default(),
        }
    }
}

impl core::fmt::Display for Mersenne31ComplexVectorized {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?} {:?}", self.c0, self.c1)
    }
}

use rand::Rng;
impl Rand for Mersenne31ComplexVectorized {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Mersenne31ComplexVectorized {
        let t_real = [(); WIDTH].map(|_| {
            Mersenne31Field::from_u64_unchecked(
                rng.random_range(0..Mersenne31Field::CHARACTERISTICS),
            )
        });
        let t_imag = [(); WIDTH].map(|_| {
            Mersenne31Field::from_u64_unchecked(
                rng.random_range(0..Mersenne31Field::CHARACTERISTICS),
            )
        });
        Mersenne31ComplexVectorized {
            c0: Mersenne31FieldVectorized(t_real),
            c1: Mersenne31FieldVectorized(t_imag),
        }
    }
}

impl BaseField for Mersenne31ComplexVectorized {
    // 2 + i is non-residue
    const QUADRATIC_NON_RESIDUE: Mersenne31ComplexVectorized = Mersenne31ComplexVectorized {
        c0: Mersenne31FieldVectorized([Mersenne31Field::TWO; WIDTH]),
        c1: Mersenne31FieldVectorized([Mersenne31Field::ONE; WIDTH]),
    };

    #[inline(always)]
    fn mul_by_non_residue(elem: &mut Self) {
        // (a + b * i)(2 + i) = (2 * a - b) + (2 * b + a)i
        let [a, b] = [elem.c0, elem.c1];
        let mut c0 = a;
        c0.double();
        c0.sub_assign(&b);

        let mut c1 = b;
        c1.double();
        c1.add_assign(&a);

        elem.c0 = c0;
        elem.c1 = c1;
    }
}

impl Field for Mersenne31ComplexVectorized {
    const ZERO: Self = Self {
        c0: Mersenne31FieldVectorized::ZERO,
        c1: Mersenne31FieldVectorized::ZERO,
    };
    const ONE: Self = Self {
        c0: Mersenne31FieldVectorized::ONE,
        c1: Mersenne31FieldVectorized::ZERO,
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

        // let t = self.c0;
        self.c1.add_assign(&self.c0);

        let mut t0 = other.c0;
        t0.add_assign(&other.c1);
        self.c1.mul_assign(&t0);
        self.c1.sub_assign(&v0);
        self.c1.sub_assign(&v1);
        self.c0 = v0;
        // Mersenne31FieldVectorized::mul_by_non_residue(&mut v1);
        self.c0.sub_assign(&v1);

        self
    }

    #[inline(always)]
    fn square(&'_ mut self) -> &'_ mut Self {
        let mut v0 = self.c0;
        v0.sub_assign(&self.c1);
        let mut v3 = self.c0;
        let mut t0 = self.c1;
        Mersenne31FieldVectorized::mul_by_non_residue(&mut t0);
        v3.sub_assign(&t0);
        let mut v2 = self.c0;
        v2.mul_assign(&self.c1);
        v0.mul_assign(&v3);
        v0.add_assign(&v2);

        self.c1 = v2;
        self.c1.double();
        self.c0 = v0;
        Mersenne31FieldVectorized::mul_by_non_residue(&mut v2);
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
        Mersenne31FieldVectorized::mul_by_non_residue(&mut v1_by_nonresidue);
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

impl Add for Mersenne31ComplexVectorized {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }
}

impl Sub for Mersenne31ComplexVectorized {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
        }
    }
}

impl Mul for Mersenne31ComplexVectorized {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let mut res = self;
        let mut v0 = self.c0;
        v0.mul_assign(&rhs.c0);
        let mut v1 = self.c1;
        v1.mul_assign(&rhs.c1);

        let t = self.c0;
        res.c1.add_assign(&t);

        let mut t0 = rhs.c0;
        t0.add_assign(&rhs.c1);
        res.c1.mul_assign(&t0);
        res.c1.sub_assign(&v0);
        res.c1.sub_assign(&v1);
        res.c0 = v0;
        Mersenne31FieldVectorized::mul_by_non_residue(&mut v1);
        res.c0.add_assign(&v1);

        res
    }
}

impl Mul<Mersenne31FieldVectorized> for Mersenne31ComplexVectorized {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Mersenne31FieldVectorized) -> Self {
        let mut res = self;
        res.c0.mul_assign(&rhs);
        res.c1.mul_assign(&rhs);
        res
    }
}

impl FieldExtension<Mersenne31FieldVectorized> for Mersenne31ComplexVectorized {
    const DEGREE: usize = 2;
    #[inline(always)]
    fn mul_assign_by_base(&mut self, base: &Mersenne31FieldVectorized) -> &mut Self {
        self.c0.mul_assign(base);
        self.c1.mul_assign(base);
        self
    }

    #[inline(always)]
    fn add_assign_base(&mut self, elem: &Mersenne31FieldVectorized) -> &mut Self {
        self.c0.add_assign(elem);
        self
    }

    #[inline(always)]
    fn sub_assign_base(&mut self, elem: &Mersenne31FieldVectorized) -> &mut Self {
        self.c0.sub_assign(elem);
        self
    }

    #[inline(always)]
    fn into_coeffs_in_base(self) -> [Mersenne31FieldVectorized; 2] {
        [self.c0, self.c1]
    }

    #[inline(always)]
    fn coeffs_in_base(&self) -> &[Mersenne31FieldVectorized] {
        unsafe {
            core::slice::from_raw_parts(self.c0.0.as_ptr() as *const Mersenne31FieldVectorized, 2)
        }
    }

    #[inline(always)]
    fn from_coeffs_in_base(coeffs: &[Mersenne31FieldVectorized]) -> Self {
        Self {
            c0: coeffs[0],
            c1: coeffs[1],
        }
    }

    fn from_coeffs_in_base_ref(coeffs: &[&Mersenne31FieldVectorized]) -> Self {
        Self {
            c0: *coeffs[0],
            c1: *coeffs[1],
        }
    }

    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31FieldVectorized>>(
        mut coeffs_iter: I,
    ) -> Self {
        Self {
            c0: coeffs_iter.next().unwrap(),
            c1: coeffs_iter.next().unwrap(),
        }
    }

    #[inline(always)]
    fn from_base(elem: Mersenne31FieldVectorized) -> Self {
        Self {
            c0: elem,
            c1: Mersenne31FieldVectorized::ZERO,
        }
    }

    #[inline(always)]
    fn get_coef_mut(&mut self, idx: usize) -> &mut Mersenne31FieldVectorized {
        if idx == 0 {
            return &mut self.c0;
        } else if idx == 1 {
            return &mut self.c1;
        } else {
            panic!("Invalid index");
        }
    }

    fn from_base_coeffs_array(coefs: &[Mersenne31FieldVectorized; 2]) -> Self {
        Self {
            c0: coefs[0],
            c1: coefs[1],
        }
    }
}

impl FieldLikeVectorized for Mersenne31ComplexVectorized {
    type Base = Mersenne31Complex;
    const SIZE_FACTOR: usize = WIDTH;

    #[inline(always)]
    fn constant(value: Self::Base) -> Self {
        Self {
            c0: Mersenne31FieldVectorized::constant(value.real_part()),
            c1: Mersenne31FieldVectorized::constant(value.imag_part()),
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
        let mut res = Self::default();
        for i in 0..Self::SIZE_FACTOR {
            res.c0.0[i] = input[i].real_part();
            res.c1.0[i] = input[i].imag_part();
        }
        res
    }

    fn as_base_array(&self) -> [Self::Base; Self::SIZE_FACTOR] {
        let mut res = [Self::Base::ZERO; Self::SIZE_FACTOR];
        for i in 0..Self::SIZE_FACTOR {
            res[i].c0 = self.c0.0[i];
            res[i].c1 = self.c1.0[i];
        }
        res
    }
}
