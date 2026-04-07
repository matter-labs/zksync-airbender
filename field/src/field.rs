use core::ops::{Index, IndexMut};

use super::*;
use rand::Rng;

pub trait Field:
    'static
    + Clone
    + Copy
    + Default
    + core::fmt::Display
    + core::fmt::Debug
    + core::hash::Hash
    + core::cmp::PartialEq
    + core::cmp::Eq
    + core::marker::Send
    + core::marker::Sync
    + core::default::Default
    + Rand
    + Sized
{
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    const MINUS_ONE: Self;

    type CharField = Self;

    // zero check
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn inverse(&self) -> Option<Self>;

    // add
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // sub
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // mul
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // square
    fn square(&'_ mut self) -> &'_ mut Self;
    // negate
    fn negate(&'_ mut self) -> &'_ mut Self;
    // double
    fn double(&'_ mut self) -> &'_ mut Self;

    fn pow(&self, mut exp: u32) -> Self {
        let mut base = *self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp % 2 == 1 {
                result.mul_assign(&base);
            }

            exp >>= 1;
            base.square();
        }

        result
    }

    fn exp_power_of_2(&mut self, power_log: usize) {
        for _ in 0..power_log {
            self.square();
        }
    }

    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        unimplemented!()
    }
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        unimplemented!()
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        // Default implementation
        self.mul_assign(a);
        self.add_assign(b);

        self
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_product(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        // Default implementation
        let mut t = *a;
        t.mul_assign(&b);
        self.add_assign(&t);

        self
    }
}

pub trait PrimeField: Field {
    const NUM_BYTES_IN_REPR: usize;

    const IS_MONT_REPR: bool;
    const MONT_K: u32;

    const CHAR_BITS: usize;
    const CHARACTERISTICS: u32;

    // Potentially unnormalized, but "natural" representation
    fn as_u32(self) -> u32;
    // < CHAR, but "natural" representation
    fn as_u32_reduced(self) -> u32;
    // any representation, that can be used with the corresponding constructor
    fn as_u32_raw_repr_reduced(self) -> u32;

    fn from_u32_unchecked(value: u32) -> Self;
    fn from_u32_with_reduction(value: u32) -> Self;
    fn from_u64_with_reduction(value: u64) -> Self {
        Self::from_u32_unchecked((value % (Self::CHARACTERISTICS as u64)) as u32)
    }
    fn from_u32(value: u32) -> Option<Self>;
    fn from_reduced_raw_repr(value: u32) -> Self;
    fn from_raw_repr_with_reduction(value: u32) -> Self;

    fn as_boolean(&self) -> bool;

    fn from_boolean(flag: bool) -> Self {
        if flag {
            Self::ONE
        } else {
            Self::ZERO
        }
    }

    fn increment_unchecked(&'_ mut self);
}

// this field can be used as base field for quadratic extension
pub trait BaseField<const N: usize>: Field {
    const NON_RESIDUE: Self;

    fn mul_by_non_residue(elem: &mut Self) {
        elem.mul_assign(&Self::NON_RESIDUE);
    }
}

pub trait FixedArrayConvertible<F: Field> {
    fn from_array<const N: usize>(array: [F; N]) -> Self;
    fn into_array<const N: usize>(self) -> [F; N];
    fn as_array<const N: usize>(&self) -> &[F; N];
    fn as_array_mut<const N: usize>(&mut self) -> &mut [F; N];
}

impl<F: Field, const M: usize> FixedArrayConvertible<F> for [F; M] {
    #[inline(always)]
    fn from_array<const N: usize>(array: [F; N]) -> Self {
        if N == M {
            unsafe {
                // Safety: we checked same size, so it's a transmute
                array.as_ptr().cast::<Self>().read()
            }
        } else {
            panic!(
                "invalid array size: internally it's [F; {}], requested [F; {}]",
                N, M
            );
        }
    }

    #[inline(always)]
    fn into_array<const N: usize>(self) -> [F; N] {
        if N == M {
            unsafe {
                // Safety: we checked same size, so it's a transmute
                self.as_ptr().cast::<[F; N]>().read()
            }
        } else {
            panic!(
                "invalid array size: internally it's [F; {}], requested [F; {}]",
                N, M
            );
        }
    }

    #[inline(always)]
    fn as_array<const N: usize>(&self) -> &[F; N] {
        if N == M {
            unsafe {
                // Safety: we checked same size, so it's a transmute
                self.as_ptr().cast::<[F; N]>().as_ref_unchecked()
            }
        } else {
            panic!(
                "invalid array size: internally it's [F; {}], requested [F; {}]",
                N, M
            );
        }
    }

    #[inline(always)]
    fn as_array_mut<const N: usize>(&mut self) -> &mut [F; N] {
        if N == M {
            unsafe {
                // Safety: we checked same size, so it's a transmute
                self.as_mut_ptr().cast::<[F; N]>().as_mut_unchecked()
            }
        } else {
            panic!(
                "invalid array size: internally it's [F; {}], requested [F; {}]",
                N, M
            );
        }
    }
}

pub trait FieldExtension<BaseField: Field>: 'static + Clone + Copy + Send + Sync {
    const DEGREE: usize;

    type Coeffs: 'static
        + Clone
        + Copy
        + core::fmt::Debug
        + Send
        + Sync
        + AsRef<[BaseField]>
        + AsMut<[BaseField]>
        + Index<usize, Output = BaseField>
        + IndexMut<usize, Output = BaseField>
        + FixedArrayConvertible<BaseField>;

    fn into_coeffs(self) -> Self::Coeffs;
    fn from_coeffs(coeffs: Self::Coeffs) -> Self;
    fn from_coeffs_ref(coeffs: &Self::Coeffs) -> Self;

    fn from_base(elem: BaseField) -> Self;

    fn add_assign_base(&mut self, elem: &BaseField) -> &mut Self;
    fn sub_assign_base(&mut self, elem: &BaseField) -> &mut Self;
    fn mul_assign_by_base(&mut self, elem: &BaseField) -> &mut Self;
}

impl<F: Field> FieldExtension<F> for F {
    const DEGREE: usize = 1;

    type Coeffs = [F; 1];

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs(self) -> Self::Coeffs {
        [self]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs(coeffs: Self::Coeffs) -> Self {
        coeffs[0]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_ref(coeffs: &Self::Coeffs) -> Self {
        coeffs[0]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: F) -> Self {
        elem
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &F) -> &mut Self {
        self.add_assign(elem)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &F) -> &mut Self {
        self.sub_assign(elem)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &F) -> &mut Self {
        self.mul_assign(elem)
    }
}

pub trait TwoAdicField: Field {
    /// The number of factors of two in this field's multiplicative group.
    const TWO_ADICITY: usize;

    /// Returns a generator of the multiplicative group of order `2^bits`.
    /// Assumes `bits < TWO_ADICITY`, otherwise the result is undefined.
    /// all functions here except for two_adic_generator should not even exist
    #[must_use]
    fn two_adic_generator() -> Self;

    #[must_use]
    fn two_adic_group_order() -> usize;

    const TWO_ADICITY_GENERATORS: &[Self];

    const TWO_ADICITY_GENERATORS_INVERSED: &[Self];
}

impl<F: PrimeField> Rand for F {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> F {
        F::from_u32_unchecked(rng.random_range(0..F::CHARACTERISTICS))
    }
}
