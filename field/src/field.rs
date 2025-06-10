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
    const TWO: Self;
    const MINUS_ONE: Self;
    const NUM_BYTES_IN_REPR: usize;

    const CHAR_BITS: usize;
    const CHARACTERISTICS: u64;

    fn as_u64(self) -> u64;
    fn from_u64_unchecked(value: u64) -> Self;
    fn from_u64_with_reduction(value: u64) -> Self;
    fn from_u64(value: u64) -> Option<Self>;
    fn as_u64_reduced(&self) -> u64;

    fn as_boolean(&self) -> bool;

    fn from_boolean(flag: bool) -> Self {
        if flag {
            Self::ONE
        } else {
            Self::ZERO
        }
    }

    fn to_le_bytes(self) -> [u8; Self::NUM_BYTES_IN_REPR];

    fn increment_unchecked(&'_ mut self);
}

// this field can be used as base field for quadratic extension
pub trait BaseField: Field {
    const QUADRATIC_NON_RESIDUE: Self;

    fn mul_by_non_residue(elem: &mut Self) {
        elem.mul_assign(&Self::QUADRATIC_NON_RESIDUE);
    }
}

pub trait FieldExtension<BaseField: Field> {
    const DEGREE: usize;
    fn mul_assign_by_base(&mut self, elem: &BaseField) -> &mut Self;
    fn into_coeffs_in_base(self) -> [BaseField; Self::DEGREE];
    fn from_base_coeffs_array(coefs: &[BaseField; Self::DEGREE]) -> Self;
    fn from_coeffs_in_base(coefs: &[BaseField]) -> Self;
    fn from_coeffs_in_base_ref(coefs: &[&BaseField]) -> Self;
    fn from_coeffs_in_base_iter<I: Iterator<Item = BaseField>>(coefs_iter: I) -> Self;
    fn coeffs_in_base(&self) -> &[BaseField];
    fn add_assign_base(&mut self, elem: &BaseField) -> &mut Self;
    fn sub_assign_base(&mut self, elem: &BaseField) -> &mut Self;
    fn from_base(elem: BaseField) -> Self;
    fn get_coef_mut(&mut self, idx: usize) -> &mut BaseField;
}

impl<F: Field> FieldExtension<F> for F {
    const DEGREE: usize = 1;
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base(coefs: &[F]) -> Self {
        coefs[0]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base_coeffs_array(coefs: &[F; Self::DEGREE]) -> Self {
        coefs[0]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_ref(coefs: &[&F]) -> Self {
        *coefs[0]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs_in_base(self) -> [Self; Self::DEGREE] {
        // Rust compiler is bugging here, not relating Self::DEGREE and 1
        unsafe { core::ptr::read((&self as *const F).cast()) }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_iter<I: Iterator<Item = F>>(mut coefs_iter: I) -> Self {
        coefs_iter.next().unwrap()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn coeffs_in_base(&self) -> &[F] {
        core::slice::from_ref(self)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &F) -> &mut Self {
        self.mul_assign(elem)
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
    fn from_base(elem: F) -> Self {
        elem
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn get_coef_mut(&mut self, idx: usize) -> &mut F {
        assert_eq!(idx, 0);
        self
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
}

impl<F: PrimeField> Rand for F {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> F {
        F::from_u64_unchecked(rng.random_range(0..F::CHARACTERISTICS))
    }
}
