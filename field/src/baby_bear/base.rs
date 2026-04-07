// SPDX-License-Identifier: MIT OR Apache-2.0
// © 2026 Matter Labs

use super::ops;
use crate::field::{Field, PrimeField};
use core::ops::{Add, Sub};

#[derive(Clone, Copy, serde::Serialize, serde::Deserialize)]
#[repr(transparent)]
pub struct BabyBearField(pub u32);

const _: () = const {
    assert!(core::mem::size_of::<BabyBearField>() == core::mem::size_of::<u32>());
    assert!(core::mem::align_of::<BabyBearField>() == core::mem::align_of::<u32>());

    ()
};

// NOTE: We choose "standard" Montgomery multiplication, where integers at rest are < modulus

impl BabyBearField {
    pub const ORDER: u32 = 0x78000001; // 2^31 - 2^27 + 1 = 15 * 2^27 + 1
    pub(crate) const MONT_K: u32 = 0x77ffffff;
    const MONT_R: u32 = const {
        let r = (1u64 << 32) % (Self::ORDER as u64);
        r as u32
    };
    const MONT_R2: u32 = const {
        let r = (1u64 << 32) % (Self::ORDER as u64);
        let r2 = (r * r) % (Self::ORDER as u64);
        r2 as u32
    };
    const NON_RES: Self = Self::new(11);
    const HALF: Self = const { Self::new(2).inverse_impl().unwrap() };

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(value: u32) -> Self {
        debug_assert!(value < Self::ORDER);

        Self(ops::mul_mod(value, Self::MONT_R2))
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn to_u32(&self) -> u32 {
        ops::mul_mod(self.0, 1u32)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn raw_u32_value(&self) -> u32 {
        self.0
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_raw_u32(value: u32) -> Self {
        debug_assert!(value < Self::ORDER);

        Self(value)
    }

    pub const fn from_nonreduced_u32(c: u32) -> Self {
        // at most two subtractions needed
        let mut c = c;
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        Self::new(c)
    }
}

impl Default for BabyBearField {
    fn default() -> Self {
        Self(0u32)
    }
}

impl PartialEq for BabyBearField {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for BabyBearField {}

impl core::hash::Hash for BabyBearField {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.0)
    }
}

impl Ord for BabyBearField {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_u32().cmp(&other.to_u32())
    }
}

impl PartialOrd for BabyBearField {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::fmt::Display for BabyBearField {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.to_u32(), f)
    }
}

impl core::fmt::Debug for BabyBearField {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.to_u32(), f)
    }
}

impl BabyBearField {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_zero_impl(&self) -> bool {
        // one representations
        self.0 == 0
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_one_impl(&self) -> bool {
        // one representations
        self.0 == Self::MONT_R
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn exp_power_of_2_impl(&mut self, power_log: usize) {
        let mut i = 0;
        while i < power_log {
            self.square_impl();
            i += 1;
        }
    }

    pub(crate) const fn inverse_impl(&self) -> Option<Self> {
        // a^(p-2) - it's anyway expensive operation, but on platform with
        // field ops it is still faster than binary GCD

        if self.is_zero_impl() {
            return None;
        }

        #[inline(always)]
        const fn mul_by_value(this: BabyBearField, other: BabyBearField) -> BabyBearField {
            let mut result = this;
            result.mul_assign_impl(&other);

            result
        }

        #[inline(always)]
        const fn square_by_value(this: BabyBearField) -> BabyBearField {
            let mut result = this;
            result.square_impl();

            result
        }

        // 0x77ffffff = 0b111_0111_1111_1111_1111_1111_1111_1111

        // even though it's not the shortest, we just make it simple for now
        // 10
        let p_10 = square_by_value(*self);
        let p_11 = mul_by_value(p_10, *self);
        let p_110 = square_by_value(p_11);
        let p_111 = mul_by_value(p_110, *self);
        let p_1110 = square_by_value(p_111);
        let p_1111 = mul_by_value(p_1110, *self);

        let mut result = p_1110;
        result.square_impl();
        result.square_impl();
        result.square_impl();
        // 1110_000
        result.mul_assign_impl(&p_111);
        // now by 4
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.mul_assign_impl(&p_1111);

        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.mul_assign_impl(&p_1111);

        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.mul_assign_impl(&p_1111);

        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.mul_assign_impl(&p_1111);

        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.mul_assign_impl(&p_1111);

        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.square_impl();
        result.mul_assign_impl(&p_1111);

        Some(result)
    }

    pub fn sqrt(&self) -> Option<Self> {
        // p+1 = 2^31, and (p+1)/4 = 2^29
        let mut candidate = *self;
        candidate.exp_power_of_2(29);

        let mut t = candidate;
        t.square();
        if t == *self {
            Some(candidate)
        } else {
            None
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn add_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.0 = ops::add_mod(self.0, other.0);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn sub_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.0 = ops::sub_mod(self.0, other.0);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.0 = ops::mul_mod(self.0, other.0);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn square_impl(&'_ mut self) -> &'_ mut Self {
        let t = *self;
        self.mul_assign_impl(&t)
    }

    #[cfg(not(feature = "modular_ops"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&'_ mut self) -> &'_ mut Self {
        if self.0 != 0 {
            *self = Self(Self::ORDER - self.0);
        }
        self
    }

    #[cfg(feature = "modular_ops")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&'_ mut self) -> &'_ mut Self {
        self.0 = ops::sub_mod(0, self.0);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn double_impl(&'_ mut self) -> &'_ mut Self {
        self.0 = ops::add_mod(self.0, self.0);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn mul_by_non_residue_impl(elem: &mut Self) {
        elem.mul_assign_impl(&Self::NON_RES);
    }
}

impl Field for BabyBearField {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(Self::MONT_R);
    const TWO: Self = Self::new(2);
    const MINUS_ONE: Self = Self::new(Self::ORDER - 1);

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_zero(&self) -> bool {
        self.is_zero_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_one(&self) -> bool {
        self.is_one_impl()
    }

    fn inverse(&self) -> Option<Self> {
        self.inverse_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.add_assign_impl(other)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.sub_assign_impl(other)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.mul_assign_impl(other)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn square(&'_ mut self) -> &'_ mut Self {
        self.square_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&'_ mut self) -> &'_ mut Self {
        self.negate_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&'_ mut self) -> &'_ mut Self {
        self.double_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn exp_power_of_2(&mut self, power_log: usize) {
        self.exp_power_of_2_impl(power_log);
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        self.double_impl();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        self.mul_assign_impl(&Self::HALF)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        self.0 = ops::fma_mod(self.0, a.0, b.0);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_product(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        self.0 = ops::fma_mod(a.0, b.0, self.0);
        self
    }
}

impl Add for BabyBearField {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn add(self, rhs: Self) -> Self {
        let lhs = self;
        let mut res = lhs;
        res.add_assign(&rhs);
        res
    }
}

impl Sub for BabyBearField {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self;
        let rhs = rhs;
        let mut res = lhs;
        res.sub_assign(&rhs);
        res
    }
}

impl PrimeField for BabyBearField {
    const NUM_BYTES_IN_REPR: usize = 4;
    const CHAR_BITS: usize = 31;
    const CHARACTERISTICS: u32 = Self::ORDER;

    const IS_MONT_REPR: bool = true;
    const MONT_K: u32 = BabyBearField::MONT_K;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_u32(self) -> u32 {
        self.as_u32_reduced()
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_u32_reduced(self) -> u32 {
        self.to_u32()
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_u32_raw_repr_reduced(self) -> u32 {
        self.0
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_u32_unchecked(value: u32) -> Self {
        Self::new(value)
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_u32_with_reduction(value: u32) -> Self {
        Self::from_nonreduced_u32(value)
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_u32(value: u32) -> Option<Self> {
        if value >= Self::ORDER {
            None
        } else {
            Some(Self::new(value))
        }
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_reduced_raw_repr(value: u32) -> Self {
        Self(value)
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_raw_repr_with_reduction(value: u32) -> Self {
        // at most two subtractions needed
        let mut c = value;
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        Self(c)
    }
    #[track_caller]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_boolean(&self) -> bool {
        debug_assert!(
            self.0 == 0 || self.0 == Self::MONT_R,
            "expected boolean value, got {}",
            self.to_u32()
        );

        // in non-debug we can just compare to 1
        self.0 == Self::MONT_R
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_boolean(flag: bool) -> Self {
        Self(if flag { Self::MONT_R } else { 0 })
    }

    fn increment_unchecked(&'_ mut self) {
        self.0 += 1;
    }
}

impl crate::BaseField<2> for BabyBearField {
    const NON_RESIDUE: BabyBearField = BabyBearField::NON_RES;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_non_residue(elem: &mut Self) {
        Self::mul_by_non_residue_impl(elem);
    }
}

impl BabyBearField {
    pub const TWO_ADIC_GENERATOR: Self = Self::new(440564289);

    // enumerated such that TWO_ADICITY_GENERATORS[domain size log2] is a generator for the corresponding size
    pub const TWO_ADICITY_GENERATORS: [Self; 27 + 1] = const {
        let mut result = [Self::ZERO; 27 + 1];
        let mut current = Self::TWO_ADIC_GENERATOR;
        let mut i = 0;
        while i < 27 {
            result[27 - i] = current;
            current.square_impl();
            i += 1;
        }

        result[0] = current;

        result
    };

    pub const TWO_ADICITY_GENERATORS_INVERSED: [Self; 27 + 1] = const {
        let mut result = [Self::ZERO; 27 + 1];
        let mut i = 0;
        while i < 27 + 1 {
            result[i] = Self::TWO_ADICITY_GENERATORS[i].inverse_impl().unwrap();
            i += 1;
        }

        result
    };
}

impl crate::TwoAdicField for BabyBearField {
    const TWO_ADICITY: usize = 27;

    fn two_adic_generator() -> Self {
        Self::TWO_ADIC_GENERATOR
    }

    fn two_adic_group_order() -> usize {
        1 << 27
    }

    const TWO_ADICITY_GENERATORS: &[Self] = &Self::TWO_ADICITY_GENERATORS;

    const TWO_ADICITY_GENERATORS_INVERSED: &[Self] = &Self::TWO_ADICITY_GENERATORS_INVERSED;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn calculator() {
        let one = BabyBearField::ONE;
        // one = 268435454
        dbg!(one);
        dbg!(one.0);

        dbg!(BabyBearField::TWO_ADICITY_GENERATORS);
        dbg!(BabyBearField::TWO_ADICITY_GENERATORS_INVERSED);
    }

    #[test]
    fn test_inversion_chain() {
        let el = BabyBearField::new(42);
        let pow = BabyBearField::CHARACTERISTICS - 2;
        dbg!(pow);
        let naive_inverse = el.pow(pow);
        let faster_inverse = el.inverse_impl().unwrap();
        assert_eq!(naive_inverse, faster_inverse);
    }
}
