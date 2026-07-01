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
    pub(crate) const NON_RES: Self = Self::new(11);
    pub(crate) const NON_RES_DOUBLED: Self = Self::new(22);
    pub const HALF: Self = const { Self::new(2).inverse_impl().unwrap() };

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
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // we are always canonical, no reductions needed
        Ord::cmp(&self.0, &other.0)
    }
}

impl PartialOrd for BabyBearField {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
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
        // a^(p-2) — Fermat's little theorem. Faster than binary GCD on platforms
        // with native modular multiplication.

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

        // p - 2 = 0x77ffffff = 0b1110 followed by 27 ones (31 bits).
        // Addition chain (29 sqr + 8 mul = 37 ops):
        //   Build x^7, x^56, x^63, x^119 = 0b1110111 (top 7 bits of p-2).
        //   Then 4× [sqr^6, mul x^63] appends six 1-bits per round, filling
        //   the remaining 24 bits to land on 31.
        let x2 = square_by_value(*self);
        let x3 = mul_by_value(x2, *self);
        let x7 = mul_by_value(square_by_value(x3), *self); // x^6 · x
        let mut x56 = x7;
        x56.exp_power_of_2_impl(3); // x^7 << 3
        let x63 = mul_by_value(x56, x7); // x^56 · x^7 = x^63
        let mut result = mul_by_value(x63, x56); // x^63 · x^56 = x^119

        let mut i = 0;
        while i < 4 {
            result.exp_power_of_2_impl(6);
            result.mul_assign_impl(&x63);
            i += 1;
        }

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

    type CharField = Self;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_zero(&self) -> bool {
        self.is_zero_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_one(&self) -> bool {
        self.is_one_impl()
    }

    fn inverse(&self) -> Option<Self> {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_muls += 37);
        self.inverse_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_adds += 1);
        self.add_assign_impl(other)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_adds += 1);
        self.sub_assign_impl(other)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_muls += 1);
        self.mul_assign_impl(other)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn square(&'_ mut self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_muls += 1);
        self.square_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&'_ mut self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_adds += 1);
        self.negate_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&'_ mut self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_adds += 1);
        self.double_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn exp_power_of_2(&mut self, power_log: usize) {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_muls += power_log);
        self.exp_power_of_2_impl(power_log);
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_adds += 1);
        self.double_impl();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fbase_muls += 1);
        self.mul_assign_impl(&Self::HALF)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| {
            s.fbase_muls += 1;
            s.fbase_adds += 1;
        });
        self.0 = ops::fma_mod(self.0, a.0, b.0);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_product(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| {
            s.fbase_muls += 1;
            s.fbase_adds += 1;
        });
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
    const CHARACTERISTICS_U32: u32 = Self::ORDER;
    const CHARACTERISTICS_U128: u128 = Self::CHARACTERISTICS_U32 as u128;

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
    fn as_u32_raw_repr(self) -> u32 {
        self.0
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
    use crate::field::Field;
    use proptest::prelude::*;

    fn arb_babybear() -> impl Strategy<Value = u32> {
        0..BabyBearField::ORDER
    }

    #[test]
    fn test_inversion_chain() {
        let el = BabyBearField::new(42);
        let pow = BabyBearField::CHARACTERISTICS_U32 - 2;
        let naive_inverse = el.pow(pow);
        let faster_inverse = el.inverse_impl().unwrap();
        assert_eq!(naive_inverse, faster_inverse);
    }

    // --- Field axiom tests ---

    proptest! {
        #[test]
        fn add_commutative(a in arb_babybear(), b in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let fb = BabyBearField::new(b);
            let mut ab = fa; ab.add_assign(&fb);
            let mut ba = fb; ba.add_assign(&fa);
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn add_associative(a in arb_babybear(), b in arb_babybear(), c in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let fb = BabyBearField::new(b);
            let fc = BabyBearField::new(c);
            let mut ab = fa; ab.add_assign(&fb);
            let mut abc_left = ab; abc_left.add_assign(&fc);
            let mut bc = fb; bc.add_assign(&fc);
            let mut abc_right = fa; abc_right.add_assign(&bc);
            prop_assert_eq!(abc_left, abc_right);
        }

        #[test]
        fn add_identity(a in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let mut r = fa;
            r.add_assign(&BabyBearField::ZERO);
            prop_assert_eq!(r, fa);
        }

        #[test]
        fn add_inverse(a in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let mut neg = fa; neg.negate();
            let mut sum = fa; sum.add_assign(&neg);
            prop_assert_eq!(sum, BabyBearField::ZERO);
        }

        #[test]
        fn mul_commutative(a in arb_babybear(), b in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let fb = BabyBearField::new(b);
            let mut ab = fa; ab.mul_assign(&fb);
            let mut ba = fb; ba.mul_assign(&fa);
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn mul_associative(a in arb_babybear(), b in arb_babybear(), c in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let fb = BabyBearField::new(b);
            let fc = BabyBearField::new(c);
            let mut ab = fa; ab.mul_assign(&fb);
            let mut abc_left = ab; abc_left.mul_assign(&fc);
            let mut bc = fb; bc.mul_assign(&fc);
            let mut abc_right = fa; abc_right.mul_assign(&bc);
            prop_assert_eq!(abc_left, abc_right);
        }

        #[test]
        fn mul_identity(a in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let mut r = fa;
            r.mul_assign(&BabyBearField::ONE);
            prop_assert_eq!(r, fa);
        }

        #[test]
        fn mul_inverse(a in 1..BabyBearField::ORDER) {
            let fa = BabyBearField::new(a);
            let inv = fa.inverse().unwrap();
            let mut product = fa;
            product.mul_assign(&inv);
            prop_assert_eq!(product, BabyBearField::ONE);
        }

        #[test]
        fn inverse_matches_fermat(a in 1..BabyBearField::ORDER) {
            let fa = BabyBearField::new(a);
            let chain = fa.inverse().unwrap();
            let fermat = fa.pow(BabyBearField::CHARACTERISTICS_U32 - 2);
            prop_assert_eq!(chain, fermat);
        }

        #[test]
        fn distributive(a in arb_babybear(), b in arb_babybear(), c in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let fb = BabyBearField::new(b);
            let fc = BabyBearField::new(c);
            let mut bc = fb; bc.add_assign(&fc);
            let mut left = fa; left.mul_assign(&bc);
            let mut ab = fa; ab.mul_assign(&fb);
            let mut ac = fa; ac.mul_assign(&fc);
            let mut right = ab; right.add_assign(&ac);
            prop_assert_eq!(left, right);
        }

        #[test]
        fn sub_is_add_neg(a in arb_babybear(), b in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let fb = BabyBearField::new(b);
            let mut via_sub = fa; via_sub.sub_assign(&fb);
            let mut neg_b = fb; neg_b.negate();
            let mut via_add = fa; via_add.add_assign(&neg_b);
            prop_assert_eq!(via_sub, via_add);
        }

        #[test]
        fn double_is_add_self(a in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let mut doubled = fa; doubled.double();
            let mut added = fa; added.add_assign(&fa);
            prop_assert_eq!(doubled, added);
        }

        #[test]
        fn square_is_mul_self(a in arb_babybear()) {
            let fa = BabyBearField::new(a);
            let mut squared = fa; squared.square();
            let mut mulled = fa; mulled.mul_assign(&fa);
            prop_assert_eq!(squared, mulled);
        }
    }

    // --- Const value and generator tests ---

    #[test]
    fn two_adicity_generators_are_valid() {
        for k in 1..=27 {
            let g = BabyBearField::TWO_ADICITY_GENERATORS[k];
            let mut powered = g;
            for _ in 0..k {
                powered.square();
            }
            assert_eq!(powered, BabyBearField::ONE, "generator[{k}]^(2^{k}) != 1");

            let mut half_powered = g;
            for _ in 0..k - 1 {
                half_powered.square();
            }
            assert_ne!(
                half_powered,
                BabyBearField::ONE,
                "generator[{k}] has order < 2^{k}"
            );
        }
    }

    #[test]
    fn two_adicity_generators_inversed_are_correct() {
        for k in 0..=27 {
            let g = BabyBearField::TWO_ADICITY_GENERATORS[k];
            let g_inv = BabyBearField::TWO_ADICITY_GENERATORS_INVERSED[k];
            let mut product = g;
            product.mul_assign(&g_inv);
            assert_eq!(
                product,
                BabyBearField::ONE,
                "generator[{k}] * inverse[{k}] != 1"
            );
        }
    }

    #[test]
    fn const_values_are_correct() {
        assert_eq!(BabyBearField::NON_RES.to_u32(), 11);

        let mut two_halves = BabyBearField::HALF;
        two_halves.double();
        assert_eq!(two_halves, BabyBearField::ONE);

        assert_eq!(BabyBearField::TWO.to_u32(), 2);

        let mut should_be_zero = BabyBearField::MINUS_ONE;
        should_be_zero.add_assign(&BabyBearField::ONE);
        assert_eq!(should_be_zero, BabyBearField::ZERO);
    }
}
