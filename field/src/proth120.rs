// SPDX-License-Identifier: MIT OR Apache-2.0
// © 2026 Matter Labs

//! The prime field `F_p` where `p = 7 * 2^120 + 1`.
//!
//! This is a 123-bit Proth prime, so a single element does not fit into the
//! `u32`-centric [`PrimeField`](crate::PrimeField) abstraction used by the
//! 31-bit fields in this crate. Instead `Proth120` is a self-contained field
//! that stores its element as a `u128` in Montgomery form (`value * R mod p`
//! with `R = 2^128`) and implements the generic [`Field`](crate::Field) trait.
//!
//! Multiplication uses Montgomery reduction (CIOS over two 64-bit limbs). No
//! extensions are defined over this field.

use crate::PrimeField;
use crate::field::Field;
use crate::Rand;
use crate::TwoAdicField;
use core::ops::{Add, Sub};
use rand::Rng;

/// The prime field `F_p` where `p = 7 * 2^120 + 1`.
///
/// The wrapped `u128` is the Montgomery representation `value * 2^128 mod p`
/// and is always kept canonical (strictly less than the modulus).
#[derive(Clone, Copy, serde::Serialize, serde::Deserialize)]
#[repr(transparent)]
pub struct Proth120(pub u128);

const _: () = const {
    assert!(core::mem::size_of::<Proth120>() == core::mem::size_of::<u128>());
    assert!(core::mem::align_of::<Proth120>() == core::mem::align_of::<u128>());

    ()
};

// --- 128-bit limb helpers used by the Montgomery routines ---

/// `a + b * c + carry`, returning `(low_64, high_64)`.
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + (b as u128) * (c as u128) + carry as u128;
    (t as u64, (t >> 64) as u64)
}

/// `a + b + carry`, returning `(low_64, carry_out)`.
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

/// `a - b - borrow`, returning `(low_64, borrow_out)`.
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let (d, b0) = a.overflowing_sub(b);
    let (d, b1) = d.overflowing_sub(borrow);
    (d, (b0 || b1) as u64)
}

impl Proth120 {
    /// The modulus `p = 7 * 2^120 + 1`.
    pub const ORDER: u128 = (7u128 << 120) + 1;
    /// Number of bits in the modulus (`p < 2^123`).
    pub const CHAR_BITS: usize = 123;

    /// Low 64-bit limb of the modulus (`p mod 2^64 == 1`).
    const P_LO: u64 = Self::ORDER as u64;
    /// High 64-bit limb of the modulus (`7 * 2^56`).
    const P_HI: u64 = (Self::ORDER >> 64) as u64;

    /// `-p^{-1} mod 2^64`. Since `p ≡ 1 (mod 2^64)` this is simply `2^64 - 1`.
    const MONT_K: u64 = u64::MAX;

    /// `R mod p` with `R = 2^128`. Equal to the Montgomery form of `1`.
    const MONT_R: u128 = const {
        // 2^128 mod p via 128 doublings starting from 1.
        let mut x = 1u128;
        let mut i = 0;
        while i < 128 {
            x = double_mod_order(x);
            i += 1;
        }
        x
    };

    /// `R^2 mod p` with `R = 2^128`. Used to enter Montgomery form.
    const MONT_R2: u128 = const {
        // 2^256 mod p — continue doubling `MONT_R` another 128 times.
        let mut x = Self::MONT_R;
        let mut i = 0;
        while i < 128 {
            x = double_mod_order(x);
            i += 1;
        }
        x
    };

    /// Constructs a field element from its natural (non-Montgomery) value.
    ///
    /// `value` must already be reduced (`value < ORDER`).
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(value: u128) -> Self {
        debug_assert!(value < Self::ORDER);

        // value * R^2 * R^{-1} = value * R = Montgomery(value)
        Self(mont_mul(value, Self::MONT_R2))
    }

    /// Returns the natural (non-Montgomery) value in `[0, ORDER)`.
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn to_u128(&self) -> u128 {
        // value * R * R^{-1} = value
        mont_mul(self.0, 1u128)
    }

    /// Returns the raw Montgomery representation.
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn raw_u128_value(&self) -> u128 {
        self.0
    }

    /// Wraps a raw (already Montgomery-form, canonical) representation.
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_raw_u128(value: u128) -> Self {
        debug_assert!(value < Self::ORDER);

        Self(value)
    }

    /// Constructs from a possibly non-reduced natural value.
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_u128_with_reduction(value: u128) -> Self {
        Self::new(value % Self::ORDER)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_zero_impl(&self) -> bool {
        self.0 == 0
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_one_impl(&self) -> bool {
        self.0 == Self::MONT_R
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn add_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        // both operands are < p < 2^123, so the sum fits into a u128.
        let mut sum = self.0 + other.0;
        if sum >= Self::ORDER {
            sum -= Self::ORDER;
        }
        self.0 = sum;
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn sub_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        let (diff, uf) = self.0.overflowing_sub(other.0);
        self.0 = if uf {
            diff.wrapping_add(Self::ORDER)
        } else {
            diff
        };
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.0 = mont_mul(self.0, other.0);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn square_impl(&'_ mut self) -> &'_ mut Self {
        self.0 = mont_mul(self.0, self.0);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&'_ mut self) -> &'_ mut Self {
        if self.0 != 0 {
            self.0 = Self::ORDER - self.0;
        }
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn double_impl(&'_ mut self) -> &'_ mut Self {
        let mut sum = self.0 + self.0;
        if sum >= Self::ORDER {
            sum -= Self::ORDER;
        }
        self.0 = sum;
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    const fn mul_by_value(self, other: Self) -> Self {
        Self(mont_mul(self.0, other.0))
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    const fn square_by_value(self) -> Self {
        Self(mont_mul(self.0, self.0))
    }

    /// Raises `self` to an arbitrary `u128` exponent via square-and-multiply.
    pub const fn pow_u128(&self, mut exp: u128) -> Self {
        let mut base = *self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.mul_by_value(base);
            }
            exp >>= 1;
            base = base.square_by_value();
        }
        result
    }

    pub(crate) const fn inverse_impl(&self) -> Option<Self> {
        if self.is_zero_impl() {
            return None;
        }

        // Fermat's little theorem: a^{p-2}. `p - 2 = 7 * 2^120 - 1`.
        Some(self.pow_u128(Self::ORDER - 2))
    }
}

/// Doubles `x` modulo [`Proth120::ORDER`], assuming `x < ORDER`.
///
/// `2x < 2^124` always fits into a `u128`, so this never overflows.
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn double_mod_order(x: u128) -> u128 {
    let two_x = x << 1;
    if two_x >= Proth120::ORDER {
        two_x - Proth120::ORDER
    } else {
        two_x
    }
}

/// Montgomery multiplication of two canonical elements (`a, b < ORDER`).
///
/// Returns `a * b * R^{-1} mod p` with `R = 2^128`, using the CIOS variant of
/// Montgomery reduction over two 64-bit limbs. The result is canonical.
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn mont_mul(a: u128, b: u128) -> u128 {
    let a = [a as u64, (a >> 64) as u64];
    let b = [b as u64, (b >> 64) as u64];
    let n = [Proth120::P_LO, Proth120::P_HI];
    let np = Proth120::MONT_K;

    // t holds an intermediate of up to (2 + 2) limbs; t[3] is scratch carry.
    let mut t = [0u64; 4];

    let mut i = 0;
    while i < 2 {
        // --- multiplication pass: t += a * b[i] ---
        let mut c;
        let (s, cc) = mac(t[0], a[0], b[i], 0);
        t[0] = s;
        c = cc;
        let (s, cc) = mac(t[1], a[1], b[i], c);
        t[1] = s;
        c = cc;
        let (s, cc) = adc(t[2], c, 0);
        t[2] = s;
        t[3] = cc;

        // --- reduction pass: m = t[0] * (-p^{-1}); t = (t + m * p) / 2^64 ---
        let m = t[0].wrapping_mul(np);
        // low limb is forced to zero and dropped (this is the division by 2^64).
        let (_zero, cc) = mac(t[0], m, n[0], 0);
        c = cc;
        let (s, cc) = mac(t[1], m, n[1], c);
        t[0] = s;
        c = cc;
        let (s, cc) = adc(t[2], c, 0);
        t[1] = s;
        t[2] = t[3].wrapping_add(cc);

        i += 1;
    }

    // The accumulated value `t[0] + t[1]·2^64 + t[2]·2^128` is < 2p; subtract p
    // once if needed. `t[2]` is the overflow bit (0 or 1).
    let (r0, brw) = sbb(t[0], n[0], 0);
    let (r1, brw) = sbb(t[1], n[1], brw);

    if t[2] < brw {
        // value < p — keep the un-subtracted limbs.
        (t[0] as u128) | ((t[1] as u128) << 64)
    } else {
        (r0 as u128) | ((r1 as u128) << 64)
    }
}

impl Default for Proth120 {
    fn default() -> Self {
        Self(0u128)
    }
}

impl PartialEq for Proth120 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for Proth120 {}

impl core::hash::Hash for Proth120 {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write_u128(self.0)
    }
}

impl Ord for Proth120 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // representations are always canonical
        Ord::cmp(&self.0, &other.0)
    }
}

impl PartialOrd for Proth120 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::fmt::Display for Proth120 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.to_u128(), f)
    }
}

impl core::fmt::Debug for Proth120 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.to_u128(), f)
    }
}

impl Add for Proth120 {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn add(self, rhs: Self) -> Self {
        let mut res = self;
        res.add_assign_impl(&rhs);
        res
    }
}

impl Sub for Proth120 {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn sub(self, rhs: Self) -> Self {
        let mut res = self;
        res.sub_assign_impl(&rhs);
        res
    }
}

impl Rand for Proth120 {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
        let lo: u64 = rng.random();
        let hi: u64 = rng.random();
        let value = ((hi as u128) << 64) | (lo as u128);
        Self::new(value % Self::ORDER)
    }
}

impl Field for Proth120 {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(Self::MONT_R);
    const TWO: Self = Self::new(2);
    const MINUS_ONE: Self = Self(Self::ORDER - Self::MONT_R);

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
}

// --- Two-adic (FFT) parameters ---
//
// `p - 1 = 7 * 2^120`, so the multiplicative group has a 2-Sylow subgroup of
// order `2^120` and the field supports FFTs on domains up to size `2^120`.

impl Proth120 {
    /// A primitive `2^120`-th root of unity (generator of the full 2-Sylow
    /// subgroup of `F_p^*`).
    ///
    /// Computed as `g^7` where `g` is the smallest quadratic non-residue:
    /// since `(p - 1) / 2^120 = 7`, raising any quadratic non-residue to the
    /// 7-th power yields an element of order exactly `2^120`.
    pub const TWO_ADIC_GENERATOR: Self = const {
        // (p - 1) / 2 — exponent used to test the Legendre symbol.
        let exp_legendre = (Self::ORDER - 1) >> 1;
        let mut cand = 2u128;
        loop {
            let g = Self::new(cand);
            // g^((p-1)/2) is ±1; it equals -1 exactly for non-residues.
            if g.pow_u128(exp_legendre).0 == Self::MINUS_ONE.0 {
                break g.pow_u128(7);
            }
            cand += 1;
        }
    };

    /// `TWO_ADICITY_GENERATORS[k]` is a generator of the multiplicative
    /// subgroup of order `2^k` (i.e. a primitive `2^k`-th root of unity), for
    /// `k` in `0..=120`. Index `0` is the identity.
    pub const TWO_ADICITY_GENERATORS: [Self; 120 + 1] = const {
        let mut result = [Self::ZERO; 120 + 1];
        let mut current = Self::TWO_ADIC_GENERATOR;
        let mut i = 0;
        while i < 120 {
            result[120 - i] = current;
            current.square_impl();
            i += 1;
        }
        // squared down to order 1
        result[0] = current;

        result
    };

    /// Multiplicative inverses of [`Self::TWO_ADICITY_GENERATORS`].
    pub const TWO_ADICITY_GENERATORS_INVERSED: [Self; 120 + 1] = const {
        let mut result = [Self::ZERO; 120 + 1];
        // It suffices to invert the top generator once; the inverse of a
        // squared-down generator is the square of the top inverse, because
        // `(g^2)^{-1} = (g^{-1})^2`.
        let mut current = match Self::TWO_ADICITY_GENERATORS[120].inverse_impl() {
            Some(v) => v,
            None => panic!("two-adic generator must be invertible"),
        };
        let mut i = 0;
        while i < 120 {
            result[120 - i] = current;
            current.square_impl();
            i += 1;
        }
        result[0] = current;

        result
    };
}

impl TwoAdicField for Proth120 {
    const TWO_ADICITY: usize = 120;

    fn two_adic_generator() -> Self {
        Self::TWO_ADIC_GENERATOR
    }

    fn two_adic_group_order() -> usize {
        // The true 2-Sylow order is `2^120`, which does not fit into a `usize`.
        // This accessor is unused for fields this large; panic rather than
        // silently return a wrapped (incorrect) value.
        unimplemented!("Proth120 two-adic group order (2^120) does not fit into usize")
    }

    const TWO_ADICITY_GENERATORS: &[Self] = &Self::TWO_ADICITY_GENERATORS;

    const TWO_ADICITY_GENERATORS_INVERSED: &[Self] = &Self::TWO_ADICITY_GENERATORS_INVERSED;
}

impl PrimeField for Proth120 {
    const NUM_BYTES_IN_REPR: usize = 16;

    const IS_MONT_REPR: bool = true;
    const MONT_K: u32 = u32::MAX;

    const CHAR_BITS: usize = 123;
    const CHARACTERISTICS_U32: u32 = u32::MAX;
    const CHARACTERISTICS_U128: u128 = 9304595970494411110326649421962412033;

    // Potentially unnormalized, but "natural" representation
    fn as_u32(self) -> u32 {
        unreachable!()
    }
    // < CHAR, but "natural" representation
    fn as_u32_reduced(self) -> u32 {
        unreachable!()
    }
    // any representation, without reduction guarantees. To be used for roundtrips
    // over newly constructed elements
    fn as_u32_raw_repr(self) -> u32 {
        unreachable!()
    }
    // any representation, that can be used with the corresponding constructor
    fn as_u32_raw_repr_reduced(self) -> u32 {
        unreachable!()
    }

    fn as_u128_reduced(self) -> u128 {
        self.to_u128()
    }

    fn from_u32_unchecked(value: u32) -> Self {
        unreachable!()
    }
    fn from_u32_with_reduction(value: u32) -> Self {
        unreachable!()
    }
    fn from_u128_with_reduction(value: u128) -> Self {
        Self::new(value % Self::CHARACTERISTICS_U128)
    }
    fn from_u32(value: u32) -> Option<Self> {
        unreachable!()
    }
    fn from_reduced_raw_repr(value: u32) -> Self {
        unreachable!()
    }
    fn from_raw_repr_with_reduction(value: u32) -> Self {
        unreachable!()
    }

    fn as_boolean(&self) -> bool {
        debug_assert!(
            self.0 == 0 || self.0 == Self::MONT_R,
            "expected boolean value, got {}",
            self.as_u128_reduced()
        );

        // in non-debug we can just compare to 1
        self.0 == Self::MONT_R
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    const P: u128 = Proth120::ORDER;

    // Independent reference modular multiplication via double-and-add. Operands
    // and modulus are < 2^123, so every intermediate `add` fits into a u128.
    fn mulmod_ref(a: u128, b: u128) -> u128 {
        let mut a = a % P;
        let mut b = b % P;
        let mut r = 0u128;
        while b > 0 {
            if b & 1 == 1 {
                r += a;
                if r >= P {
                    r -= P;
                }
            }
            a <<= 1;
            if a >= P {
                a -= P;
            }
            b >>= 1;
        }
        r
    }

    fn arb_proth120() -> impl Strategy<Value = u128> {
        any::<u128>().prop_map(|x| x % P)
    }

    #[test]
    fn modulus_value_is_correct() {
        assert_eq!(P, 7u128 * (1u128 << 120) + 1);
        assert_eq!(Proth120::P_LO, 1);
        assert_eq!(Proth120::P_HI, 7u64 << 56);
    }

    #[test]
    fn roundtrip_montgomery() {
        for v in [0u128, 1, 2, 42, P - 1, P / 2, (1u128 << 120)] {
            assert_eq!(Proth120::new(v).to_u128(), v);
        }
    }

    #[test]
    fn const_values_are_correct() {
        assert_eq!(Proth120::ZERO.to_u128(), 0);
        assert_eq!(Proth120::ONE.to_u128(), 1);
        assert_eq!(Proth120::TWO.to_u128(), 2);
        assert_eq!(Proth120::MINUS_ONE.to_u128(), P - 1);

        let mut should_be_zero = Proth120::MINUS_ONE;
        should_be_zero.add_assign(&Proth120::ONE);
        assert_eq!(should_be_zero, Proth120::ZERO);

        assert!(Proth120::ONE.is_one());
        assert!(Proth120::ZERO.is_zero());
    }

    proptest! {
        #[test]
        fn mul_matches_reference(a in arb_proth120(), b in arb_proth120()) {
            let fa = Proth120::new(a);
            let fb = Proth120::new(b);
            let mut prod = fa;
            prod.mul_assign(&fb);
            prop_assert_eq!(prod.to_u128(), mulmod_ref(a, b));
        }

        #[test]
        fn add_matches_reference(a in arb_proth120(), b in arb_proth120()) {
            let fa = Proth120::new(a);
            let fb = Proth120::new(b);
            let mut sum = fa;
            sum.add_assign(&fb);
            prop_assert_eq!(sum.to_u128(), (a + b) % P);
        }

        #[test]
        fn sub_matches_reference(a in arb_proth120(), b in arb_proth120()) {
            let fa = Proth120::new(a);
            let fb = Proth120::new(b);
            let mut diff = fa;
            diff.sub_assign(&fb);
            prop_assert_eq!(diff.to_u128(), (a + P - b) % P);
        }

        #[test]
        fn mul_commutative(a in arb_proth120(), b in arb_proth120()) {
            let fa = Proth120::new(a);
            let fb = Proth120::new(b);
            let mut ab = fa; ab.mul_assign(&fb);
            let mut ba = fb; ba.mul_assign(&fa);
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn mul_associative(a in arb_proth120(), b in arb_proth120(), c in arb_proth120()) {
            let fa = Proth120::new(a);
            let fb = Proth120::new(b);
            let fc = Proth120::new(c);
            let mut ab = fa; ab.mul_assign(&fb);
            let mut abc_left = ab; abc_left.mul_assign(&fc);
            let mut bc = fb; bc.mul_assign(&fc);
            let mut abc_right = fa; abc_right.mul_assign(&bc);
            prop_assert_eq!(abc_left, abc_right);
        }

        #[test]
        fn mul_identity(a in arb_proth120()) {
            let fa = Proth120::new(a);
            let mut r = fa;
            r.mul_assign(&Proth120::ONE);
            prop_assert_eq!(r, fa);
        }

        #[test]
        fn distributive(a in arb_proth120(), b in arb_proth120(), c in arb_proth120()) {
            let fa = Proth120::new(a);
            let fb = Proth120::new(b);
            let fc = Proth120::new(c);
            let mut bc = fb; bc.add_assign(&fc);
            let mut left = fa; left.mul_assign(&bc);
            let mut ab = fa; ab.mul_assign(&fb);
            let mut ac = fa; ac.mul_assign(&fc);
            let mut right = ab; right.add_assign(&ac);
            prop_assert_eq!(left, right);
        }

        #[test]
        fn mul_inverse(a in 1u128..P) {
            let fa = Proth120::new(a);
            let inv = fa.inverse().unwrap();
            let mut product = fa;
            product.mul_assign(&inv);
            prop_assert_eq!(product, Proth120::ONE);
        }

        #[test]
        fn square_is_mul_self(a in arb_proth120()) {
            let fa = Proth120::new(a);
            let mut squared = fa; squared.square();
            let mut mulled = fa; mulled.mul_assign(&fa);
            prop_assert_eq!(squared, mulled);
        }

        #[test]
        fn negate_is_additive_inverse(a in arb_proth120()) {
            let fa = Proth120::new(a);
            let mut neg = fa; neg.negate();
            let mut sum = fa; sum.add_assign(&neg);
            prop_assert_eq!(sum, Proth120::ZERO);
        }

        #[test]
        fn double_is_add_self(a in arb_proth120()) {
            let fa = Proth120::new(a);
            let mut doubled = fa; doubled.double();
            let mut added = fa; added.add_assign(&fa);
            prop_assert_eq!(doubled, added);
        }
    }

    #[test]
    fn zero_has_no_inverse() {
        assert!(Proth120::ZERO.inverse().is_none());
    }

    // --- Two-adic (FFT) parameter tests ---

    #[test]
    fn two_adicity_is_correct() {
        assert_eq!(Proth120::TWO_ADICITY, 120);
        // p - 1 = 7 * 2^120, so the 2-Sylow subgroup has order exactly 2^120.
        assert_eq!(P - 1, 7u128 << 120);
    }

    #[test]
    fn primitive_root_has_full_order() {
        let g = Proth120::two_adic_generator();
        // g^(2^120) == 1
        let mut t = g;
        t.exp_power_of_2(120);
        assert_eq!(t, Proth120::ONE);
        // g^(2^119) != 1 (order is exactly 2^120, not a proper divisor)
        let mut t = g;
        t.exp_power_of_2(119);
        assert_ne!(t, Proth120::ONE);
    }

    #[test]
    fn two_adicity_generators_are_valid() {
        for k in 1..=120 {
            let g = Proth120::TWO_ADICITY_GENERATORS[k];
            let mut powered = g;
            powered.exp_power_of_2(k);
            assert_eq!(powered, Proth120::ONE, "generator[{k}]^(2^{k}) != 1");

            let mut half_powered = g;
            half_powered.exp_power_of_2(k - 1);
            assert_ne!(
                half_powered,
                Proth120::ONE,
                "generator[{k}] has order < 2^{k}"
            );
        }
        assert_eq!(Proth120::TWO_ADICITY_GENERATORS[0], Proth120::ONE);
    }

    #[test]
    fn two_adicity_generators_inversed_are_correct() {
        for k in 0..=120 {
            let g = Proth120::TWO_ADICITY_GENERATORS[k];
            let g_inv = Proth120::TWO_ADICITY_GENERATORS_INVERSED[k];
            let mut product = g;
            product.mul_assign(&g_inv);
            assert_eq!(product, Proth120::ONE, "generator[{k}] * inverse[{k}] != 1");
        }
    }

    #[test]
    fn generators_are_successive_squares() {
        // generator[k-1] == generator[k]^2
        for k in 1..=120 {
            let mut sq = Proth120::TWO_ADICITY_GENERATORS[k];
            sq.square();
            assert_eq!(sq, Proth120::TWO_ADICITY_GENERATORS[k - 1]);
        }
    }
}
