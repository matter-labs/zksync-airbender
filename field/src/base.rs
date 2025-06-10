// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.

use super::*;
use crate::ops;
use core::ops::{Add, Sub};

// If we use divisions for reduction (that makes sense on M1 family and in proved environment),
// then representation of the field element is always canonical, other wise it's <= MODULUS (so zero has two representations)

#[derive(Clone, Copy, serde::Serialize, serde::Deserialize)]
#[repr(transparent)]
pub struct Mersenne31Field(pub u32);

const _: () = const {
    assert!(core::mem::size_of::<Mersenne31Field>() == core::mem::size_of::<u32>());
    assert!(core::mem::align_of::<Mersenne31Field>() == core::mem::align_of::<u32>());

    ()
};

impl Mersenne31Field {
    pub const ORDER: u32 = (1 << 31) - 1;
    pub const MSBITMASK: u32 = 1 << 31;

    #[cfg(not(feature = "use_division"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(value: u32) -> Self {
        debug_assert!((value >> 31) == 0);

        Self(value)
    }

    #[cfg(feature = "use_division")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(value: u32) -> Self {
        debug_assert!(value < Self::ORDER);

        Self(value)
    }

    #[cfg(not(feature = "use_division"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn to_reduced_u32(&self) -> u32 {
        // our canonical representation is 0..=modulus (31 bits full range), but not larger
        if self.0 == Self::ORDER {
            0
        } else {
            self.0
        }

        // let mut c = self.0;
        // if c >= Self::ORDER {
        //     c -= Self::ORDER;
        // }
        // c
    }

    #[cfg(feature = "use_division")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn to_reduced_u32(&self) -> u32 {
        self.0
    }

    #[cfg(not(feature = "use_division"))]
    pub const fn from_nonreduced_u32(c: u32) -> Self {
        let mut c = c;
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        Self::new(c)
    }

    #[cfg(feature = "use_division")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_nonreduced_u32(c: u32) -> Self {
        Self(ops::reduce_with_division(c))
    }

    pub const fn mul_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, multiplication by 2^k is just a left rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = (self.0 << exp) & ((1 << 31) - 1);
        let right = self.0 >> (31 - exp);
        let rotated = left | right;
        Self::new(rotated)
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    pub const fn div_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, division by 2^k is just a right rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = self.0 >> exp;
        let right = (self.0 << (31 - exp)) & ((1 << 31) - 1);
        let rotated = left | right;
        Self::new(rotated)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_negative_u64_with_reduction(x: u64) -> Self {
        let x_low = (x as u32) & ((1 << 31) - 1);
        let x_high = ((x >> 31) as u32) & ((1 << 31) - 1);
        let x_sign = (x >> 63) as u32;
        let res_wrapped = x_low.wrapping_add(x_high);
        let res_wrapped = res_wrapped - x_sign;
        let msb = res_wrapped & (1 << 31);
        let mut sum = res_wrapped;
        sum ^= msb;
        let mut res = sum + (msb != 0) as u32;
        if res >= Self::ORDER {
            res -= Self::ORDER;
        }
        Mersenne31Field(res)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_u62(x: u64) -> Self {
        let product_low = (x as u32) & ((1 << 31) - 1);
        let product_high = (x >> 31) as u32;
        let result = ops::add_mod(product_low, product_high);

        Self(result)
    }
}

impl Default for Mersenne31Field {
    fn default() -> Self {
        Self(0u32)
    }
}

impl PartialEq for Mersenne31Field {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.to_reduced_u32() == other.to_reduced_u32()
    }
}
impl Eq for Mersenne31Field {}

impl Hash for Mersenne31Field {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.to_reduced_u32())
    }
}

impl Ord for Mersenne31Field {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_reduced_u32().cmp(&other.to_reduced_u32())
    }
}

impl PartialOrd for Mersenne31Field {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Mersenne31Field {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Display::fmt(&self.as_u64_reduced(), f)
    }
}

impl Debug for Mersenne31Field {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Debug::fmt(&self.as_u64_reduced(), f)
    }
}

impl Mersenne31Field {
    #[cfg(not(feature = "use_division"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_zero_impl(&self) -> bool {
        // two representations
        self.0 == 0 || self.0 == Self::ORDER

        // self.to_reduced_u32() == 0
    }

    #[cfg(feature = "use_division")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_zero_impl(&self) -> bool {
        self.0 == 0
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_one_impl(&self) -> bool {
        // one representations
        self.0 == 1
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
        //Since the nonzero elements of GF(pn) form a finite group with respect to multiplication,
        // a^p^n−1 = 1 (for a ≠ 0), thus the inverse of a is a^p^n−2.
        if self.is_zero_impl() {
            return None;
        }

        let mut p101 = *self;
        p101.exp_power_of_2_impl(2);
        p101.mul_assign_impl(self);

        let mut p1111 = p101;
        p1111.square_impl();
        p1111.mul_assign_impl(&p101);

        let mut p11111111 = p1111;
        p11111111.exp_power_of_2_impl(4);
        p11111111.mul_assign_impl(&p1111);

        let mut p111111110000 = p11111111;
        p111111110000.exp_power_of_2_impl(4);

        let mut p111111111111 = p111111110000;
        p111111111111.mul_assign_impl(&p1111);

        let mut p1111111111111111 = p111111110000;
        p1111111111111111.exp_power_of_2_impl(4);
        p1111111111111111.mul_assign_impl(&p11111111);

        let mut p1111111111111111111111111111 = p1111111111111111;
        p1111111111111111111111111111.exp_power_of_2_impl(12);
        p1111111111111111111111111111.mul_assign_impl(&p111111111111);

        let mut p1111111111111111111111111111101 = p1111111111111111111111111111;
        p1111111111111111111111111111101.exp_power_of_2_impl(3);
        p1111111111111111111111111111101.mul_assign_impl(&p101);
        Some(p1111111111111111111111111111101)
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

    // #[cfg(all(feature = "use_division", feature = "use_mulmod_csr"))]
    // #[cfg_attr(not(feature = "no_inline"), inline(always))]
    // pub(crate) const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
    //     #[cfg_attr(not(feature = "no_inline"), inline(always))]
    //     const fn ct_impl(a: u32, b: u32) -> u32 {
    //         let product = (a as u64) * (b as u64);
    //         let product_low = (product as u32) & ((1 << 31) - 1);
    //         let product_high = (product >> 31) as u32;
    //         reduce_with_division(product_low + product_high)
    //     }

    //     #[cfg_attr(not(feature = "no_inline"), inline(always))]
    //     #[cfg(target_arch = "riscv32")]
    //     fn rt_impl(a: u32, b: u32) -> u32 {
    //         let mut result;
    //         unsafe {
    //             core::arch::asm!(
    //                 "csrrw x0, 0x7c2, {inp1}",
    //                 "csrrw {rd}, 0x7c2, {inp2}",
    //                 inp1 = in(reg) a,
    //                 inp2 = in(reg) b,
    //                 rd = out(reg) result,
    //                 options(nomem, nostack, preserves_flags)
    //             )
    //         }

    //         result
    //     }

    //     #[cfg_attr(not(feature = "no_inline"), inline(always))]
    //     #[cfg(not(target_arch = "riscv32"))]
    //     fn rt_impl(a: u32, b: u32) -> u32 {
    //         let product = (a as u64) * (b as u64);
    //         let product_low = (product as u32) & ((1 << 31) - 1);
    //         let product_high = (product >> 31) as u32;
    //         reduce_with_division(product_low + product_high)
    //     }

    //     #[cfg_attr(not(feature = "no_inline"), inline(always))]
    //     const fn impl_inner(a: u32, b: u32) -> u32 {
    //         core::intrinsics::const_eval_select(
    //             (a,b,),
    //             ct_impl,
    //             rt_impl,
    //         )
    //     }

    //     *self = Self(impl_inner(self.0, other.0));

    //     self

    // }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn square_impl(&'_ mut self) -> &'_ mut Self {
        let t = *self;
        self.mul_assign_impl(&t)
    }

    #[cfg(not(feature = "use_division"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&'_ mut self) -> &'_ mut Self {
        // we can just jump between implementations of 0
        *self = Self(Self::ORDER - self.0);
        self

        // if self.is_zero_impl() == false {
        //     *self = Self(Self::ORDER - self.to_reduced_u32());
        // }
        // self
    }

    #[cfg(all(feature = "use_division", not(feature = "modular_ops")))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&'_ mut self) -> &'_ mut Self {
        *self = Self(ops::reduce_with_division(Self::ORDER.wrapping_sub(self.0)));

        self
    }

    #[cfg(feature = "modular_ops")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&'_ mut self) -> &'_ mut Self {
        self.0 = ops::sub_mod(0, self.0);

        self
    }

    #[cfg(not(feature = "use_division"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn double_impl(&'_ mut self) -> &'_ mut Self {
        let mut sum = self.0 << 1;
        let msb = sum & Self::MSBITMASK;
        sum ^= msb;
        sum += (msb != 0) as u32;
        //if sum >= Self::ORDER { sum -= Self::ORDER };
        self.0 = sum;

        self
    }

    #[cfg(feature = "use_division")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn double_impl(&'_ mut self) -> &'_ mut Self {
        let t = *self;
        self.add_assign_impl(&t);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn mul_by_non_residue_impl(elem: &mut Self) {
        elem.negate_impl();
    }
}

impl Field for Mersenne31Field {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);

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

    // TODO: could be optimized a little further?
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        *self = self.mul_2exp_u64(1);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        *self = self.div_2exp_u64(1);
        self
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

impl Add for Mersenne31Field {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn add(self, rhs: Self) -> Self {
        let lhs = self;
        let mut res = lhs;
        res.add_assign(&rhs);
        res
    }
}

impl Sub for Mersenne31Field {
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

impl PrimeField for Mersenne31Field {
    const TWO: Self = Self(2);
    const MINUS_ONE: Self = Self(Self::ORDER - 1);
    const NUM_BYTES_IN_REPR: usize = 4;
    const CHAR_BITS: usize = 31;
    const CHARACTERISTICS: u64 = Self::ORDER as u64;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_u64(self) -> u64 {
        self.0 as u64
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_u64_unchecked(value: u64) -> Self {
        Self::new(value as u32)
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_u64(value: u64) -> Option<Self> {
        if value as u32 >= Self::ORDER {
            None
        } else {
            Some(Self(value as u32))
        }
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_u64_with_reduction(value: u64) -> Self {
        // p = 2^31 - 1, so 2^32 = 2p + 2 = 2
        Self((value % Self::ORDER as u64) as u32)
    }
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_u64_reduced(&self) -> u64 {
        self.to_reduced_u32() as u64
    }
    #[track_caller]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn as_boolean(&self) -> bool {
        debug_assert!(
            {
                let as_uint = self.to_reduced_u32();
                as_uint == 0 || as_uint == 1
            },
            "expected boolean value, got {}",
            self.to_reduced_u32()
        );

        // in non-debug we can just compare to 1
        self.0 == 1
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_boolean(flag: bool) -> Self {
        Self(flag as u32)
    }

    fn to_le_bytes(self) -> [u8; Self::NUM_BYTES_IN_REPR] {
        self.0.to_le_bytes()
    }

    fn increment_unchecked(&'_ mut self) {
        self.0 += 1;
    }
}

impl BaseField for Mersenne31Field {
    const QUADRATIC_NON_RESIDUE: Mersenne31Field = Mersenne31Field::MINUS_ONE;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_non_residue(elem: &mut Self) {
        Self::mul_by_non_residue_impl(elem);
    }
}
