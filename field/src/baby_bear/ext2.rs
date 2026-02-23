// Quadratic extension for BabyBear. Uses v^2 - 11 = 0

use super::base::BabyBearField;
use crate::field::{Field, FieldExtension, PrimeField};
use core::ops::{Add, Mul, Sub};

#[cfg(not(target_arch = "riscv32"))]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C, align(8))]
pub struct BabyBearExt2 {
    pub c0: BabyBearField,
    pub c1: BabyBearField,
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct BabyBearExt2 {
    pub c0: BabyBearField,
    pub c1: BabyBearField,
}

const _: () = const {
    assert!(core::mem::size_of::<BabyBearExt2>() == 2 * core::mem::size_of::<u32>());

    #[cfg(not(target_arch = "riscv32"))]
    assert!(core::mem::align_of::<BabyBearExt2>() == 8);

    #[cfg(target_arch = "riscv32")]
    assert!(core::mem::align_of::<BabyBearExt2>() == 4);

    ()
};

impl BabyBearExt2 {
    pub const fn new(real: BabyBearField, imag: BabyBearField) -> Self {
        Self { c0: real, c1: imag }
    }

    pub fn real_part(&self) -> BabyBearField {
        self.c0
    }

    pub fn imag_part(&self) -> BabyBearField {
        self.c1
    }

    pub fn conjugate(&'_ mut self) -> &'_ mut Self {
        self.c1.negate();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_zero_impl(&self) -> bool {
        self.c0.is_zero_impl() && self.c1.is_zero_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn is_one_impl(&self) -> bool {
        self.c0.is_one_impl() && self.c1.is_zero_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn add_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.add_assign_impl(&other.c0);
        self.c1.add_assign_impl(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn sub_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.sub_assign_impl(&other.c0);
        self.c1.sub_assign_impl(&other.c1);

        self
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ops")))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        let mut v0 = self.c0;
        v0.mul_assign_impl(&other.c0);
        let mut v1 = self.c1;
        v1.mul_assign_impl(&other.c1);

        self.c1.add_assign_impl(&self.c0);

        let mut t0 = other.c0;
        t0.add_assign_impl(&other.c1);
        self.c1.mul_assign_impl(&t0);
        self.c1.sub_assign_impl(&v0);
        self.c1.sub_assign_impl(&v1);
        self.c0 = v0;
        BabyBearField::mul_by_non_residue_impl(&mut v1);
        self.c0.add_assign_impl(&v1);

        self
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        // here our optimization goal is just minimal number of ops,
        // so we go schoolbook
        // v^2 - nr == 0
        // (a + v * b) * (c + v * d) = (ac + nr * bd) + nr * (ad + bc)

        let mut v0 = self.c0;
        v0.mul_assign_impl(&other.c0);
        let mut v1 = self.c1;
        v1.mul_assign_impl(&other.c1);

        let mut v01 = self.c0;
        v01.mul_assign_impl(&other.c1);
        let mut v10 = self.c1;
        v10.mul_assign_impl(&other.c0);

        self.c0 = v0;
        BabyBearField::mul_by_non_residue_impl(&mut v1);
        self.c0.add_assign_impl(&v1);

        self.c1 = v01;
        self.c1.add_assign_impl(&v10);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn square_impl(&mut self) -> &mut Self {
        // We go schoolbook
        // v^2 - nr = 0
        // (a + v * b) ^ 2 = (a^2 + nr * b^2) + v * 2 * ab

        let mut v0 = self.c0;
        v0.mul_assign_impl(&self.c0);

        let mut v1 = self.c1;
        v1.mul_assign_impl(&self.c1);

        let mut cross = self.c0;
        cross.mul_assign_impl(&self.c1);

        self.c0 = v0;
        BabyBearField::mul_by_non_residue_impl(&mut v1);
        self.c0.add_assign_impl(&v1);

        self.c1 = cross;
        self.c1.double_impl();

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn negate_impl(&mut self) -> &mut Self {
        self.c0.negate_impl();
        self.c1.negate_impl();

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn double_impl(&mut self) -> &mut Self {
        self.c0.double_impl();
        self.c1.double_impl();

        self
    }

    pub(crate) const fn inverse_impl(&self) -> Option<Self> {
        let mut v0 = self.c0;
        v0.square_impl();
        let mut v1 = self.c1;
        v1.square_impl();
        // v0 = v0 - beta * v1
        let mut v1_by_nonresidue = v1;
        BabyBearField::mul_by_non_residue_impl(&mut v1_by_nonresidue);
        v0.sub_assign_impl(&v1_by_nonresidue);
        match v0.inverse_impl() {
            Some(inversed) => {
                let mut c0 = self.c0;
                c0.mul_assign_impl(&inversed);
                let mut c1 = self.c1;
                c1.mul_assign_impl(&inversed);
                c1.negate_impl();

                let new = Self { c0, c1 };
                Some(new)
            }
            None => None,
        }
    }
}

impl core::cmp::PartialEq for BabyBearExt2 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.c0 == other.c0 && self.c1 == other.c1
    }
}

impl core::cmp::Eq for BabyBearExt2 {}

impl core::default::Default for BabyBearExt2 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn default() -> Self {
        Self {
            c0: BabyBearField::ZERO,
            c1: BabyBearField::ZERO,
        }
    }
}

impl crate::Rand for BabyBearExt2 {
    fn random_element<R: rand::Rng + ?Sized>(rng: &mut R) -> Self {
        Self {
            c0: BabyBearField::random_element(rng),
            c1: BabyBearField::random_element(rng),
        }
    }
}

impl Field for BabyBearExt2 {
    const ZERO: Self = Self {
        c0: BabyBearField::ZERO,
        c1: BabyBearField::ZERO,
    };

    const ONE: Self = Self {
        c0: BabyBearField::ONE,
        c1: BabyBearField::ZERO,
    };

    type CharField = BabyBearField;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_zero(&self) -> bool {
        self.is_zero_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_one(&self) -> bool {
        self.is_one_impl()
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
    fn square(&mut self) -> &mut Self {
        self.square_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&mut self) -> &mut Self {
        self.negate_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&mut self) -> &mut Self {
        self.double_impl()
    }

    fn inverse(&self) -> Option<Self> {
        self.inverse_impl()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        self.c0.mul_by_two();
        self.c1.mul_by_two();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        self.c0.div_by_two();
        self.c1.div_by_two();
        self
    }
}

impl Add for BabyBearExt2 {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn add(self, rhs: Self) -> Self {
        let mut lhs = self;
        lhs.add_assign(&rhs);
        lhs
    }
}

impl Mul for BabyBearExt2 {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul(self, rhs: Self) -> Self {
        let mut lhs = self;
        lhs.mul_assign(&rhs);
        lhs
    }
}

impl Mul<BabyBearField> for BabyBearExt2 {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul(self, rhs: BabyBearField) -> Self {
        let mut lhs = self;
        lhs.mul_assign_by_base(&rhs);
        lhs
    }
}

impl Sub for BabyBearExt2 {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn sub(self, rhs: Self) -> Self {
        let mut lhs = self;
        lhs.sub_assign(&rhs);
        lhs
    }
}

// for F4 = F2(F2) extension
impl crate::BaseField<2> for BabyBearExt2 {
    // (0, 1) is non-residue
    const NON_RESIDUE: BabyBearExt2 = BabyBearExt2 {
        c0: BabyBearField::ZERO,
        c1: BabyBearField::ONE,
    };

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_non_residue(elem: &mut Self) {
        // (a + b * v)(0 + v) = b * v^2 + a * v
        let (c1, mut c0) = (elem.c0, elem.c1);
        BabyBearField::mul_by_non_residue_impl(&mut c0);

        elem.c0 = c0;
        elem.c1 = c1;
    }
}

// for F6 = F3(F2) extension
impl crate::BaseField<3> for BabyBearExt2 {
    // (1, 1) is non-residue
    const NON_RESIDUE: BabyBearExt2 = BabyBearExt2 {
        c0: BabyBearField::ONE,
        c1: BabyBearField::ONE,
    };

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_non_residue(elem: &mut Self) {
        // (a + b * v)(1 + v) = a + b * v^2 + (a + b) * v
        let (c0, mut c1) = (elem.c0, elem.c1);
        elem.c1.add_assign(&c0);
        BabyBearField::mul_by_non_residue_impl(&mut c1);
        elem.c0.add_assign(&c1);
    }
}

impl core::fmt::Debug for BabyBearExt2 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F2[{}, {}]",
            self.c0.as_u32_reduced(),
            self.c1.as_u32_reduced()
        )
    }
}

impl core::fmt::Display for BabyBearExt2 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F2[{}, {}]",
            self.c0.as_u32_reduced(),
            self.c1.as_u32_reduced()
        )
    }
}

impl FieldExtension<BabyBearField> for BabyBearExt2 {
    const DEGREE: usize = 2;

    type Coeffs = [BabyBearField; 2];

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs(self) -> Self::Coeffs {
        [self.c0, self.c1]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs(coeffs: Self::Coeffs) -> Self {
        let [c0, c1] = coeffs;
        Self { c0, c1 }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_ref(coeffs: &Self::Coeffs) -> Self {
        <Self as FieldExtension<BabyBearField>>::from_coeffs(*coeffs)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &BabyBearField) -> &mut Self {
        self.c0.add_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &BabyBearField) -> &mut Self {
        self.c0.sub_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &BabyBearField) -> &mut Self {
        self.c0.mul_assign(elem);
        self.c1.mul_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: BabyBearField) -> Self {
        Self {
            c0: elem,
            c1: BabyBearField::ZERO,
        }
    }
}
