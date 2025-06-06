// SPDX-License-Identifier: MIT OR Apache-2.0
// Portions derived from Plonky3 and adapted by Matter Labs.
// © 2024 Polygon Labs – original; © 2025 Matter Labs - adapted for RISC-V.

use super::*;
use core::ops::{Add, Mul, Sub};

#[cfg(not(target_arch = "riscv32"))]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C, align(8))]
pub struct Mersenne31Complex {
    pub c0: Mersenne31Field,
    pub c1: Mersenne31Field,
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct Mersenne31Complex {
    pub c0: Mersenne31Field,
    pub c1: Mersenne31Field,
}

const _: () = const {
    assert!(core::mem::size_of::<Mersenne31Complex>() == 2 * core::mem::size_of::<u32>());

    #[cfg(not(target_arch = "riscv32"))]
    assert!(core::mem::align_of::<Mersenne31Complex>() == 8);

    #[cfg(target_arch = "riscv32")]
    assert!(core::mem::align_of::<Mersenne31Complex>() == 4);

    ()
};

impl Mersenne31Complex {
    pub const TWO_ADIC_GENERATOR: Self = Self {
        c0: Mersenne31Field::new(311014874),
        c1: Mersenne31Field::new(1584694829),
    };

    // enumerated such that TWO_ADICITY_GENERATORS[domain size log2] is a generator for the corresponding size
    pub const TWO_ADICITY_GENERATORS: [Self; 31 + 1] = const {
        let mut result = [Self::ZERO; 31 + 1];
        let mut current = Self::TWO_ADIC_GENERATOR;
        let mut i = 0;
        while i < 31 {
            result[31 - i] = current;
            current.square_impl();
            i += 1;
        }

        result[0] = current;

        result
    };

    pub const TWO_ADICITY_GENERATORS_INVERSED: [Self; 31 + 1] = const {
        let mut result = [Self::ZERO; 31 + 1];
        let mut i = 0;
        while i < 32 {
            result[i] = Self::TWO_ADICITY_GENERATORS[i].inverse_impl().unwrap();
            i += 1;
        }

        result
    };

    pub const fn new(real: Mersenne31Field, imag: Mersenne31Field) -> Self {
        Self { c0: real, c1: imag }
    }

    pub fn real_part(&self) -> Mersenne31Field {
        self.c0
    }

    pub fn imag_part(&self) -> Mersenne31Field {
        self.c1
    }

    pub fn conjugate(&'_ mut self) -> &'_ mut Self {
        self.c1.negate();
        self
    }

    pub fn div_2exp_u64(&self, exp: u64) -> Self {
        Self::new(
            self.real_part().div_2exp_u64(exp),
            self.imag_part().div_2exp_u64(exp),
        )
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
        // Same - we can subtract instead
        // Mersenne31Field::mul_by_non_residue_impl(&mut v1);
        // self.c0.add_assign_impl(&v1);
        self.c0.sub_assign_impl(&v1);

        self
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        // here our optimization goal is just minimal number of ops,
        // so we go schoolbook
        // (a + i * b) * (c + i * d) = (ac - bd) + i * (ad + bc)
        let mut v0 = self.c0;
        v0.mul_assign_impl(&other.c0);
        let mut v1 = self.c1;
        v1.mul_assign_impl(&other.c1);

        let mut v01 = self.c0;
        v01.mul_assign_impl(&other.c1);
        let mut v10 = self.c1;
        v10.mul_assign_impl(&other.c0);

        self.c0 = v0;
        self.c0.sub_assign_impl(&v1);

        self.c1 = v01;
        self.c1.add_assign_impl(&v10);

        self
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ops")))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn square_impl(&mut self) -> &mut Self {
        let mut v0 = self.c0;
        v0.sub_assign_impl(&self.c1);
        let mut v3 = self.c0;
        // t0 only happens here, and instead of multiplying by non-residue and subtracting, we can just add
        // let mut t0: Mersenne31Field = self.c1;
        // Mersenne31Field::mul_by_non_residue_impl(&mut t0);
        // v3.sub_assign_impl(&t0);
        v3.add_assign_impl(&self.c1);
        let mut v2 = self.c0;
        v2.mul_assign_impl(&self.c1);
        v0.mul_assign_impl(&v3);
        v0.add_assign_impl(&v2);

        self.c1 = v2;
        self.c1.double_impl();
        self.c0 = v0;
        // Same - we can subtract instead
        // Mersenne31Field::mul_by_non_residue_impl(&mut v2);
        // self.c0.add_assign_impl(&v2);
        self.c0.sub_assign_impl(&v2);

        self
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) const fn square_impl(&mut self) -> &mut Self {
        // here our optimization goal is just minimal number of ops,
        // so we go schoolbook
        // (a + i * b) ^ 2 = (a^2 - b^2) + i * 2 * ab

        let mut v0 = self.c0;
        v0.mul_assign_impl(&self.c0);

        let mut v1 = self.c1;
        v1.mul_assign_impl(&self.c1);

        let mut cross = self.c0;
        cross.mul_assign_impl(&self.c1);

        self.c0 = v0;
        self.c0.sub_assign_impl(&v1);

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
        Mersenne31Field::mul_by_non_residue_impl(&mut v1_by_nonresidue);
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

impl core::cmp::PartialEq for Mersenne31Complex {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.c0 == other.c0 && self.c1 == other.c1
    }
}

impl core::cmp::Eq for Mersenne31Complex {}

impl core::default::Default for Mersenne31Complex {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn default() -> Self {
        Self {
            c0: Mersenne31Field::ZERO,
            c1: Mersenne31Field::ZERO,
        }
    }
}

impl Rand for Mersenne31Complex {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self {
            c0: Mersenne31Field::random_element(rng),
            c1: Mersenne31Field::random_element(rng),
        }
    }
}

impl Field for Mersenne31Complex {
    const ZERO: Self = Self {
        c0: Mersenne31Field::ZERO,
        c1: Mersenne31Field::ZERO,
    };

    const ONE: Self = Self {
        c0: Mersenne31Field::ONE,
        c1: Mersenne31Field::ZERO,
    };

    type CharField = Mersenne31Field;

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

impl Add for Mersenne31Complex {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn add(self, rhs: Self) -> Self {
        let mut lhs = self;
        lhs.add_assign(&rhs);
        lhs
    }
}

impl Mul for Mersenne31Complex {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul(self, rhs: Self) -> Self {
        let mut lhs = self;
        lhs.mul_assign(&rhs);
        lhs
    }
}

impl Mul<Mersenne31Field> for Mersenne31Complex {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn mul(self, rhs: Mersenne31Field) -> Self {
        let mut lhs = self;
        lhs.mul_assign_by_base(&rhs);
        lhs
    }
}

impl Sub for Mersenne31Complex {
    type Output = Self;
    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn sub(self, rhs: Self) -> Self {
        let mut lhs = self;
        lhs.sub_assign(&rhs);
        lhs
    }
}

impl BaseField for Mersenne31Complex {
    // 2 + i is non-residue
    const QUADRATIC_NON_RESIDUE: Mersenne31Complex = Mersenne31Complex {
        c0: Mersenne31Field::TWO,
        c1: Mersenne31Field::ONE,
    };

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_non_residue(elem: &mut Self) {
        // (a + b * i)(2 + i) = (2 * a - b) + (2 * b + a)i
        let (a, b) = (elem.c0, elem.c1);
        let mut real = a;
        real.double();
        real.sub_assign(&b);

        let mut imag = b;
        imag.double();
        imag.add_assign(&a);

        elem.c0 = real;
        elem.c1 = imag;
    }
}

impl TwoAdicField for Mersenne31Complex {
    const TWO_ADICITY: usize = 31;

    fn two_adic_generator() -> Self {
        // element of order p+1 - generator of cicrcle group
        Self {
            c0: Mersenne31Field::new(311014874),
            c1: Mersenne31Field::new(1584694829),
        }
    }

    fn two_adic_group_order() -> usize {
        1 << 31
    }
}

impl core::fmt::Debug for Mersenne31Complex {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F2[{}, {}]",
            self.c0.as_u64_reduced(),
            self.c1.as_u64_reduced()
        )
    }
}

impl core::fmt::Display for Mersenne31Complex {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F2[{}, {}]",
            self.c0.as_u64_reduced(),
            self.c1.as_u64_reduced()
        )
    }
}

impl FieldExtension<Mersenne31Field> for Mersenne31Complex {
    const DEGREE: usize = 2;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.c0.mul_assign(elem);
        self.c1.mul_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs_in_base(self) -> [Mersenne31Field; 2] {
        let Self { c0, c1 } = self;

        [c0, c1]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base_coeffs_array(coefs: &[Mersenne31Field; 2]) -> Self {
        Self {
            c0: coefs[0],
            c1: coefs[1],
        }
    }

    fn from_coeffs_in_base(coeffs: &[Mersenne31Field]) -> Self {
        Self {
            c0: coeffs[0],
            c1: coeffs[1],
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_ref(coeffs: &[&Mersenne31Field]) -> Self {
        Self {
            c0: *coeffs[0],
            c1: *coeffs[1],
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31Field>>(mut coefs_iter: I) -> Self {
        Self {
            c0: coefs_iter.next().unwrap(),
            c1: coefs_iter.next().unwrap(),
        }
    }

    fn coeffs_in_base(&self) -> &[Mersenne31Field] {
        // todo!();
        unsafe { core::slice::from_raw_parts(self.c0.0 as *const Mersenne31Field, 2) }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.c0.add_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.c0.sub_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: Mersenne31Field) -> Self {
        Self {
            c0: elem,
            c1: Mersenne31Field::ZERO,
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn get_coef_mut(&mut self, _idx: usize) -> &mut Mersenne31Field {
        todo!();
    }
}
