// Quardic extension for BabyBear as 2 over 2 tower. Uses v^2 - (0, 1) = 0

use crate::baby_bear::base::BabyBearField;
use crate::baby_bear::ext2::BabyBearExt2;
use crate::field::BaseField;
use crate::field::{Field, FieldExtension, PrimeField};
use rand::Rng;

#[cfg(not(target_arch = "riscv32"))]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C, align(16))]
pub struct BabyBearExt4 {
    pub c0: BabyBearExt2,
    pub c1: BabyBearExt2,
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct BabyBearExt4 {
    pub c0: BabyBearExt2,
    pub c1: BabyBearExt2,
}

const _: () = const {
    assert!(core::mem::size_of::<BabyBearExt4>() == 4 * core::mem::size_of::<u32>());

    #[cfg(not(target_arch = "riscv32"))]
    assert!(core::mem::align_of::<BabyBearExt4>() == 16);

    #[cfg(target_arch = "riscv32")]
    assert!(core::mem::align_of::<BabyBearExt4>() == 4);

    ()
};

impl BabyBearExt4 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(c0: BabyBearExt2, c1: BabyBearExt2) -> Self {
        Self { c0, c1 }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_array_of_base(els: [BabyBearField; 4]) -> Self {
        Self {
            c0: BabyBearExt2 {
                c0: els[0],
                c1: els[1],
            },
            c1: BabyBearExt2 {
                c0: els[2],
                c1: els[3],
            },
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub unsafe fn read_unaligned(base_ptr: *const BabyBearField) -> Self {
        let [c0, c1, c2, c3] = base_ptr.cast::<[BabyBearField; 4]>().read();
        Self {
            c0: BabyBearExt2 { c0: c0, c1: c1 },
            c1: BabyBearExt2 { c0: c2, c1: c3 },
        }
    }

    #[cfg(not(target_arch = "riscv32"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn project_ref_from_array(els: &'_ [BabyBearField; 4]) -> &'_ Self {
        if core::mem::align_of::<Self>() == core::mem::align_of::<BabyBearField>()
            && core::mem::size_of::<Self>() == core::mem::size_of::<BabyBearField>() * 4
        {
            // alignments and expected sized match, so we can just cast pointer
            unsafe { core::mem::transmute(els) }
        } else {
            unimplemented!()
        }
    }

    #[cfg(target_arch = "riscv32")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn project_ref_from_array(els: &'_ [BabyBearField; 4]) -> &'_ Self {
        // alignments match, so we can just cast pointer
        unsafe { core::mem::transmute(els) }
    }
}

impl core::cmp::PartialEq for BabyBearExt4 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.c0 == other.c0 && self.c1 == other.c1
    }
}

impl core::cmp::Eq for BabyBearExt4 {}

impl core::default::Default for BabyBearExt4 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn default() -> Self {
        Self {
            c0: BabyBearExt2::ZERO,
            c1: BabyBearExt2::ZERO,
        }
    }
}

impl crate::Rand for BabyBearExt4 {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self {
            c0: crate::Rand::random_element(rng),
            c1: crate::Rand::random_element(rng),
        }
    }
}

impl Field for BabyBearExt4 {
    const ZERO: Self = Self {
        c0: BabyBearExt2::ZERO,
        c1: BabyBearExt2::ZERO,
    };

    const ONE: Self = Self {
        c0: BabyBearExt2::ONE,
        c1: BabyBearExt2::ZERO,
    };

    type CharField = BabyBearExt2;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_one(&self) -> bool {
        self.c0.is_one() && self.c1.is_zero()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        let mut v0 = self.c0;
        v0.mul_assign(&other.c0);
        let mut v1 = self.c1;
        v1.mul_assign(&other.c1);

        let t = self.c0;
        self.c1.add_assign(&t);

        let mut t0 = other.c0;
        t0.add_assign(&other.c1);
        self.c1.mul_assign(&t0);
        self.c1.sub_assign(&v0);
        self.c1.sub_assign(&v1);
        self.c0 = v0;
        <BabyBearExt2 as BaseField<2>>::mul_by_non_residue(&mut v1);
        self.c0.add_assign(&v1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn square(&mut self) -> &mut Self {
        let mut v0 = self.c0;
        v0.sub_assign(&self.c1);
        let mut v3 = self.c0;
        let mut t0 = self.c1;
        <BabyBearExt2 as BaseField<2>>::mul_by_non_residue(&mut t0);
        v3.sub_assign(&t0);
        let mut v2 = self.c0;
        v2.mul_assign(&self.c1);
        v0.mul_assign(&v3);
        v0.add_assign(&v2);

        self.c1 = v2;
        self.c1.double();
        self.c0 = v0;
        <BabyBearExt2 as BaseField<2>>::mul_by_non_residue(&mut v2);
        self.c0.add_assign(&v2);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&mut self) -> &mut Self {
        self.c0.negate();
        self.c1.negate();

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&mut self) -> &mut Self {
        self.c0.double();
        self.c1.double();

        self
    }

    fn inverse(&self) -> Option<Self> {
        let mut v0 = self.c0;
        v0.square();
        let mut v1 = self.c1;
        v1.square();
        // v0 = v0 - beta * v1
        let mut v1_by_nonresidue = v1;
        <BabyBearExt2 as BaseField<2>>::mul_by_non_residue(&mut v1_by_nonresidue);
        v0.sub_assign(&v1_by_nonresidue);
        match v0.inverse() {
            Some(inversed) => {
                let mut c0 = self.c0;
                c0.mul_assign(&inversed);
                let mut c1 = self.c1;
                c1.mul_assign(&inversed);
                c1.negate();

                let new = Self { c0, c1 };
                Some(new)
            }
            None => None,
        }
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

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        self.mul_assign(a);
        self.add_assign(b);

        self
    }
}

impl core::fmt::Debug for BabyBearExt4 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F4[{}, {}, {}, {}]",
            self.c0.c0.as_u32_reduced(),
            self.c0.c1.as_u32_reduced(),
            self.c1.c0.as_u32_reduced(),
            self.c1.c1.as_u32_reduced(),
        )
    }
}

impl core::fmt::Display for BabyBearExt4 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F4[{}, {}, {}, {}]",
            self.c0.c0.as_u32_reduced(),
            self.c0.c1.as_u32_reduced(),
            self.c1.c0.as_u32_reduced(),
            self.c1.c1.as_u32_reduced(),
        )
    }
}

impl FieldExtension<BabyBearExt2> for BabyBearExt4 {
    const DEGREE: usize = 2;

    type Coeffs = [BabyBearExt2; 2];

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
        <Self as FieldExtension<BabyBearExt2>>::from_coeffs(*coeffs)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &BabyBearExt2) -> &mut Self {
        self.c0.add_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &BabyBearExt2) -> &mut Self {
        self.c0.sub_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &BabyBearExt2) -> &mut Self {
        self.c0.mul_assign(elem);
        self.c1.mul_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: BabyBearExt2) -> Self {
        Self {
            c0: elem,
            c1: BabyBearExt2::ZERO,
        }
    }
}

impl FieldExtension<BabyBearField> for BabyBearExt4 {
    const DEGREE: usize = 4;

    type Coeffs = [BabyBearField; 4];

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs(self) -> Self::Coeffs {
        [self.c0.c0, self.c0.c1, self.c1.c0, self.c1.c1]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs(coeffs: Self::Coeffs) -> Self {
        Self {
            c0: BabyBearExt2 {
                c0: coeffs[0],
                c1: coeffs[1],
            },
            c1: BabyBearExt2 {
                c0: coeffs[2],
                c1: coeffs[3],
            },
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_ref(coeffs: &Self::Coeffs) -> Self {
        <Self as FieldExtension<BabyBearField>>::from_coeffs(*coeffs)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &BabyBearField) -> &mut Self {
        self.c0.add_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &BabyBearField) -> &mut Self {
        self.c0.sub_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &BabyBearField) -> &mut Self {
        self.c0.mul_assign_by_base(elem);
        self.c1.mul_assign_by_base(elem);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: BabyBearField) -> Self {
        let c0 = BabyBearExt2::from_base(elem);
        Self {
            c0,
            c1: BabyBearExt2::ZERO,
        }
    }
}
