// Degree 6 extension for BabyBear as 3 over 2 tower. Uses v^3 - (1, 1) = 0

use crate::baby_bear::base::BabyBearField;
use crate::baby_bear::ext2::BabyBearExt2;
use crate::field::BaseField;
use crate::field::{Field, FieldExtension, PrimeField};
use rand::Rng;

#[cfg(not(target_arch = "riscv32"))]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C, align(8))]
pub struct BabyBearExt6 {
    pub c0: BabyBearExt2,
    pub c1: BabyBearExt2,
    pub c2: BabyBearExt2,
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct BabyBearExt6 {
    pub c0: BabyBearExt2,
    pub c1: BabyBearExt2,
    pub c2: BabyBearExt2,
}

const _: () = const {
    assert!(core::mem::size_of::<BabyBearExt6>() == 6 * core::mem::size_of::<u32>());

    #[cfg(not(target_arch = "riscv32"))]
    assert!(core::mem::align_of::<BabyBearExt6>() == 8);

    #[cfg(target_arch = "riscv32")]
    assert!(core::mem::align_of::<BabyBearExt6>() == 4);

    ()
};

impl BabyBearExt6 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(c0: BabyBearExt2, c1: BabyBearExt2, c2: BabyBearExt2) -> Self {
        Self { c0, c1, c2 }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_array_of_base(els: [BabyBearField; 6]) -> Self {
        Self {
            c0: BabyBearExt2 {
                c0: els[0],
                c1: els[1],
            },
            c1: BabyBearExt2 {
                c0: els[2],
                c1: els[3],
            },
            c2: BabyBearExt2 {
                c0: els[4],
                c1: els[5],
            },
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub unsafe fn read_unaligned(base_ptr: *const BabyBearField) -> Self {
        let [c0, c1, c2, c3, c4, c5] = base_ptr.cast::<[BabyBearField; 6]>().read();
        Self {
            c0: BabyBearExt2 { c0: c0, c1: c1 },
            c1: BabyBearExt2 { c0: c2, c1: c3 },
            c2: BabyBearExt2 { c0: c4, c1: c5 },
        }
    }

    #[cfg(not(target_arch = "riscv32"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn project_ref_from_array(els: &'_ [BabyBearField; 6]) -> &'_ Self {
        if core::mem::align_of::<Self>() == core::mem::align_of::<BabyBearField>()
            && core::mem::size_of::<Self>() == core::mem::size_of::<BabyBearField>() * 6
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

impl core::cmp::PartialEq for BabyBearExt6 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.c0 == other.c0 && self.c1 == other.c1
    }
}

impl core::cmp::Eq for BabyBearExt6 {}

impl core::default::Default for BabyBearExt6 {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn default() -> Self {
        Self {
            c0: BabyBearExt2::ZERO,
            c1: BabyBearExt2::ZERO,
            c2: BabyBearExt2::ZERO,
        }
    }
}

impl crate::Rand for BabyBearExt6 {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self {
            c0: crate::Rand::random_element(rng),
            c1: crate::Rand::random_element(rng),
            c2: crate::Rand::random_element(rng),
        }
    }
}

impl Field for BabyBearExt6 {
    const ZERO: Self = Self {
        c0: BabyBearExt2::ZERO,
        c1: BabyBearExt2::ZERO,
        c2: BabyBearExt2::ZERO,
    };

    const ONE: Self = Self {
        c0: BabyBearExt2::ONE,
        c1: BabyBearExt2::ZERO,
        c2: BabyBearExt2::ZERO,
    };

    type CharField = BabyBearExt2;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_one(&self) -> bool {
        self.c0.is_one() && self.c1.is_zero() && self.c2.is_zero()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
        self.c2.add_assign(&other.c2);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
        self.c2.sub_assign(&other.c2);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        let mut c_c = self.c2;
        a_a.mul_assign(&other.c0);
        b_b.mul_assign(&other.c1);
        c_c.mul_assign(&other.c2);

        let mut t1 = other.c1;
        t1.add_assign(&other.c2);
        {
            let mut tmp = self.c1;
            tmp.add_assign(&self.c2);

            t1.mul_assign(&tmp);
            t1.sub_assign(&b_b);
            t1.sub_assign(&c_c);
            <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut t1);
            t1.add_assign(&a_a);
        }

        let mut t3 = other.c0;
        t3.add_assign(&other.c2);
        {
            let mut tmp = self.c0;
            tmp.add_assign(&self.c2);

            t3.mul_assign(&tmp);
            t3.sub_assign(&a_a);
            t3.add_assign(&b_b);
            t3.sub_assign(&c_c);
        }

        let mut t2 = other.c0;
        t2.add_assign(&other.c1);
        {
            let mut tmp = self.c0;
            tmp.add_assign(&self.c1);

            t2.mul_assign(&tmp);
            t2.sub_assign(&a_a);
            t2.sub_assign(&b_b);
            <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut c_c);
            t2.add_assign(&c_c);
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn square(&mut self) -> &mut Self {
        let mut s0 = self.c0;
        s0.square();
        let mut ab = self.c0;
        ab.mul_assign(&self.c1);
        let mut s1 = ab;
        s1.double();
        let mut s2 = self.c0;
        s2.sub_assign(&self.c1);
        s2.add_assign(&self.c2);
        s2.square();
        let mut bc = self.c1;
        bc.mul_assign(&self.c2);
        let mut s3 = bc;
        s3.double();
        let mut s4 = self.c2;
        s4.square();

        self.c0 = s3;
        <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut self.c0);
        self.c0.add_assign(&s0);

        self.c1 = s4;
        <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut self.c1);
        self.c1.add_assign(&s1);

        self.c2 = s1;
        self.c2.add_assign(&s2);
        self.c2.add_assign(&s3);
        self.c2.sub_assign(&s0);
        self.c2.sub_assign(&s4);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&mut self) -> &mut Self {
        self.c0.negate();
        self.c1.negate();
        self.c2.negate();

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&mut self) -> &mut Self {
        self.c0.double();
        self.c1.double();
        self.c2.double();

        self
    }

    fn inverse(&self) -> Option<Self> {
        let mut c0 = self.c2;
        <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut c0);
        c0.mul_assign(&self.c1);
        c0.negate();
        {
            let mut c0s = self.c0;
            c0s.square();
            c0.add_assign(&c0s);
        }
        let mut c1 = self.c2;
        c1.square();
        <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut c1);
        {
            let mut c01 = self.c0;
            c01.mul_assign(&self.c1);
            c1.sub_assign(&c01);
        }
        let mut c2 = self.c1;
        c2.square();
        {
            let mut c02 = self.c0;
            c02.mul_assign(&self.c2);
            c2.sub_assign(&c02);
        }

        let mut tmp1 = self.c2;
        tmp1.mul_assign(&c1);
        let mut tmp2 = self.c1;
        tmp2.mul_assign(&c2);
        tmp1.add_assign(&tmp2);
        <BabyBearExt2 as BaseField<3>>::mul_by_non_residue(&mut tmp1);
        tmp2 = self.c0;
        tmp2.mul_assign(&c0);
        tmp1.add_assign(&tmp2);

        match tmp1.inverse() {
            Some(t) => {
                let mut tmp = Self {
                    c0: t,
                    c1: t,
                    c2: t,
                };
                tmp.c0.mul_assign(&c0);
                tmp.c1.mul_assign(&c1);
                tmp.c2.mul_assign(&c2);

                Some(tmp)
            }
            None => None,
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        self.c0.mul_by_two();
        self.c1.mul_by_two();
        self.c2.mul_by_two();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        self.c0.div_by_two();
        self.c1.div_by_two();
        self.c2.div_by_two();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        self.mul_assign(a);
        self.add_assign(b);

        self
    }
}

impl core::fmt::Debug for BabyBearExt6 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F6[{}, {}, {}, {}, {}, {}]",
            self.c0.c0.as_u32_reduced(),
            self.c0.c1.as_u32_reduced(),
            self.c1.c0.as_u32_reduced(),
            self.c1.c1.as_u32_reduced(),
            self.c2.c0.as_u32_reduced(),
            self.c2.c1.as_u32_reduced(),
        )
    }
}

impl core::fmt::Display for BabyBearExt6 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F6[{}, {}, {}, {}, {}, {}]",
            self.c0.c0.as_u32_reduced(),
            self.c0.c1.as_u32_reduced(),
            self.c1.c0.as_u32_reduced(),
            self.c1.c1.as_u32_reduced(),
            self.c2.c0.as_u32_reduced(),
            self.c2.c1.as_u32_reduced(),
        )
    }
}

impl FieldExtension<BabyBearExt2> for BabyBearExt6 {
    const DEGREE: usize = 3;

    type Coeffs = [BabyBearExt2; 3];

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs(self) -> Self::Coeffs {
        [self.c0, self.c1, self.c2]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs(coeffs: Self::Coeffs) -> Self {
        let [c0, c1, c2] = coeffs;
        Self { c0, c1, c2 }
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
    fn from_base(elem: BabyBearExt2) -> Self {
        Self {
            c0: elem,
            c1: BabyBearExt2::ZERO,
            c2: BabyBearExt2::ZERO,
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &BabyBearExt2) -> &mut Self {
        self.c0.mul_assign(elem);
        self.c1.mul_assign(elem);
        self.c2.mul_assign(elem);
        self
    }
}

impl FieldExtension<BabyBearField> for BabyBearExt6 {
    const DEGREE: usize = 6;

    type Coeffs = [BabyBearField; 6];

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs(self) -> Self::Coeffs {
        [
            self.c0.c0, self.c0.c1, self.c1.c0, self.c1.c1, self.c2.c0, self.c2.c1,
        ]
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
            c2: BabyBearExt2 {
                c0: coeffs[4],
                c1: coeffs[5],
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
        self.c2.mul_assign_by_base(elem);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: BabyBearField) -> Self {
        let c0 = BabyBearExt2::from_base(elem);
        Self {
            c0,
            c1: BabyBearExt2::ZERO,
            c2: BabyBearExt2::ZERO,
        }
    }
}
