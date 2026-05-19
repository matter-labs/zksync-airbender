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

    // 2-over-2 tower Karatsuba multiplication. Three E2 mults + add/sub overhead.
    // Preferred on targets where base-field mul is significantly more expensive
    // than add (every non-riscv32 build).
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) fn mul_assign_tower_impl(&mut self, other: &Self) {
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
    }

    // Flat quartic schoolbook multiplication operating directly on base-field limbs.
    // Preferred on the riscv32 + modular_ops verifier path: there each base mul/add
    // is one `mop.rr.{0,2}` instruction, so trading ~3 muls for ~4 fewer adds vs.
    // the tower Karatsuba is a net instruction count win.
    //
    // For E4 = B[α,β,αβ] with α²=11, β²=α the multiplication table gives:
    //   out[0] = a0·b0 + 11·a1·b1 + 11·a2·b3 + 11·a3·b2
    //   out[1] = a0·b1 + a1·b0  +    a2·b2  + 11·a3·b3
    //   out[2] = a0·b2 + 11·a1·b3 +  a2·b0  + 11·a3·b1
    //   out[3] = a0·b3 + a1·b2  +    a2·b1  +    a3·b0
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) fn mul_assign_flat_impl(&mut self, other: &Self) {
        let a0 = self.c0.c0;
        let a1 = self.c0.c1;
        let a2 = self.c1.c0;
        let a3 = self.c1.c1;
        let b0 = other.c0.c0;
        let b1 = other.c0.c1;
        let b2 = other.c1.c0;
        let b3 = other.c1.c1;

        let mut a1n = a1;
        BabyBearField::mul_by_non_residue_impl(&mut a1n);
        let mut a2n = a2;
        BabyBearField::mul_by_non_residue_impl(&mut a2n);
        let mut a3n = a3;
        BabyBearField::mul_by_non_residue_impl(&mut a3n);

        // out[0] = a0·b0 + a1n·b1 + a2n·b3 + a3n·b2
        let mut o0 = a0;
        o0.mul_assign(&b0);
        let mut t = a1n;
        t.mul_assign(&b1);
        o0.add_assign(&t);
        let mut t = a2n;
        t.mul_assign(&b3);
        o0.add_assign(&t);
        let mut t = a3n;
        t.mul_assign(&b2);
        o0.add_assign(&t);

        // out[1] = a0·b1 + a1·b0 + a2·b2 + a3n·b3
        let mut o1 = a0;
        o1.mul_assign(&b1);
        let mut t = a1;
        t.mul_assign(&b0);
        o1.add_assign(&t);
        let mut t = a2;
        t.mul_assign(&b2);
        o1.add_assign(&t);
        let mut t = a3n;
        t.mul_assign(&b3);
        o1.add_assign(&t);

        // out[2] = a0·b2 + a1n·b3 + a2·b0 + a3n·b1
        let mut o2 = a0;
        o2.mul_assign(&b2);
        let mut t = a1n;
        t.mul_assign(&b3);
        o2.add_assign(&t);
        let mut t = a2;
        t.mul_assign(&b0);
        o2.add_assign(&t);
        let mut t = a3n;
        t.mul_assign(&b1);
        o2.add_assign(&t);

        // out[3] = a0·b3 + a1·b2 + a2·b1 + a3·b0
        let mut o3 = a0;
        o3.mul_assign(&b3);
        let mut t = a1;
        t.mul_assign(&b2);
        o3.add_assign(&t);
        let mut t = a2;
        t.mul_assign(&b1);
        o3.add_assign(&t);
        let mut t = a3;
        t.mul_assign(&b0);
        o3.add_assign(&t);

        self.c0 = BabyBearExt2 { c0: o0, c1: o1 };
        self.c1 = BabyBearExt2 { c0: o2, c1: o3 };
    }

    // Tower squaring derived from the Chung-Hasan complex-squaring trick over E2.
    // Companion to `mul_assign_tower_impl`.
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) fn square_tower_impl(&mut self) {
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
    }

    // Flat quartic squaring. Exploits aᵢ=bᵢ symmetry so cross products appear
    // doubled.
    //   out[0] = a0² + 11·a1² + 2·11·a2·a3
    //   out[1] = 2·a0·a1 + a2² + 11·a3²
    //   out[2] = 2·a0·a2 + 2·11·a1·a3
    //   out[3] = 2·(a0·a3 + a1·a2)
    // Companion to `mul_assign_flat_impl`.
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub(crate) fn square_flat_impl(&mut self) {
        let a0 = self.c0.c0;
        let a1 = self.c0.c1;
        let a2 = self.c1.c0;
        let a3 = self.c1.c1;

        let mut a1n = a1;
        BabyBearField::mul_by_non_residue_impl(&mut a1n);
        let mut a3n = a3;
        BabyBearField::mul_by_non_residue_impl(&mut a3n);

        // a2·a3 is shared between out[0] (scaled by 22) and out[3] (doubled).
        let mut a2a3 = a2;
        a2a3.mul_assign(&a3);
        let mut a2a3_11 = a2a3;
        BabyBearField::mul_by_non_residue_impl(&mut a2a3_11);

        // out[0] = a0² + a1n·a1 + 2·(11·a2·a3)
        let mut o0 = a0;
        o0.mul_assign(&a0);
        let mut t = a1n;
        t.mul_assign(&a1);
        o0.add_assign(&t);
        let mut t = a2a3_11;
        t.double();
        o0.add_assign(&t);

        // out[1] = 2·a0·a1 + a2² + a3n·a3
        let mut o1 = a0;
        o1.mul_assign(&a1);
        o1.double();
        let mut t = a2;
        t.mul_assign(&a2);
        o1.add_assign(&t);
        let mut t = a3n;
        t.mul_assign(&a3);
        o1.add_assign(&t);

        // out[2] = 2·a0·a2 + 2·(11·a1·a3)
        let mut o2 = a0;
        o2.mul_assign(&a2);
        o2.double();
        let mut t = a1n;
        t.mul_assign(&a3);
        t.double();
        o2.add_assign(&t);

        // out[3] = 2·(a0·a3 + a1·a2)
        let mut o3 = a0;
        o3.mul_assign(&a3);
        let mut t = a1;
        t.mul_assign(&a2);
        o3.add_assign(&t);
        o3.double();

        self.c0 = BabyBearExt2 { c0: o0, c1: o1 };
        self.c1 = BabyBearExt2 { c0: o2, c1: o3 };
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

    const MINUS_ONE: Self = Self {
        c0: BabyBearExt2::MINUS_ONE,
        c1: BabyBearExt2::ZERO,
    };

    const TWO: Self = Self {
        c0: BabyBearExt2::TWO,
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
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_adds += 1);
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_adds += 1);
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_muls += 1);

        #[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
        {
            self.mul_assign_flat_impl(other);
        }
        #[cfg(not(all(target_arch = "riscv32", feature = "modular_ops")))]
        {
            self.mul_assign_tower_impl(other);
        }
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn square(&mut self) -> &mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_muls += 1);

        #[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
        {
            self.square_flat_impl();
        }
        #[cfg(not(all(target_arch = "riscv32", feature = "modular_ops")))]
        {
            self.square_tower_impl();
        }
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&mut self) -> &mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_adds += 1);
        self.c0.negate();
        self.c1.negate();

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&mut self) -> &mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_adds += 1);
        self.c0.double();
        self.c1.double();

        self
    }

    fn inverse(&self) -> Option<Self> {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_muls += 6);
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
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_adds += 1);
        self.c0.mul_by_two();
        self.c1.mul_by_two();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        #[cfg(feature = "verifier_stats")]
        crate::stats::FIELD_STATS.with_borrow_mut(|s| s.fext_muls += 1);
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

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    fn arb_bf() -> impl Strategy<Value = BabyBearField> {
        (0..BabyBearField::ORDER).prop_map(BabyBearField::new)
    }

    fn arb_e4() -> impl Strategy<Value = BabyBearExt4> {
        (arb_bf(), arb_bf(), arb_bf(), arb_bf())
            .prop_map(|(a, b, c, d)| BabyBearExt4::from_array_of_base([a, b, c, d]))
    }

    proptest! {
        #[test]
        fn add_commutative(a in arb_e4(), b in arb_e4()) {
            let mut ab = a; ab.add_assign(&b);
            let mut ba = b; ba.add_assign(&a);
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn add_associative(a in arb_e4(), b in arb_e4(), c in arb_e4()) {
            let mut ab = a; ab.add_assign(&b);
            let mut abc_left = ab; abc_left.add_assign(&c);
            let mut bc = b; bc.add_assign(&c);
            let mut abc_right = a; abc_right.add_assign(&bc);
            prop_assert_eq!(abc_left, abc_right);
        }

        #[test]
        fn add_identity(a in arb_e4()) {
            let mut r = a;
            r.add_assign(&BabyBearExt4::ZERO);
            prop_assert_eq!(r, a);
        }

        #[test]
        fn add_inverse(a in arb_e4()) {
            let mut neg = a; neg.negate();
            let mut sum = a; sum.add_assign(&neg);
            prop_assert_eq!(sum, BabyBearExt4::ZERO);
        }

        #[test]
        fn mul_commutative(a in arb_e4(), b in arb_e4()) {
            let mut ab = a; ab.mul_assign(&b);
            let mut ba = b; ba.mul_assign(&a);
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn mul_associative(a in arb_e4(), b in arb_e4(), c in arb_e4()) {
            let mut ab = a; ab.mul_assign(&b);
            let mut abc_left = ab; abc_left.mul_assign(&c);
            let mut bc = b; bc.mul_assign(&c);
            let mut abc_right = a; abc_right.mul_assign(&bc);
            prop_assert_eq!(abc_left, abc_right);
        }

        #[test]
        fn mul_identity(a in arb_e4()) {
            let mut r = a;
            r.mul_assign(&BabyBearExt4::ONE);
            prop_assert_eq!(r, a);
        }

        #[test]
        fn mul_zero(a in arb_e4()) {
            let mut r = a;
            r.mul_assign(&BabyBearExt4::ZERO);
            prop_assert_eq!(r, BabyBearExt4::ZERO);
        }

        #[test]
        fn mul_inverse(a in arb_e4()) {
            prop_assume!(!a.is_zero());
            let inv = a.inverse().unwrap();
            let mut product = a;
            product.mul_assign(&inv);
            prop_assert_eq!(product, BabyBearExt4::ONE);
        }

        #[test]
        fn distributive(a in arb_e4(), b in arb_e4(), c in arb_e4()) {
            let mut bc = b; bc.add_assign(&c);
            let mut left = a; left.mul_assign(&bc);
            let mut ab = a; ab.mul_assign(&b);
            let mut ac = a; ac.mul_assign(&c);
            let mut right = ab; right.add_assign(&ac);
            prop_assert_eq!(left, right);
        }

        #[test]
        fn sub_is_add_neg(a in arb_e4(), b in arb_e4()) {
            let mut via_sub = a; via_sub.sub_assign(&b);
            let mut neg_b = b; neg_b.negate();
            let mut via_add = a; via_add.add_assign(&neg_b);
            prop_assert_eq!(via_sub, via_add);
        }

        #[test]
        fn double_is_add_self(a in arb_e4()) {
            let mut doubled = a; doubled.double();
            let mut added = a; added.add_assign(&a);
            prop_assert_eq!(doubled, added);
        }

        #[test]
        fn square_is_mul_self(a in arb_e4()) {
            let mut squared = a; squared.square();
            let mut mulled = a; mulled.mul_assign(&a);
            prop_assert_eq!(squared, mulled);
        }

        // Cross-check Field::mul against the FieldExtension scalar paths by
        // exercising mul against scalar embeddings (from_base).
        #[test]
        fn mul_by_base_via_extension_matches_full_mul(a in arb_e4(), s in arb_bf()) {
            let s_e4 = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(s);
            let mut full = a; full.mul_assign(&s_e4);
            let mut via_base = a;
            <BabyBearExt4 as FieldExtension<BabyBearField>>::mul_assign_by_base(&mut via_base, &s);
            prop_assert_eq!(full, via_base);
        }

        #[test]
        fn mul_by_e2_via_extension_matches_full_mul(a in arb_e4(), s0 in arb_bf(), s1 in arb_bf()) {
            let s_e2 = BabyBearExt2 { c0: s0, c1: s1 };
            let s_e4 = <BabyBearExt4 as FieldExtension<BabyBearExt2>>::from_base(s_e2);
            let mut full = a; full.mul_assign(&s_e4);
            let mut via_base = a;
            <BabyBearExt4 as FieldExtension<BabyBearExt2>>::mul_assign_by_base(&mut via_base, &s_e2);
            prop_assert_eq!(full, via_base);
        }

        // Cross-check that the tower-Karatsuba and flat-quartic implementations
        // agree. The Field-trait dispatch picks one based on target_arch + feature,
        // but the inherent helpers stay reachable on every target so this test
        // exercises both algorithms on host regardless of which one is wired into
        // the trait on a given build.
        #[test]
        fn mul_tower_eq_flat(a in arb_e4(), b in arb_e4()) {
            let mut via_tower = a; via_tower.mul_assign_tower_impl(&b);
            let mut via_flat = a;  via_flat.mul_assign_flat_impl(&b);
            prop_assert_eq!(via_tower, via_flat);
        }

        #[test]
        fn square_tower_eq_flat(a in arb_e4()) {
            let mut via_tower = a; via_tower.square_tower_impl();
            let mut via_flat = a;  via_flat.square_flat_impl();
            prop_assert_eq!(via_tower, via_flat);
        }

        // Pin each helper to mul-self semantics independently, so a single-sided
        // bug in either algorithm is caught even if the cross-check above were
        // somehow symmetric.
        #[test]
        fn square_flat_eq_mul_flat_self(a in arb_e4()) {
            let mut sq = a; sq.square_flat_impl();
            let mut mu = a; mu.mul_assign_flat_impl(&a);
            prop_assert_eq!(sq, mu);
        }
    }
}
