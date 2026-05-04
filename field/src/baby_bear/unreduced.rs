use crate::baby_bear::base::BabyBearField;
use crate::baby_bear::ext2::BabyBearExt2;
use crate::baby_bear::ext4::BabyBearExt4;
use crate::field::UnreducedAccumulator;

#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct BabyBearRawProductSum(pub u128);

impl BabyBearRawProductSum {
    pub const ZERO: Self = Self(0);

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn from_product(a: BabyBearField, b: BabyBearField) -> Self {
        let raw = (a.0 as u64).wrapping_mul(b.0 as u64);
        Self(raw as u128)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn add_assign_product(&mut self, a: BabyBearField, b: BabyBearField) {
        let raw = (a.0 as u64).wrapping_mul(b.0 as u64);
        self.0 = self.0.wrapping_add(raw as u128);
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn finalize(self) -> BabyBearField {
        debug_assert!(self.0 < (1u128 << 127));

        let x = mont_reduce_step(self.0);
        let x = mont_reduce_step(x);
        let x = mont_reduce_step(x);

        let x = (x as u64) % BabyBearField::ORDER as u64;
        let x = x as u32;

        let corrected = crate::baby_bear::ops::mul_mod(x, BabyBearField::MONT_R2);
        let corrected = crate::baby_bear::ops::mul_mod(corrected, BabyBearField::MONT_R2);
        BabyBearField::from_raw_u32(corrected)
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct BabyBearExt4RawProductSum {
    pub lanes: [u128; 4],
}

impl BabyBearExt4RawProductSum {
    pub const ZERO: Self = Self { lanes: [0; 4] };

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn from_base_times_ext(a: BabyBearField, c: BabyBearExt4) -> Self {
        let a = a.0 as u64;
        let coeffs = [c.c0.c0.0, c.c0.c1.0, c.c1.c0.0, c.c1.c1.0];
        Self {
            lanes: [
                a.wrapping_mul(coeffs[0] as u64) as u128,
                a.wrapping_mul(coeffs[1] as u64) as u128,
                a.wrapping_mul(coeffs[2] as u64) as u128,
                a.wrapping_mul(coeffs[3] as u64) as u128,
            ],
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn add_assign_base_times_ext(&mut self, a: BabyBearField, c: BabyBearExt4) {
        let coeffs = [c.c0.c0.0, c.c0.c1.0, c.c1.c0.0, c.c1.c1.0];
        for k in 0..4 {
            let raw = (a.0 as u64).wrapping_mul(coeffs[k] as u64);
            self.lanes[k] = self.lanes[k].wrapping_add(raw as u128);
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn add_assign_ext(&mut self, e: BabyBearExt4) {
        let coeffs = [e.c0.c0.0, e.c0.c1.0, e.c1.c0.0, e.c1.c1.0];
        for k in 0..4 {
            let delta = (coeffs[k] as u128) << 32;
            self.lanes[k] = self.lanes[k].wrapping_add(delta);
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub fn finalize(self) -> BabyBearExt4 {
        let [l0, l1, l2, l3] = self.lanes;
        BabyBearExt4 {
            c0: BabyBearExt2 {
                c0: BabyBearRawProductSum(l0).finalize(),
                c1: BabyBearRawProductSum(l1).finalize(),
            },
            c1: BabyBearExt2 {
                c0: BabyBearRawProductSum(l2).finalize(),
                c1: BabyBearRawProductSum(l3).finalize(),
            },
        }
    }
}

impl UnreducedAccumulator<BabyBearField, BabyBearExt4> for BabyBearExt4RawProductSum {
    const ZERO: Self = Self::ZERO;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base_times_ext(&mut self, a: BabyBearField, c: BabyBearExt4) {
        Self::add_assign_base_times_ext(self, a, c)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_ext(&mut self, e: BabyBearExt4) {
        Self::add_assign_ext(self, e)
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn finalize(self) -> BabyBearExt4 {
        Self::finalize(self)
    }
}

// One Montgomery reduction step on a u128: result ≡ x · R⁻¹ (mod p).
// Bound: result ≤ x/R + p. Precondition: x + m·p must not overflow u128.
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn mont_reduce_step(x: u128) -> u128 {
    let low32 = x as u32;
    let m = low32.wrapping_mul(BabyBearField::MONT_K);
    let addend = (m as u128) * (BabyBearField::ORDER as u128);
    (x + addend) >> 32
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::field::{Field, FieldExtension};
    use proptest::prelude::*;

    fn arb_babybear() -> impl Strategy<Value = BabyBearField> {
        (0..BabyBearField::ORDER).prop_map(BabyBearField::new)
    }

    #[test]
    fn single_product_reduces_like_mul_mod() {
        let a = BabyBearField::new(3);
        let b = BabyBearField::new(5);

        let mut acc = BabyBearRawProductSum::ZERO;
        acc.add_assign_product(a, b);

        let mut expected = a;
        expected.mul_assign(&b);

        assert_eq!(acc.finalize(), expected);
    }

    #[test]
    fn two_products_match_reduced_sum() {
        let pairs = [
            (BabyBearField::new(3), BabyBearField::new(5)),
            (BabyBearField::new(7), BabyBearField::new(11)),
        ];

        let mut acc = BabyBearRawProductSum::ZERO;
        for (a, b) in pairs {
            acc.add_assign_product(a, b);
        }
        let got = acc.finalize();

        let mut expected = BabyBearField::ZERO;
        for (a, b) in pairs {
            let mut ab = a;
            ab.mul_assign(&b);
            expected.add_assign(&ab);
        }

        assert_eq!(got, expected);
    }

    fn arb_ext4() -> impl Strategy<Value = BabyBearExt4> {
        [
            arb_babybear(),
            arb_babybear(),
            arb_babybear(),
            arb_babybear(),
        ]
        .prop_map(|[a, b, c, d]| {
            <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs([a, b, c, d])
        })
    }

    #[test]
    fn ext4_single_base_times_ext_matches_reference() {
        let a = BabyBearField::new(7);
        let c = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs([
            BabyBearField::new(3),
            BabyBearField::new(5),
            BabyBearField::new(11),
            BabyBearField::new(13),
        ]);

        let mut acc = BabyBearExt4RawProductSum::ZERO;
        acc.add_assign_base_times_ext(a, c);

        let mut expected = c;
        expected.mul_assign_by_base(&a);

        assert_eq!(acc.finalize(), expected);
    }

    proptest! {
        #[test]
        fn sum_of_products_matches_reference(
            pairs in prop::collection::vec((arb_babybear(), arb_babybear()), 0..=256)
        ) {
            let mut acc = BabyBearRawProductSum::ZERO;
            for (a, b) in &pairs {
                acc.add_assign_product(*a, *b);
            }
            let got = acc.finalize();

            let mut expected = BabyBearField::ZERO;
            for (a, b) in &pairs {
                let mut ab = *a;
                ab.mul_assign(b);
                expected.add_assign(&ab);
            }

            prop_assert_eq!(got, expected);
        }

        #[test]
        fn ext4_add_assign_ext_matches_reference(
            initial_terms in prop::collection::vec((arb_babybear(), arb_ext4()), 0..=8),
            adds in prop::collection::vec(arb_ext4(), 0..=8),
        ) {
            let mut acc = BabyBearExt4RawProductSum::ZERO;
            for (a, c) in &initial_terms {
                acc.add_assign_base_times_ext(*a, *c);
            }
            for e in &adds {
                acc.add_assign_ext(*e);
            }
            let got = acc.finalize();

            let mut expected = BabyBearExt4::ZERO;
            for (a, c) in &initial_terms {
                let mut term = *c;
                term.mul_assign_by_base(a);
                expected.add_assign(&term);
            }
            for e in &adds {
                expected.add_assign(e);
            }

            prop_assert_eq!(got, expected);
        }

        #[test]
        fn ext4_sum_of_base_times_ext_matches_reference(
            terms in prop::collection::vec((arb_babybear(), arb_ext4()), 0..=256)
        ) {
            let mut acc = BabyBearExt4RawProductSum::ZERO;
            for (a, c) in &terms {
                acc.add_assign_base_times_ext(*a, *c);
            }
            let got = acc.finalize();

            let mut expected = BabyBearExt4::ZERO;
            for (a, c) in &terms {
                let mut term = *c;
                term.mul_assign_by_base(a);
                expected.add_assign(&term);
            }

            prop_assert_eq!(got, expected);
        }
    }
}
