use super::*;
use rand::Rng;

pub trait Field:
    'static
    + Clone
    + Copy
    + Default
    + core::fmt::Display
    + core::fmt::Debug
    + core::hash::Hash
    + core::cmp::PartialEq
    + core::cmp::Eq
    + core::marker::Send
    + core::marker::Sync
    + core::default::Default
    + Rand
    + Sized
{
    const ZERO: Self;
    const ONE: Self;

    type CharField = Self;

    // zero check
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn inverse(&self) -> Option<Self>;

    // add
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // sub
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // mul
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // square
    fn square(&'_ mut self) -> &'_ mut Self;
    // negate
    fn negate(&'_ mut self) -> &'_ mut Self;
    // double
    fn double(&'_ mut self) -> &'_ mut Self;

    fn pow(&self, mut exp: u32) -> Self {
        let mut base = *self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp % 2 == 1 {
                result.mul_assign(&base);
            }

            exp >>= 1;
            base.square();
        }

        result
    }

    fn exp_power_of_2(&mut self, power_log: usize) {
        for _ in 0..power_log {
            self.square();
        }
    }

    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        unimplemented!()
    }
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        unimplemented!()
    }
    #[inline(always)]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        // Default implementation
        self.mul_assign(a);
        self.add_assign(b);

        self
    }
    #[inline(always)]
    fn add_assign_product(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        // Default implementation
        let mut t = *a;
        t.mul_assign(&b);
        self.add_assign(&t);

        self
    }
}

pub trait PrimeField: Field {
    const TWO: Self;
    const MINUS_ONE: Self;
    const NUM_BYTES_IN_REPR: usize;

    const CHAR_BITS: usize;
    const CHARACTERISTICS: u64;

    fn as_u64(self) -> u64;
    fn from_u64_unchecked(value: u64) -> Self;
    fn from_u64_with_reduction(value: u64) -> Self;
    fn from_u64(value: u64) -> Option<Self>;
    fn as_u64_reduced(&self) -> u64;

    fn as_boolean(&self) -> bool;

    fn from_boolean(flag: bool) -> Self {
        if flag {
            Self::ONE
        } else {
            Self::ZERO
        }
    }

    fn to_le_bytes(self) -> [u8; Self::NUM_BYTES_IN_REPR];

    fn increment_unchecked(&'_ mut self);
}

// this field can be used as base field for quadratic extension
pub trait BaseField: Field {
    const QUADRATIC_NON_RESIDUE: Self;

    fn mul_by_non_residue(elem: &mut Self) {
        elem.mul_assign(&Self::QUADRATIC_NON_RESIDUE);
    }
}

// #[repr(C)]
// #[derive(Clone, Copy, Hash)]
// pub struct ExtensionField<F: Field, const DEGREE: usize> {
//     pub coeffs: [F; DEGREE],
// }

// impl<F: Field, const DEGREE: usize> core::cmp::PartialEq for ExtensionField<F, DEGREE> {
//     #[inline(always)]
//     fn eq(&self, other: &Self) -> bool {
//         self.coeffs
//             .iter()
//             .zip(other.coeffs.iter())
//             .all(|(x, y)| x.eq(y))
//     }
// }

// impl<F: Field, const DEGREE: usize> core::cmp::Eq for ExtensionField<F, DEGREE> {}

// impl<F: Field, const DEGREE: usize> core::default::Default for ExtensionField<F, DEGREE> {
//     #[inline(always)]
//     fn default() -> Self {
//         ExtensionField {
//             coeffs: [F::default(); DEGREE],
//         }
//     }
// }

// impl<F: BaseField> Field for ExtensionField<F, 2>
// where
//     ExtensionField<F, 2>: core::fmt::Debug + core::fmt::Display,
// {
//     const ZERO: Self = ExtensionField {
//         coeffs: [F::ZERO; 2],
//     };
//     const ONE: Self = ExtensionField {
//         coeffs: [F::ONE, F::ZERO],
//     };
//     type CharField = F::CharField;

//     #[inline]
//     fn is_zero(&self) -> bool {
//         self.coeffs[0].is_zero() && self.coeffs[1].is_zero()
//     }
//     #[inline]
//     fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
//         self.coeffs[0].add_assign(&other.coeffs[0]);
//         self.coeffs[1].add_assign(&other.coeffs[1]);

//         self
//     }

//     #[inline]
//     fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
//         self.coeffs[0].sub_assign(&other.coeffs[0]);
//         self.coeffs[1].sub_assign(&other.coeffs[1]);

//         self
//     }

//     #[inline]
//     fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
//         let mut v0 = self.coeffs[0];
//         v0.mul_assign(&other.coeffs[0]);
//         let mut v1 = self.coeffs[1];
//         v1.mul_assign(&other.coeffs[1]);

//         let t = self.coeffs[0];
//         self.coeffs[1].add_assign(&t);

//         let mut t0 = other.coeffs[0];
//         t0.add_assign(&other.coeffs[1]);
//         self.coeffs[1].mul_assign(&t0);
//         self.coeffs[1].sub_assign(&v0);
//         self.coeffs[1].sub_assign(&v1);
//         self.coeffs[0] = v0;
//         F::mul_by_non_residue(&mut v1);
//         self.coeffs[0].add_assign(&v1);

//         self
//     }

//     #[inline]
//     fn square(&mut self) -> &mut Self {
//         let mut v0 = self.coeffs[0];
//         v0.sub_assign(&self.coeffs[1]);
//         let mut v3 = self.coeffs[0];
//         let mut t0 = self.coeffs[1];
//         F::mul_by_non_residue(&mut t0);
//         v3.sub_assign(&t0);
//         let mut v2 = self.coeffs[0];
//         v2.mul_assign(&self.coeffs[1]);
//         v0.mul_assign(&v3);
//         v0.add_assign(&v2);

//         self.coeffs[1] = v2;
//         self.coeffs[1].double();
//         self.coeffs[0] = v0;
//         F::mul_by_non_residue(&mut v2);
//         self.coeffs[0].add_assign(&v2);

//         self
//     }

//     #[inline]
//     fn negate(&mut self) -> &mut Self {
//         self.coeffs[0].negate();
//         self.coeffs[1].negate();

//         self
//     }

//     #[inline]
//     fn double(&mut self) -> &mut Self {
//         self.coeffs[0].double();
//         self.coeffs[1].double();

//         self
//     }

//     fn inverse(&self) -> Option<Self> {
//         let mut v0 = self.coeffs[0];
//         v0.square();
//         let mut v1 = self.coeffs[1];
//         v1.square();
//         // v0 = v0 - beta * v1
//         let mut v1_by_nonresidue = v1;
//         F::mul_by_non_residue(&mut v1_by_nonresidue);
//         v0.sub_assign(&v1_by_nonresidue);
//         match v0.inverse() {
//             Some(inversed) => {
//                 let mut c0 = self.coeffs[0];
//                 c0.mul_assign(&inversed);
//                 let mut c1 = self.coeffs[1];
//                 c1.mul_assign(&inversed);
//                 c1.negate();

//                 let new = Self { coeffs: [c0, c1] };
//                 Some(new)
//             }
//             None => None,
//         }
//     }

//     #[inline]
//     fn mul_by_two(&'_ mut self) -> &'_ mut Self {
//         self.coeffs[0].mul_by_two();
//         self.coeffs[1].mul_by_two();
//         self
//     }

//     #[inline]
//     fn div_by_two(&'_ mut self) -> &'_ mut Self {
//         self.coeffs[0].div_by_two();
//         self.coeffs[1].div_by_two();
//         self
//     }
// }

pub trait FieldExtension<BaseField: Field> {
    const DEGREE: usize;
    fn mul_assign_by_base(&mut self, elem: &BaseField) -> &mut Self;
    fn into_coeffs_in_base(self) -> [BaseField; Self::DEGREE];
    fn from_base_coeffs_array(coefs: &[BaseField; Self::DEGREE]) -> Self;
    fn from_coeffs_in_base(coefs: &[BaseField]) -> Self;
    fn from_coeffs_in_base_ref(coefs: &[&BaseField]) -> Self;
    fn from_coeffs_in_base_iter<I: Iterator<Item = BaseField>>(coefs_iter: I) -> Self;
    fn coeffs_in_base(&self) -> &[BaseField];
    fn add_assign_base(&mut self, elem: &BaseField) -> &mut Self;
    fn sub_assign_base(&mut self, elem: &BaseField) -> &mut Self;
    fn from_base(elem: BaseField) -> Self;
    fn get_coef_mut(&mut self, idx: usize) -> &mut BaseField;
}

impl<F: Field> FieldExtension<F> for F {
    const DEGREE: usize = 1;
    #[inline(always)]
    fn from_coeffs_in_base(coefs: &[F]) -> Self {
        coefs[0]
    }

    #[inline(always)]
    fn from_base_coeffs_array(coefs: &[F; Self::DEGREE]) -> Self {
        coefs[0]
    }

    #[inline(always)]
    fn from_coeffs_in_base_ref(coefs: &[&F]) -> Self {
        *coefs[0]
    }

    #[inline(always)]
    fn into_coeffs_in_base(self) -> [Self; Self::DEGREE] {
        [self; Self::DEGREE]
    }

    #[inline(always)]
    fn from_coeffs_in_base_iter<I: Iterator<Item = F>>(mut coefs_iter: I) -> Self {
        coefs_iter.next().unwrap()
    }

    #[inline(always)]
    fn coeffs_in_base(&self) -> &[F] {
        core::slice::from_ref(self)
    }

    #[inline(always)]
    fn mul_assign_by_base(&mut self, elem: &F) -> &mut Self {
        self.mul_assign(elem)
    }

    #[inline(always)]
    fn add_assign_base(&mut self, elem: &F) -> &mut Self {
        self.add_assign(elem)
    }

    #[inline(always)]
    fn sub_assign_base(&mut self, elem: &F) -> &mut Self {
        self.sub_assign(elem)
    }

    #[inline(always)]
    fn from_base(elem: F) -> Self {
        elem
    }

    #[inline(always)]
    fn get_coef_mut(&mut self, idx: usize) -> &mut F {
        assert_eq!(idx, 0);
        self
    }
}

// impl<F: Field, const N: usize> FieldExtension<F> for ExtensionField<F, N> {
//     const DEGREE: usize = N;
//     #[inline(always)]
//     fn mul_assign_by_base(&mut self, base: &F) -> &mut Self {
//         self.coeffs.iter_mut().for_each(|x| {
//             x.mul_assign(base);
//         });
//         self
//     }

//     #[inline(always)]
//     fn add_assign_base(&mut self, elem: &F) -> &mut Self {
//         self.coeffs[0].add_assign(elem);
//         self
//     }

//     #[inline(always)]
//     fn sub_assign_base(&mut self, elem: &F) -> &mut Self {
//         self.coeffs[0].sub_assign(elem);
//         self
//     }

//     #[inline(always)]
//     fn into_coeffs_in_base(self) -> [F; Self::DEGREE] {
//         debug_assert_eq!(Self::DEGREE, N);
//         unsafe { core::ptr::read(self.coeffs.as_ptr().cast()) }
//     }

//     #[inline(always)]
//     fn coeffs_in_base(&self) -> &[F] {
//         &self.coeffs
//     }

//     #[inline(always)]
//     fn from_coeffs_in_base(coeffs: &[F]) -> Self {
//         debug_assert_eq!(coeffs.len(), 2);
//         unsafe {
//             Self {
//                 coeffs: coeffs.try_into().unwrap_unchecked(),
//             }
//         }
//     }

//     #[inline(always)]
//     fn from_coeffs_in_base_ref(coeffs: &[&F]) -> Self {
//         Self {
//             coeffs: core::array::from_fn(|idx| *coeffs[idx]),
//         }
//     }

//     #[inline(always)]
//     fn from_coeffs_in_base_iter<I: Iterator<Item = F>>(mut coefs_iter: I) -> Self {
//         Self {
//             coeffs: core::array::from_fn(|_| coefs_iter.next().unwrap()),
//         }
//     }

//     #[inline(always)]
//     fn from_base(elem: F) -> Self {
//         let coeffs = core::array::from_fn(|idx: usize| if idx == 0 { elem } else { F::ZERO });
//         Self { coeffs }
//     }

//     #[inline(always)]
//     fn get_coef_mut(&mut self, idx: usize) -> &mut F {
//         &mut self.coeffs[idx]
//     }
// }

pub trait TwoAdicField: Field {
    /// The number of factors of two in this field's multiplicative group.
    const TWO_ADICITY: usize;

    /// Returns a generator of the multiplicative group of order `2^bits`.
    /// Assumes `bits < TWO_ADICITY`, otherwise the result is undefined.
    /// all functions here except for two_adic_generator should not even exist
    #[must_use]
    fn two_adic_generator() -> Self;

    #[must_use]
    fn two_adic_group_order() -> usize;
}

impl<F: PrimeField> Rand for F {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> F {
        F::from_u64_unchecked(rng.random_range(0..F::CHARACTERISTICS))
    }
}

// impl<F: Field + Rand, const DEGREE: usize> Rand for ExtensionField<F, DEGREE> {
//     fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
//         Self {
//             coeffs: core::array::from_fn(|_: usize| F::random_element(rng)),
//         }
//     }
// }
