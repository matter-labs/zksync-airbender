use crate::{baby_bear::ext4::BabyBearExt4, Field};

#[no_mangle]
#[inline(never)]
pub fn test_e4_mul_via_fma_option(a: &mut BabyBearExt4, b: &BabyBearExt4) {
    a.mul_assign(b);
}

#[no_mangle]
#[inline(never)]
pub fn test_e4_square_via_fma_option(a: &mut BabyBearExt4) {
    a.square();
}

#[no_mangle]
#[inline(never)]
pub fn test_e4_fma_via_fma_option(a: &mut BabyBearExt4, b: &BabyBearExt4, c: &BabyBearExt4) {
    a.add_assign_product(b, c);
}

#[cfg(test)]
mod cpu_extension_eq_hash {
    use crate::baby_bear::{
        base::BabyBearField, ext2::BabyBearExt2, ext4::BabyBearExt4, ext6::BabyBearExt6,
    };
    use crate::{Mersenne31Complex, Mersenne31Field, Mersenne31Quartic};
    use std::collections::hash_map::DefaultHasher;
    use std::fmt::Debug;
    use std::hash::{Hash, Hasher};

    fn hash(value: &impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    fn assert_eq_hash_consistent<T: Eq + Hash + Debug>(values: &[T]) {
        for left in values {
            for right in values {
                if left == right {
                    assert_eq!(hash(left), hash(right), "{left:?} == {right:?}");
                }
            }
        }
    }

    #[test]
    fn ext6_equality_compares_c2() {
        let left = BabyBearExt6::from_array_of_base([1, 2, 3, 4, 5, 6].map(BabyBearField::new));
        let right = BabyBearExt6 {
            c2: BabyBearExt2::new(BabyBearField::new(5), BabyBearField::new(7)),
            ..left
        };
        assert_ne!(
            left, right,
            "the third extension coefficient participates in equality"
        );
    }

    #[test]
    fn extension_equality_agrees_with_hash() {
        // Mersenne31 has two representations of zero; component hashes must
        // agree with component equality, rather than hashing the raw limbs.
        let zero = Mersenne31Field::new(0);
        let alternate_zero = Mersenne31Field::new(Mersenne31Field::ORDER);
        assert_eq_hash_consistent(&[
            Mersenne31Complex::new(zero, zero),
            Mersenne31Complex::new(alternate_zero, zero),
            Mersenne31Complex::new(zero, alternate_zero),
        ]);
        assert_eq_hash_consistent(&[
            Mersenne31Quartic::from_array_of_base([zero; 4]),
            Mersenne31Quartic::from_array_of_base([alternate_zero; 4]),
        ]);
        assert_eq_hash_consistent(&[
            BabyBearExt2::new(BabyBearField::new(1), BabyBearField::new(2)),
            BabyBearExt2::new(BabyBearField::new(1), BabyBearField::new(2)),
        ]);
        assert_eq_hash_consistent(&[
            BabyBearExt4::from_array_of_base([1, 2, 3, 4].map(BabyBearField::new)),
            BabyBearExt4::from_array_of_base([1, 2, 3, 4].map(BabyBearField::new)),
        ]);
        assert_eq_hash_consistent(&[
            BabyBearExt6::from_array_of_base([1, 2, 3, 4, 5, 6].map(BabyBearField::new)),
            BabyBearExt6::from_array_of_base([1, 2, 3, 4, 5, 6].map(BabyBearField::new)),
            BabyBearExt6::from_array_of_base([1, 2, 3, 4, 5, 7].map(BabyBearField::new)),
        ]);
    }
}
