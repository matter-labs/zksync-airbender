use field::baby_bear::{base::BabyBearField as F, ext4::BabyBearExt4 as E};
use field::{FieldExtension, PrimeField};
use verifier::add_sub_lui_auipc_mop::sec_100::common::{
    eval_multilinear_with_monomial_tensor, precompute_monomial_tensor,
};
use verifier_common::blake2s_u32::AlignedArray64;
use verifier_common::lazy_vec::LazyVec;

#[test]
fn authenticated_words_match_materialized_coefficients() {
    for k in 0..=5 {
        let challenges: Vec<E> = (0..k)
            .map(|j| E::from_array_of_base(core::array::from_fn(|i| F::new(17 + 3 * j + i as u32))))
            .collect();
        let mut weights = LazyVec::<E, 32>::new();
        precompute_monomial_tensor(&challenges, &mut weights);
        for seed in [0u32, 1, 7919] {
            let coefficients: Vec<E> = (0..1u32 << k)
                .map(|j| {
                    E::from_array_of_base(core::array::from_fn(|i| F::new(seed * (j + i as u32))))
                })
                .collect();
            let mut words = AlignedArray64::<u32, 128>::from_value(0);
            for (j, coefficient) in coefficients.iter().enumerate() {
                for (i, base) in <E as FieldExtension<F>>::into_coeffs(*coefficient)
                    .as_ref()
                    .iter()
                    .enumerate()
                {
                    words[4 * j + i] = base.as_u32_raw_repr();
                }
            }
            let leaf: &[E] = unsafe { words.transmute_subslice(0, coefficients.len()) };
            assert_eq!(leaf, &coefficients[..], "k={k}, seed={seed}");
            assert_eq!(
                eval_multilinear_with_monomial_tensor(leaf, weights.as_slice()),
                eval_multilinear_with_monomial_tensor(&coefficients, weights.as_slice()),
                "k={k}, seed={seed}",
            );
        }
    }
}
