use fft::GoodAllocator;
use field::{Field, FieldExtension, PrimeField};

pub fn evaluate_virtual_range_check_setup_poly<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const BITS: u32,
>(
    evaluation_point: &[E],
    trace_len_log2: u32,
) -> E {
    assert_eq!(evaluation_point.len(), trace_len_log2 as usize);
    assert!(BITS <= trace_len_log2);
    // for poly P(x_1, x_2, ..., xN) x1 represents MSB in enumeration of hypercube values in our system,
    // so we blindly guess a poly that has a form of [0, 1, 2, ..., 2^BITS-1, 0, 0, ..., 0]

    // Such poly is (x_N + 2 * x_{N - 1} + 4 * x_{N - 2} + ... + 2^K * x_{N-K}) * (1 - X_{N - K - 1}) * (1 - X_{N - K - 2}) + ...
    // and it's obviously multilinear

    let mut result = E::ZERO;
    let mut prefactor = F::ONE;
    for el in evaluation_point.iter().rev().take(BITS as usize) {
        let mut t = *el;
        t.mul_assign_by_base(&prefactor);
        result.add_assign(&t);
        prefactor.double();
    }

    for el in evaluation_point.iter().rev().skip(BITS as usize) {
        let mut t = E::ONE;
        t.sub_assign(el);
        result.mul_assign(&t);
    }

    result
}

pub fn materialize_virtual_range_check_setup_poly<
    F: PrimeField,
    A: GoodAllocator,
    const BITS: u32,
>(
    trace_len_log2: u32,
) -> Box<[F], A> {
    assert!(BITS <= trace_len_log2);
    let mut result = Vec::with_capacity_in(1 << trace_len_log2, A::default());
    result.resize(1 << trace_len_log2, F::ZERO);
    for (i, dst) in result[..(1 << BITS)].iter_mut().enumerate() {
        *dst = F::from_u32_unchecked(i as u32);
    }

    result.into_boxed_slice()
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use field::{
        baby_bear::{base::BabyBearField, ext4::BabyBearExt4},
        Rand,
    };

    use super::*;
    type F = BabyBearField;
    type E = BabyBearExt4;

    #[test]
    fn check_consistency() {
        use crate::gkr::sumcheck::eq_poly::*;
        let worker = worker::Worker::new_with_num_threads(8);
        let mut rng = rand::rng();
        for domain_size_log2 in 19..=24 {
            let eval_point: Vec<E> = (0..domain_size_log2)
                .map(|_| E::random_element(&mut rng))
                .collect();
            let mut eq_polys = make_eq_poly_in_full::<E>(&eval_point[..], &worker);
            let eq_poly = eq_polys.pop().unwrap();
            let naive_poly = materialize_virtual_range_check_setup_poly::<F, Global, 16>(
                domain_size_log2 as u32,
            );
            let naive_eval = evaluate_with_precomputed_eq(&naive_poly[..], &eq_poly[..]);
            let succinct_eval = evaluate_virtual_range_check_setup_poly::<F, E, 16>(
                &eval_point,
                domain_size_log2 as u32,
            );
            assert_eq!(
                naive_eval, succinct_eval,
                "diverged for domain 2^{}",
                domain_size_log2
            );
        }
    }
}
