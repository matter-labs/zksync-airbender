use fft::GoodAllocator;
use field::{Field, FieldExtension, PrimeField};
use worker::Worker;

pub fn evaluate_virtual_inits_and_teardowns_base_address_setup_polys<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const WORD_BITS: u32,
>(
    evaluation_point: &[E],
    trace_len_log2: u32,
) -> (E, E) {
    assert_eq!(evaluation_point.len(), trace_len_log2 as usize);
    assert!(WORD_BITS <= 3);
    // for poly P(x_1, x_2, ..., xN) x1 represents MSB in enumeration of hypercube values in our system

    // for inits and teardowns base addresses we want one poly that is just wraps around 2^16,
    // and has values that are 0 mod 2^WORD_BITS, and another poly that has the same value
    // for every 2^(16 - WORD_BITS) values, and then increments by 1

    // poly that cycles is easy - 2^WORD_BITS * (x_N + 2 * x_{N - 1} + 4 * x_{N - 2} + ... + 2^K * x_{N-K}),
    // it just has no dependency on the coordinates that encode higher bits

    // poyl that increments it also easy - it should just have no dependency on lower bits
    // (x_(N - (16 - WORD_BITS)) + 2 * x_{N - 1 - (16 - WORD_BITS)} + ...)

    let mut low_eval = E::ZERO;
    let mut prefactor = F::from_u32_unchecked(1 << WORD_BITS);
    for el in evaluation_point
        .iter()
        .rev()
        .take((16 - WORD_BITS) as usize)
    {
        let mut t = *el;
        t.mul_assign_by_base(&prefactor);
        low_eval.add_assign(&t);
        prefactor.double();
    }

    let mut high_eval = E::ZERO;
    let mut prefactor = F::ONE;
    for el in evaluation_point
        .iter()
        .rev()
        .skip((16 - WORD_BITS) as usize)
    {
        let mut t = *el;
        t.mul_assign_by_base(&prefactor);
        high_eval.add_assign(&t);
        prefactor.double();
    }

    (low_eval, high_eval)
}

pub fn materialize_virtual_inits_and_teardowns_base_address_setup_poly<
    F: PrimeField,
    A: GoodAllocator,
    const WORD_BITS: u32,
>(
    trace_len_log2: u32,
    worker: &Worker,
) -> (Box<[F], A>, Box<[F], A>) {
    let mut low_eval = Box::new_uninit_slice_in(1 << trace_len_log2, A::default());
    let mut high_eval = Box::new_uninit_slice_in(1 << trace_len_log2, A::default());
    use crate::gkr::prover::apply_row_wise;
    apply_row_wise::<_, ()>(
        vec![&mut low_eval[..], &mut high_eval[..]],
        vec![],
        1 << trace_len_log2,
        worker,
        |dests, _, chunk_start, chunk_size| {
            assert_eq!(dests.len(), 2);
            let destinations: [&mut [core::mem::MaybeUninit<F>]; 2] = dests.try_into().unwrap();
            let [low, high] = destinations;
            let low_mask = (1 << 16) - 1;
            for index in 0..chunk_size {
                let absolute_index = chunk_start + index;
                let low_val = ((absolute_index as u32) << WORD_BITS) & low_mask;
                low[index].write(F::from_u32_unchecked(low_val));
                let high_val = absolute_index >> (16 - WORD_BITS);
                high[index].write(F::from_u32_unchecked(high_val as u32));
            }
        },
    );

    unsafe { (low_eval.assume_init(), high_eval.assume_init()) }
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
        for domain_size_log2 in 24..=24 {
            let eval_point: Vec<E> = (0..domain_size_log2)
                .map(|_| E::random_element(&mut rng))
                .collect();
            let mut eq_polys = make_eq_poly_in_full::<E>(&eval_point[..], &worker);
            let eq_poly = eq_polys.pop().unwrap();
            let (naive_low, naive_high) =
                materialize_virtual_inits_and_teardowns_base_address_setup_poly::<F, Global, 2>(
                    domain_size_log2 as u32,
                    &worker,
                );
            let naive_eval_low = evaluate_with_precomputed_eq(&naive_low[..], &eq_poly[..]);
            let naive_eval_high = evaluate_with_precomputed_eq(&naive_high[..], &eq_poly[..]);
            let (succinct_eval_low, succinct_eval_high) =
                evaluate_virtual_inits_and_teardowns_base_address_setup_polys::<F, E, 2>(
                    &eval_point,
                    domain_size_log2 as u32,
                );
            assert_eq!(
                naive_eval_low, succinct_eval_low,
                "low diverged for domain 2^{}",
                domain_size_log2
            );
            assert_eq!(
                naive_eval_high, succinct_eval_high,
                "high diverged for domain 2^{}",
                domain_size_log2
            );
        }
    }
}
