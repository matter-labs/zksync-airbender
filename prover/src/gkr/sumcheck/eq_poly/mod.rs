use std::mem::MaybeUninit;

use field::{Field, FieldExtension, TwoAdicField};
use worker::{IterableWithGeometry, Worker};

use crate::gkr::PAR_THRESHOLD;

use super::*;

#[inline(always)]
fn compute_next_layer<E: Field>(
    prev: &[E],
    left: &mut [MaybeUninit<E>],
    right: &mut [MaybeUninit<E>],
    f1: &E,
) {
    for (p, (left_dst, right_dst)) in prev.iter().zip(left.iter_mut().zip(right.iter_mut())) {
        let mut right = *p;
        right.mul_assign(f1);
        let mut left = *p;
        left.sub_assign(&right);

        left_dst.write(left);
        right_dst.write(right);
    }
}

pub fn make_eq_poly_impl<E: Field, const FULL: bool>(
    challenges: &[E],
    worker: &Worker,
) -> Vec<Box<[E]>> {
    assert!(challenges.len() > 0);

    let mut result = Vec::with_capacity(challenges.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let mut size = 1;
    let mut idx = challenges.len();

    let bound = if FULL {
        challenges.len() + 1
    } else {
        challenges.len()
    };

    for _ in 1..bound {
        let half_size = size;
        size *= 2;
        idx -= 1;

        let challenge = challenges[idx];

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");

        let f1 = challenge;

        assert_eq!(previous_layer.len(), half_size);

        let (left, right) = layer.split_at_mut(half_size);

        worker.scope_with_threshold(half_size, PAR_THRESHOLD, |scope, geometry| {
            previous_layer
                .chunks_for_geometry(geometry)
                .enumerate()
                .zip(
                    left.chunks_for_geometry_mut(geometry)
                        .zip(right.chunks_for_geometry_mut(geometry)),
                )
                .for_each(|((idx, prev), (left_chunk, right_chunk))| {
                    Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                        compute_next_layer(prev, left_chunk, right_chunk, &f1)
                    });
                })
        });

        result.push(unsafe { layer.assume_init() });
    }

    result
}

pub fn make_eq_poly_reduced<E: Field>(challenges: &[E], worker: &Worker) -> Vec<Box<[E]>> {
    make_eq_poly_impl::<E, false>(challenges, worker)
}

pub fn make_eq_poly_in_full<E: Field>(challenges: &[E], worker: &Worker) -> Vec<Box<[E]>> {
    make_eq_poly_impl::<E, true>(challenges, worker)
}

// Domain equality polys
fn make_domain_eq_poly_impl<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    const FULL: bool,
>(
    challenges: &[E],
) -> Vec<Box<[E]>> {
    // See WHIR comments: our equality poly is special here as we choose not the 0/1 hypercube, but 1/omega one.
    // So our equality is eq(X, Y) = 1 / (omega - 1) ^ 2 * (X - 1)(Y - 1) + (1 - (X - 1)/(omega - 1))(1 - (Y - 1)/(omega - 1))

    assert!(challenges.len() > 0);
    // challenges[0] is the challenge used to fold a variable, that is encoded as MSB in the values enumeration,
    // and we will produce the outputs in a same form. We also keep all intermediate forms for simplicity
    let mut result = Vec::with_capacity(challenges.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let mut size = 1;
    let mut idx = challenges.len();

    let bound = if FULL {
        challenges.len() + 1
    } else {
        challenges.len()
    };

    for _ in 1..bound {
        size *= 2;
        idx -= 1;

        let omega = F::TWO_ADICITY_GENERATORS[idx + 1];
        let mut omega_minus_one = omega;
        omega_minus_one.sub_assign(&F::ONE);
        let omega_minus_one_inverse = omega_minus_one.inverse().expect("not 1-sized domain");

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");

        // eq(X, challenge)
        let challenge = challenges[idx];

        let mut eq_at_1 = E::ONE;
        eq_at_1.sub_assign(&challenge);
        eq_at_1.mul_assign_by_base(&omega_minus_one_inverse);
        eq_at_1.add_assign(&E::ONE);

        let mut eq_at_omega = challenge;
        eq_at_omega.sub_assign(&E::ONE);
        eq_at_omega.mul_assign_by_base(&omega_minus_one_inverse);

        dbg!(eq_at_1);
        dbg!(eq_at_omega);

        let half_size = size / 2;

        assert_eq!(previous_layer.len(), half_size);

        for index in 0..half_size {
            let mut left = previous_layer[index];
            let mut right = left;
            left.mul_assign(&eq_at_1);
            right.mul_assign(&eq_at_omega);
            layer[index].write(left);
            layer[index + half_size].write(right);
        }

        let layer = unsafe { layer.assume_init() };
        dbg!(&layer);
        result.push(layer);
    }

    result
}

pub fn make_domain_eq_poly_reduced<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    challenges: &[E],
) -> Vec<Box<[E]>> {
    make_domain_eq_poly_impl::<F, E, false>(challenges)
}

pub fn make_domain_eq_poly_in_full<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    challenges: &[E],
) -> Vec<Box<[E]>> {
    make_domain_eq_poly_impl::<F, E, true>(challenges)
}

pub(crate) fn evaluate_with_precomputed_eq<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_values: &[F],
    eq: &[E],
) -> E {
    assert_eq!(base_field_values.len(), eq.len());
    let mut result = E::ZERO;
    for (a, b) in base_field_values.iter().zip(eq.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }

    result
}

#[track_caller]
pub(crate) fn evaluate_with_precomputed_eq_ext<E: Field>(ext_field_values: &[E], eq: &[E]) -> E {
    assert_eq!(ext_field_values.len(), eq.len());
    let mut result = E::ZERO;
    for (a, b) in ext_field_values.iter().zip(eq.iter()) {
        let mut t = *b;
        t.mul_assign(a);
        result.add_assign(&t);
    }

    result
}

pub(crate) fn evaluate_constant_and_quadratic_coeffs_with_precomputed_eq<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    values: &[[E; 2]],
    eq: &[E],
    worker: &Worker,
) -> [E; 2] {
    let work_size = values.len();

    assert_eq!(work_size, eq.len());

    if work_size == 0 {
        return [E::ZERO; 2];
    }

    let mut partial_results = vec![
        [E::ZERO; 2];
        worker
            .get_geometry_with_threshold(work_size, PAR_THRESHOLD)
            .len()
    ];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let values_chunks = values.chunks_for_geometry(geometry);
        let eq_chunks = eq.chunks_for_geometry(geometry);

        partial_results
            .iter_mut()
            .enumerate()
            .zip(values_chunks.zip(eq_chunks))
            .for_each(|((idx, partial), (v_chunk, e_chunk))| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    let mut res0 = E::ZERO;
                    let mut res1 = E::ZERO;

                    for (a, b) in v_chunk.iter().zip(e_chunk.iter()) {
                        let mut t0 = *b;
                        t0.mul_assign(&a[0]);
                        res0.add_assign(&t0);

                        let mut t1 = *b;
                        t1.mul_assign(&a[1]);
                        res1.add_assign(&t1);
                    }

                    *partial = [res0, res1];
                })
            });
    });

    partial_results
        .iter()
        .fold([E::ZERO; 2], |mut acc, [a, b]| {
            acc[0].add_assign(a);
            acc[1].add_assign(b);
            acc
        })
}

#[cfg(test)]
pub(crate) fn evaluate_constant_and_quadratic_coeffs_with_precomputed_eq_serial<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    values: &[[E; 2]],
    eq: &[E],
) -> [E; 2] {
    assert_eq!(values.len(), eq.len());
    let mut result_0 = E::ZERO;
    let mut result_1 = E::ZERO;
    for (a, b) in values.iter().zip(eq.iter()) {
        let [a0, a1] = a;

        let mut t0 = *b;
        t0.mul_assign(a0);
        result_0.add_assign(&t0);

        let mut t1 = *b;
        t1.mul_assign(a1);
        result_1.add_assign(&t1);
    }

    [result_0, result_1]
}

#[cfg(test)]
pub fn make_eq_poly_impl_serial<E: Field, const FULL: bool>(challenges: &[E]) -> Vec<Box<[E]>> {
    assert!(challenges.len() > 0);
    // challenges[0] is the challenge used to fold a variable, that is encoded as MSB in the values enumeration,
    // and we will produce the outputs in a same form. We also keep all intermediate forms for simplicity
    let mut result = Vec::with_capacity(challenges.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let mut size = 1;
    let mut idx = challenges.len();

    let bound = if FULL {
        challenges.len() + 1
    } else {
        challenges.len()
    };

    for _ in 1..bound {
        size *= 2;
        idx -= 1;

        let challenge = challenges[idx];

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");

        let f1 = challenge;

        let half_size = size / 2;

        assert_eq!(previous_layer.len(), half_size);

        for index in 0..half_size {
            let mut right = previous_layer[index];
            right.mul_assign(&f1);
            let mut left = previous_layer[index];
            left.sub_assign(&right);
            layer[index].write(left);
            layer[index + half_size].write(right);
        }

        result.push(unsafe { layer.assume_init() });
    }

    result
}

#[cfg(test)]
pub fn make_eq_poly_reduced_serial<E: Field>(challenges: &[E]) -> Vec<Box<[E]>> {
    make_eq_poly_impl_serial::<E, false>(challenges)
}

#[cfg(test)]
pub fn make_eq_poly_in_full_serial<E: Field>(challenges: &[E]) -> Vec<Box<[E]>> {
    make_eq_poly_impl_serial::<E, true>(challenges)
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use rand::{rngs::ThreadRng, RngCore};

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_in_ext(rng: &mut ThreadRng) -> E
    where
        [(); <E as FieldExtension<F>>::DEGREE]: Sized,
    {
        let coefs = [(); <E as FieldExtension<F>>::DEGREE]
            .map(|_| F::from_u32_with_reduction(rng.next_u32()));
        <E as FieldExtension<F>>::from_coeffs(coefs)
    }

    #[test]
    fn test_evaluate_constant_and_quadratic_coeffs_with_precomputed_eq() {
        let mut rng = rand::rng();

        let size = 1 << 10;
        let eq: Vec<E> = (0..size).map(|_| random_in_ext(&mut rng)).collect();
        let values: Vec<[E; 2]> = (0..size)
            .map(|_| [random_in_ext(&mut rng), random_in_ext(&mut rng)])
            .collect();

        let expected =
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq_serial::<F, E>(&values, &eq);

        for i in 1..=10 {
            let worker = Worker::new_with_num_threads(i);
            assert_eq!(
                evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                    &values, &eq, &worker
                ),
                expected
            );
        }
    }

    #[test]
    fn test_make_eq_poly_impl() {
        let mut rng = rand::rng();
        let size = 16;
        let challenges: Vec<E> = (0..size).map(|_| random_in_ext(&mut rng)).collect();

        let expected_full = make_eq_poly_in_full_serial(&challenges);
        let expected_reduced = make_eq_poly_reduced_serial(&challenges);

        for i in 1..=10 {
            let worker = Worker::new_with_num_threads(i);
            let res_full = make_eq_poly_in_full(&challenges, &worker);
            let res_reduced = make_eq_poly_reduced(&challenges, &worker);
            assert_eq!(res_full.len(), expected_full.len());
            assert_eq!(res_reduced.len(), expected_reduced.len());

            assert!(res_full
                .iter()
                .zip(expected_full.iter())
                .all(|(r, e)| **r == **e));
            assert!(res_reduced
                .iter()
                .zip(expected_reduced.iter())
                .all(|(r, e)| **r == **e))
        }
    }
}
