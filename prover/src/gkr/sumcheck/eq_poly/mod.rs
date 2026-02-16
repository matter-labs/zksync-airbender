use field::{Field, FieldExtension, TwoAdicField};

use super::*;

pub fn make_eq_poly_impl<E: Field, const FULL: bool>(challenges: &[E]) -> Vec<Box<[E]>> {
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
        let mut f0 = E::ONE;
        f0.sub_assign(&challenge);

        let half_size = size / 2;

        assert_eq!(previous_layer.len(), half_size);

        for index in 0..half_size {
            let mut left = previous_layer[index];
            let mut right = left;
            left.mul_assign(&f0);
            right.mul_assign(&f1);
            layer[index].write(left);
            layer[index + half_size].write(right);
        }

        result.push(unsafe { layer.assume_init() });
    }

    result
}

pub fn make_eq_poly_reduced<E: Field>(challenges: &[E]) -> Vec<Box<[E]>> {
    make_eq_poly_impl::<E, false>(challenges)
}

pub fn make_eq_poly_in_full<E: Field>(challenges: &[E]) -> Vec<Box<[E]>> {
    make_eq_poly_impl::<E, true>(challenges)
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
