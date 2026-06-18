use field::{Field, FieldExtension, PrimeField};

pub mod access_and_fold;
pub mod eq_poly;
pub mod evaluation_kernels;

#[cfg(test)]
mod tests;

// for notations: if we have a poly p(x0, x1, x2, x3, ...) then x0 is the most signinicant bit in the
// indexing of the array

pub fn output_univariate_monomial_form_max_quadratic<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    folding_challenge_for_coordinate_form_previous_round: E,
    previous_round_claim: E,
    constant_coefficient_from_partial_sum: E,
    quadratic_coefficient_from_partial_sum: E,
) -> [E; 4] {
    // part of the EQ poly that matches the coordinate being folded is (1 - prev_round) * (1 - X) + X * prev_round = X * (prev_round * 2 - 1) + (1 - prev_round)

    let c = quadratic_coefficient_from_partial_sum;
    let e = constant_coefficient_from_partial_sum;

    let mut b = E::ONE;
    b.sub_assign(&folding_challenge_for_coordinate_form_previous_round);

    let mut a = folding_challenge_for_coordinate_form_previous_round;
    a.double();
    a.sub_assign(&E::ONE);

    let a_plus_b = folding_challenge_for_coordinate_form_previous_round;
    let a_plus_b_inv = a_plus_b.inverse().expect("non-zero");

    let mut be = b;
    be.mul_assign(&e);

    let mut d = previous_round_claim;
    d.sub_assign(&be);
    d.mul_assign(&a_plus_b_inv);
    d.sub_assign(&c);
    d.sub_assign(&e);

    // and so we have (a * X + b) * (c * X^2 + d * X + e)

    let c0 = be;

    let c1 = {
        let mut ae = a;
        ae.mul_assign(&e);

        let mut bd = b;
        bd.mul_assign(&d);

        let mut c1 = ae;
        c1.add_assign(&bd);

        c1
    };

    let c2 = {
        let mut ad = a;
        ad.mul_assign(&d);

        let mut bc = b;
        bc.mul_assign(&c);

        let mut c2 = ad;
        c2.add_assign(&bc);

        c2
    };

    let mut c3 = a;
    c3.mul_assign(&c);

    [c0, c1, c2, c3]
}

pub fn evaluate_small_univariate_poly<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const N: usize,
>(
    coeffs: &[E; N],
    point: &E,
) -> E {
    let mut result = coeffs[N - 1];
    for i in (0..(N - 1)).rev() {
        result.mul_assign(point);
        result.add_assign(&coeffs[i]);
    }
    result
}

#[inline(always)]
pub fn evaluate_eq_poly_at_line<F: PrimeField, E: FieldExtension<F> + Field>(x: &E) -> [E; 2] {
    let mut f0 = E::ONE;
    f0.sub_assign(x);

    [f0, *x]
}

pub fn evaluate_eq_poly<F: PrimeField, E: FieldExtension<F> + Field>(x: &E, y: &E) -> E {
    let mut t0 = E::ONE;
    t0.sub_assign(x);
    let mut t1 = E::ONE;
    t1.sub_assign(y);
    t0.mul_assign(&t1);

    let mut result = *x;
    result.mul_assign(y);
    result.add_assign(&t0);

    result
}

pub fn evaluate_multivariate_eq_poly<F: PrimeField, E: FieldExtension<F> + Field>(
    x: &[E],
    y: &[E],
) -> E {
    assert!(x.len() > 0);
    assert_eq!(x.len(), y.len());
    let mut result = evaluate_eq_poly::<F, E>(&x[0], &y[0]);
    for i in 1..x.len() {
        let t = evaluate_eq_poly::<F, E>(&x[i], &y[i]);
        result.mul_assign(&t);
    }
    result
}
