use field::{Field, FieldExtension, PrimeField};

use crate::definitions::SumcheckCoefficientsStrategy;
use crate::gkr::prover::GKRSumcheckRoundMessage;
use crate::gkr::whir::WhirSumcheckRoundMessage;

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

/// The message of one GKR layer sumcheck round, as it goes into the proof and
/// the transcript: the round polynomial is `eq(tau, X) * h(X)` with
/// `tau = folding_challenge_for_coordinate_form_previous_round`, a quadratic
/// `h(X) = e + d * X + c * X^2`, and `previous_round_claim` the NORMALIZED
/// running claim `H = (1 - tau) * h(0) + tau * h(1)` (earlier eq factors
/// divided out).
///
/// * [`SumcheckCoefficientsStrategy::Plain`] — the 4 monomial coefficients of
///   the cubic `eq(tau, X) * h(X)`
///   ([`output_univariate_monomial_form_max_quadratic`]);
/// * [`SumcheckCoefficientsStrategy::Minimal`] — `[d, c]`: the claim fixes
///   the constant term, `e = H - tau * (c + d)`, so a verifier needs no
///   inversion to open the round ([`next_normalized_sumcheck_claim`]).
pub fn output_sumcheck_round_message_max_quadratic<F: PrimeField, E: FieldExtension<F> + Field>(
    strategy: SumcheckCoefficientsStrategy,
    folding_challenge_for_coordinate_form_previous_round: E,
    previous_round_claim: E,
    constant_coefficient_from_partial_sum: E,
    quadratic_coefficient_from_partial_sum: E,
) -> GKRSumcheckRoundMessage<E> {
    match strategy {
        SumcheckCoefficientsStrategy::Plain => {
            output_univariate_monomial_form_max_quadratic::<F, E>(
                folding_challenge_for_coordinate_form_previous_round,
                previous_round_claim,
                constant_coefficient_from_partial_sum,
                quadratic_coefficient_from_partial_sum,
            )
            .into()
        }
        SumcheckCoefficientsStrategy::Minimal => {
            let tau = folding_challenge_for_coordinate_form_previous_round;
            let c = quadratic_coefficient_from_partial_sum;
            let e = constant_coefficient_from_partial_sum;

            // H = (1 - tau) * e + tau * (c + d + e), solved for d exactly as
            // the plain builder does
            let mut one_minus_tau = E::ONE;
            one_minus_tau.sub_assign(&tau);
            let mut constant_part = one_minus_tau;
            constant_part.mul_assign(&e);
            let mut d = previous_round_claim;
            d.sub_assign(&constant_part);
            d.mul_assign(&tau.inverse().expect("non-zero"));
            d.sub_assign(&c);
            d.sub_assign(&e);

            let mut message = GKRSumcheckRoundMessage::new();
            message.push(d);
            message.push(c);
            message
        }
    }
}

/// The NORMALIZED running claim after a GKR layer sumcheck round is bound at
/// `challenge`: `h(challenge)`, the round polynomial at the challenge with
/// its eq factor `eq(tau, challenge)` divided out. Computed from the round's
/// wire `message` ([`output_sumcheck_round_message_max_quadratic`]) alone —
/// exactly what a verifier holds — so it doubles as the reference of the
/// verifier's round update.
pub fn next_normalized_sumcheck_claim<F: PrimeField, E: FieldExtension<F> + Field>(
    strategy: SumcheckCoefficientsStrategy,
    message: &[E],
    folding_challenge_for_coordinate_form_previous_round: E,
    previous_round_claim: E,
    challenge: &E,
) -> E {
    assert_eq!(message.len(), strategy.gkr_round_coefficients());
    let tau = folding_challenge_for_coordinate_form_previous_round;
    match strategy {
        SumcheckCoefficientsStrategy::Plain => {
            let mut result = message[3];
            for coeff in message[..3].iter().rev() {
                result.mul_assign(challenge);
                result.add_assign(coeff);
            }
            let eq_factor = evaluate_eq_poly::<F, E>(challenge, &tau);
            result.mul_assign(&eq_factor.inverse().expect("eq factor non-zero"));
            result
        }
        SumcheckCoefficientsStrategy::Minimal => {
            let [d, c] = [message[0], message[1]];
            // e = H - tau * (c + d)
            let mut linear_part = c;
            linear_part.add_assign(&d);
            linear_part.mul_assign(&tau);
            let mut e = previous_round_claim;
            e.sub_assign(&linear_part);
            // h(r) = e + r * (d + r * c)
            let mut result = c;
            result.mul_assign(challenge);
            result.add_assign(&d);
            result.mul_assign(challenge);
            result.add_assign(&e);
            result
        }
    }
}

/// The message of one WHIR sumcheck round, as it goes into the proof and the
/// transcript, from the monomial coefficients `[c0, c1, c2]` of its quadratic
/// round polynomial: all three under
/// [`SumcheckCoefficientsStrategy::Plain`], `[c0, c2]` under
/// [`SumcheckCoefficientsStrategy::Minimal`] (the claim `2 * c0 + c1 + c2`
/// fixes `c1`).
pub fn whir_sumcheck_round_message<E: Field>(
    strategy: SumcheckCoefficientsStrategy,
    monomial_coefficients: &[E; 3],
) -> WhirSumcheckRoundMessage<E> {
    match strategy {
        SumcheckCoefficientsStrategy::Plain => (*monomial_coefficients).into(),
        SumcheckCoefficientsStrategy::Minimal => {
            let mut message = WhirSumcheckRoundMessage::new();
            message.push(monomial_coefficients[0]);
            message.push(monomial_coefficients[2]);
            message
        }
    }
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
    assert!(!x.is_empty());
    assert_eq!(x.len(), y.len());
    let mut result = evaluate_eq_poly::<F, E>(&x[0], &y[0]);
    for i in 1..x.len() {
        let t = evaluate_eq_poly::<F, E>(&x[i], &y[i]);
        result.mul_assign(&t);
    }
    result
}
