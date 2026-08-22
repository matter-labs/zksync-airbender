//! CPU oracle for the window tensor round tail: the three main-layer sumcheck
//! rounds a width-3 window replaces, driven from the reduced 27-cell tensor on
//! `{0, 1, infinity}^3`.

use gpu_core::primitives::field::E4;

use crate::upstream::{
    commit_field_els, draw_random_field_els, evaluate_eq_poly, evaluate_small_univariate_poly,
    output_univariate_monomial_form_max_quadratic, BabyBearField, Blake2sTranscript, Field, Seed,
};

fn eq_weight(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        let mut weight = E4::ONE;
        weight.sub_assign(&coordinate);
        weight
    } else {
        coordinate
    }
}

fn contract_two_axes(cells: &[E4], weights: &[E4; 4]) -> E4 {
    let mut accumulator = E4::ZERO;
    for x1 in 0..2 {
        for x2 in 0..2 {
            let mut value = cells[3 * x1 + x2];
            value.mul_assign(&weights[2 * x1 + x2]);
            accumulator.add_assign(&value);
        }
    }
    accumulator
}

fn contract_one_axis(cells: &[E4], weights: &[E4; 2]) -> E4 {
    let mut accumulator = E4::ZERO;
    for x2 in 0..2 {
        let mut value = cells[x2];
        value.mul_assign(&weights[x2]);
        accumulator.add_assign(&value);
    }
    accumulator
}

fn bind_univariate(at_zero: E4, at_one: E4, leading: E4, challenge: E4) -> E4 {
    let mut linear = at_one;
    linear.sub_assign(&leading);
    linear.sub_assign(&at_zero);
    linear.mul_assign(&challenge);

    let mut quadratic = leading;
    quadratic.mul_assign(&challenge);
    quadratic.mul_assign(&challenge);

    let mut bound = at_zero;
    bound.add_assign(&linear);
    bound.add_assign(&quadratic);
    bound
}

fn round_update(
    at_zero: E4,
    leading: E4,
    prev_coordinate: E4,
    seed: &mut Seed,
    claim: &mut E4,
    eq_prefactor: &mut E4,
) -> ([E4; 4], E4) {
    let mut normalized_claim = *claim;
    normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

    let coeffs = output_univariate_monomial_form_max_quadratic::<BabyBearField, E4>(
        prev_coordinate,
        normalized_claim,
        at_zero,
        leading,
    );
    commit_field_els::<BabyBearField, E4, Blake2sTranscript>(seed, &coeffs);
    let challenge = draw_random_field_els::<BabyBearField, E4, Blake2sTranscript>(seed, 1)[0];

    *claim = evaluate_small_univariate_poly::<BabyBearField, E4, 4>(&coeffs, &challenge);
    *eq_prefactor = evaluate_eq_poly::<BabyBearField, E4>(&challenge, &prev_coordinate);

    (coeffs, challenge)
}

/// Play the three peeled rounds of one width-3 window.
///
/// `tensor` is indexed `9 * x0 + 3 * x1 + x2` over `{0, 1, infinity}`, carries
/// no equality factor for the three peeled coordinates, and `rho` holds the
/// previous claim point's coordinates of those same three variables. Returns
/// the three rounds' four coefficients each (round-major) and the three drawn
/// challenges; `seed`, `claim` and `eq_prefactor` advance in place.
#[doc(hidden)]
pub fn tensor_round_tail_reference(
    tensor: [E4; 27],
    rho: &[E4; 3],
    seed: &mut [u32; 8],
    claim: &mut E4,
    eq_prefactor: &mut E4,
) -> ([E4; 12], [E4; 3]) {
    let pair_weights: [E4; 4] = core::array::from_fn(|index| {
        let mut weight = eq_weight(index >> 1, rho[1]);
        weight.mul_assign(&eq_weight(index & 1, rho[2]));
        weight
    });
    let single_weights: [E4; 2] = core::array::from_fn(|index| eq_weight(index, rho[2]));

    let mut transcript_seed = Seed(*seed);
    let mut coeffs = [E4::ZERO; 12];
    let mut challenges = [E4::ZERO; 3];

    let (round, challenge) = round_update(
        contract_two_axes(&tensor[0..9], &pair_weights),
        contract_two_axes(&tensor[18..27], &pair_weights),
        rho[0],
        &mut transcript_seed,
        claim,
        eq_prefactor,
    );
    coeffs[0..4].copy_from_slice(&round);
    challenges[0] = challenge;

    let bound_nine: [E4; 9] = core::array::from_fn(|index| {
        bind_univariate(
            tensor[index],
            tensor[9 + index],
            tensor[18 + index],
            challenges[0],
        )
    });

    let (round, challenge) = round_update(
        contract_one_axis(&bound_nine[0..3], &single_weights),
        contract_one_axis(&bound_nine[6..9], &single_weights),
        rho[1],
        &mut transcript_seed,
        claim,
        eq_prefactor,
    );
    coeffs[4..8].copy_from_slice(&round);
    challenges[1] = challenge;

    let bound_three: [E4; 3] = core::array::from_fn(|index| {
        bind_univariate(
            bound_nine[index],
            bound_nine[3 + index],
            bound_nine[6 + index],
            challenges[1],
        )
    });

    let (round, challenge) = round_update(
        bound_three[0],
        bound_three[2],
        rho[2],
        &mut transcript_seed,
        claim,
        eq_prefactor,
    );
    coeffs[8..12].copy_from_slice(&round);
    challenges[2] = challenge;

    *seed = transcript_seed.0;
    (coeffs, challenges)
}
