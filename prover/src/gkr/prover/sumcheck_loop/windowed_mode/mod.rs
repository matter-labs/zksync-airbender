use super::*;

use crate::gkr::prover::sumcheck::access_and_fold::*;

pub(crate) mod program;
pub(crate) mod full_size_scratch;
pub(crate) mod uniskip;
pub(crate) mod lsb_chain;
pub(crate) mod lsb_generic;

#[cfg(target_arch = "aarch64")]
pub(crate) mod neon;

#[cfg(target_arch = "aarch64")]
pub(crate) mod lsb_bench;

pub fn evaluate_claim_from_intermediate_matrix_27<E: Field>(
    eq_prefix: &[E; 4],
    accumulator: &[E; 27],
) -> [E; 3] {
    let mut evals = [E::ZERO; 3];
    for x0 in 0..3 {
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let eq_offset = x1 * 2;
            let dst_offset = dst_offset + 3 * x1;
            for x2 in 0..2 {
                let dst_offset = dst_offset + x2;
                let eq_offset = eq_offset + x2;
                let mut value = accumulator[dst_offset];
                value.mul_assign(&eq_prefix[eq_offset]);
                evals[x0].add_assign(&value);
            }
        }
    }

    evals
}

pub fn evaluate_claim_from_intermediate_matrix_9<E: Field>(
    eq_prefix: &[E; 2],
    accumulator: &[E; 9],
) -> [E; 3] {
    let mut evals = [E::ZERO; 3];
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..2 {
            let dst_offset = dst_offset + x2;
            let eq_offset = x2;
            let mut value = accumulator[dst_offset];
            value.mul_assign(&eq_prefix[eq_offset]);
            evals[x1].add_assign(&value);
        }
    }

    evals
}

#[inline(always)]
pub fn bind_univariate<F: Field>(c0: F, c1: F, c2: F, challenge: F) -> F {
    // The univariate is given by its values at {0, 1, inf}: c0 = P(0), c1 = P(1),
    // c2 = leading coefficient. So P(X) = c0 + (c1 - c2 - c0) * X + c2 * X^2.
    let mut c1 = c1;
    c1.sub_assign(&c2);
    c1.sub_assign(&c0);
    c1.mul_assign(&challenge);

    let mut c2 = c2;
    c2.mul_assign(&challenge);
    c2.mul_assign(&challenge);

    let mut binded = c0;
    binded.add_assign(&c1);
    binded.add_assign(&c2);

    binded
}

pub fn bind_accumulator_27<E: Field>(accumulator: &[E; 27], challenge: &E) -> [E; 9] {
    let mut next_accumulator = [E::ZERO; 9];
    for x1 in 0..3 {
        let src_offset = 3 * x1;
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_offset = src_offset + x2;
            let dst_offset = dst_offset + x2;
            {
                let binded = bind_univariate(
                    accumulator[0 + src_offset],
                    accumulator[9 + src_offset],
                    accumulator[18 + src_offset],
                    *challenge,
                );
                next_accumulator[dst_offset] = binded;
            }
        }
    }

    next_accumulator
}

pub fn bind_accumulator_9<E: Field>(accumulator: &[E; 9], challenge: &E) -> [E; 3] {
    let mut next_accumulator = [E::ZERO; 3];
    for x2 in 0..3 {
        let src_offset = x2;
        let dst_offset = x2;
        {
            let binded = bind_univariate(
                accumulator[0 + src_offset],
                accumulator[3 + src_offset],
                accumulator[6 + src_offset],
                *challenge,
            );
            next_accumulator[dst_offset] = binded;
        }
    }

    next_accumulator
}
