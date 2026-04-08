use super::common::{
    dot_eq, draw_field_els_into, fold_standard_claims, make_eq_poly, read_field_el,
    read_reduced_field_el, verify_final_step_check, verify_sumcheck_rounds, EXT_DEGREE,
};
use super::constants::*;
use verifier_common::blake2s_u32::DelegatedBlake2sState;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{GKRVerificationError, GKRVerifierOutput, LayerState, LazyVec};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
use verifier_common::transcript::Blake2sTranscript;
#[inline(always)]
#[allow(unused_variables, clippy::needless_borrow)]
unsafe fn eval_linear_relation(
    evals: &[[BabyBearExt4; 2]],
    terms: &[(usize, usize)],
    constant: usize,
    j: usize,
) -> BabyBearExt4 {
    let mut result = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(constant as u32));
    let mut i = 0;
    while i < terms.len() {
        let (idx, coeff) = *terms.get_unchecked(i);
        let mut t = evals.get_unchecked(idx)[j];
        field_ops::mul_assign_by_base(&mut t, &BabyBearField::from_reduced_raw_repr(coeff as u32));
        field_ops::add_assign(&mut result, &t);
        i += 1;
    }
    result
}
#[inline(always)]
#[allow(unused_variables, clippy::needless_borrow)]
unsafe fn eval_vector_lookup(
    evals: &[[BabyBearExt4; 2]],
    alpha: BabyBearExt4,
    col_descs: &[(usize, usize)],
    terms: &[(usize, usize)],
    j: usize,
) -> BabyBearExt4 {
    let mut result = BabyBearExt4::ZERO;
    let mut term_offset: usize = 0;
    let mut i = 0;
    while i < col_descs.len() {
        field_ops::mul_assign(&mut result, &alpha);
        let (col_const, num_terms) = *col_descs.get_unchecked(i);
        let mut col_val =
            BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(col_const as u32));
        let mut k = 0;
        while k < num_terms {
            let (idx, coeff) = *terms.get_unchecked(term_offset + k);
            let mut t = evals.get_unchecked(idx)[j];
            field_ops::mul_assign_by_base(
                &mut t,
                &BabyBearField::from_reduced_raw_repr(coeff as u32),
            );
            field_ops::add_assign(&mut col_val, &t);
            k += 1;
        }
        field_ops::add_assign(&mut result, &col_val);
        term_offset += num_terms;
        i += 1;
    }
    result
}
#[inline(always)]
#[allow(unused_variables, clippy::needless_borrow)]
unsafe fn eval_max_quadratic(
    evals: &[[BabyBearExt4; 2]],
    quad_outer: &[(usize, usize)],
    quad_inner: &[(usize, usize)],
    linear: &[(usize, usize)],
    constant: usize,
    j: usize,
) -> BabyBearExt4 {
    let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(constant as u32));
    let mut inner_offset: usize = 0;
    let mut i = 0;
    while i < quad_outer.len() {
        let (addr_a, num_inner) = *quad_outer.get_unchecked(i);
        let mut inner = BabyBearExt4::ZERO;
        let mut k = 0;
        while k < num_inner {
            let (addr_b, coeff) = *quad_inner.get_unchecked(inner_offset + k);
            let mut t = evals.get_unchecked(addr_b)[j];
            field_ops::mul_assign_by_base(
                &mut t,
                &BabyBearField::from_reduced_raw_repr(coeff as u32),
            );
            field_ops::add_assign(&mut inner, &t);
            k += 1;
        }
        let a_val = evals.get_unchecked(addr_a)[j];
        field_ops::mul_assign(&mut inner, &a_val);
        field_ops::add_assign(&mut val, &inner);
        inner_offset += num_inner;
        i += 1;
    }
    let mut li = 0;
    while li < linear.len() {
        let (addr, coeff) = *linear.get_unchecked(li);
        let mut lt = evals.get_unchecked(addr)[j];
        field_ops::mul_assign_by_base(&mut lt, &BabyBearField::from_reduced_raw_repr(coeff as u32));
        field_ops::add_assign(&mut val, &lt);
        li += 1;
    }
    val
}
const ME_OP_ADD_BASE_CONST: usize = 0;
const ME_OP_ADD_EVAL: usize = 1;
const ME_OP_ADD_ONE_MINUS_EVAL: usize = 2;
const ME_OP_CH_MUL_EVAL: usize = 3;
const ME_OP_CH_MUL_CONST: usize = 4;
const ME_OP_CH_MUL_EVAL_PLUS_CONST: usize = 5;
const ME_OP_CH_MUL_EVAL_PLUS_DYN: usize = 6;
const ME_OP_BYTE_VALUE_PAIR: usize = 7;
#[inline(always)]
#[allow(unused_variables, clippy::needless_borrow)]
unsafe fn eval_memory_expr(
    evals: &[[BabyBearExt4; 2]],
    challenges: &[BabyBearExt4],
    additive_part: BabyBearExt4,
    ops: &[[usize; 6]],
    j: usize,
) -> BabyBearExt4 {
    let mut result = additive_part;
    let mut i = 0;
    while i < ops.len() {
        let op = *ops.get_unchecked(i);
        match op[0] {
            ME_OP_ADD_BASE_CONST => {
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(op[1] as u32),
                );
            }
            ME_OP_ADD_EVAL => {
                field_ops::add_assign(&mut result, &evals.get_unchecked(op[1])[j]);
            }
            ME_OP_ADD_ONE_MINUS_EVAL => {
                let mut t = BabyBearExt4::ONE;
                field_ops::sub_assign(&mut t, &evals.get_unchecked(op[1])[j]);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_EVAL => {
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(op[2])[j]);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_CONST => {
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(op[2] as u32),
                );
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_EVAL_PLUS_CONST => {
                let mut ev = evals.get_unchecked(op[2])[j];
                field_ops::add_assign_base(
                    &mut ev,
                    &BabyBearField::from_reduced_raw_repr(op[3] as u32),
                );
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(&mut t, &ev);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_EVAL_PLUS_DYN => {
                let mut ev = evals.get_unchecked(op[2])[j];
                if op[4] != 0 {
                    field_ops::add_assign_base(
                        &mut ev,
                        &BabyBearField::from_reduced_raw_repr(op[4] as u32),
                    );
                }
                let mut dyn_val = evals.get_unchecked(op[3])[j];
                field_ops::mul_assign_by_base(
                    &mut dyn_val,
                    &BabyBearField::from_reduced_raw_repr(op[5] as u32),
                );
                field_ops::add_assign(&mut ev, &dyn_val);
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(&mut t, &ev);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_BYTE_VALUE_PAIR => {
                let mut hi = evals.get_unchecked(op[3])[j];
                field_ops::mul_assign_by_base(
                    &mut hi,
                    &BabyBearField::from_reduced_raw_repr(268434910u32),
                );
                field_ops::add_assign(&mut hi, &evals.get_unchecked(op[2])[j]);
                let mut t = challenges[op[1]];
                field_ops::mul_assign(&mut t, &hi);
                field_ops::add_assign(&mut result, &t);
            }
            _ => core::hint::unreachable_unchecked(),
        }
        i += 1;
    }
    result
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_0_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 216usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
        (1usize, 8usize, 0usize),
        (1usize, 9usize, 0usize),
        (1usize, 10usize, 0usize),
        (1usize, 11usize, 0usize),
        (1usize, 12usize, 0usize),
        (1usize, 13usize, 0usize),
        (1usize, 14usize, 0usize),
        (1usize, 15usize, 0usize),
        (1usize, 16usize, 0usize),
        (1usize, 17usize, 0usize),
        (1usize, 18usize, 0usize),
        (1usize, 19usize, 0usize),
        (1usize, 20usize, 0usize),
        (1usize, 21usize, 0usize),
        (1usize, 22usize, 0usize),
        (1usize, 23usize, 0usize),
        (1usize, 24usize, 0usize),
        (1usize, 25usize, 0usize),
        (1usize, 26usize, 0usize),
        (1usize, 27usize, 0usize),
        (1usize, 28usize, 0usize),
        (1usize, 29usize, 0usize),
        (1usize, 30usize, 0usize),
        (1usize, 31usize, 0usize),
        (1usize, 32usize, 0usize),
        (1usize, 33usize, 0usize),
        (1usize, 34usize, 0usize),
        (1usize, 35usize, 0usize),
        (1usize, 36usize, 0usize),
        (1usize, 37usize, 0usize),
        (1usize, 38usize, 0usize),
        (1usize, 39usize, 0usize),
        (2usize, 40usize, 41usize),
        (2usize, 42usize, 43usize),
        (2usize, 44usize, 45usize),
        (2usize, 46usize, 47usize),
        (2usize, 48usize, 49usize),
        (2usize, 50usize, 51usize),
        (2usize, 52usize, 53usize),
        (2usize, 54usize, 55usize),
        (1usize, 56usize, 0usize),
        (2usize, 57usize, 58usize),
        (2usize, 59usize, 60usize),
        (2usize, 61usize, 62usize),
        (2usize, 63usize, 64usize),
        (2usize, 65usize, 66usize),
        (2usize, 67usize, 68usize),
        (2usize, 69usize, 70usize),
        (2usize, 71usize, 72usize),
        (2usize, 73usize, 74usize),
        (2usize, 75usize, 76usize),
        (2usize, 77usize, 78usize),
        (2usize, 79usize, 80usize),
        (2usize, 81usize, 82usize),
        (2usize, 83usize, 84usize),
        (2usize, 85usize, 86usize),
        (2usize, 87usize, 88usize),
        (2usize, 89usize, 90usize),
        (2usize, 91usize, 92usize),
        (2usize, 93usize, 94usize),
        (2usize, 95usize, 96usize),
        (1usize, 97usize, 0usize),
        (2usize, 98usize, 99usize),
        (2usize, 100usize, 101usize),
        (2usize, 102usize, 103usize),
        (2usize, 104usize, 105usize),
        (2usize, 106usize, 107usize),
        (2usize, 108usize, 109usize),
        (2usize, 110usize, 111usize),
        (2usize, 112usize, 113usize),
        (2usize, 114usize, 115usize),
        (2usize, 116usize, 117usize),
        (2usize, 118usize, 119usize),
        (2usize, 120usize, 121usize),
        (2usize, 122usize, 123usize),
        (2usize, 124usize, 125usize),
        (2usize, 126usize, 127usize),
        (2usize, 128usize, 129usize),
        (2usize, 130usize, 131usize),
        (2usize, 132usize, 133usize),
        (2usize, 134usize, 135usize),
        (2usize, 136usize, 137usize),
        (2usize, 138usize, 139usize),
        (2usize, 140usize, 141usize),
        (2usize, 142usize, 143usize),
        (2usize, 144usize, 145usize),
        (2usize, 146usize, 147usize),
        (2usize, 148usize, 149usize),
        (2usize, 150usize, 151usize),
        (2usize, 152usize, 153usize),
        (2usize, 154usize, 155usize),
        (2usize, 156usize, 157usize),
        (2usize, 158usize, 159usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 216usize {
        let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = output_claims.get(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = output_claims.get(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = output_claims.get(o1);
            let mut t1 = current_batch;
            field_ops::mul_assign(&mut t1, &c1);
            field_ops::add_assign(&mut combined, &t1);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        }
        i += 1;
    }
    combined
}
#[inline(always)]
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_0_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 1usize] =
            [(1usize, [255usize, 0usize, 0usize, 0usize])];
        let mut _sg = 0;
        while _sg < 1usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 6usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 671088619usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 161usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 162usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 163usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 164usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [3usize, 0usize, 163usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 165usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 166usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 167usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 168usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 6usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 671088619usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 163usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 164usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [3usize, 0usize, 163usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 169usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 170usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 171usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 172usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 173usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 174usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 177usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 178usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 179usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 180usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 175usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 176usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 181usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 182usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 183usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 185usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 186usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 189usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 190usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 191usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 192usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 187usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 188usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 193usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 194usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 195usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 196usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 197usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 198usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 201usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 202usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 203usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 204usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 199usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 200usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 205usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 206usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 207usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 208usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 209usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 210usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 6usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 939524073usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 213usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 214usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 215usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 216usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 163usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 164usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 211usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 212usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 6usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 939524073usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 215usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 216usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [3usize, 0usize, 215usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 217usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 218usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 219usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 220usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 221usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 222usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 223usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 224usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [3usize, 0usize, 215usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 219usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 220usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 223usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 224usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 225usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 226usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 227usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 228usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 229usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 230usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 231usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 232usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 227usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 228usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 231usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 232usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 233usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 234usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 235usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 236usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 237usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 238usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 239usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 240usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 235usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 236usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 239usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 240usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 241usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 242usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 243usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 244usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 245usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 246usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 247usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 248usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 243usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 244usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 7usize] = [
                [0usize, 268435454usize, 0usize, 0usize, 0usize, 0usize],
                [5usize, 0usize, 215usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 216usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 247usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 248usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 6usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 1207959527usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 249usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 250usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 251usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 252usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 4usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 1744826211usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 256usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const MEM_A_OPS: [[usize; 6]; 6usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 1207959527usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 256usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 253usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 254usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_a = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_A_OPS,
                j,
            );
            const MEM_B_OPS: [[usize; 6]; 2usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 1744826211usize, 0usize, 0usize, 0usize],
            ];
            let mut mem_b = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &MEM_B_OPS,
                j,
            );
            field_ops::mul_assign(&mut mem_a, &mem_b);
            let val = mem_a;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (8usize, 268435454usize),
                (8usize, 268435454usize),
                (8usize, 268435454usize),
                (72usize, 268435454usize),
                (72usize, 268435454usize),
                (8usize, 268435454usize),
                (8usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (9usize, 268435454usize),
                (9usize, 268435454usize),
                (9usize, 268435454usize),
                (73usize, 268435454usize),
                (73usize, 268435454usize),
                (9usize, 268435454usize),
                (9usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (10usize, 268435454usize),
                (10usize, 268435454usize),
                (10usize, 268435454usize),
                (74usize, 268435454usize),
                (74usize, 268435454usize),
                (10usize, 268435454usize),
                (10usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (11usize, 268435454usize),
                (11usize, 268435454usize),
                (11usize, 268435454usize),
                (75usize, 268435454usize),
                (75usize, 268435454usize),
                (11usize, 268435454usize),
                (11usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (12usize, 268435454usize),
                (12usize, 268435454usize),
                (12usize, 268435454usize),
                (76usize, 268435454usize),
                (76usize, 268435454usize),
                (12usize, 268435454usize),
                (12usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (13usize, 268435454usize),
                (13usize, 268435454usize),
                (13usize, 268435454usize),
                (77usize, 268435454usize),
                (77usize, 268435454usize),
                (13usize, 268435454usize),
                (13usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (14usize, 268435454usize),
                (14usize, 268435454usize),
                (14usize, 268435454usize),
                (78usize, 268435454usize),
                (78usize, 268435454usize),
                (14usize, 268435454usize),
                (14usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (15usize, 268435454usize),
                (15usize, 268435454usize),
                (15usize, 268435454usize),
                (79usize, 268435454usize),
                (79usize, 268435454usize),
                (15usize, 268435454usize),
                (15usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (16usize, 268435454usize),
                (16usize, 268435454usize),
                (16usize, 268435454usize),
                (80usize, 268435454usize),
                (80usize, 268435454usize),
                (16usize, 268435454usize),
                (16usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (17usize, 268435454usize),
                (17usize, 268435454usize),
                (17usize, 268435454usize),
                (81usize, 268435454usize),
                (81usize, 268435454usize),
                (17usize, 268435454usize),
                (17usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (18usize, 268435454usize),
                (18usize, 268435454usize),
                (18usize, 268435454usize),
                (82usize, 268435454usize),
                (82usize, 268435454usize),
                (18usize, 268435454usize),
                (18usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (19usize, 268435454usize),
                (19usize, 268435454usize),
                (19usize, 268435454usize),
                (83usize, 268435454usize),
                (83usize, 268435454usize),
                (19usize, 268435454usize),
                (19usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (20usize, 268435454usize),
                (20usize, 268435454usize),
                (20usize, 268435454usize),
                (84usize, 268435454usize),
                (84usize, 268435454usize),
                (20usize, 268435454usize),
                (20usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (21usize, 268435454usize),
                (21usize, 268435454usize),
                (21usize, 268435454usize),
                (85usize, 268435454usize),
                (85usize, 268435454usize),
                (21usize, 268435454usize),
                (21usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (22usize, 268435454usize),
                (22usize, 268435454usize),
                (22usize, 268435454usize),
                (86usize, 268435454usize),
                (86usize, 268435454usize),
                (22usize, 268435454usize),
                (22usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (23usize, 268435454usize),
                (23usize, 268435454usize),
                (23usize, 268435454usize),
                (87usize, 268435454usize),
                (87usize, 268435454usize),
                (23usize, 268435454usize),
                (23usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 2usize] = [(3usize, 16usize), (5usize, 16usize)];
            const VAL_QI: [(usize, usize); 32usize] = [
                (88usize, 268435454usize),
                (89usize, 268435454usize),
                (90usize, 268435454usize),
                (91usize, 268435454usize),
                (92usize, 268435454usize),
                (93usize, 268435454usize),
                (94usize, 268435454usize),
                (95usize, 268435454usize),
                (96usize, 268435454usize),
                (97usize, 268435454usize),
                (98usize, 268435454usize),
                (99usize, 268435454usize),
                (100usize, 268435454usize),
                (101usize, 268435454usize),
                (102usize, 268435454usize),
                (103usize, 268435454usize),
                (8usize, 268435454usize),
                (9usize, 268435454usize),
                (10usize, 268435454usize),
                (11usize, 268435454usize),
                (12usize, 268435454usize),
                (13usize, 268435454usize),
                (14usize, 268435454usize),
                (15usize, 268435454usize),
                (16usize, 268435454usize),
                (17usize, 268435454usize),
                (18usize, 268435454usize),
                (19usize, 268435454usize),
                (20usize, 268435454usize),
                (21usize, 268435454usize),
                (22usize, 268435454usize),
                (23usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 3usize] = [
            (1usize, [135usize, 0usize, 0usize, 0usize]),
            (1usize, [136usize, 0usize, 0usize, 0usize]),
            (6usize, [88usize, 158usize, 261usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 3usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(89usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(90usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(91usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(92usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(93usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(94usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(95usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(96usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(97usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(98usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(99usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(100usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(101usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(102usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 2usize] = [
            (1usize, [103usize, 0usize, 0usize, 0usize]),
            (6usize, [256usize, 159usize, 262usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 2usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(257usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (161usize, 268435454usize),
                (139usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (162usize, 268435454usize),
                (139usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (165usize, 268435454usize),
                (140usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (166usize, 268435454usize),
                (140usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (171usize, 268435454usize),
                (141usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (172usize, 268435454usize),
                (141usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (177usize, 268435454usize),
                (142usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (178usize, 268435454usize),
                (142usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (183usize, 268435454usize),
                (143usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (184usize, 268435454usize),
                (143usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (189usize, 268435454usize),
                (144usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (190usize, 268435454usize),
                (144usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (195usize, 268435454usize),
                (145usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (196usize, 268435454usize),
                (145usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (201usize, 268435454usize),
                (146usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (202usize, 268435454usize),
                (146usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (207usize, 268435454usize),
                (147usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (208usize, 268435454usize),
                (147usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (213usize, 268435454usize),
                (148usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (214usize, 268435454usize),
                (148usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (217usize, 268435454usize),
                (149usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (218usize, 268435454usize),
                (149usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (221usize, 268435454usize),
                (150usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (222usize, 268435454usize),
                (150usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (225usize, 268435454usize),
                (151usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (226usize, 268435454usize),
                (151usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (229usize, 268435454usize),
                (152usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (230usize, 268435454usize),
                (152usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (233usize, 268435454usize),
                (153usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (234usize, 268435454usize),
                (153usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (237usize, 268435454usize),
                (154usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (238usize, 268435454usize),
                (154usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (241usize, 268435454usize),
                (155usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (242usize, 268435454usize),
                (155usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (245usize, 268435454usize),
                (156usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (246usize, 268435454usize),
                (156usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (256usize, 1744830467usize),
                (249usize, 268435454usize),
                (157usize, 133099247usize),
            ];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 1476395013usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 1744830467usize),
                (250usize, 268435454usize),
                (157usize, 1744830467usize),
            ];
            let mut val = eval_linear_relation(evals, &VAL_TERMS, 133099247usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(40usize, 268435454usize), (167usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
            let c_val = evals.get_unchecked(160usize)[j];
            const D_VAL_COLS: [(usize, usize); 3usize] =
                [(0usize, 1usize), (0usize, 1usize), (0usize, 1usize)];
            const D_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (260usize, 268435454usize),
                (259usize, 268435454usize),
                (258usize, 268435454usize),
            ];
            let mut d_val =
                eval_vector_lookup(evals, lookup_alpha, &D_VAL_COLS, &D_VAL_VL_TERMS, j);
            field_ops::add_assign(&mut d_val, &lookup_additive_challenge);
            let out0 = {
                let mut num = d_val;
                let mut cb_tmp = c_val;
                field_ops::mul_assign(&mut cb_tmp, &a_val);
                field_ops::sub_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &d_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(41usize, 268435454usize), (168usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(42usize, 268435454usize), (173usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(43usize, 268435454usize), (174usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(44usize, 268435454usize), (179usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(45usize, 268435454usize), (180usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(46usize, 268435454usize), (185usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(47usize, 268435454usize), (186usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(48usize, 268435454usize), (191usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(49usize, 268435454usize), (192usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(50usize, 268435454usize), (197usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(51usize, 268435454usize), (198usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(52usize, 268435454usize), (203usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(53usize, 268435454usize), (204usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(54usize, 268435454usize), (209usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(55usize, 268435454usize), (210usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(56usize, 268435454usize), (219usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(57usize, 268435454usize), (220usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(58usize, 268435454usize), (223usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(59usize, 268435454usize), (224usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(60usize, 268435454usize), (227usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(61usize, 268435454usize), (228usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(62usize, 268435454usize), (231usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(63usize, 268435454usize), (232usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(64usize, 268435454usize), (235usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(65usize, 268435454usize), (236usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(66usize, 268435454usize), (239usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(67usize, 268435454usize), (240usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(68usize, 268435454usize), (243usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(69usize, 268435454usize), (244usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(70usize, 268435454usize), (247usize, 268435454usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524009usize, 0usize), (0usize, 1usize), (0usize, 1usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(71usize, 268435454usize), (248usize, 268435454usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] = [
                (1879048146usize, 0usize),
                (0usize, 2usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (102usize, 2013200385usize),
                (134usize, 65536usize),
                (72usize, 2013200385usize),
                (104usize, 65536usize),
            ];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(134217679usize, 0usize), (0usize, 2usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (101usize, 2013200385usize),
                (133usize, 65536usize),
                (73usize, 2013200385usize),
                (105usize, 65536usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(402653133usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(74usize, 2013200385usize), (106usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(402653133usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(75usize, 2013200385usize), (107usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(402653133usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(99usize, 2013200385usize), (131usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(402653133usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(100usize, 2013200385usize), (132usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(76usize, 2013200385usize), (108usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(77usize, 2013200385usize), (109usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(78usize, 2013200385usize), (110usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(79usize, 2013200385usize), (111usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(95usize, 2013200385usize), (127usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(96usize, 2013200385usize), (128usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(97usize, 2013200385usize), (129usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(671088587usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(98usize, 2013200385usize), (130usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(80usize, 2013200385usize), (112usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(81usize, 2013200385usize), (113usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(82usize, 2013200385usize), (114usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(83usize, 2013200385usize), (115usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(84usize, 2013200385usize), (116usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(85usize, 2013200385usize), (117usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(86usize, 2013200385usize), (118usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(87usize, 2013200385usize), (119usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(88usize, 2013200385usize), (120usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(89usize, 2013200385usize), (121usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(90usize, 2013200385usize), (122usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(91usize, 2013200385usize), (123usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(92usize, 2013200385usize), (124usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const A_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(93usize, 2013200385usize), (125usize, 65536usize)];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 3usize] =
                [(939524041usize, 0usize), (0usize, 0usize), (0usize, 2usize)];
            const B_VAL_VL_TERMS: [(usize, usize); 2usize] =
                [(94usize, 2013200385usize), (126usize, 65536usize)];
            let mut b_val =
                eval_vector_lookup(evals, lookup_alpha, &B_VAL_COLS, &B_VAL_VL_TERMS, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(255usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(255usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(255usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 9usize] = [
                (0usize, 268435454usize),
                (1usize, 536870908usize),
                (2usize, 1073741816usize),
                (3usize, 134217711usize),
                (4usize, 268435422usize),
                (5usize, 536870844usize),
                (6usize, 1073741688usize),
                (7usize, 134217455usize),
                (251usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 7usize),
                (1usize, 6usize),
                (2usize, 5usize),
                (3usize, 4usize),
                (4usize, 3usize),
                (5usize, 2usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 28usize] = [
                (0usize, 268435454usize),
                (1usize, 536870908usize),
                (2usize, 536870908usize),
                (3usize, 536870908usize),
                (4usize, 536870908usize),
                (5usize, 536870908usize),
                (7usize, 536870908usize),
                (1usize, 268435454usize),
                (2usize, 536870908usize),
                (3usize, 536870908usize),
                (4usize, 536870908usize),
                (5usize, 536870908usize),
                (7usize, 536870908usize),
                (2usize, 268435454usize),
                (3usize, 536870908usize),
                (4usize, 536870908usize),
                (5usize, 536870908usize),
                (7usize, 536870908usize),
                (3usize, 268435454usize),
                (4usize, 536870908usize),
                (5usize, 536870908usize),
                (7usize, 536870908usize),
                (4usize, 268435454usize),
                (5usize, 536870908usize),
                (7usize, 536870908usize),
                (5usize, 268435454usize),
                (7usize, 536870908usize),
                (7usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 7usize] = [
                (0usize, 1744830467usize),
                (1usize, 1744830467usize),
                (2usize, 1744830467usize),
                (3usize, 1744830467usize),
                (4usize, 1744830467usize),
                (5usize, 1744830467usize),
                (7usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 6usize] = [
                (0usize, 4usize),
                (1usize, 4usize),
                (2usize, 4usize),
                (5usize, 3usize),
                (6usize, 1usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (6usize, 268435454usize),
                (8usize, 1744830467usize),
                (167usize, 268435454usize),
                (219usize, 268435454usize),
                (6usize, 268435454usize),
                (8usize, 268435454usize),
                (167usize, 1744830467usize),
                (219usize, 268435454usize),
                (6usize, 268435454usize),
                (8usize, 268435454usize),
                (167usize, 268435454usize),
                (219usize, 1744830467usize),
                (8usize, 268435454usize),
                (167usize, 1744830467usize),
                (219usize, 268435454usize),
                (7usize, 268435454usize),
                (8usize, 1744830467usize),
                (219usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(24usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (9usize, 1744830467usize),
                (168usize, 268435454usize),
                (220usize, 268435454usize),
                (9usize, 268435454usize),
                (168usize, 1744830467usize),
                (220usize, 268435454usize),
                (9usize, 268435454usize),
                (168usize, 268435454usize),
                (220usize, 1744830467usize),
                (9usize, 268435454usize),
                (168usize, 1744830467usize),
                (220usize, 268435454usize),
                (9usize, 1744830467usize),
                (220usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(24usize, 268435454usize), (25usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (10usize, 1744830467usize),
                (173usize, 268435454usize),
                (223usize, 268435454usize),
                (10usize, 268435454usize),
                (173usize, 1744830467usize),
                (223usize, 268435454usize),
                (10usize, 268435454usize),
                (173usize, 268435454usize),
                (223usize, 1744830467usize),
                (10usize, 268435454usize),
                (173usize, 1744830467usize),
                (223usize, 268435454usize),
                (10usize, 1744830467usize),
                (223usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(25usize, 268435454usize), (26usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (11usize, 1744830467usize),
                (174usize, 268435454usize),
                (224usize, 268435454usize),
                (11usize, 268435454usize),
                (174usize, 1744830467usize),
                (224usize, 268435454usize),
                (11usize, 268435454usize),
                (174usize, 268435454usize),
                (224usize, 1744830467usize),
                (11usize, 268435454usize),
                (174usize, 1744830467usize),
                (224usize, 268435454usize),
                (11usize, 1744830467usize),
                (224usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(26usize, 268435454usize), (27usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (12usize, 1744830467usize),
                (179usize, 268435454usize),
                (227usize, 268435454usize),
                (12usize, 268435454usize),
                (179usize, 1744830467usize),
                (227usize, 268435454usize),
                (12usize, 268435454usize),
                (179usize, 268435454usize),
                (227usize, 1744830467usize),
                (12usize, 268435454usize),
                (179usize, 1744830467usize),
                (227usize, 268435454usize),
                (12usize, 1744830467usize),
                (227usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(27usize, 268435454usize), (28usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (13usize, 1744830467usize),
                (180usize, 268435454usize),
                (228usize, 268435454usize),
                (13usize, 268435454usize),
                (180usize, 1744830467usize),
                (228usize, 268435454usize),
                (13usize, 268435454usize),
                (180usize, 268435454usize),
                (228usize, 1744830467usize),
                (13usize, 268435454usize),
                (180usize, 1744830467usize),
                (228usize, 268435454usize),
                (13usize, 1744830467usize),
                (228usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(28usize, 268435454usize), (29usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (14usize, 1744830467usize),
                (185usize, 268435454usize),
                (231usize, 268435454usize),
                (14usize, 268435454usize),
                (185usize, 1744830467usize),
                (231usize, 268435454usize),
                (14usize, 268435454usize),
                (185usize, 268435454usize),
                (231usize, 1744830467usize),
                (14usize, 268435454usize),
                (185usize, 1744830467usize),
                (231usize, 268435454usize),
                (14usize, 1744830467usize),
                (231usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(29usize, 268435454usize), (30usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (15usize, 1744830467usize),
                (186usize, 268435454usize),
                (232usize, 268435454usize),
                (15usize, 268435454usize),
                (186usize, 1744830467usize),
                (232usize, 268435454usize),
                (15usize, 268435454usize),
                (186usize, 268435454usize),
                (232usize, 1744830467usize),
                (15usize, 268435454usize),
                (186usize, 1744830467usize),
                (232usize, 268435454usize),
                (15usize, 1744830467usize),
                (232usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(30usize, 268435454usize), (31usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (16usize, 1744830467usize),
                (191usize, 268435454usize),
                (235usize, 268435454usize),
                (16usize, 268435454usize),
                (191usize, 1744830467usize),
                (235usize, 268435454usize),
                (16usize, 268435454usize),
                (191usize, 268435454usize),
                (235usize, 1744830467usize),
                (16usize, 268435454usize),
                (191usize, 1744830467usize),
                (235usize, 268435454usize),
                (16usize, 1744830467usize),
                (235usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(31usize, 268435454usize), (32usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (17usize, 1744830467usize),
                (192usize, 268435454usize),
                (236usize, 268435454usize),
                (17usize, 268435454usize),
                (192usize, 1744830467usize),
                (236usize, 268435454usize),
                (17usize, 268435454usize),
                (192usize, 268435454usize),
                (236usize, 1744830467usize),
                (17usize, 268435454usize),
                (192usize, 1744830467usize),
                (236usize, 268435454usize),
                (17usize, 1744830467usize),
                (236usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(32usize, 268435454usize), (33usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (18usize, 1744830467usize),
                (197usize, 268435454usize),
                (239usize, 268435454usize),
                (18usize, 268435454usize),
                (197usize, 1744830467usize),
                (239usize, 268435454usize),
                (18usize, 268435454usize),
                (197usize, 268435454usize),
                (239usize, 1744830467usize),
                (18usize, 268435454usize),
                (197usize, 1744830467usize),
                (239usize, 268435454usize),
                (18usize, 1744830467usize),
                (239usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(33usize, 268435454usize), (34usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (19usize, 1744830467usize),
                (198usize, 268435454usize),
                (240usize, 268435454usize),
                (19usize, 268435454usize),
                (198usize, 1744830467usize),
                (240usize, 268435454usize),
                (19usize, 268435454usize),
                (198usize, 268435454usize),
                (240usize, 1744830467usize),
                (19usize, 268435454usize),
                (198usize, 1744830467usize),
                (240usize, 268435454usize),
                (19usize, 1744830467usize),
                (240usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(34usize, 268435454usize), (35usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (20usize, 1744830467usize),
                (203usize, 268435454usize),
                (243usize, 268435454usize),
                (20usize, 268435454usize),
                (203usize, 1744830467usize),
                (243usize, 268435454usize),
                (20usize, 268435454usize),
                (203usize, 268435454usize),
                (243usize, 1744830467usize),
                (20usize, 268435454usize),
                (203usize, 1744830467usize),
                (243usize, 268435454usize),
                (20usize, 1744830467usize),
                (243usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(35usize, 268435454usize), (36usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (21usize, 1744830467usize),
                (204usize, 268435454usize),
                (244usize, 268435454usize),
                (21usize, 268435454usize),
                (204usize, 1744830467usize),
                (244usize, 268435454usize),
                (21usize, 268435454usize),
                (204usize, 268435454usize),
                (244usize, 1744830467usize),
                (21usize, 268435454usize),
                (204usize, 1744830467usize),
                (244usize, 268435454usize),
                (21usize, 1744830467usize),
                (244usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(36usize, 268435454usize), (37usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (22usize, 1744830467usize),
                (209usize, 268435454usize),
                (247usize, 268435454usize),
                (22usize, 268435454usize),
                (209usize, 1744830467usize),
                (247usize, 268435454usize),
                (22usize, 268435454usize),
                (209usize, 268435454usize),
                (247usize, 1744830467usize),
                (22usize, 268435454usize),
                (209usize, 1744830467usize),
                (247usize, 268435454usize),
                (22usize, 1744830467usize),
                (247usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(37usize, 268435454usize), (38usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (23usize, 1744830467usize),
                (210usize, 268435454usize),
                (248usize, 268435454usize),
                (23usize, 268435454usize),
                (210usize, 1744830467usize),
                (248usize, 268435454usize),
                (23usize, 268435454usize),
                (210usize, 268435454usize),
                (248usize, 1744830467usize),
                (23usize, 268435454usize),
                (210usize, 1744830467usize),
                (248usize, 268435454usize),
                (23usize, 1744830467usize),
                (248usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(38usize, 268435454usize), (39usize, 1744970275usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 2usize] = [(40usize, 2usize), (56usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (167usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(104usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (40usize, 4usize),
                (41usize, 2usize),
                (56usize, 2usize),
                (57usize, 1usize),
                (167usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (72usize, 2013200385usize),
                (104usize, 65536usize),
                (105usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 8usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (73usize, 2013200385usize),
                (105usize, 65536usize),
                (106usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 11usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 24usize] = [
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (74usize, 2013200385usize),
                (106usize, 65536usize),
                (107usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 14usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (75usize, 2013200385usize),
                (107usize, 65536usize),
                (108usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 17usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (76usize, 2013200385usize),
                (108usize, 65536usize),
                (109usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 20usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 45usize] = [
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (77usize, 2013200385usize),
                (109usize, 65536usize),
                (110usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 23usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 52usize] = [
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (78usize, 2013200385usize),
                (110usize, 65536usize),
                (111usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 26usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 59usize] = [
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (79usize, 2013200385usize),
                (111usize, 65536usize),
                (112usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 29usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 66usize] = [
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (80usize, 2013200385usize),
                (112usize, 65536usize),
                (113usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 32usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 73usize] = [
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (81usize, 2013200385usize),
                (113usize, 65536usize),
                (114usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 35usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 80usize] = [
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (82usize, 2013200385usize),
                (114usize, 65536usize),
                (115usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 38usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 87usize] = [
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (83usize, 2013200385usize),
                (115usize, 65536usize),
                (116usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 41usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 94usize] = [
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (84usize, 2013200385usize),
                (116usize, 65536usize),
                (117usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 44usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 101usize] = [
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (85usize, 2013200385usize),
                (117usize, 65536usize),
                (118usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 47usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 1usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 108usize] = [
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (56usize, 1744830467usize),
                (219usize, 268435454usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (167usize, 268435454usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (86usize, 2013200385usize),
                (118usize, 65536usize),
                (119usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 48usize] = [
                (40usize, 2usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (56usize, 1usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (167usize, 1usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 109usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (219usize, 2013200385usize),
                (220usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (167usize, 2013200385usize),
                (168usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
                (219usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (87usize, 2013200385usize),
                (119usize, 65536usize),
                (120usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 45usize] = [
                (41usize, 2usize),
                (42usize, 4usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (57usize, 1usize),
                (58usize, 2usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (168usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 102usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (220usize, 2013200385usize),
                (223usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (168usize, 2013200385usize),
                (173usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
                (220usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (88usize, 2013200385usize),
                (120usize, 65536usize),
                (121usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 42usize] = [
                (42usize, 2usize),
                (43usize, 4usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (58usize, 1usize),
                (59usize, 2usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 95usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (223usize, 2013200385usize),
                (224usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
                (223usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (89usize, 2013200385usize),
                (121usize, 65536usize),
                (122usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 39usize] = [
                (43usize, 2usize),
                (44usize, 4usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (59usize, 1usize),
                (60usize, 2usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (174usize, 1usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 88usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (224usize, 2013200385usize),
                (227usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (174usize, 2013200385usize),
                (179usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
                (224usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (90usize, 2013200385usize),
                (122usize, 65536usize),
                (123usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 36usize] = [
                (44usize, 2usize),
                (45usize, 4usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (60usize, 1usize),
                (61usize, 2usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (179usize, 1usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 81usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (227usize, 2013200385usize),
                (228usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (179usize, 2013200385usize),
                (180usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
                (227usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (91usize, 2013200385usize),
                (123usize, 65536usize),
                (124usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 33usize] = [
                (45usize, 2usize),
                (46usize, 4usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (61usize, 1usize),
                (62usize, 2usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (180usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 74usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (228usize, 2013200385usize),
                (231usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (180usize, 2013200385usize),
                (185usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
                (228usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (92usize, 2013200385usize),
                (124usize, 65536usize),
                (125usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 30usize] = [
                (46usize, 2usize),
                (47usize, 4usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (62usize, 1usize),
                (63usize, 2usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 67usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (231usize, 2013200385usize),
                (232usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
                (231usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (93usize, 2013200385usize),
                (125usize, 65536usize),
                (126usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 27usize] = [
                (47usize, 2usize),
                (48usize, 4usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (63usize, 1usize),
                (64usize, 2usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (186usize, 1usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 60usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (232usize, 2013200385usize),
                (235usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (186usize, 2013200385usize),
                (191usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
                (232usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (94usize, 2013200385usize),
                (126usize, 65536usize),
                (127usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 24usize] = [
                (48usize, 2usize),
                (49usize, 4usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (64usize, 1usize),
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (191usize, 1usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 53usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (235usize, 2013200385usize),
                (236usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (191usize, 2013200385usize),
                (192usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
                (235usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (95usize, 2013200385usize),
                (127usize, 65536usize),
                (128usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 21usize] = [
                (49usize, 2usize),
                (50usize, 4usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (65usize, 1usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (192usize, 1usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (236usize, 2013200385usize),
                (239usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (192usize, 2013200385usize),
                (197usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
                (236usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (96usize, 2013200385usize),
                (128usize, 65536usize),
                (129usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 18usize] = [
                (50usize, 2usize),
                (51usize, 4usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (66usize, 1usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (197usize, 1usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 39usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (239usize, 2013200385usize),
                (240usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
                (239usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (97usize, 2013200385usize),
                (129usize, 65536usize),
                (130usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 15usize] = [
                (51usize, 2usize),
                (52usize, 4usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (67usize, 1usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (198usize, 1usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 32usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (240usize, 2013200385usize),
                (243usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (198usize, 2013200385usize),
                (203usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
                (240usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (98usize, 2013200385usize),
                (130usize, 65536usize),
                (131usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 12usize] = [
                (52usize, 2usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (68usize, 1usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (203usize, 1usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 25usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (243usize, 2013200385usize),
                (244usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
                (243usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (99usize, 2013200385usize),
                (131usize, 65536usize),
                (132usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 9usize] = [
                (53usize, 2usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (69usize, 1usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (204usize, 1usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (244usize, 2013200385usize),
                (247usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (204usize, 2013200385usize),
                (209usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
                (244usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (100usize, 2013200385usize),
                (132usize, 65536usize),
                (133usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 6usize] = [
                (54usize, 2usize),
                (55usize, 4usize),
                (70usize, 1usize),
                (71usize, 2usize),
                (209usize, 1usize),
                (210usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 11usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (247usize, 2013200385usize),
                (248usize, 268435454usize),
                (210usize, 2013200385usize),
                (209usize, 2013200385usize),
                (210usize, 268435454usize),
                (248usize, 65536usize),
                (247usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (101usize, 2013200385usize),
                (133usize, 65536usize),
                (134usize, 1744830467usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 3usize] =
                [(55usize, 2usize), (71usize, 1usize), (210usize, 1usize)];
            const VAL_QI: [(usize, usize); 4usize] = [
                (71usize, 65536usize),
                (248usize, 2013200385usize),
                (210usize, 2013200385usize),
                (248usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (102usize, 2013200385usize),
                (103usize, 1744830467usize),
                (134usize, 65536usize),
            ];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (8usize, 268435454usize),
                (8usize, 268435454usize),
                (8usize, 268435454usize),
                (72usize, 268435454usize),
                (88usize, 268435454usize),
                (167usize, 268435454usize),
                (8usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(169usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (9usize, 268435454usize),
                (9usize, 268435454usize),
                (9usize, 268435454usize),
                (73usize, 268435454usize),
                (89usize, 268435454usize),
                (168usize, 268435454usize),
                (9usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(170usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (10usize, 268435454usize),
                (10usize, 268435454usize),
                (10usize, 268435454usize),
                (74usize, 268435454usize),
                (90usize, 268435454usize),
                (173usize, 268435454usize),
                (10usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(175usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (11usize, 268435454usize),
                (11usize, 268435454usize),
                (11usize, 268435454usize),
                (75usize, 268435454usize),
                (91usize, 268435454usize),
                (174usize, 268435454usize),
                (11usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(176usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (12usize, 268435454usize),
                (12usize, 268435454usize),
                (12usize, 268435454usize),
                (76usize, 268435454usize),
                (92usize, 268435454usize),
                (179usize, 268435454usize),
                (12usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(181usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (13usize, 268435454usize),
                (13usize, 268435454usize),
                (13usize, 268435454usize),
                (77usize, 268435454usize),
                (93usize, 268435454usize),
                (180usize, 268435454usize),
                (13usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(182usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (14usize, 268435454usize),
                (14usize, 268435454usize),
                (14usize, 268435454usize),
                (78usize, 268435454usize),
                (94usize, 268435454usize),
                (185usize, 268435454usize),
                (14usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(187usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (15usize, 268435454usize),
                (15usize, 268435454usize),
                (15usize, 268435454usize),
                (79usize, 268435454usize),
                (95usize, 268435454usize),
                (186usize, 268435454usize),
                (15usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(188usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (16usize, 268435454usize),
                (16usize, 268435454usize),
                (16usize, 268435454usize),
                (80usize, 268435454usize),
                (96usize, 268435454usize),
                (191usize, 268435454usize),
                (16usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(193usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (17usize, 268435454usize),
                (17usize, 268435454usize),
                (17usize, 268435454usize),
                (81usize, 268435454usize),
                (97usize, 268435454usize),
                (192usize, 268435454usize),
                (17usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(194usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (18usize, 268435454usize),
                (18usize, 268435454usize),
                (18usize, 268435454usize),
                (82usize, 268435454usize),
                (98usize, 268435454usize),
                (197usize, 268435454usize),
                (18usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(199usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (19usize, 268435454usize),
                (19usize, 268435454usize),
                (19usize, 268435454usize),
                (83usize, 268435454usize),
                (99usize, 268435454usize),
                (198usize, 268435454usize),
                (19usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(200usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (20usize, 268435454usize),
                (20usize, 268435454usize),
                (20usize, 268435454usize),
                (84usize, 268435454usize),
                (100usize, 268435454usize),
                (203usize, 268435454usize),
                (20usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(205usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (21usize, 268435454usize),
                (21usize, 268435454usize),
                (21usize, 268435454usize),
                (85usize, 268435454usize),
                (101usize, 268435454usize),
                (204usize, 268435454usize),
                (21usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(206usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (22usize, 268435454usize),
                (22usize, 268435454usize),
                (22usize, 268435454usize),
                (86usize, 268435454usize),
                (102usize, 268435454usize),
                (209usize, 268435454usize),
                (22usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(211usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 7usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (23usize, 268435454usize),
                (23usize, 268435454usize),
                (23usize, 268435454usize),
                (87usize, 268435454usize),
                (103usize, 268435454usize),
                (210usize, 268435454usize),
                (23usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(212usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(39usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(136usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(136usize, 268435454usize), (137usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(137usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(138usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 6usize] = [
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (7usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 6usize] = [
                (39usize, 268435454usize),
                (39usize, 268435454usize),
                (39usize, 268435454usize),
                (136usize, 1744830467usize),
                (138usize, 268435454usize),
                (39usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(3usize, 268435454usize), (253usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 1usize] = [(254usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(0usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(0usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(1usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(1usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(2usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(2usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(3usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(3usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(4usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(4usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(5usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(5usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(6usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(6usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(7usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(7usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(7usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(24usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(24usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(24usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(25usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(25usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(25usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(26usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(26usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(26usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(27usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(27usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(27usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(28usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(28usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(28usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(29usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(29usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(29usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(30usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(30usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(30usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(31usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(31usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(31usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(32usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(32usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(32usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(33usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(33usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(33usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(34usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(34usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(34usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(35usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(35usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(35usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(36usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(36usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(36usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(37usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(37usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(37usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(38usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(38usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(38usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(39usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(39usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(39usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(136usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(136usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(136usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(139usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(139usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(139usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(140usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(140usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(140usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(141usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(141usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(141usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(142usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(142usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(142usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(143usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(143usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(143usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(144usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(144usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(144usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(145usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(145usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(145usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(146usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(146usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(146usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(147usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(147usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(147usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(148usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(148usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(148usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(149usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(149usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(149usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(150usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(150usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(150usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(151usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(151usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(151usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(152usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(152usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(152usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(153usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(153usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(153usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(154usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(154usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(154usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(155usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(155usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(155usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(156usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(156usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(156usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(157usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(157usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(157usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_1_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 56usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
        (1usize, 8usize, 0usize),
        (1usize, 9usize, 0usize),
        (1usize, 10usize, 0usize),
        (2usize, 11usize, 12usize),
        (2usize, 13usize, 14usize),
        (2usize, 15usize, 16usize),
        (2usize, 17usize, 18usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (2usize, 23usize, 24usize),
        (2usize, 25usize, 26usize),
        (2usize, 27usize, 28usize),
        (2usize, 29usize, 30usize),
        (2usize, 31usize, 32usize),
        (2usize, 33usize, 34usize),
        (1usize, 35usize, 0usize),
        (1usize, 36usize, 0usize),
        (2usize, 37usize, 38usize),
        (2usize, 39usize, 40usize),
        (2usize, 41usize, 42usize),
        (2usize, 43usize, 44usize),
        (2usize, 45usize, 46usize),
        (2usize, 47usize, 48usize),
        (2usize, 49usize, 50usize),
        (2usize, 51usize, 52usize),
        (2usize, 53usize, 54usize),
        (2usize, 55usize, 56usize),
        (1usize, 57usize, 0usize),
        (1usize, 58usize, 0usize),
        (2usize, 59usize, 60usize),
        (2usize, 61usize, 62usize),
        (2usize, 63usize, 64usize),
        (2usize, 65usize, 66usize),
        (2usize, 67usize, 68usize),
        (2usize, 69usize, 70usize),
        (2usize, 71usize, 72usize),
        (2usize, 73usize, 74usize),
        (2usize, 75usize, 76usize),
        (2usize, 77usize, 78usize),
        (2usize, 79usize, 80usize),
        (2usize, 81usize, 82usize),
        (2usize, 83usize, 84usize),
        (2usize, 85usize, 86usize),
        (2usize, 87usize, 88usize),
        (1usize, 89usize, 0usize),
        (1usize, 90usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 56usize {
        let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = output_claims.get(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = output_claims.get(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = output_claims.get(o1);
            let mut t1 = current_batch;
            field_ops::mul_assign(&mut t1, &c1);
            field_ops::add_assign(&mut combined, &t1);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        }
        i += 1;
    }
    combined
}
#[inline(always)]
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_1_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 11usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 3usize, 0usize, 0usize]),
            (2usize, [5usize, 7usize, 0usize, 0usize]),
            (2usize, [9usize, 11usize, 0usize, 0usize]),
            (2usize, [13usize, 15usize, 0usize, 0usize]),
            (2usize, [17usize, 19usize, 0usize, 0usize]),
            (2usize, [2usize, 4usize, 0usize, 0usize]),
            (2usize, [6usize, 8usize, 0usize, 0usize]),
            (2usize, [10usize, 12usize, 0usize, 0usize]),
            (2usize, [14usize, 16usize, 0usize, 0usize]),
            (2usize, [18usize, 20usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 11usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(21usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(22usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(23usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(24usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(25usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(26usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(27usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(28usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(29usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(30usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(31usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(32usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(33usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(34usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(35usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 1usize] = [(36usize, 268435454usize)];
            let mut b_val = eval_linear_relation(evals, &B_VAL_TERMS, 0usize, j);
            let out0 = {
                field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
                field_ops::add_assign(&mut b_val, &lookup_additive_challenge);
                let mut num = a_val;
                field_ops::add_assign(&mut num, &b_val);
                num
            };
            let out1 = {
                let mut den = a_val;
                field_ops::mul_assign(&mut den, &b_val);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 35usize] = [
            (7usize, [54usize, 55usize, 56usize, 0usize]),
            (8usize, [52usize, 53usize, 50usize, 51usize]),
            (8usize, [48usize, 49usize, 46usize, 47usize]),
            (8usize, [44usize, 45usize, 42usize, 43usize]),
            (1usize, [40usize, 0usize, 0usize, 0usize]),
            (1usize, [41usize, 0usize, 0usize, 0usize]),
            (7usize, [95usize, 96usize, 97usize, 0usize]),
            (8usize, [93usize, 94usize, 91usize, 92usize]),
            (8usize, [89usize, 90usize, 87usize, 88usize]),
            (8usize, [85usize, 86usize, 83usize, 84usize]),
            (8usize, [81usize, 82usize, 79usize, 80usize]),
            (8usize, [77usize, 78usize, 75usize, 76usize]),
            (8usize, [73usize, 74usize, 71usize, 72usize]),
            (8usize, [69usize, 70usize, 67usize, 68usize]),
            (8usize, [65usize, 66usize, 63usize, 64usize]),
            (8usize, [61usize, 62usize, 59usize, 60usize]),
            (1usize, [57usize, 0usize, 0usize, 0usize]),
            (1usize, [58usize, 0usize, 0usize, 0usize]),
            (8usize, [158usize, 159usize, 156usize, 157usize]),
            (8usize, [154usize, 155usize, 152usize, 153usize]),
            (8usize, [150usize, 151usize, 148usize, 149usize]),
            (8usize, [146usize, 147usize, 144usize, 145usize]),
            (8usize, [142usize, 143usize, 140usize, 141usize]),
            (8usize, [138usize, 139usize, 136usize, 137usize]),
            (8usize, [134usize, 135usize, 132usize, 133usize]),
            (8usize, [130usize, 131usize, 128usize, 129usize]),
            (8usize, [126usize, 127usize, 124usize, 125usize]),
            (8usize, [122usize, 123usize, 120usize, 121usize]),
            (8usize, [118usize, 119usize, 116usize, 117usize]),
            (8usize, [114usize, 115usize, 112usize, 113usize]),
            (8usize, [110usize, 111usize, 108usize, 109usize]),
            (8usize, [106usize, 107usize, 104usize, 105usize]),
            (8usize, [102usize, 103usize, 100usize, 101usize]),
            (1usize, [98usize, 0usize, 0usize, 0usize]),
            (1usize, [99usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 35usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(37usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(39usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(37usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(38usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(39usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 1744830467usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_2_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 30usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (2usize, 11usize, 12usize),
        (2usize, 13usize, 14usize),
        (2usize, 15usize, 16usize),
        (2usize, 17usize, 18usize),
        (1usize, 19usize, 0usize),
        (1usize, 20usize, 0usize),
        (2usize, 21usize, 22usize),
        (2usize, 23usize, 24usize),
        (2usize, 25usize, 26usize),
        (2usize, 27usize, 28usize),
        (2usize, 29usize, 30usize),
        (1usize, 31usize, 0usize),
        (1usize, 32usize, 0usize),
        (2usize, 33usize, 34usize),
        (2usize, 35usize, 36usize),
        (2usize, 37usize, 38usize),
        (2usize, 39usize, 40usize),
        (2usize, 41usize, 42usize),
        (2usize, 43usize, 44usize),
        (2usize, 45usize, 46usize),
        (2usize, 47usize, 48usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 30usize {
        let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = output_claims.get(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = output_claims.get(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = output_claims.get(o1);
            let mut t1 = current_batch;
            field_ops::mul_assign(&mut t1, &c1);
            field_ops::add_assign(&mut combined, &t1);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        }
        i += 1;
    }
    combined
}
#[inline(always)]
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_2_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 30usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (1usize, [5usize, 0usize, 0usize, 0usize]),
            (2usize, [6usize, 7usize, 0usize, 0usize]),
            (2usize, [8usize, 9usize, 0usize, 0usize]),
            (1usize, [10usize, 0usize, 0usize, 0usize]),
            (8usize, [35usize, 36usize, 33usize, 34usize]),
            (8usize, [31usize, 32usize, 29usize, 30usize]),
            (8usize, [27usize, 28usize, 25usize, 26usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [15usize, 16usize, 13usize, 14usize]),
            (1usize, [11usize, 0usize, 0usize, 0usize]),
            (1usize, [12usize, 0usize, 0usize, 0usize]),
            (8usize, [57usize, 58usize, 55usize, 56usize]),
            (8usize, [53usize, 54usize, 51usize, 52usize]),
            (8usize, [49usize, 50usize, 47usize, 48usize]),
            (8usize, [45usize, 46usize, 43usize, 44usize]),
            (8usize, [41usize, 42usize, 39usize, 40usize]),
            (1usize, [37usize, 0usize, 0usize, 0usize]),
            (1usize, [38usize, 0usize, 0usize, 0usize]),
            (8usize, [89usize, 90usize, 87usize, 88usize]),
            (8usize, [85usize, 86usize, 83usize, 84usize]),
            (8usize, [81usize, 82usize, 79usize, 80usize]),
            (8usize, [77usize, 78usize, 75usize, 76usize]),
            (8usize, [73usize, 74usize, 71usize, 72usize]),
            (8usize, [69usize, 70usize, 67usize, 68usize]),
            (8usize, [65usize, 66usize, 63usize, 64usize]),
            (8usize, [61usize, 62usize, 59usize, 60usize]),
        ];
        let mut _sg = 0;
        while _sg < 30usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_3_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 17usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (2usize, 5usize, 6usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (1usize, 11usize, 0usize),
        (1usize, 12usize, 0usize),
        (2usize, 13usize, 14usize),
        (2usize, 15usize, 16usize),
        (2usize, 17usize, 18usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (2usize, 23usize, 24usize),
        (2usize, 25usize, 26usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 17usize {
        let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = output_claims.get(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = output_claims.get(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = output_claims.get(o1);
            let mut t1 = current_batch;
            field_ops::mul_assign(&mut t1, &c1);
            field_ops::add_assign(&mut combined, &t1);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        }
        i += 1;
    }
    combined
}
#[inline(always)]
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_3_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 17usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (1usize, [3usize, 0usize, 0usize, 0usize]),
            (2usize, [4usize, 5usize, 0usize, 0usize]),
            (1usize, [6usize, 0usize, 0usize, 0usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [15usize, 16usize, 13usize, 14usize]),
            (8usize, [11usize, 12usize, 9usize, 10usize]),
            (1usize, [7usize, 0usize, 0usize, 0usize]),
            (1usize, [8usize, 0usize, 0usize, 0usize]),
            (8usize, [31usize, 32usize, 29usize, 30usize]),
            (8usize, [27usize, 28usize, 25usize, 26usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [47usize, 48usize, 45usize, 46usize]),
            (8usize, [43usize, 44usize, 41usize, 42usize]),
            (8usize, [39usize, 40usize, 37usize, 38usize]),
            (8usize, [35usize, 36usize, 33usize, 34usize]),
        ];
        let mut _sg = 0;
        while _sg < 17usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_4_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 10usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (2usize, 3usize, 4usize),
        (2usize, 5usize, 6usize),
        (2usize, 7usize, 8usize),
        (1usize, 9usize, 0usize),
        (1usize, 10usize, 0usize),
        (2usize, 11usize, 12usize),
        (2usize, 13usize, 14usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 10usize {
        let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = output_claims.get(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = output_claims.get(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = output_claims.get(o1);
            let mut t1 = current_batch;
            field_ops::mul_assign(&mut t1, &c1);
            field_ops::add_assign(&mut combined, &t1);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        }
        i += 1;
    }
    combined
}
#[inline(always)]
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_4_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 10usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (8usize, [11usize, 12usize, 9usize, 10usize]),
            (8usize, [7usize, 8usize, 5usize, 6usize]),
            (8usize, [17usize, 18usize, 15usize, 16usize]),
            (1usize, [13usize, 0usize, 0usize, 0usize]),
            (1usize, [14usize, 0usize, 0usize, 0usize]),
            (8usize, [25usize, 26usize, 23usize, 24usize]),
            (8usize, [21usize, 22usize, 19usize, 20usize]),
        ];
        let mut _sg = 0;
        while _sg < 10usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_5_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 5usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (2usize, 6usize, 7usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 5usize {
        let (n, o0, o1) = unsafe { *DESCS.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = output_claims.get(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = output_claims.get(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = output_claims.get(o1);
            let mut t1 = current_batch;
            field_ops::mul_assign(&mut t1, &c1);
            field_ops::add_assign(&mut combined, &t1);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        }
        i += 1;
    }
    combined
}
#[inline(always)]
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_5_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 5usize] = [
            (3usize, [1usize, 0usize, 0usize, 0usize]),
            (3usize, [2usize, 0usize, 0usize, 0usize]),
            (8usize, [5usize, 6usize, 3usize, 4usize]),
            (8usize, [9usize, 10usize, 7usize, 8usize]),
            (8usize, [13usize, 14usize, 11usize, 12usize]),
        ];
        let mut _sg = 0;
        while _sg < 5usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
    indices: &[usize],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    let mut _idx = 0usize;
    {
        let si = unsafe { *indices.get_unchecked(_idx) };
        _idx += 1;
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let e2 = unsafe { *es.get_unchecked(2) };
        let e3 = unsafe { *es.get_unchecked(3) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        let mut c0 = bc;
        field_ops::mul_assign(&mut c0, &v01);
        field_ops::add_assign(&mut acc[0], &c0);
        let mut v23 = e2;
        field_ops::mul_assign(&mut v23, &e3);
        let mut c1 = bc;
        field_ops::mul_assign(&mut c1, &v23);
        field_ops::add_assign(&mut acc[1], &c1);
    }
    {
        let si = unsafe { *indices.get_unchecked(_idx) };
        _idx += 1;
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let e2 = unsafe { *es.get_unchecked(2) };
        let e3 = unsafe { *es.get_unchecked(3) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        let mut c0 = bc;
        field_ops::mul_assign(&mut c0, &v01);
        field_ops::add_assign(&mut acc[0], &c0);
        let mut v23 = e2;
        field_ops::mul_assign(&mut v23, &e3);
        let mut c1 = bc;
        field_ops::mul_assign(&mut c1, &v23);
        field_ops::add_assign(&mut acc[1], &c1);
    }
    {
        let si0 = unsafe { *indices.get_unchecked(_idx) };
        let si1 = unsafe { *indices.get_unchecked(_idx + 1) };
        _idx += 2;
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(si0) };
        let v1 = unsafe { evals.get_unchecked(si1) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let si0 = unsafe { *indices.get_unchecked(_idx) };
        let si1 = unsafe { *indices.get_unchecked(_idx + 1) };
        _idx += 2;
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(si0) };
        let v1 = unsafe { evals.get_unchecked(si1) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let si0 = unsafe { *indices.get_unchecked(_idx) };
        let si1 = unsafe { *indices.get_unchecked(_idx + 1) };
        _idx += 2;
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(si0) };
        let v1 = unsafe { evals.get_unchecked(si1) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[allow(
    unused_braces,
    unused_mut,
    unused_variables,
    unused_unsafe,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
pub fn verify_gkr<I: NonDeterminismSource>() -> Result<
    GKRVerifierOutput<
        'static,
        BabyBearExt4,
        GKR_ROUNDS,
        GKR_ADDRS,
        SETUP_CAP_WORDS,
        MEM_CAP_WORDS,
        WIT_CAP_WORDS,
    >,
    GKRVerificationError,
> {
    unsafe {
        let mut transcript_buf = LazyVec::<u32, GKR_TRANSCRIPT_U32>::new();
        {
            let mut i = 0;
            while i < GKR_TRANSCRIPT_U32 {
                transcript_buf.push(I::read_word());
                i += 1;
            }
        }
        let setup_cap: [u32; SETUP_CAP_WORDS] = {
            let src = &transcript_buf.as_slice()
                [CAPS_OFFSET_IN_TRANSCRIPT..CAPS_OFFSET_IN_TRANSCRIPT + SETUP_CAP_WORDS];
            *<&[u32; SETUP_CAP_WORDS]>::try_from(src).unwrap_unchecked()
        };
        let memory_cap: [u32; MEM_CAP_WORDS] = {
            let src = &transcript_buf.as_slice()[CAPS_OFFSET_IN_TRANSCRIPT + SETUP_CAP_WORDS
                ..CAPS_OFFSET_IN_TRANSCRIPT + SETUP_CAP_WORDS + MEM_CAP_WORDS];
            *<&[u32; MEM_CAP_WORDS]>::try_from(src).unwrap_unchecked()
        };
        let witness_cap: [u32; WIT_CAP_WORDS] = {
            let src = &transcript_buf.as_slice()[CAPS_OFFSET_IN_TRANSCRIPT
                + SETUP_CAP_WORDS
                + MEM_CAP_WORDS
                ..CAPS_OFFSET_IN_TRANSCRIPT + SETUP_CAP_WORDS + MEM_CAP_WORDS + WIT_CAP_WORDS];
            *<&[u32; WIT_CAP_WORDS]>::try_from(src).unwrap_unchecked()
        };
        let mut ts =
            TranscriptState::new(Blake2sTranscript::commit_initial(transcript_buf.as_slice()));
        let mut init_challenges = LazyVec::<BabyBearExt4, 3>::new();
        unsafe {
            init_challenges.set_len(3);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let constraints_batch_challenge = *init_challenges.get(2);
        let (linearization_challenges, permutation_argument_additive_part) = {
            let ext_start = 0usize;
            let num_lin = 6usize;
            let mut lin = LazyVec::<BabyBearExt4, 6usize>::new();
            let mut i = 0;
            while i < num_lin {
                let base = ext_start + i * EXT_DEGREE;
                let mut arr = LazyVec::<BabyBearField, EXT_DEGREE>::new();
                let mut k = 0;
                while k < EXT_DEGREE {
                    arr.push(BabyBearField::from_raw_repr_with_reduction(
                        *transcript_buf.get(base + k),
                    ));
                    k += 1;
                }
                lin.push(unsafe {
                    core::mem::transmute::<[BabyBearField; EXT_DEGREE], BabyBearExt4>(
                        arr.into_array(),
                    )
                });
                i += 1;
            }
            let add_base = ext_start + num_lin * EXT_DEGREE;
            let mut add_arr = LazyVec::<BabyBearField, EXT_DEGREE>::new();
            let mut k = 0;
            while k < EXT_DEGREE {
                add_arr.push(BabyBearField::from_raw_repr_with_reduction(
                    *transcript_buf.get(add_base + k),
                ));
                k += 1;
            }
            let additive = unsafe {
                core::mem::transmute::<[BabyBearField; EXT_DEGREE], BabyBearExt4>(
                    add_arr.into_array(),
                )
            };
            (unsafe { lin.into_array() }, additive)
        };
        let address_high_bits_shift: u32 = 0u32;
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 128usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>());
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(128usize) };
        let mut all_challenges = LazyVec::<BabyBearExt4, { GKR_ROUNDS + 1 }>::new();
        unsafe {
            all_challenges.set_len(5usize);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, all_challenges.as_mut_slice());
        let batching_challenge = *all_challenges.get(5usize - 1);
        let mut eq_buf = LazyVec::<BabyBearExt4, 16usize>::new();
        let eq_challenges: &[BabyBearExt4; 4usize] = all_challenges.as_slice()[..4usize]
            .try_into()
            .unwrap_unchecked();
        make_eq_poly(eq_challenges, &mut eq_buf);
        let mut prev_claims: LazyVec<BabyBearExt4, GKR_ADDRS> = LazyVec::new();
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[0usize..16usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[16usize..32usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[32usize..48usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[48usize..64usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[64usize..80usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[80usize..96usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[96usize..112usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] = evals_slice[112usize..128usize]
                .try_into()
                .unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        let prev_point = {
            let mut lv = LazyVec::<BabyBearExt4, GKR_ROUNDS>::new();
            for i in 0..4usize {
                lv.push(*all_challenges.get(i));
            }
            unsafe {
                lv.set_len(GKR_ROUNDS);
            }
            unsafe { lv.into_array() }
        };
        let mut state = LayerState {
            prev_point,
            prev_point_len: 4usize,
            prev_claims,
            batching_challenge,
        };
        let mut eval_buf = CommitBuf::<GKR_EVAL_BUF>::new();
        const DIM_REDUCE_INDICES_6: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_7: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_8: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_9: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_10: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_11: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_12: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_13: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_14: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_15: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_16: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_17: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_18: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_19: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_20: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_21: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_22: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        const DIM_REDUCE_INDICES_23: [usize; 8usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
        ];
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 3usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    23usize,
                )?;
            let mut fc_len = 3usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_23,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    23usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 4usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                )?;
            let mut fc_len = 4usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_22,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    22usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 5usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                )?;
            let mut fc_len = 5usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_21,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    21usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 6usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                )?;
            let mut fc_len = 6usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_20,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    20usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 7usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                )?;
            let mut fc_len = 7usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_19,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    19usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 8usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                )?;
            let mut fc_len = 8usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_18,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    18usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 9usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                )?;
            let mut fc_len = 9usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_17,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    17usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 10usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                )?;
            let mut fc_len = 10usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_16,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    16usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 11usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                )?;
            let mut fc_len = 11usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_15,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    15usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 12usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                )?;
            let mut fc_len = 12usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_14,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    14usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 13usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                )?;
            let mut fc_len = 13usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_13,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    13usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 14usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                )?;
            let mut fc_len = 14usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_12,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    12usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 15usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                )?;
            let mut fc_len = 15usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_11,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    11usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 16usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                )?;
            let mut fc_len = 16usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_10,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    10usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 17usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                )?;
            let mut fc_len = 17usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_9,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    9usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 18usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                )?;
            let mut fc_len = 18usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_8,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    8usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_7,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    7usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 20usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 20usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_6,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    6usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        let challenge_powers: [BabyBearExt4; GKR_MAX_POW] = {
            let mut lv = LazyVec::<BabyBearExt4, GKR_MAX_POW>::new();
            let mut pow = BabyBearExt4::ONE;
            for _ in 0..GKR_MAX_POW {
                lv.push(pow);
                field_ops::mul_assign(&mut pow, &constraints_batch_challenge);
            }
            unsafe { lv.into_array() }
        };
        {
            let initial_claim = layer_5_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 15usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(15usize);
                let f = layer_5_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                    &linearization_challenges,
                    permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    5usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<15usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_4_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 27usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(27usize);
                let f = layer_4_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                    &linearization_challenges,
                    permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    4usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<27usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_3_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 49usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(49usize);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                    &linearization_challenges,
                    permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    3usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<49usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_2_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 91usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(91usize);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                    &linearization_challenges,
                    permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    2usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<91usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_1_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 160usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(160usize);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                    &linearization_challenges,
                    permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    1usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<160usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_0_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 263usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(263usize);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                    &linearization_challenges,
                    permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    0usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<263usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        let mut draw_buf = LazyVec::<BabyBearExt4, 1>::new();
        unsafe {
            draw_buf.set_len(1);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut ts, draw_buf.as_mut_slice());
        let whir_batching_challenge = *draw_buf.get(0);
        let grand_product_accumulator: BabyBearExt4 = read_field_el::<I>();
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            base_layer_addrs: LAYER_0_SORTED_ADDRS,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            grand_product_accumulator,
            additional_base_layer_openings: BASE_LAYER_ADDITIONAL_OPENINGS,
            whir_batching_challenge,
            whir_transcript_seed: ts.seed,
            setup_cap,
            memory_cap,
            witness_cap,
        })
    }
}
