use super::common::{
    dot_eq, draw_field_els_into, draw_single_field_el, ext_from_nds, ext_from_raw_words,
    fold_standard_claims, make_eq_poly, read_field_el, read_reduced_field_el,
    verify_final_step_check, verify_sumcheck_rounds, EXT_DEGREE,
};
use super::constants::*;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{GKRVerifierOutput, LayerState, LazyVec};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
use verifier_common::transcript::Blake2sTranscript;
#[inline(always)]
#[allow(unused_variables)]
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
#[allow(unused_variables)]
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
#[allow(unused_variables)]
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
#[allow(unused_variables)]
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
#[allow(unused_variables)]
unsafe fn layer_0_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 241usize] = [
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
        (2usize, 17usize, 18usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (2usize, 23usize, 24usize),
        (2usize, 25usize, 26usize),
        (2usize, 27usize, 28usize),
        (2usize, 29usize, 30usize),
        (2usize, 31usize, 32usize),
        (2usize, 33usize, 34usize),
        (2usize, 35usize, 36usize),
        (2usize, 37usize, 38usize),
        (2usize, 39usize, 40usize),
        (2usize, 41usize, 42usize),
        (2usize, 43usize, 44usize),
        (2usize, 45usize, 46usize),
        (1usize, 47usize, 0usize),
        (2usize, 48usize, 49usize),
        (2usize, 50usize, 51usize),
        (2usize, 52usize, 53usize),
        (2usize, 54usize, 55usize),
        (2usize, 56usize, 57usize),
        (2usize, 58usize, 59usize),
        (2usize, 60usize, 61usize),
        (2usize, 62usize, 63usize),
        (2usize, 64usize, 65usize),
        (2usize, 66usize, 67usize),
        (2usize, 68usize, 69usize),
        (2usize, 70usize, 71usize),
        (2usize, 72usize, 73usize),
        (2usize, 74usize, 75usize),
        (2usize, 76usize, 77usize),
        (2usize, 78usize, 79usize),
        (2usize, 80usize, 81usize),
        (2usize, 82usize, 83usize),
        (2usize, 84usize, 85usize),
        (2usize, 86usize, 87usize),
        (2usize, 88usize, 89usize),
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
    while i < 241usize {
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
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
            [(1usize, [263usize, 0usize, 0usize, 0usize])];
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
                [3usize, 2usize, 175usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 176usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 177usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 178usize, 0usize, 0usize, 0usize],
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
                [3usize, 2usize, 181usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 182usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 183usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 184usize, 0usize, 0usize, 0usize],
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
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 179usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 180usize, 0usize, 0usize, 0usize],
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
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 183usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 184usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 189usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 185usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 186usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    189usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 192usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 193usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 194usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 195usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 189usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 190usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 191usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    189usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 196usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 197usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 202usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 198usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 199usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 200usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 201usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    202usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 205usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 206usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 207usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 208usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 202usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 203usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 204usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    202usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 209usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 210usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 215usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 211usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 212usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 213usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 214usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    215usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 218usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 219usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 220usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 221usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 215usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 216usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 217usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    215usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 222usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 223usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 228usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 224usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 225usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 226usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 227usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    228usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 231usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 232usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 233usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 234usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 228usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 229usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 230usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    228usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 235usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 236usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 241usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 237usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 238usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 239usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 240usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    241usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 244usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 245usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 246usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 247usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 241usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 242usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 243usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    241usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 248usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 249usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 254usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 250usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 251usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 252usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 253usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    254usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 257usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 258usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 259usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 260usize, 0usize, 0usize, 0usize],
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
                [6usize, 0usize, 183usize, 254usize, 0usize, 134217711usize],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 255usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 256usize, 0usize, 0usize, 0usize],
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
                [
                    6usize,
                    0usize,
                    183usize,
                    254usize,
                    1073741816usize,
                    134217711usize,
                ],
                [3usize, 1usize, 184usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 264usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 261usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 262usize, 0usize, 0usize, 0usize],
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
            const VAL_OPS: [[usize; 6]; 4usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 2013261665usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 264usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 265usize, 0usize, 0usize, 0usize],
            ];
            let mut val = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &VAL_OPS,
                j,
            );
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_OPS: [[usize; 6]; 2usize] = [
                [0usize, 0usize, 0usize, 0usize, 0usize, 0usize],
                [4usize, 0usize, 2013261665usize, 0usize, 0usize, 0usize],
            ];
            let mut val = eval_memory_expr(
                evals,
                linearization_challenges,
                permutation_argument_additive_part,
                &VAL_OPS,
                j,
            );
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 1usize] =
            [(6usize, [264usize, 173usize, 274usize, 0usize])];
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(265usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (175usize, 268435454usize),
                (159usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (176usize, 268435454usize),
                (159usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (181usize, 268435454usize),
                (160usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (182usize, 268435454usize),
                (160usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (185usize, 268435454usize),
                (161usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (186usize, 268435454usize),
                (161usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (192usize, 268435454usize),
                (162usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (193usize, 268435454usize),
                (162usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (198usize, 268435454usize),
                (163usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (199usize, 268435454usize),
                (163usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (205usize, 268435454usize),
                (164usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (206usize, 268435454usize),
                (164usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (211usize, 268435454usize),
                (165usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (212usize, 268435454usize),
                (165usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (218usize, 268435454usize),
                (166usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (219usize, 268435454usize),
                (166usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (224usize, 268435454usize),
                (167usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (225usize, 268435454usize),
                (167usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (231usize, 268435454usize),
                (168usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (232usize, 268435454usize),
                (168usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (237usize, 268435454usize),
                (169usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (238usize, 268435454usize),
                (169usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (244usize, 268435454usize),
                (170usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (245usize, 268435454usize),
                (170usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (250usize, 268435454usize),
                (171usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (251usize, 268435454usize),
                (171usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (264usize, 1744830467usize),
                (257usize, 268435454usize),
                (172usize, 133099247usize),
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
                (265usize, 1744830467usize),
                (258usize, 268435454usize),
                (172usize, 1744830467usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (1879048114usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 8usize] = [
                (254usize, 268435454usize),
                (241usize, 268435454usize),
                (228usize, 268435454usize),
                (215usize, 268435454usize),
                (202usize, 268435454usize),
                (189usize, 268435454usize),
                (263usize, 134213359usize),
                (177usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
            let c_val = evals.get_unchecked(174usize)[j];
            const D_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const D_VAL_VL_TERMS: [(usize, usize); 8usize] = [
                (273usize, 268435454usize),
                (272usize, 268435454usize),
                (271usize, 268435454usize),
                (270usize, 268435454usize),
                (269usize, 268435454usize),
                (268usize, 268435454usize),
                (267usize, 268435454usize),
                (266usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (55usize, 268435454usize),
                (47usize, 268435454usize),
                (39usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (56usize, 268435454usize),
                (48usize, 268435454usize),
                (40usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (57usize, 268435454usize),
                (49usize, 268435454usize),
                (41usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (58usize, 268435454usize),
                (50usize, 268435454usize),
                (42usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (59usize, 268435454usize),
                (51usize, 268435454usize),
                (43usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (60usize, 268435454usize),
                (52usize, 268435454usize),
                (44usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (61usize, 268435454usize),
                (53usize, 268435454usize),
                (45usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 134217647usize),
                (1usize, 671088555usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 402653101usize),
                (62usize, 268435454usize),
                (54usize, 268435454usize),
                (46usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (79usize, 268435454usize),
                (71usize, 268435454usize),
                (63usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (80usize, 268435454usize),
                (72usize, 268435454usize),
                (64usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (81usize, 268435454usize),
                (73usize, 268435454usize),
                (65usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (82usize, 268435454usize),
                (74usize, 268435454usize),
                (66usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (83usize, 268435454usize),
                (75usize, 268435454usize),
                (67usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (84usize, 268435454usize),
                (76usize, 268435454usize),
                (68usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (85usize, 268435454usize),
                (77usize, 268435454usize),
                (69usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (86usize, 268435454usize),
                (78usize, 268435454usize),
                (70usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (103usize, 268435454usize),
                (95usize, 268435454usize),
                (87usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (104usize, 268435454usize),
                (96usize, 268435454usize),
                (88usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (105usize, 268435454usize),
                (97usize, 268435454usize),
                (89usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (106usize, 268435454usize),
                (98usize, 268435454usize),
                (90usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (107usize, 268435454usize),
                (99usize, 268435454usize),
                (91usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (108usize, 268435454usize),
                (100usize, 268435454usize),
                (92usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (109usize, 268435454usize),
                (101usize, 268435454usize),
                (93usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 671088555usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 402653101usize),
                (110usize, 268435454usize),
                (102usize, 268435454usize),
                (94usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (127usize, 268435454usize),
                (119usize, 268435454usize),
                (111usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (128usize, 268435454usize),
                (120usize, 268435454usize),
                (112usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (129usize, 268435454usize),
                (121usize, 268435454usize),
                (113usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (130usize, 268435454usize),
                (122usize, 268435454usize),
                (114usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (131usize, 268435454usize),
                (123usize, 268435454usize),
                (115usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (132usize, 268435454usize),
                (124usize, 268435454usize),
                (116usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (133usize, 268435454usize),
                (125usize, 268435454usize),
                (117usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 671088555usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 402653101usize),
                (6usize, 1073741816usize),
                (134usize, 268435454usize),
                (126usize, 268435454usize),
                (118usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (151usize, 268435454usize),
                (143usize, 268435454usize),
                (135usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (152usize, 268435454usize),
                (144usize, 268435454usize),
                (136usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (153usize, 268435454usize),
                (145usize, 268435454usize),
                (137usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (154usize, 268435454usize),
                (146usize, 268435454usize),
                (138usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (155usize, 268435454usize),
                (147usize, 268435454usize),
                (139usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (156usize, 268435454usize),
                (148usize, 268435454usize),
                (140usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (157usize, 268435454usize),
                (149usize, 268435454usize),
                (141usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 8usize] = [
                (0usize, 7usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (0usize, 1073741816usize),
                (1usize, 1073741816usize),
                (2usize, 1073741816usize),
                (3usize, 1073741816usize),
                (4usize, 671088555usize),
                (5usize, 1073741816usize),
                (6usize, 1073741816usize),
                (158usize, 268435454usize),
                (150usize, 268435454usize),
                (142usize, 268435454usize),
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(263usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(263usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(263usize, 1744830467usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(178usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(180usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 16usize] = [
                (1usize, 268435454usize),
                (2usize, 536870908usize),
                (3usize, 805306362usize),
                (4usize, 1073741816usize),
                (5usize, 1342177270usize),
                (6usize, 1610612724usize),
                (8usize, 134217711usize),
                (9usize, 268435422usize),
                (10usize, 402653133usize),
                (11usize, 536870844usize),
                (12usize, 1073741688usize),
                (13usize, 134217455usize),
                (14usize, 268434910usize),
                (15usize, 536869820usize),
                (16usize, 1073739640usize),
                (177usize, 1744830467usize),
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
                (6usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(263usize, 1744830467usize)];
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
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 5usize] = [
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
                (263usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(263usize, 1744830467usize)];
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
                (6usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 7usize] = [
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 7usize] = [
                (0usize, 268435454usize),
                (1usize, 268435454usize),
                (2usize, 268435454usize),
                (3usize, 268435454usize),
                (4usize, 268435454usize),
                (5usize, 268435454usize),
                (6usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 5usize] = [
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 5usize] = [
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
                (263usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 5usize] = [
                (7usize, 268435454usize),
                (8usize, 268435454usize),
                (9usize, 268435454usize),
                (10usize, 268435454usize),
                (11usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 4usize] = [
                (0usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (6usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 4usize] = [
                (11usize, 1610612820usize),
                (11usize, 1610612820usize),
                (11usize, 1610612820usize),
                (11usize, 1073741784usize),
            ];
            const VAL_LN: [(usize, usize); 17usize] = [
                (0usize, 134217711usize),
                (1usize, 536870908usize),
                (2usize, 805306362usize),
                (3usize, 939524073usize),
                (4usize, 1207959527usize),
                (5usize, 1610612724usize),
                (6usize, 1476394981usize),
                (8usize, 134217711usize),
                (9usize, 268435422usize),
                (10usize, 402653133usize),
                (11usize, 536870844usize),
                (12usize, 1073741688usize),
                (13usize, 134217455usize),
                (14usize, 268434910usize),
                (15usize, 536869820usize),
                (16usize, 1073739640usize),
                (179usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(7usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(17usize, 1744830467usize)];
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
            const VAL_QI: [(usize, usize); 1usize] = [(8usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(18usize, 1744830467usize)];
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
            const VAL_QI: [(usize, usize); 1usize] = [(9usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(19usize, 1744830467usize)];
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
            const VAL_QI: [(usize, usize); 1usize] = [(10usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(20usize, 1744830467usize)];
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
            const VAL_QI: [(usize, usize); 1usize] = [(11usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(21usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(7usize, 5usize)];
            const VAL_QI: [(usize, usize); 5usize] = [
                (12usize, 268435454usize),
                (13usize, 536870908usize),
                (14usize, 1073741816usize),
                (15usize, 134217711usize),
                (16usize, 268435422usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(22usize, 1744830467usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (23usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 536853436usize, j);
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (24usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 671036075usize, j);
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (25usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 805218714usize, j);
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (26usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 939401353usize, j);
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
            const VAL_LN: [(usize, usize); 6usize] = [
                (4usize, 268435454usize),
                (17usize, 1744830467usize),
                (18usize, 1744830467usize),
                (19usize, 1744830467usize),
                (20usize, 1744830467usize),
                (21usize, 1744830467usize),
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
                (0usize, 1usize),
                (1usize, 9usize),
                (2usize, 8usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 5usize),
                (18usize, 5usize),
                (19usize, 4usize),
                (20usize, 3usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 41usize] = [
                (187usize, 1744830467usize),
                (1usize, 1744970275usize),
                (2usize, 1476674629usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 1744831011usize),
                (187usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 1744831011usize),
                (200usize, 1744830467usize),
                (187usize, 1744830467usize),
                (187usize, 1744830467usize),
                (187usize, 1744830467usize),
                (213usize, 1744830467usize),
                (18usize, 1744970275usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1075279736usize),
                (40usize, 1744831011usize),
                (18usize, 1744970275usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 1744831011usize),
                (19usize, 270392798usize),
                (20usize, 1077376888usize),
                (21usize, 1345672534usize),
                (40usize, 1744831011usize),
                (20usize, 806984090usize),
                (21usize, 1882263826usize),
                (40usize, 1744831011usize),
                (21usize, 1075279736usize),
                (40usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(39usize, 268435454usize), (40usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (23usize, 1744830467usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
                (252usize, 1744830467usize),
                (200usize, 1744830467usize),
                (187usize, 1744830467usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
                (47usize, 1744830467usize),
                (48usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(47usize, 268435454usize), (48usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 3usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 26usize] = [
                (190usize, 1744830467usize),
                (50usize, 268435454usize),
                (56usize, 1744831011usize),
                (255usize, 1744830467usize),
                (27usize, 1744830467usize),
                (50usize, 268435454usize),
                (56usize, 1744831011usize),
                (190usize, 1744830467usize),
                (190usize, 1744830467usize),
                (242usize, 1744830467usize),
                (27usize, 1744830467usize),
                (50usize, 268435454usize),
                (56usize, 1744831011usize),
                (50usize, 268435454usize),
                (56usize, 1744831011usize),
                (47usize, 268435454usize),
                (55usize, 1744830467usize),
                (56usize, 544usize),
                (49usize, 268435454usize),
                (55usize, 1744830467usize),
                (56usize, 1744831011usize),
                (58usize, 268435454usize),
                (49usize, 268435454usize),
                (55usize, 1744830467usize),
                (56usize, 1744831011usize),
                (58usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(55usize, 268435454usize), (56usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 11usize),
                (2usize, 10usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 7usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 55usize] = [
                (188usize, 1744830467usize),
                (1usize, 1744970275usize),
                (2usize, 1476674629usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (188usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (201usize, 1744830467usize),
                (188usize, 1744830467usize),
                (188usize, 1744830467usize),
                (188usize, 1744830467usize),
                (214usize, 1744830467usize),
                (18usize, 1744970275usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1075279736usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (18usize, 1744970275usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (19usize, 270392798usize),
                (20usize, 1077376888usize),
                (21usize, 1345672534usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (20usize, 806984090usize),
                (21usize, 1882263826usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (21usize, 1075279736usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(41usize, 268435454usize), (42usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (24usize, 1744830467usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
                (253usize, 1744830467usize),
                (201usize, 1744830467usize),
                (188usize, 1744830467usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
                (49usize, 1744830467usize),
                (50usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(49usize, 268435454usize), (50usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 5usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 2usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 33usize] = [
                (191usize, 1744830467usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (256usize, 1744830467usize),
                (28usize, 1744830467usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (191usize, 1744830467usize),
                (191usize, 1744830467usize),
                (243usize, 1744830467usize),
                (28usize, 1744830467usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (48usize, 268435454usize),
                (58usize, 1744831011usize),
                (50usize, 268435454usize),
                (55usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (50usize, 268435454usize),
                (55usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(57usize, 268435454usize), (58usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 11usize),
                (2usize, 10usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 7usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 55usize] = [
                (194usize, 1744830467usize),
                (1usize, 1744970275usize),
                (2usize, 1476674629usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (194usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (207usize, 1744830467usize),
                (194usize, 1744830467usize),
                (194usize, 1744830467usize),
                (194usize, 1744830467usize),
                (220usize, 1744830467usize),
                (18usize, 1744970275usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1075279736usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (18usize, 1744970275usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (19usize, 270392798usize),
                (20usize, 1077376888usize),
                (21usize, 1345672534usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (20usize, 806984090usize),
                (21usize, 1882263826usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (21usize, 1075279736usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(43usize, 268435454usize), (44usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (25usize, 1744830467usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
                (259usize, 1744830467usize),
                (207usize, 1744830467usize),
                (194usize, 1744830467usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
                (51usize, 1744830467usize),
                (52usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(51usize, 268435454usize), (52usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 5usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 35usize] = [
                (196usize, 1744830467usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (261usize, 1744830467usize),
                (29usize, 1744830467usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (196usize, 1744830467usize),
                (196usize, 1744830467usize),
                (248usize, 1744830467usize),
                (29usize, 1744830467usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(59usize, 268435454usize), (60usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 11usize),
                (2usize, 10usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 7usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 55usize] = [
                (195usize, 1744830467usize),
                (1usize, 1744970275usize),
                (2usize, 1476674629usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (195usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (208usize, 1744830467usize),
                (195usize, 1744830467usize),
                (195usize, 1744830467usize),
                (195usize, 1744830467usize),
                (221usize, 1744830467usize),
                (18usize, 1744970275usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1075279736usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (18usize, 1744970275usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (19usize, 270392798usize),
                (20usize, 1077376888usize),
                (21usize, 1345672534usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (20usize, 806984090usize),
                (21usize, 1882263826usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (21usize, 1075279736usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(45usize, 268435454usize), (46usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (26usize, 1744830467usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
                (260usize, 1744830467usize),
                (208usize, 1744830467usize),
                (195usize, 1744830467usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
                (53usize, 1744830467usize),
                (54usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(53usize, 268435454usize), (54usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 5usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 35usize] = [
                (197usize, 1744830467usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (262usize, 1744830467usize),
                (30usize, 1744830467usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (197usize, 1744830467usize),
                (197usize, 1744830467usize),
                (249usize, 1744830467usize),
                (30usize, 1744830467usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (50usize, 268435454usize),
                (55usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(61usize, 268435454usize), (62usize, 268434910usize)];
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
            const VAL_LN: [(usize, usize); 6usize] = [
                (4usize, 268435454usize),
                (17usize, 1744830467usize),
                (18usize, 1744830467usize),
                (19usize, 1744830467usize),
                (20usize, 1744830467usize),
                (21usize, 1744830467usize),
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
                (0usize, 1usize),
                (1usize, 8usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 6usize),
                (18usize, 5usize),
                (19usize, 4usize),
                (20usize, 3usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 34usize] = [
                (190usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (64usize, 1744831011usize),
                (213usize, 1744830467usize),
                (239usize, 1744830467usize),
                (200usize, 1744830467usize),
                (200usize, 1744830467usize),
                (200usize, 1744830467usize),
                (200usize, 1744830467usize),
                (17usize, 940083337usize),
                (18usize, 1747067427usize),
                (19usize, 1343575382usize),
                (20usize, 1075279736usize),
                (21usize, 1880166674usize),
                (64usize, 1744831011usize),
                (18usize, 806984090usize),
                (19usize, 1210476135usize),
                (20usize, 942180489usize),
                (21usize, 1747067427usize),
                (64usize, 1744831011usize),
                (19usize, 403492045usize),
                (20usize, 538688444usize),
                (21usize, 1343575382usize),
                (64usize, 1744831011usize),
                (20usize, 135196399usize),
                (21usize, 1075279736usize),
                (64usize, 1744831011usize),
                (21usize, 940083337usize),
                (64usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(63usize, 268435454usize), (64usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (200usize, 1744830467usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
                (27usize, 1744830467usize),
                (252usize, 1744830467usize),
                (213usize, 1744830467usize),
                (27usize, 1744830467usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(71usize, 268435454usize), (72usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 3usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 2usize),
                (20usize, 3usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 26usize] = [
                (27usize, 1744830467usize),
                (27usize, 1744830467usize),
                (74usize, 268435454usize),
                (80usize, 1744831011usize),
                (242usize, 1744830467usize),
                (203usize, 1744830467usize),
                (203usize, 1744830467usize),
                (27usize, 1744830467usize),
                (203usize, 1744830467usize),
                (72usize, 268435454usize),
                (79usize, 1744830467usize),
                (80usize, 1744831011usize),
                (81usize, 268435454usize),
                (72usize, 268435454usize),
                (79usize, 1744830467usize),
                (80usize, 1744831011usize),
                (81usize, 268435454usize),
                (74usize, 268435454usize),
                (80usize, 1744831011usize),
                (71usize, 268435454usize),
                (79usize, 1744830467usize),
                (80usize, 544usize),
                (73usize, 268435454usize),
                (79usize, 1744830467usize),
                (80usize, 1744831011usize),
                (82usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(79usize, 268435454usize), (80usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 10usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (191usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
                (214usize, 1744830467usize),
                (240usize, 1744830467usize),
                (201usize, 1744830467usize),
                (201usize, 1744830467usize),
                (201usize, 1744830467usize),
                (201usize, 1744830467usize),
                (17usize, 940083337usize),
                (18usize, 1747067427usize),
                (19usize, 1343575382usize),
                (20usize, 1075279736usize),
                (21usize, 1880166674usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
                (18usize, 806984090usize),
                (19usize, 1210476135usize),
                (20usize, 942180489usize),
                (21usize, 1747067427usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
                (19usize, 403492045usize),
                (20usize, 538688444usize),
                (21usize, 1343575382usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
                (20usize, 135196399usize),
                (21usize, 1075279736usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
                (21usize, 940083337usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(65usize, 268435454usize), (66usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (201usize, 1744830467usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
                (28usize, 1744830467usize),
                (253usize, 1744830467usize),
                (214usize, 1744830467usize),
                (28usize, 1744830467usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(73usize, 268435454usize), (74usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 3usize),
                (18usize, 3usize),
                (19usize, 4usize),
                (20usize, 2usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 27usize] = [
                (28usize, 1744830467usize),
                (28usize, 1744830467usize),
                (71usize, 268435454usize),
                (80usize, 268435454usize),
                (81usize, 1744830467usize),
                (82usize, 1744831011usize),
                (243usize, 1744830467usize),
                (204usize, 1744830467usize),
                (204usize, 1744830467usize),
                (28usize, 1744830467usize),
                (204usize, 1744830467usize),
                (73usize, 268435454usize),
                (81usize, 1744830467usize),
                (82usize, 544usize),
                (73usize, 268435454usize),
                (81usize, 1744830467usize),
                (82usize, 544usize),
                (71usize, 268435454usize),
                (80usize, 268435454usize),
                (81usize, 1744830467usize),
                (82usize, 1744831011usize),
                (72usize, 268435454usize),
                (82usize, 1744831011usize),
                (74usize, 268435454usize),
                (79usize, 268435454usize),
                (81usize, 1744830467usize),
                (82usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(81usize, 268435454usize), (82usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 10usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (196usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
                (220usize, 1744830467usize),
                (246usize, 1744830467usize),
                (207usize, 1744830467usize),
                (207usize, 1744830467usize),
                (207usize, 1744830467usize),
                (207usize, 1744830467usize),
                (17usize, 940083337usize),
                (18usize, 1747067427usize),
                (19usize, 1343575382usize),
                (20usize, 1075279736usize),
                (21usize, 1880166674usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
                (18usize, 806984090usize),
                (19usize, 1210476135usize),
                (20usize, 942180489usize),
                (21usize, 1747067427usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
                (19usize, 403492045usize),
                (20usize, 538688444usize),
                (21usize, 1343575382usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
                (20usize, 135196399usize),
                (21usize, 1075279736usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
                (21usize, 940083337usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(67usize, 268435454usize), (68usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (207usize, 1744830467usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
                (29usize, 1744830467usize),
                (259usize, 1744830467usize),
                (220usize, 1744830467usize),
                (29usize, 1744830467usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(75usize, 268435454usize), (76usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (29usize, 1744830467usize),
                (29usize, 1744830467usize),
                (72usize, 268435454usize),
                (81usize, 268435454usize),
                (83usize, 1744830467usize),
                (84usize, 1744831011usize),
                (248usize, 1744830467usize),
                (209usize, 1744830467usize),
                (209usize, 1744830467usize),
                (29usize, 1744830467usize),
                (209usize, 1744830467usize),
                (74usize, 268435454usize),
                (79usize, 268435454usize),
                (83usize, 1744830467usize),
                (84usize, 1744831011usize),
                (74usize, 268435454usize),
                (79usize, 268435454usize),
                (83usize, 1744830467usize),
                (84usize, 1744831011usize),
                (72usize, 268435454usize),
                (81usize, 268435454usize),
                (83usize, 1744830467usize),
                (84usize, 1744831011usize),
                (73usize, 268435454usize),
                (82usize, 268435454usize),
                (83usize, 1744830467usize),
                (84usize, 1744831011usize),
                (71usize, 268435454usize),
                (80usize, 268435454usize),
                (83usize, 1744830467usize),
                (84usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(83usize, 268435454usize), (84usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 10usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (197usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
                (221usize, 1744830467usize),
                (247usize, 1744830467usize),
                (208usize, 1744830467usize),
                (208usize, 1744830467usize),
                (208usize, 1744830467usize),
                (208usize, 1744830467usize),
                (17usize, 940083337usize),
                (18usize, 1747067427usize),
                (19usize, 1343575382usize),
                (20usize, 1075279736usize),
                (21usize, 1880166674usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
                (18usize, 806984090usize),
                (19usize, 1210476135usize),
                (20usize, 942180489usize),
                (21usize, 1747067427usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
                (19usize, 403492045usize),
                (20usize, 538688444usize),
                (21usize, 1343575382usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
                (20usize, 135196399usize),
                (21usize, 1075279736usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
                (21usize, 940083337usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(69usize, 268435454usize), (70usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (208usize, 1744830467usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
                (30usize, 1744830467usize),
                (260usize, 1744830467usize),
                (221usize, 1744830467usize),
                (30usize, 1744830467usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(77usize, 268435454usize), (78usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (30usize, 1744830467usize),
                (30usize, 1744830467usize),
                (73usize, 268435454usize),
                (82usize, 268435454usize),
                (85usize, 1744830467usize),
                (86usize, 1744831011usize),
                (249usize, 1744830467usize),
                (210usize, 1744830467usize),
                (210usize, 1744830467usize),
                (30usize, 1744830467usize),
                (210usize, 1744830467usize),
                (71usize, 268435454usize),
                (80usize, 268435454usize),
                (85usize, 1744830467usize),
                (86usize, 1744831011usize),
                (71usize, 268435454usize),
                (80usize, 268435454usize),
                (85usize, 1744830467usize),
                (86usize, 1744831011usize),
                (73usize, 268435454usize),
                (82usize, 268435454usize),
                (85usize, 1744830467usize),
                (86usize, 1744831011usize),
                (74usize, 268435454usize),
                (79usize, 268435454usize),
                (85usize, 1744830467usize),
                (86usize, 1744831011usize),
                (72usize, 268435454usize),
                (81usize, 268435454usize),
                (85usize, 1744830467usize),
                (86usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(85usize, 268435454usize), (86usize, 268434910usize)];
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
            const VAL_LN: [(usize, usize); 6usize] = [
                (4usize, 268435454usize),
                (17usize, 1744830467usize),
                (18usize, 1744830467usize),
                (19usize, 1744830467usize),
                (20usize, 1744830467usize),
                (21usize, 1744830467usize),
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 8usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 6usize),
                (18usize, 5usize),
                (19usize, 4usize),
                (20usize, 3usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 34usize] = [
                (27usize, 1744830467usize),
                (187usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (88usize, 1744831011usize),
                (226usize, 1744830467usize),
                (213usize, 1744830467usize),
                (213usize, 1744830467usize),
                (187usize, 1744830467usize),
                (187usize, 1744830467usize),
                (17usize, 1208378983usize),
                (18usize, 538688444usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1343575382usize),
                (88usize, 1744831011usize),
                (18usize, 1343575382usize),
                (19usize, 405589197usize),
                (20usize, 942180489usize),
                (21usize, 1478771781usize),
                (88usize, 1744831011usize),
                (19usize, 1075279736usize),
                (20usize, 673884843usize),
                (21usize, 1210476135usize),
                (88usize, 1744831011usize),
                (20usize, 1611871028usize),
                (21usize, 1747067427usize),
                (88usize, 1744831011usize),
                (21usize, 135196399usize),
                (88usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(87usize, 268435454usize), (88usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (213usize, 1744830467usize),
                (27usize, 1744830467usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
                (252usize, 1744830467usize),
                (27usize, 1744830467usize),
                (239usize, 1744830467usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(95usize, 268435454usize), (96usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 3usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 25usize] = [
                (31usize, 1744830467usize),
                (190usize, 1744830467usize),
                (31usize, 1744830467usize),
                (98usize, 268435454usize),
                (104usize, 1744831011usize),
                (216usize, 1744830467usize),
                (216usize, 1744830467usize),
                (190usize, 1744830467usize),
                (31usize, 1744830467usize),
                (98usize, 268435454usize),
                (104usize, 1744831011usize),
                (98usize, 268435454usize),
                (104usize, 1744831011usize),
                (96usize, 268435454usize),
                (103usize, 1744830467usize),
                (104usize, 1744831011usize),
                (105usize, 268435454usize),
                (97usize, 268435454usize),
                (103usize, 1744830467usize),
                (104usize, 1744831011usize),
                (106usize, 268435454usize),
                (96usize, 268435454usize),
                (103usize, 1744830467usize),
                (104usize, 1744831011usize),
                (105usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(103usize, 268435454usize), (104usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 10usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (28usize, 1744830467usize),
                (188usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
                (227usize, 1744830467usize),
                (214usize, 1744830467usize),
                (214usize, 1744830467usize),
                (188usize, 1744830467usize),
                (188usize, 1744830467usize),
                (17usize, 1208378983usize),
                (18usize, 538688444usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1343575382usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
                (18usize, 1343575382usize),
                (19usize, 405589197usize),
                (20usize, 942180489usize),
                (21usize, 1478771781usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
                (19usize, 1075279736usize),
                (20usize, 673884843usize),
                (21usize, 1210476135usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
                (20usize, 1611871028usize),
                (21usize, 1747067427usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
                (21usize, 135196399usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(89usize, 268435454usize), (90usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (214usize, 1744830467usize),
                (28usize, 1744830467usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
                (253usize, 1744830467usize),
                (28usize, 1744830467usize),
                (240usize, 1744830467usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(97usize, 268435454usize), (98usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 5usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 3usize),
                (20usize, 4usize),
                (21usize, 3usize),
            ];
            const VAL_QI: [(usize, usize); 29usize] = [
                (32usize, 1744830467usize),
                (191usize, 1744830467usize),
                (32usize, 1744830467usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 1744831011usize),
                (217usize, 1744830467usize),
                (217usize, 1744830467usize),
                (191usize, 1744830467usize),
                (32usize, 1744830467usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 1744831011usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 1744831011usize),
                (97usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 544usize),
                (98usize, 268435454usize),
                (103usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 1744831011usize),
                (97usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 544usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(105usize, 268435454usize), (106usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 10usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (29usize, 1744830467usize),
                (194usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
                (233usize, 1744830467usize),
                (220usize, 1744830467usize),
                (220usize, 1744830467usize),
                (194usize, 1744830467usize),
                (194usize, 1744830467usize),
                (17usize, 1208378983usize),
                (18usize, 538688444usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1343575382usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
                (18usize, 1343575382usize),
                (19usize, 405589197usize),
                (20usize, 942180489usize),
                (21usize, 1478771781usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
                (19usize, 1075279736usize),
                (20usize, 673884843usize),
                (21usize, 1210476135usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
                (20usize, 1611871028usize),
                (21usize, 1747067427usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
                (21usize, 135196399usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(91usize, 268435454usize), (92usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (220usize, 1744830467usize),
                (29usize, 1744830467usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
                (259usize, 1744830467usize),
                (29usize, 1744830467usize),
                (246usize, 1744830467usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(99usize, 268435454usize), (100usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 5usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (33usize, 1744830467usize),
                (196usize, 1744830467usize),
                (33usize, 1744830467usize),
                (96usize, 268435454usize),
                (105usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
                (222usize, 1744830467usize),
                (222usize, 1744830467usize),
                (196usize, 1744830467usize),
                (33usize, 1744830467usize),
                (96usize, 268435454usize),
                (105usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
                (96usize, 268435454usize),
                (105usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
                (98usize, 268435454usize),
                (103usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
                (98usize, 268435454usize),
                (103usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(107usize, 268435454usize), (108usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 10usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (30usize, 1744830467usize),
                (195usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
                (234usize, 1744830467usize),
                (221usize, 1744830467usize),
                (221usize, 1744830467usize),
                (195usize, 1744830467usize),
                (195usize, 1744830467usize),
                (17usize, 1208378983usize),
                (18usize, 538688444usize),
                (19usize, 270392798usize),
                (20usize, 806984090usize),
                (21usize, 1343575382usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
                (18usize, 1343575382usize),
                (19usize, 405589197usize),
                (20usize, 942180489usize),
                (21usize, 1478771781usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
                (19usize, 1075279736usize),
                (20usize, 673884843usize),
                (21usize, 1210476135usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
                (20usize, 1611871028usize),
                (21usize, 1747067427usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
                (21usize, 135196399usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(93usize, 268435454usize), (94usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 2usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (221usize, 1744830467usize),
                (30usize, 1744830467usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
                (260usize, 1744830467usize),
                (30usize, 1744830467usize),
                (247usize, 1744830467usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(101usize, 268435454usize), (102usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 5usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (34usize, 1744830467usize),
                (197usize, 1744830467usize),
                (34usize, 1744830467usize),
                (97usize, 268435454usize),
                (106usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
                (223usize, 1744830467usize),
                (223usize, 1744830467usize),
                (197usize, 1744830467usize),
                (34usize, 1744830467usize),
                (97usize, 268435454usize),
                (106usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
                (97usize, 268435454usize),
                (106usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
                (96usize, 268435454usize),
                (105usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(109usize, 268435454usize), (110usize, 268434910usize)];
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
            const VAL_LN: [(usize, usize); 6usize] = [
                (4usize, 268435454usize),
                (17usize, 1744830467usize),
                (18usize, 1744830467usize),
                (19usize, 1744830467usize),
                (20usize, 1744830467usize),
                (21usize, 1744830467usize),
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
                (0usize, 1usize),
                (1usize, 8usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 6usize),
                (18usize, 5usize),
                (19usize, 4usize),
                (20usize, 3usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 34usize] = [
                (31usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 1343575382usize),
                (18usize, 270392798usize),
                (19usize, 1747067427usize),
                (20usize, 403492045usize),
                (21usize, 1611871028usize),
                (112usize, 1744831011usize),
                (239usize, 1744830467usize),
                (200usize, 1744830467usize),
                (226usize, 1744830467usize),
                (226usize, 1744830467usize),
                (213usize, 1744830467usize),
                (213usize, 1744830467usize),
                (17usize, 1611871028usize),
                (18usize, 137293551usize),
                (19usize, 1613968180usize),
                (20usize, 270392798usize),
                (21usize, 1478771781usize),
                (112usize, 1744831011usize),
                (18usize, 538688444usize),
                (19usize, 540785596usize),
                (20usize, 1210476135usize),
                (21usize, 405589197usize),
                (112usize, 1744831011usize),
                (19usize, 2097152usize),
                (20usize, 673884843usize),
                (21usize, 1882263826usize),
                (112usize, 1744831011usize),
                (20usize, 671787691usize),
                (21usize, 538688444usize),
                (112usize, 1744831011usize),
                (21usize, 1880166674usize),
                (112usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(111usize, 268435454usize), (112usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (226usize, 1744830467usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
                (31usize, 1744830467usize),
                (252usize, 1744830467usize),
                (226usize, 1744830467usize),
                (31usize, 1744830467usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(119usize, 268435454usize), (120usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 3usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 2usize),
                (20usize, 4usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 25usize] = [
                (35usize, 1744830467usize),
                (31usize, 1744830467usize),
                (122usize, 268435454usize),
                (128usize, 1744831011usize),
                (203usize, 1744830467usize),
                (229usize, 1744830467usize),
                (229usize, 1744830467usize),
                (31usize, 1744830467usize),
                (216usize, 1744830467usize),
                (120usize, 268435454usize),
                (127usize, 1744830467usize),
                (128usize, 1744831011usize),
                (129usize, 268435454usize),
                (120usize, 268435454usize),
                (127usize, 1744830467usize),
                (128usize, 1744831011usize),
                (129usize, 268435454usize),
                (122usize, 268435454usize),
                (128usize, 1744831011usize),
                (121usize, 268435454usize),
                (127usize, 1744830467usize),
                (128usize, 1744831011usize),
                (130usize, 268435454usize),
                (122usize, 268435454usize),
                (128usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(127usize, 268435454usize), (128usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 10usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (32usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 1343575382usize),
                (18usize, 270392798usize),
                (19usize, 1747067427usize),
                (20usize, 403492045usize),
                (21usize, 1611871028usize),
                (112usize, 268435454usize),
                (113usize, 1744830467usize),
                (114usize, 1744831011usize),
                (240usize, 1744830467usize),
                (201usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (214usize, 1744830467usize),
                (214usize, 1744830467usize),
                (17usize, 1611871028usize),
                (18usize, 137293551usize),
                (19usize, 1613968180usize),
                (20usize, 270392798usize),
                (21usize, 1478771781usize),
                (112usize, 268435454usize),
                (113usize, 1744830467usize),
                (114usize, 1744831011usize),
                (18usize, 538688444usize),
                (19usize, 540785596usize),
                (20usize, 1210476135usize),
                (21usize, 405589197usize),
                (112usize, 268435454usize),
                (113usize, 1744830467usize),
                (114usize, 1744831011usize),
                (19usize, 2097152usize),
                (20usize, 673884843usize),
                (21usize, 1882263826usize),
                (112usize, 268435454usize),
                (113usize, 1744830467usize),
                (114usize, 1744831011usize),
                (20usize, 671787691usize),
                (21usize, 538688444usize),
                (112usize, 268435454usize),
                (113usize, 1744830467usize),
                (114usize, 1744831011usize),
                (21usize, 1880166674usize),
                (112usize, 268435454usize),
                (113usize, 1744830467usize),
                (114usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(113usize, 268435454usize), (114usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (227usize, 1744830467usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
                (32usize, 1744830467usize),
                (253usize, 1744830467usize),
                (227usize, 1744830467usize),
                (32usize, 1744830467usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(121usize, 268435454usize), (122usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 3usize),
                (18usize, 3usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 29usize] = [
                (36usize, 1744830467usize),
                (32usize, 1744830467usize),
                (119usize, 268435454usize),
                (128usize, 268435454usize),
                (129usize, 1744830467usize),
                (130usize, 1744831011usize),
                (204usize, 1744830467usize),
                (230usize, 1744830467usize),
                (230usize, 1744830467usize),
                (32usize, 1744830467usize),
                (217usize, 1744830467usize),
                (121usize, 268435454usize),
                (129usize, 1744830467usize),
                (130usize, 544usize),
                (121usize, 268435454usize),
                (129usize, 1744830467usize),
                (130usize, 544usize),
                (119usize, 268435454usize),
                (128usize, 268435454usize),
                (129usize, 1744830467usize),
                (130usize, 1744831011usize),
                (122usize, 268435454usize),
                (127usize, 268435454usize),
                (129usize, 1744830467usize),
                (130usize, 1744831011usize),
                (119usize, 268435454usize),
                (128usize, 268435454usize),
                (129usize, 1744830467usize),
                (130usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(129usize, 268435454usize), (130usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 10usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (33usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 1343575382usize),
                (18usize, 270392798usize),
                (19usize, 1747067427usize),
                (20usize, 403492045usize),
                (21usize, 1611871028usize),
                (113usize, 268435454usize),
                (115usize, 1744830467usize),
                (116usize, 1744831011usize),
                (246usize, 1744830467usize),
                (207usize, 1744830467usize),
                (233usize, 1744830467usize),
                (233usize, 1744830467usize),
                (220usize, 1744830467usize),
                (220usize, 1744830467usize),
                (17usize, 1611871028usize),
                (18usize, 137293551usize),
                (19usize, 1613968180usize),
                (20usize, 270392798usize),
                (21usize, 1478771781usize),
                (113usize, 268435454usize),
                (115usize, 1744830467usize),
                (116usize, 1744831011usize),
                (18usize, 538688444usize),
                (19usize, 540785596usize),
                (20usize, 1210476135usize),
                (21usize, 405589197usize),
                (113usize, 268435454usize),
                (115usize, 1744830467usize),
                (116usize, 1744831011usize),
                (19usize, 2097152usize),
                (20usize, 673884843usize),
                (21usize, 1882263826usize),
                (113usize, 268435454usize),
                (115usize, 1744830467usize),
                (116usize, 1744831011usize),
                (20usize, 671787691usize),
                (21usize, 538688444usize),
                (113usize, 268435454usize),
                (115usize, 1744830467usize),
                (116usize, 1744831011usize),
                (21usize, 1880166674usize),
                (113usize, 268435454usize),
                (115usize, 1744830467usize),
                (116usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(115usize, 268435454usize), (116usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (233usize, 1744830467usize),
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
                (33usize, 1744830467usize),
                (259usize, 1744830467usize),
                (233usize, 1744830467usize),
                (33usize, 1744830467usize),
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(123usize, 268435454usize), (124usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (37usize, 1744830467usize),
                (33usize, 1744830467usize),
                (120usize, 268435454usize),
                (129usize, 268435454usize),
                (131usize, 1744830467usize),
                (132usize, 1744831011usize),
                (209usize, 1744830467usize),
                (235usize, 1744830467usize),
                (235usize, 1744830467usize),
                (33usize, 1744830467usize),
                (222usize, 1744830467usize),
                (122usize, 268435454usize),
                (127usize, 268435454usize),
                (131usize, 1744830467usize),
                (132usize, 1744831011usize),
                (122usize, 268435454usize),
                (127usize, 268435454usize),
                (131usize, 1744830467usize),
                (132usize, 1744831011usize),
                (120usize, 268435454usize),
                (129usize, 268435454usize),
                (131usize, 1744830467usize),
                (132usize, 1744831011usize),
                (119usize, 268435454usize),
                (128usize, 268435454usize),
                (131usize, 1744830467usize),
                (132usize, 1744831011usize),
                (120usize, 268435454usize),
                (129usize, 268435454usize),
                (131usize, 1744830467usize),
                (132usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(131usize, 268435454usize), (132usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 10usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (34usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 1343575382usize),
                (18usize, 270392798usize),
                (19usize, 1747067427usize),
                (20usize, 403492045usize),
                (21usize, 1611871028usize),
                (114usize, 268435454usize),
                (117usize, 1744830467usize),
                (118usize, 1744831011usize),
                (247usize, 1744830467usize),
                (208usize, 1744830467usize),
                (234usize, 1744830467usize),
                (234usize, 1744830467usize),
                (221usize, 1744830467usize),
                (221usize, 1744830467usize),
                (17usize, 1611871028usize),
                (18usize, 137293551usize),
                (19usize, 1613968180usize),
                (20usize, 270392798usize),
                (21usize, 1478771781usize),
                (114usize, 268435454usize),
                (117usize, 1744830467usize),
                (118usize, 1744831011usize),
                (18usize, 538688444usize),
                (19usize, 540785596usize),
                (20usize, 1210476135usize),
                (21usize, 405589197usize),
                (114usize, 268435454usize),
                (117usize, 1744830467usize),
                (118usize, 1744831011usize),
                (19usize, 2097152usize),
                (20usize, 673884843usize),
                (21usize, 1882263826usize),
                (114usize, 268435454usize),
                (117usize, 1744830467usize),
                (118usize, 1744831011usize),
                (20usize, 671787691usize),
                (21usize, 538688444usize),
                (114usize, 268435454usize),
                (117usize, 1744830467usize),
                (118usize, 1744831011usize),
                (21usize, 1880166674usize),
                (114usize, 268435454usize),
                (117usize, 1744830467usize),
                (118usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(117usize, 268435454usize), (118usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 2usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (234usize, 1744830467usize),
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
                (34usize, 1744830467usize),
                (260usize, 1744830467usize),
                (234usize, 1744830467usize),
                (34usize, 1744830467usize),
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(125usize, 268435454usize), (126usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 5usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (38usize, 1744830467usize),
                (34usize, 1744830467usize),
                (121usize, 268435454usize),
                (130usize, 268435454usize),
                (133usize, 1744830467usize),
                (134usize, 1744831011usize),
                (210usize, 1744830467usize),
                (236usize, 1744830467usize),
                (236usize, 1744830467usize),
                (34usize, 1744830467usize),
                (223usize, 1744830467usize),
                (119usize, 268435454usize),
                (128usize, 268435454usize),
                (133usize, 1744830467usize),
                (134usize, 1744831011usize),
                (119usize, 268435454usize),
                (128usize, 268435454usize),
                (133usize, 1744830467usize),
                (134usize, 1744831011usize),
                (121usize, 268435454usize),
                (130usize, 268435454usize),
                (133usize, 1744830467usize),
                (134usize, 1744831011usize),
                (120usize, 268435454usize),
                (129usize, 268435454usize),
                (133usize, 1744830467usize),
                (134usize, 1744831011usize),
                (121usize, 268435454usize),
                (130usize, 268435454usize),
                (133usize, 1744830467usize),
                (134usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(133usize, 268435454usize), (134usize, 268434910usize)];
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
            const VAL_LN: [(usize, usize); 6usize] = [
                (4usize, 268435454usize),
                (17usize, 1744830467usize),
                (18usize, 1744830467usize),
                (19usize, 1744830467usize),
                (20usize, 1744830467usize),
                (21usize, 1744830467usize),
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 6usize),
                (18usize, 5usize),
                (19usize, 4usize),
                (20usize, 3usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 27usize] = [
                (35usize, 1744830467usize),
                (213usize, 1744830467usize),
                (226usize, 1744830467usize),
                (239usize, 1744830467usize),
                (239usize, 1744830467usize),
                (200usize, 1744830467usize),
                (187usize, 1744830467usize),
                (17usize, 1476674629usize),
                (18usize, 940083337usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (136usize, 1744831011usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (136usize, 1744831011usize),
                (19usize, 538688444usize),
                (20usize, 405589197usize),
                (21usize, 809081242usize),
                (136usize, 1744831011usize),
                (20usize, 1880166674usize),
                (21usize, 137293551usize),
                (136usize, 1744831011usize),
                (21usize, 270392798usize),
                (136usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(135usize, 268435454usize), (136usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 16usize] = [
                (239usize, 1744830467usize),
                (31usize, 1744830467usize),
                (252usize, 1744830467usize),
                (252usize, 1744830467usize),
                (31usize, 1744830467usize),
                (226usize, 1744830467usize),
                (143usize, 1744830467usize),
                (144usize, 1744831011usize),
                (143usize, 1744830467usize),
                (144usize, 1744831011usize),
                (143usize, 1744830467usize),
                (144usize, 1744831011usize),
                (143usize, 1744830467usize),
                (144usize, 1744831011usize),
                (143usize, 1744830467usize),
                (144usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(143usize, 268435454usize), (144usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 2usize),
                (19usize, 3usize),
                (20usize, 3usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 21usize] = [
                (255usize, 1744830467usize),
                (216usize, 1744830467usize),
                (229usize, 1744830467usize),
                (242usize, 1744830467usize),
                (242usize, 1744830467usize),
                (203usize, 1744830467usize),
                (190usize, 1744830467usize),
                (145usize, 268435454usize),
                (151usize, 1744830467usize),
                (152usize, 1744831011usize),
                (154usize, 268435454usize),
                (146usize, 268435454usize),
                (152usize, 1744831011usize),
                (143usize, 268435454usize),
                (151usize, 1744830467usize),
                (152usize, 544usize),
                (143usize, 268435454usize),
                (151usize, 1744830467usize),
                (152usize, 544usize),
                (146usize, 268435454usize),
                (152usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(151usize, 268435454usize), (152usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 37usize] = [
                (36usize, 1744830467usize),
                (214usize, 1744830467usize),
                (227usize, 1744830467usize),
                (240usize, 1744830467usize),
                (240usize, 1744830467usize),
                (201usize, 1744830467usize),
                (188usize, 1744830467usize),
                (17usize, 1476674629usize),
                (18usize, 940083337usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (136usize, 268435454usize),
                (137usize, 1744830467usize),
                (138usize, 1744831011usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (136usize, 268435454usize),
                (137usize, 1744830467usize),
                (138usize, 1744831011usize),
                (19usize, 538688444usize),
                (20usize, 405589197usize),
                (21usize, 809081242usize),
                (136usize, 268435454usize),
                (137usize, 1744830467usize),
                (138usize, 1744831011usize),
                (20usize, 1880166674usize),
                (21usize, 137293551usize),
                (136usize, 268435454usize),
                (137usize, 1744830467usize),
                (138usize, 1744831011usize),
                (21usize, 270392798usize),
                (136usize, 268435454usize),
                (137usize, 1744830467usize),
                (138usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(137usize, 268435454usize), (138usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 16usize] = [
                (240usize, 1744830467usize),
                (32usize, 1744830467usize),
                (253usize, 1744830467usize),
                (253usize, 1744830467usize),
                (32usize, 1744830467usize),
                (227usize, 1744830467usize),
                (145usize, 1744830467usize),
                (146usize, 1744831011usize),
                (145usize, 1744830467usize),
                (146usize, 1744831011usize),
                (145usize, 1744830467usize),
                (146usize, 1744831011usize),
                (145usize, 1744830467usize),
                (146usize, 1744831011usize),
                (145usize, 1744830467usize),
                (146usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(145usize, 268435454usize), (146usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 23usize] = [
                (256usize, 1744830467usize),
                (217usize, 1744830467usize),
                (230usize, 1744830467usize),
                (243usize, 1744830467usize),
                (243usize, 1744830467usize),
                (204usize, 1744830467usize),
                (191usize, 1744830467usize),
                (146usize, 268435454usize),
                (151usize, 268435454usize),
                (153usize, 1744830467usize),
                (154usize, 1744831011usize),
                (143usize, 268435454usize),
                (152usize, 268435454usize),
                (153usize, 1744830467usize),
                (154usize, 1744831011usize),
                (144usize, 268435454usize),
                (154usize, 1744831011usize),
                (144usize, 268435454usize),
                (154usize, 1744831011usize),
                (143usize, 268435454usize),
                (152usize, 268435454usize),
                (153usize, 1744830467usize),
                (154usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(153usize, 268435454usize), (154usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 37usize] = [
                (37usize, 1744830467usize),
                (220usize, 1744830467usize),
                (233usize, 1744830467usize),
                (246usize, 1744830467usize),
                (246usize, 1744830467usize),
                (207usize, 1744830467usize),
                (194usize, 1744830467usize),
                (17usize, 1476674629usize),
                (18usize, 940083337usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (137usize, 268435454usize),
                (139usize, 1744830467usize),
                (140usize, 1744831011usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (137usize, 268435454usize),
                (139usize, 1744830467usize),
                (140usize, 1744831011usize),
                (19usize, 538688444usize),
                (20usize, 405589197usize),
                (21usize, 809081242usize),
                (137usize, 268435454usize),
                (139usize, 1744830467usize),
                (140usize, 1744831011usize),
                (20usize, 1880166674usize),
                (21usize, 137293551usize),
                (137usize, 268435454usize),
                (139usize, 1744830467usize),
                (140usize, 1744831011usize),
                (21usize, 270392798usize),
                (137usize, 268435454usize),
                (139usize, 1744830467usize),
                (140usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(139usize, 268435454usize), (140usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 16usize] = [
                (246usize, 1744830467usize),
                (33usize, 1744830467usize),
                (259usize, 1744830467usize),
                (259usize, 1744830467usize),
                (33usize, 1744830467usize),
                (233usize, 1744830467usize),
                (147usize, 1744830467usize),
                (148usize, 1744831011usize),
                (147usize, 1744830467usize),
                (148usize, 1744831011usize),
                (147usize, 1744830467usize),
                (148usize, 1744831011usize),
                (147usize, 1744830467usize),
                (148usize, 1744831011usize),
                (147usize, 1744830467usize),
                (148usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(147usize, 268435454usize), (148usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 27usize] = [
                (261usize, 1744830467usize),
                (222usize, 1744830467usize),
                (235usize, 1744830467usize),
                (248usize, 1744830467usize),
                (248usize, 1744830467usize),
                (209usize, 1744830467usize),
                (196usize, 1744830467usize),
                (143usize, 268435454usize),
                (152usize, 268435454usize),
                (155usize, 1744830467usize),
                (156usize, 1744831011usize),
                (144usize, 268435454usize),
                (153usize, 268435454usize),
                (155usize, 1744830467usize),
                (156usize, 1744831011usize),
                (145usize, 268435454usize),
                (154usize, 268435454usize),
                (155usize, 1744830467usize),
                (156usize, 1744831011usize),
                (145usize, 268435454usize),
                (154usize, 268435454usize),
                (155usize, 1744830467usize),
                (156usize, 1744831011usize),
                (144usize, 268435454usize),
                (153usize, 268435454usize),
                (155usize, 1744830467usize),
                (156usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(155usize, 268435454usize), (156usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 8usize),
                (18usize, 7usize),
                (19usize, 6usize),
                (20usize, 5usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 37usize] = [
                (38usize, 1744830467usize),
                (221usize, 1744830467usize),
                (234usize, 1744830467usize),
                (247usize, 1744830467usize),
                (247usize, 1744830467usize),
                (208usize, 1744830467usize),
                (195usize, 1744830467usize),
                (17usize, 1476674629usize),
                (18usize, 940083337usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (138usize, 268435454usize),
                (141usize, 1744830467usize),
                (142usize, 1744831011usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 1343575382usize),
                (21usize, 1747067427usize),
                (138usize, 268435454usize),
                (141usize, 1744830467usize),
                (142usize, 1744831011usize),
                (19usize, 538688444usize),
                (20usize, 405589197usize),
                (21usize, 809081242usize),
                (138usize, 268435454usize),
                (141usize, 1744830467usize),
                (142usize, 1744831011usize),
                (20usize, 1880166674usize),
                (21usize, 137293551usize),
                (138usize, 268435454usize),
                (141usize, 1744830467usize),
                (142usize, 1744831011usize),
                (21usize, 270392798usize),
                (138usize, 268435454usize),
                (141usize, 1744830467usize),
                (142usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(141usize, 268435454usize), (142usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 2usize),
                (18usize, 2usize),
                (19usize, 2usize),
                (20usize, 2usize),
                (21usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 16usize] = [
                (247usize, 1744830467usize),
                (34usize, 1744830467usize),
                (260usize, 1744830467usize),
                (260usize, 1744830467usize),
                (34usize, 1744830467usize),
                (234usize, 1744830467usize),
                (149usize, 1744830467usize),
                (150usize, 1744831011usize),
                (149usize, 1744830467usize),
                (150usize, 1744831011usize),
                (149usize, 1744830467usize),
                (150usize, 1744831011usize),
                (149usize, 1744830467usize),
                (150usize, 1744831011usize),
                (149usize, 1744830467usize),
                (150usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(149usize, 268435454usize), (150usize, 268434910usize)];
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
                (0usize, 1usize),
                (1usize, 1usize),
                (2usize, 1usize),
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (17usize, 4usize),
                (18usize, 4usize),
                (19usize, 4usize),
                (20usize, 4usize),
                (21usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 27usize] = [
                (262usize, 1744830467usize),
                (223usize, 1744830467usize),
                (236usize, 1744830467usize),
                (249usize, 1744830467usize),
                (249usize, 1744830467usize),
                (210usize, 1744830467usize),
                (197usize, 1744830467usize),
                (144usize, 268435454usize),
                (153usize, 268435454usize),
                (157usize, 1744830467usize),
                (158usize, 1744831011usize),
                (145usize, 268435454usize),
                (154usize, 268435454usize),
                (157usize, 1744830467usize),
                (158usize, 1744831011usize),
                (146usize, 268435454usize),
                (151usize, 268435454usize),
                (157usize, 1744830467usize),
                (158usize, 1744831011usize),
                (146usize, 268435454usize),
                (151usize, 268435454usize),
                (157usize, 1744830467usize),
                (158usize, 1744831011usize),
                (145usize, 268435454usize),
                (154usize, 268435454usize),
                (157usize, 1744830467usize),
                (158usize, 1744831011usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(157usize, 268435454usize), (158usize, 268434910usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(200usize, 268435454usize), (203usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(201usize, 268435454usize), (204usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(207usize, 268435454usize), (209usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(208usize, 268435454usize), (210usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(213usize, 268435454usize), (216usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(214usize, 268435454usize), (217usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(221usize, 268435454usize), (223usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(226usize, 268435454usize), (229usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(227usize, 268435454usize), (230usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(233usize, 268435454usize), (235usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(234usize, 268435454usize), (236usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(239usize, 268435454usize), (242usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(240usize, 268435454usize), (243usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(246usize, 268435454usize), (248usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(247usize, 268435454usize), (249usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(200usize, 268435454usize), (203usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(201usize, 268435454usize), (204usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(207usize, 268435454usize), (209usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(208usize, 268435454usize), (210usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(226usize, 268435454usize), (229usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(227usize, 268435454usize), (230usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(233usize, 268435454usize), (235usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(234usize, 268435454usize), (236usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(239usize, 268435454usize), (242usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(240usize, 268435454usize), (243usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(246usize, 268435454usize), (248usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(247usize, 268435454usize), (249usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(187usize, 268435454usize), (190usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(188usize, 268435454usize), (191usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(194usize, 268435454usize), (196usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(195usize, 268435454usize), (197usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(213usize, 268435454usize), (216usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(214usize, 268435454usize), (217usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(221usize, 268435454usize), (223usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(252usize, 268435454usize), (255usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(253usize, 268435454usize), (256usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(259usize, 268435454usize), (261usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(260usize, 268435454usize), (262usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(252usize, 268435454usize), (255usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(253usize, 268435454usize), (256usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(259usize, 268435454usize), (261usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(260usize, 268435454usize), (262usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(252usize, 268435454usize), (255usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(253usize, 268435454usize), (256usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(259usize, 268435454usize), (261usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(260usize, 268435454usize), (262usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(187usize, 268435454usize), (255usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(188usize, 268435454usize), (256usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(194usize, 268435454usize), (261usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(195usize, 268435454usize), (262usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(213usize, 268435454usize), (216usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(214usize, 268435454usize), (217usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(221usize, 268435454usize), (223usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(226usize, 268435454usize), (229usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(227usize, 268435454usize), (230usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(233usize, 268435454usize), (235usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(234usize, 268435454usize), (236usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(226usize, 268435454usize), (229usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(227usize, 268435454usize), (230usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(233usize, 268435454usize), (235usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(234usize, 268435454usize), (236usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(239usize, 268435454usize), (242usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(240usize, 268435454usize), (243usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(246usize, 268435454usize), (248usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(247usize, 268435454usize), (249usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(252usize, 268435454usize), (255usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(253usize, 268435454usize), (256usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(259usize, 268435454usize), (261usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(260usize, 268435454usize), (262usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(8usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(8usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(8usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(9usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(9usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(9usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(10usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(10usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(10usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(11usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(11usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(11usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(12usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(12usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(12usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(13usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(13usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(14usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(14usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(14usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(15usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(15usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(15usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(16usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(16usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(16usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(159usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(159usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(159usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(160usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(160usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(160usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(161usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(161usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(161usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(162usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(162usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(162usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(163usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(163usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(163usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(164usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(164usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(164usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(165usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(165usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(165usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(166usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(166usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(166usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(167usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(167usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(167usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(168usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(168usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(168usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(169usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(169usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(170usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(170usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(171usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(171usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(171usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(172usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(172usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(172usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_1_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 29usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
        (1usize, 8usize, 0usize),
        (2usize, 9usize, 10usize),
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
        (2usize, 35usize, 36usize),
        (2usize, 37usize, 38usize),
        (2usize, 39usize, 40usize),
        (2usize, 41usize, 42usize),
        (2usize, 43usize, 44usize),
        (1usize, 45usize, 0usize),
        (1usize, 46usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 29usize {
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 29usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 3usize, 0usize, 0usize]),
            (2usize, [5usize, 7usize, 0usize, 0usize]),
            (2usize, [9usize, 11usize, 0usize, 0usize]),
            (2usize, [13usize, 15usize, 0usize, 0usize]),
            (2usize, [2usize, 4usize, 0usize, 0usize]),
            (2usize, [6usize, 8usize, 0usize, 0usize]),
            (2usize, [10usize, 12usize, 0usize, 0usize]),
            (2usize, [14usize, 16usize, 0usize, 0usize]),
            (7usize, [45usize, 46usize, 47usize, 0usize]),
            (8usize, [43usize, 44usize, 41usize, 42usize]),
            (8usize, [39usize, 40usize, 37usize, 38usize]),
            (8usize, [35usize, 36usize, 33usize, 34usize]),
            (8usize, [31usize, 32usize, 29usize, 30usize]),
            (8usize, [27usize, 28usize, 25usize, 26usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [88usize, 89usize, 86usize, 87usize]),
            (8usize, [84usize, 85usize, 82usize, 83usize]),
            (8usize, [80usize, 81usize, 78usize, 79usize]),
            (8usize, [76usize, 77usize, 74usize, 75usize]),
            (8usize, [72usize, 73usize, 70usize, 71usize]),
            (8usize, [68usize, 69usize, 66usize, 67usize]),
            (8usize, [64usize, 65usize, 62usize, 63usize]),
            (8usize, [60usize, 61usize, 58usize, 59usize]),
            (8usize, [56usize, 57usize, 54usize, 55usize]),
            (8usize, [52usize, 53usize, 50usize, 51usize]),
            (1usize, [48usize, 0usize, 0usize, 0usize]),
            (1usize, [49usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 29usize {
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
#[allow(unused_variables)]
unsafe fn layer_2_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 16usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (2usize, 5usize, 6usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (2usize, 11usize, 12usize),
        (2usize, 13usize, 14usize),
        (2usize, 15usize, 16usize),
        (2usize, 17usize, 18usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (1usize, 23usize, 0usize),
        (1usize, 24usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 16usize {
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 16usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (2usize, [5usize, 6usize, 0usize, 0usize]),
            (2usize, [7usize, 8usize, 0usize, 0usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [15usize, 16usize, 13usize, 14usize]),
            (8usize, [11usize, 12usize, 9usize, 10usize]),
            (8usize, [45usize, 46usize, 43usize, 44usize]),
            (8usize, [41usize, 42usize, 39usize, 40usize]),
            (8usize, [37usize, 38usize, 35usize, 36usize]),
            (8usize, [33usize, 34usize, 31usize, 32usize]),
            (8usize, [29usize, 30usize, 27usize, 28usize]),
            (1usize, [25usize, 0usize, 0usize, 0usize]),
            (1usize, [26usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 16usize {
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
#[allow(unused_variables)]
unsafe fn layer_3_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 8usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (2usize, 3usize, 4usize),
        (2usize, 5usize, 6usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (2usize, 11usize, 12usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 8usize {
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 8usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (8usize, [11usize, 12usize, 9usize, 10usize]),
            (8usize, [7usize, 8usize, 5usize, 6usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [15usize, 16usize, 13usize, 14usize]),
        ];
        let mut _sg = 0;
        while _sg < 8usize {
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
#[allow(unused_variables)]
unsafe fn layer_4_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 6usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 6usize {
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 6usize] = [
            (3usize, [1usize, 0usize, 0usize, 0usize]),
            (3usize, [2usize, 0usize, 0usize, 0usize]),
            (8usize, [5usize, 6usize, 3usize, 4usize]),
            (8usize, [11usize, 12usize, 9usize, 10usize]),
            (1usize, [7usize, 0usize, 0usize, 0usize]),
            (1usize, [8usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 6usize {
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
#[allow(unused_variables)]
unsafe fn layer_5_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 5usize] = [
        (2usize, 0usize, 1usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
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
            (8usize, [6usize, 7usize, 4usize, 5usize]),
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (1usize, [1usize, 0usize, 0usize, 0usize]),
            (1usize, [2usize, 0usize, 0usize, 0usize]),
            (1usize, [3usize, 0usize, 0usize, 0usize]),
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
#[allow(unused_unsafe)]
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
    combined
}
#[inline(always)]
#[allow(unused_unsafe)]
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
    acc
}
#[allow(unused_variables, unused_mut, unused_unsafe)]
pub fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>() -> Result<
    GKRVerifierOutput<'static, BabyBearExt4, GKR_ROUNDS, GKR_ADDRS, TOTAL_CAP_WORDS>,
    E::Error,
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
        let oracle_caps: [u32; TOTAL_CAP_WORDS] = {
            let mut caps = [0u32; TOTAL_CAP_WORDS];
            let src = transcript_buf.as_slice();
            let base = CAPS_OFFSET_IN_TRANSCRIPT;
            let mut dst = 0;
            let mut i = 0;
            while i < NUM_ORACLES {
                let words = ORACLE_CAP_WORDS[i];
                let src_offset = ORACLE_CAP_TRANSCRIPT_OFFSETS[i];
                let mut j = 0;
                while j < words {
                    caps[dst + j] = src[base + src_offset + j];
                    j += 1;
                }
                dst += words;
                i += 1;
            }
            caps
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
                let raw = unsafe {
                    (transcript_buf.as_slice().as_ptr().add(base) as *const [u32; EXT_DEGREE])
                        .as_ref_unchecked()
                };
                lin.push(ext_from_raw_words::<BabyBearField, BabyBearExt4>(raw));
                i += 1;
            }
            let add_base = ext_start + num_lin * EXT_DEGREE;
            let raw = unsafe {
                (transcript_buf.as_slice().as_ptr().add(add_base) as *const [u32; EXT_DEGREE])
                    .as_ref_unchecked()
            };
            let additive = ext_from_raw_words::<BabyBearField, BabyBearExt4>(raw);
            (unsafe { lin.into_array() }, additive)
        };
        let address_high_bits_shift: u32 = 0u32;
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 96usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>());
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(96usize) };
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
        const DIM_REDUCE_INDICES_6: [usize; 6usize] =
            [2usize, 3usize, 4usize, 5usize, 0usize, 1usize];
        const DIM_REDUCE_INDICES_7: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_8: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_9: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_10: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_11: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_12: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_13: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_14: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_15: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_16: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_17: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_18: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_19: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_20: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_21: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_22: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_23: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        {
            let initial_claim =
                dim_reducing_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 3usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    23usize,
                )?;
            let mut fc_len = 3usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_23,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 4usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                )?;
            let mut fc_len = 4usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_22,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 5usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                )?;
            let mut fc_len = 5usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_21,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 6usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                )?;
            let mut fc_len = 6usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_20,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 7usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                )?;
            let mut fc_len = 7usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_19,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 8usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                )?;
            let mut fc_len = 8usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_18,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 9usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                )?;
            let mut fc_len = 9usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_17,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 10usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                )?;
            let mut fc_len = 10usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_16,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 11usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                )?;
            let mut fc_len = 11usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_15,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 12usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                )?;
            let mut fc_len = 12usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_14,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 13usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                )?;
            let mut fc_len = 13usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_13,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 14usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                )?;
            let mut fc_len = 14usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_12,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 15usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                )?;
            let mut fc_len = 15usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_11,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 16usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                )?;
            let mut fc_len = 16usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_10,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 17usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                )?;
            let mut fc_len = 17usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_9,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 18usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                )?;
            let mut fc_len = 18usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_8,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_7,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 20usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_6,
                );
                verify_final_step_check::<E>(
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 8usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
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
                verify_final_step_check::<E>(
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
            fold_standard_claims::<8usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 13usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(13usize);
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
                verify_final_step_check::<E>(
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
            fold_standard_claims::<13usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 25usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(25usize);
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
                verify_final_step_check::<E>(
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
            fold_standard_claims::<25usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 47usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(47usize);
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
                verify_final_step_check::<E>(
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
            fold_standard_claims::<47usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 90usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(90usize);
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
                verify_final_step_check::<E>(
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
            fold_standard_claims::<90usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 275usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(275usize);
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
                verify_final_step_check::<E>(
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
            fold_standard_claims::<275usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        let whir_batching_challenge = draw_single_field_el(&mut ts);
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
            oracle_caps,
        })
    }
}
